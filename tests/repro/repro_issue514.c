/*
 * repro_issue514.c -- Reproduce-first case for OPEN bug #514.
 *
 * Issue: #514 -- "trace_path data_flow mode doesn't surface arg expressions;
 *                NestJS DI patterns defeat ~70% of caller resolution"
 *
 * Sub-claim reproduced: (A) data_flow mode omits argument expressions.
 *
 * Why sub-claim A over sub-claim B (NestJS DI caller resolution):
 *   (A) has a crisp binary assertion: the "e" field either appears in the JSON
 *   output or it does not.  (B) is a statistical claim (~70% failure rate) that
 *   requires a NestJS-specific fixture and a headcount of resolved callers across
 *   many call sites -- impossible to assert precisely in a unit test.  (A) can
 *   be reproduced with a small two-function Python fixture and one strstr check.
 *
 * Root cause:
 *   The MCP schema for trace_path documents data_flow mode as "follow CALLS +
 *   DATA_FLOWS with arg expressions" (mcp.c line 356-357 and 363-364).  Argument
 *   expressions at each call site ARE stored in the graph: pass_parallel.c::
 *   append_args_json serializes each CBMCallArg as {"i":<index>,"e":"<expr>,...}
 *   into the CALLS edge properties_json column.  However,
 *   bfs_to_json_array() (mcp.c ~line 2283) only emits the node fields (name,
 *   qualified_name, hop, risk, is_test) from cbm_node_hop_t.  The edge that
 *   carried the arg expressions is NOT propagated by cbm_store_bfs() into the
 *   cbm_traverse_result_t (cbm_edge_info_t carries only from_name, to_name,
 *   type, confidence -- no properties_json).  So even if the user requests
 *   mode="data_flow", every hop in the response lacks the "args" field and the
 *   individual arg expression text ("e") is permanently absent from the output.
 *
 * Expected (correct) behaviour:
 *   After indexing a two-function Python file where caller() passes a compound
 *   expression (payload_info + 1) to callee(), a trace_path call with
 *   mode="data_flow" and direction="outbound" on "caller" must include the
 *   argument expression text "payload_info" in the response JSON -- either in an
 *   "args" array inside the hop object, or as a standalone "e" field.
 *
 * Actual (buggy) behaviour:
 *   The response is:
 *     {"function":"caller","direction":"outbound","mode":"data_flow",
 *      "callees":[{"name":"callee","qualified_name":"...","hop":1}]}
 *   The hop object contains NO "args" and NO "e"/"arg_expr" field.
 *   strstr(resp, "payload_info") returns NULL.
 *
 * Why RED on current code:
 *   The precondition assertion (CALLS edges >= 1) passes -- edge creation
 *   and arg serialisation in pass_parallel.c are correct.  The final
 *   ASSERT_NOT_NULL(strstr(resp, "payload_info")) FAILS because
 *   bfs_to_json_array() never reads or re-emits edge properties_json, so the
 *   arg expression "payload_info" stored in the CALLS edge is permanently
 *   discarded before it reaches the MCP JSON output.
 *
 * Fix location (not implemented here):
 *   cbm_store_bfs() in src/store/store.c must propagate edge properties_json
 *   into the cbm_traverse_result_t (extend cbm_edge_info_t or cbm_node_hop_t).
 *   bfs_to_json_array() in src/mcp/mcp.c must then emit an "args" field when
 *   mode == "data_flow" and the incoming edge has a non-empty args array.
 */

#include <foundation/compat.h>
#include "test_framework.h"
#include "repro_harness.h"
#include "repro_trace.h"

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

/*
 * Fixture: two Python functions in one file.
 *
 *   def callee(x):
 *       return x * 2
 *
 *   def caller():
 *       result = callee(payload_info + 1)
 *       return result
 *
 * caller() passes the compound expression (payload_info + 1) as the first
 * positional argument to callee().  The extractor captures this as a CBMCallArg
 * with .expr == "payload_info + 1" (or a prefix thereof after sanitization).
 * append_args_json serializes it into the CALLS edge as:
 *   {"args":[{"i":0,"e":"payload_info + 1"}]}
 *
 * The expression token "payload_info" is unique enough to identify in the
 * output: strstr(resp, "payload_info") is the assertion anchor.
 *
 * Python is used here because its CALLS extraction (including arg expressions)
 * is proven reliable -- see repro_issue480.c for the same fixture approach.
 */
static const RFile k_files[] = {
    {
        "service.py",
        "def callee(x):\n"
        "    return x * 2\n"
        "\n"
        "def caller():\n"
        "    result = callee(payload_info + 1)\n"
        "    return result\n"
    }
};

/*
 * TEST: repro_issue514_data_flow_surfaces_arg_expr
 *
 * Precondition (must be GREEN to prove this is a data_flow surfacing bug):
 *   rh_count_edges(store, project, "CALLS") >= 1
 *   If this fires RED, the extractor has a regression unrelated to #514.
 *
 * Failing assertion (RED on current code):
 *   strstr(resp, "payload_info") != NULL
 *   i.e. the argument expression text must appear somewhere in the response.
 */
TEST(repro_issue514_data_flow_surfaces_arg_expr) {
    RProj lp;
    cbm_store_t *store = rh_index_files(&lp, k_files,
                                        (int)(sizeof(k_files) / sizeof(k_files[0])));
    ASSERT_NOT_NULL(store);

    /*
     * Precondition: at least one CALLS edge must exist after indexing.
     * If this fires RED the fixture is broken, not data_flow mode.
     * The caller() -> callee(payload_info + 1) call must produce one edge.
     */
    int calls_count = rh_count_edges(store, lp.project, "CALLS");
    fprintf(stderr,
            "  [514] CALLS edges=%d  (expected>=1; 0=extraction regression)\n",
            calls_count);
    ASSERT_GT(calls_count, 0);

    /*
     * Invoke trace_path with mode="data_flow", direction="outbound" on "caller".
     *
     * Args (matching the trace_path JSON schema in mcp.c ~line 355-374):
     *   function_name  -- "caller": the function that passes the argument
     *   project        -- lp.project: derived from the temp dir
     *   direction      -- "outbound": follow callees (caller -> callee)
     *   depth          -- 2: one hop is enough
     *   mode           -- "data_flow": the mode that promises arg expressions
     *
     * Expected response (correct):
     *   {"function":"caller","direction":"outbound","mode":"data_flow",
     *    "callees":[{"name":"callee","qualified_name":"...","hop":1,
     *                "args":[{"i":0,"e":"payload_info + 1"}]}]}
     *   -- or any JSON structure that includes the string "payload_info".
     *
     * Buggy response:
     *   {"function":"caller","direction":"outbound","mode":"data_flow",
     *    "callees":[{"name":"callee","qualified_name":"...","hop":1}]}
     *   -- no "args", no "e", no "payload_info" anywhere.
     */
    char args[512];
    snprintf(args, sizeof(args),
             "{\"function_name\":\"caller\","
             "\"project\":\"%s\","
             "\"direction\":\"outbound\","
             "\"depth\":2,"
             "\"mode\":\"data_flow\",\"format\":\"json\"}",
             lp.project);

    char *resp = rh_call(&lp, "trace_path", args);
    ASSERT_NOT_NULL(resp);

    fprintf(stderr, "  [514] trace_path data_flow response: %.400s\n", resp);

    yyjson_doc *trace = rh_trace_json(resp);
    ASSERT_NOT_NULL(trace);
    yyjson_val *root = yyjson_doc_get_root(trace);
    ASSERT_NULL(yyjson_obj_get(root, "error"));
    char expected_qn[512];
    yyjson_val *callees = yyjson_obj_get(root, "callees");
    snprintf(expected_qn, sizeof(expected_qn), "%s.service.callee", lp.project);
    yyjson_val *callee = rh_trace_row(callees, expected_qn);
    ASSERT_NOT_NULL(callee);
    ASSERT_EQ(yyjson_get_int(yyjson_arr_get(callee, 1)), 1);
    ASSERT_STR_EQ(yyjson_get_str(yyjson_arr_get(yyjson_obj_get(callees, "cols"), 2)), "args");
    yyjson_val *call_args = yyjson_arr_get(callee, 2);
    ASSERT_EQ(yyjson_arr_size(call_args), 1);
    ASSERT_STR_EQ(yyjson_get_str(yyjson_obj_get(yyjson_arr_get_first(call_args), "e")),
                  "payload_info + 1");
    yyjson_doc_free(trace);

    free(resp);
    rh_cleanup(&lp, store);
    PASS();
}

/*
 * Sub-claim (B), minimal form from the issue thread: a NestJS controller
 * calling a service injected through a constructor parameter property
 * (`constructor(private readonly catService: CatService)`) must produce an
 * inbound caller for CatService.findAll.
 */
static const RFile k_nest_files[] = {
    {"src/cats/cat.service.ts", "export class CatService {\n"
                                "  findAll(): string[] {\n"
                                "    return [\"a\"];\n"
                                "  }\n"
                                "}\n"},
    {"src/cats/cat.controller.ts", "import { CatService } from \"./cat.service\";\n"
                                   "\n"
                                   "export class CatController {\n"
                                   "  constructor(private readonly catService: CatService) {}\n"
                                   "\n"
                                   "  list() {\n"
                                   "    return this.catService.findAll();\n"
                                   "  }\n"
                                   "}\n"},
};

/* Run trace_path inbound depth 1 on fn_name against the fixture project.
 * rh_index_files restores CBM_CACHE_DIR after indexing; point the query at
 * the fixture's cache so trace_path finds the project. */
static char *rh514_trace_inbound(RProj *lp, const char *fn_name) {
    char args[512];
    snprintf(args, sizeof(args),
             "{\"function_name\":\"%s\","
             "\"project\":\"%s\","
             "\"direction\":\"inbound\","
             "\"depth\":1}",
             fn_name, lp->project);

    return rh_call(lp, "trace_path", args);
}

TEST(repro_issue514_ctor_param_property_callers) {
    RProj lp;
    cbm_store_t *store =
        rh_index_files(&lp, k_nest_files, (int)(sizeof(k_nest_files) / sizeof(k_nest_files[0])));
    ASSERT_NOT_NULL(store);

    char *resp = rh514_trace_inbound(&lp, "findAll");
    ASSERT_NOT_NULL(resp);
    fprintf(stderr, "  [514] trace_path inbound response: %.400s\n", resp);

    ASSERT_NULL(strstr(resp, "function not found"));
    ASSERT_NOT_NULL(strstr(resp, "CatController.list"));

    free(resp);
    rh_cleanup(&lp, store);
    PASS();
}

/* Same DI shape, but the injected class is imported through a tsconfig
 * `paths` alias, the norm in NestJS monorepos. The alias branch of import
 * resolution stripped the dotted basename (`cat.service` -> `cat`), so the
 * IMPORTS edge missed the module and the DI call lost its target. */
static const RFile k_nest_alias_files[] = {
    {"apps/api/tsconfig.json",
     "{\"compilerOptions\":{\"baseUrl\":\"./\",\"paths\":{\"@app/*\":[\"src/*\"]}}}\n"},
    {"apps/api/src/cats/cat.service.ts", "export class CatService {\n"
                                         "  findAll(): string[] {\n"
                                         "    return [\"a\"];\n"
                                         "  }\n"
                                         "}\n"},
    {"apps/api/src/other/cat.service.ts",
     "export class CatService { findAll(): string[] { return [\"decoy\"]; } }\n"},
    {"apps/api/src/cats/cat.controller.ts",
     "import { CatService } from \"@app/cats/cat.service\";\n"
     "\n"
     "export class CatController {\n"
     "  constructor(private readonly catService: CatService) {}\n"
     "\n"
     "  list() {\n"
     "    return this.catService.findAll();\n"
     "  }\n"
     "}\n"},
};

TEST(repro_issue514_ctor_param_property_alias_import_callers) {
    RProj lp;
    cbm_store_t *store = rh_index_files(
        &lp, k_nest_alias_files, (int)(sizeof(k_nest_alias_files) / sizeof(k_nest_alias_files[0])));
    ASSERT_NOT_NULL(store);

    char caller_qn[512];
    char target_qn[512];
    snprintf(caller_qn, sizeof(caller_qn), "%s.apps.api.src.cats.cat.controller.CatController.list",
             lp.project);
    snprintf(target_qn, sizeof(target_qn), "%s.apps.api.src.cats.cat.service.CatService.findAll",
             lp.project);
    cbm_node_t *caller = calloc(1, sizeof(*caller));
    cbm_node_t *target = calloc(1, sizeof(*target));
    ASSERT_NOT_NULL(caller);
    ASSERT_NOT_NULL(target);
    ASSERT_EQ(cbm_store_find_node_by_qn(store, lp.project, caller_qn, caller), CBM_STORE_OK);
    ASSERT_EQ(cbm_store_find_node_by_qn(store, lp.project, target_qn, target), CBM_STORE_OK);
    cbm_edge_t *edges = NULL;
    int edge_count = 0;
    ASSERT_EQ(cbm_store_find_edges_by_source_type(store, caller->id, "CALLS", &edges, &edge_count),
              CBM_STORE_OK);
    fprintf(stderr, "  [514] alias caller CALLS edges=%d; expected target=%s\n", edge_count,
            target_qn);
    ASSERT_EQ(edge_count, 1);
    ASSERT_EQ(edges[0].target_id, target->id);
    cbm_store_free_edges(edges, edge_count);
    cbm_store_free_nodes(caller, 1);
    cbm_store_free_nodes(target, 1);

    /* A qualified lookup selects the intended method despite its decoy. */
    char *resp = rh514_trace_inbound(&lp, target_qn);
    ASSERT_NOT_NULL(resp);
    fprintf(stderr, "  [514] trace_path inbound (alias) response: %.400s\n", resp);
    ASSERT_NULL(strstr(resp, "function not found"));
    ASSERT_NOT_NULL(strstr(resp, caller_qn));

    free(resp);
    rh_cleanup(&lp, store);
    PASS();
}

/* Repositories are injected by string token and typed as an INTERFACE:
 * `@Inject("order.OrderRepository") private readonly repo: OrderRepository`.
 * Interface method signatures were not graph nodes, so the call had no
 * target and trace_path found no callers. */
static const RFile k_nest_iface_files[] = {
    {"apps/api/tsconfig.json", "{\"compilerOptions\":{\"baseUrl\":\"./\",\"paths\":{\"@acme/order/"
                               "*\":[\"libs/order/src/*\"]}}}\n"},
    {"apps/api/libs/order/src/domain/order.repository.ts",
     "export interface OrderRepository {\n"
     "  save(orderId: string): Promise<void>;\n"
     "  findOneOrFail(orderId: string): Promise<{ id: string }>;\n"
     "}\n"},
    {"apps/api/libs/order/src/application/command/handler/cancel-order.handler.ts",
     "import { Inject } from \"@nestjs/common\";\n"
     "import { OrderRepository } from \"@acme/order/domain/order.repository\";\n"
     "\n"
     "export class CancelOrderHandler {\n"
     "  constructor(\n"
     "    @Inject(\"order.OrderRepository\")\n"
     "    private readonly orderRepository: OrderRepository,\n"
     "  ) {}\n"
     "\n"
     "  async execute(orderId: string): Promise<void> {\n"
     "    const order = await this.orderRepository.findOneOrFail(orderId);\n"
     "    await this.orderRepository.save(order.id);\n"
     "  }\n"
     "}\n"},
};

TEST(repro_issue514_inject_token_interface_callers) {
    RProj lp;
    cbm_store_t *store = rh_index_files(
        &lp, k_nest_iface_files, (int)(sizeof(k_nest_iface_files) / sizeof(k_nest_iface_files[0])));
    ASSERT_NOT_NULL(store);

    char *save = rh514_trace_inbound(&lp, "save");
    char *find = rh514_trace_inbound(&lp, "findOneOrFail");
    ASSERT_NOT_NULL(save);
    ASSERT_NOT_NULL(find);
    fprintf(stderr, "  [514] trace_path inbound save: %.400s\n", save);
    fprintf(stderr, "  [514] trace_path inbound findOneOrFail: %.400s\n", find);

    ASSERT_NOT_NULL(strstr(save, "CancelOrderHandler.execute"));
    ASSERT_NOT_NULL(strstr(find, "CancelOrderHandler.execute"));

    free(save);
    free(find);
    rh_cleanup(&lp, store);
    PASS();
}

/* ── Suite ─────────────────────────────────────────────────────────────────── */
SUITE(repro_issue514) {
    RUN_TEST(repro_issue514_data_flow_surfaces_arg_expr);
    RUN_TEST(repro_issue514_ctor_param_property_callers);
    RUN_TEST(repro_issue514_ctor_param_property_alias_import_callers);
    RUN_TEST(repro_issue514_inject_token_interface_callers);
}
