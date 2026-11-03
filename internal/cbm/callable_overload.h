/*
 * callable_overload.h — same-file overloads as separate graph nodes (Java,
 * Kotlin, Swift), without changing the QN of anything that is not overloaded.
 *
 * The graph keys a node by its QN, and a callable QN carries no signature, so
 * five `action(...)` overloads of one class became ONE node (the last one's
 * span) that collected the callers of all five. Upstream's callable identity
 * plumbing (callable_sig.h, #2061) can suffix every callable QN with its
 * signature, but switching a language on renames every callable of that
 * language. This module applies the same suffix to overloads only:
 *
 *   - definitions: cbm_split_overloads runs once a file's def list is final.
 *     For each group of two or more Function/Method defs of one file that
 *     share a QN and a label, the first (by start line) keeps the base QN;
 *     each later one whose signature no earlier member has takes
 *     base QN + signature suffix (CBMDefinition.qn_sig_off marks it); a later
 *     one with an earlier member's signature takes that member's QN (the same
 *     definition seen twice, e.g. Swift `#if` twins, stays one node). Every
 *     member carries its parameter shape as the `overload_params` property.
 *   - calls: the call site records its argument shape (CBMCall.arg_shape);
 *     the resolvers bind a call that lands on an overload group to the
 *     members whose parameter shape accepts it
 *     (cbm_pipeline_overload_targets, pipeline_internal.h).
 *
 * Shape grammar (both sides): entries separated by ','; "" = none.
 *   parameter entry: label (Swift: the argument label, '_' when none;
 *                    Kotlin: the parameter name; Java: '_'), then '=' when
 *                    it has a default, '~' when variadic.
 *   argument entry:  label (Swift: the argument label; Kotlin: the name of
 *                    a named argument; '_' otherwise), or '*' for a trailing
 *                    closure / lambda.
 */
#ifndef CBM_CALLABLE_OVERLOAD_H
#define CBM_CALLABLE_OVERLOAD_H

#include "cbm.h"
#include "arena.h"
#include "tree_sitter/api.h"
#include <stdbool.h>

/* The node property every overload group member carries: its parameter
 * shape, CBM_OVERLOAD_NO_PARAMS for an empty parameter list (the properties
 * writer drops empty strings), "?" when unknown. */
#define CBM_OVERLOAD_PARAMS_PROP "overload_params"
#define CBM_OVERLOAD_NO_PARAMS "-"

/* True for the languages whose same-file overloads are split (Java, Kotlin,
 * Swift). */
bool cbm_overload_lang(CBMLanguage lang);

/* Record the signature suffix and the parameter shape of a callable def
 * (Java/Kotlin/Swift Function or Method; no-op otherwise). `func_node` is the
 * declaration node. */
void cbm_overload_describe_def(CBMArena *a, CBMDefinition *def, TSNode func_node,
                               const char *source, CBMLanguage lang);

/* The argument shape of a call node (Java method_invocation, Kotlin/Swift
 * call_expression), or NULL when the node is not one of those. Arena-owned. */
const char *cbm_call_args_shape(CBMArena *a, TSNode call_node, const char *source,
                                CBMLanguage lang);

/* Split the file's same-QN callable groups (see the file comment). */
void cbm_split_overloads(CBMArena *a, CBMFileResult *result, CBMLanguage lang);

/* Does a callable with parameter shape `params` accept a call with argument
 * shape `args`? An unknown side (NULL or "?") accepts. Swift compares labels
 * in order; Kotlin binds positional, named and trailing-lambda arguments;
 * Java compares counts. Defaults and varargs are honoured. */
bool cbm_callable_shape_matches(const char *params, const char *args, CBMLanguage lang);

#endif /* CBM_CALLABLE_OVERLOAD_H */
