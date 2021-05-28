/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.lint.basic
import PostPort

namespace Mathlib

/-!
# Linters about type classes

This file defines several linters checking the correct usage of type classes
and the appropriate definition of instances:

 * `instance_priority` ensures that blanket instances have low priority
 * `has_inhabited_instances` checks that every type has an `inhabited` instance
 * `impossible_instance` checks that there are no instances which can never apply
 * `incorrect_type_class_argument` checks that only type classes are used in
   instance-implicit arguments
 * `dangerous_instance` checks for instances that generate subproblems with metavariables
 * `fails_quickly` checks that type class resolution finishes quickly
 * `has_coe_variable` checks that there is no instance of type `has_coe α t`
 * `inhabited_nonempty` checks whether `[inhabited α]` arguments could be generalized
   to `[nonempty α]`
 * `decidable_classical` checks propositions for `[decidable_... p]` hypotheses that are not used
   in the statement, and could thus be removed by using `classical` in the proof.
 * `linter.has_coe_to_fun` checks whether necessary `has_coe_to_fun` instances are declared
-/

/-- Pretty prints a list of arguments of a declaration. Assumes `l` is a list of argument positions
and binders (or any other element that can be pretty printed).
`l` can be obtained e.g. by applying `list.indexes_values` to a list obtained by
`get_pi_binders`. -/
/-- checks whether an instance that always applies has priority ≥ 1000. -/
/--
There are places where typeclass arguments are specified with implicit `{}` brackets instead of
the usual `[]` brackets. This is done when the instances can be inferred because they are implicit
arguments to the type of one of the other arguments. When they can be inferred from these other
arguments,  it is faster to use this method than to use type class inference.

For example, when writing lemmas about `(f : α →+* β)`, it is faster to specify the fact that `α`
and `β` are `semiring`s as `{rα : semiring α} {rβ : semiring β}` rather than the usual
`[semiring α] [semiring β]`.
-/
/--
Certain instances always apply during type-class resolution. For example, the instance
