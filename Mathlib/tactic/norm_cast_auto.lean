/-
Copyright (c) 2019 Paul-Nicolas Madelaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Nicolas Madelaine, Robert Y. Lewis

Normalizing casts inside expressions.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.converter.interactive
import Mathlib.tactic.hint
import Mathlib.PostPort

universes l u_1 u_2 

namespace Mathlib

/-!
# A tactic for normalizing casts inside expressions

This tactic normalizes casts inside expressions.
It can be thought of as a call to the simplifier with a specific set of lemmas to
move casts upwards in the expression.
It has special handling of numerals and a simple heuristic to help moving
casts "past" binary operators.
Contrary to simp, it should be safe to use as a non-terminating tactic.

The algorithm implemented here is described in the paper
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.

## Important definitions
* `tactic.interactive.norm_cast`
* `tactic.interactive.push_cast`
* `tactic.interactive.exact_mod_cast`
* `tactic.interactive.apply_mod_cast`
* `tactic.interactive.rw_mod_cast`
* `tactic.interactive.assumption_mod_cast`
-/

namespace tactic


/--
Runs `mk_instance` with a time limit.

This is a work around to the fact that in some cases
mk_instance times out instead of failing,
for example: `has_lift_t ℤ ℕ`

`mk_instance_fast` is used when we assume the type class search
should end instantly.
-/
end tactic


namespace norm_cast


/--
Output a trace message if `trace.norm_cast` is enabled.
-/
/--
`label` is a type used to classify `norm_cast` lemmas.
* elim lemma:   LHS has 0 head coes and ≥ 1 internal coe
* move lemma:   LHS has 1 head coe and 0 internal coes,    RHS has 0 head coes and ≥ 1 internal coes
* squash lemma: LHS has ≥ 1 head coes and 0 internal coes, RHS has fewer head coes
-/
inductive label where
| elim : label
| move : label
| squash : label

namespace label


/-- Convert `label` into `string`. -/
protected def to_string : label → string := sorry

protected instance has_to_string : has_to_string label := has_to_string.mk label.to_string

protected instance has_repr : has_repr label := has_repr.mk label.to_string

/-- Convert `string` into `label`. -/
def of_string : string → Option label := sorry

end label


/-- Count how many coercions are at the top of the expression. -/
/-- Count how many coercions are inside the expression, including the top ones. -/
/-- Count how many coercions are inside the expression, excluding the top ones. -/
/--
Classifies a declaration of type `ty` as a `norm_cast` rule.
-/
/-- The cache for `norm_cast` attribute stores three `simp_lemma` objects. -/
/-- Empty `norm_cast_cache`. -/
/-- `add_elim cache e` adds `e` as an `elim` lemma to `cache`. -/
/-- `add_move cache e` adds `e` as a `move` lemma to `cache`. -/
/-- `add_squash cache e` adds `e` as an `squash` lemma to `cache`. -/
/--
The type of the `norm_cast` attribute.
The optional label is used to overwrite the classifier.
-/
/--
Efficient getter for the `@[norm_cast]` attribute parameter that does not call `eval_expr`.

See Note [user attribute parameters].
-/
/--
`add_lemma cache decl` infers the proper `norm_cast` attribute for `decl` and adds it to `cache`.
-/
-- special lemmas to handle the ≥, > and ≠ operators

/--
`mk_cache names` creates a `norm_cast_cache`. It infers the proper `norm_cast` attributes
for names in `names`, and collects the lemmas attributed with specific `norm_cast` attributes.
-/
-- names has the declarations in reverse order

--some special lemmas to handle binary relations

/--
The `norm_cast` attribute.
-/
/-- Classify a declaration as a `norm_cast` rule. -/
/--
Gets the `norm_cast` classification label for a declaration. Applies the
override specified on the attribute, if necessary.
-/
end norm_cast


namespace tactic.interactive


/--
`push_cast` rewrites the expression to move casts toward the leaf nodes.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
Equivalent to `simp only with push_cast`.
Can also be used at hypotheses.

`push_cast` can also be used at hypotheses and with extra simp rules.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```
-/
end tactic.interactive


namespace norm_cast


/-- Prove `a = b` using the given simp set. -/
/-- Prove `a = b` by simplifying using move and squash lemmas. -/
/--
This is the main heuristic used alongside the elim and move lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash lemma
-/
/--
Discharging function used during simplification in the "squash" step.

TODO: norm_cast takes a list of expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
/--
Core rewriting function used in the "squash" step, which moves casts upwards
and eliminates them.

It tries to rewrite an expression using the elim and move lemmas.
On failure, it calls the splitting procedure heuristic.
-/
/-!
The following auxiliary functions are used to handle numerals.
-/

/--
If possible, rewrite `(n : α)` to `((n : ℕ) : α)` where `n` is a numeral and `α ≠ ℕ`.
Returns a pair of the new expression and proof that they are equal.
-/
/--
If possible, rewrite `((n : ℕ) : α)` to `(n : α)` where `n` is a numeral.
Returns a pair of the new expression and proof that they are equal.
-/
/-- A local variant on `simplify_top_down`. -/
/--
The core simplification routine of `norm_cast`.
-/
/--
A small variant of `push_cast` suited for non-interactive use.

`derive_push_cast extra_lems e` returns an expression `e'` and a proof that `e = e'`.
-/
end norm_cast


namespace tactic


/-- `aux_mod_cast e` runs `norm_cast` on `e` and returns the result. If `include_goal` is true, it
also normalizes the goal. -/
/-- `exact_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to use `e` to close the goal. -/
/-- `apply_mod_cast e` runs `norm_cast` on the goal and `e`, and tries to apply `e`. -/
/-- `assumption_mod_cast` runs `norm_cast` on the goal. For each local hypothesis `h`, it also
normalizes `h` and tries to use that to close the goal. -/
end tactic


namespace tactic.interactive


/--
Normalize casts at the given locations by moving them "upwards".
As opposed to simp, norm_cast can be used without necessarily closing the goal.
-/
/--
Rewrite with the given rules and normalize casts between steps.
-/
/--
Normalize the goal and the given expression, then close the goal with exact.
-/
/--
Normalize the goal and the given expression, then apply the expression to the goal.
-/
/--
Normalize the goal and every expression in the local context, then close the goal with assumption.
-/
end tactic.interactive


namespace conv.interactive


/-- the converter version of `norm_cast' -/
end conv.interactive


-- TODO: move this elsewhere?

theorem ite_cast {α : Sort u_1} {β : Sort u_2} [has_lift_t α β] {c : Prop} [Decidable c] {a : α}
    {b : α} : ↑(ite c a b) = ite c ↑a ↑b :=
  sorry

/--
The `norm_cast` family of tactics is used to normalize casts inside expressions.
It is basically a simp tactic with a specific set of lemmas to move casts
upwards in the expression.
Therefore it can be used more safely as a non-terminating tactic.
It also has special handling of numerals.

For instance, given an assumption
```lean
a b : ℤ
h : ↑a + ↑b < (10 : ℚ)
```

writing `norm_cast at h` will turn `h` into
```lean
h : a + b < 10
```

You can also use `exact_mod_cast`, `apply_mod_cast`, `rw_mod_cast`
or `assumption_mod_cast`.
Writing `exact_mod_cast h` and `apply_mod_cast h` will normalize the goal and
`h` before using `exact h` or `apply h`.
Writing `assumption_mod_cast` will normalize the goal and for every
expression `h` in the context it will try to normalize `h` and use
`exact h`.
`rw_mod_cast` acts like the `rw` tactic but it applies `norm_cast` between steps.

`push_cast` rewrites the expression to move casts toward the leaf nodes.
This uses `norm_cast` lemmas in the forward direction.
For example, `↑(a + b)` will be written to `↑a + ↑b`.
It is equivalent to `simp only with push_cast`.
It can also be used at hypotheses with `push_cast at h`
and with extra simp lemmas with `push_cast [int.add_zero]`.

```lean
example (a b : ℕ) (h1 : ((a + b : ℕ) : ℤ) = 10) (h2 : ((a + b + 0 : ℕ) : ℤ) = 10) :
  ((a + b : ℕ) : ℤ) = 10 :=
begin
  push_cast,
  push_cast at h1,
  push_cast [int.add_zero] at h2,
end
```

The implementation and behavior of the `norm_cast` family is described in detail at
<https://lean-forward.github.io/norm_cast/norm_cast.pdf>.
-/
/--
The `norm_cast` attribute should be given to lemmas that describe the
end Mathlib