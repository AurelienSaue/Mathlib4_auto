/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.norm_cast
import Mathlib.data.int.cast
import Mathlib.PostPort

namespace Mathlib

/-!
# A tactic to shift `ℕ` goals to `ℤ`

It is often easier to work in `ℤ`, where subtraction is well behaved, than in `ℕ` where it isn't.
`zify` is a tactic that casts goals and hypotheses about natural numbers to ones about integers.
It makes use of `push_cast`, part of the `norm_cast` family, to simplify these goals.

## Implementation notes

`zify` is extensible, using the attribute `@[zify]` to label lemmas used for moving propositions
from `ℕ` to `ℤ`.
`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.

`zify` is very nearly just `simp only with zify push_cast`. There are a few minor differences:
* `zify` lemmas are used in the opposite order of the standard simp form.
  E.g. we will rewrite with `int.coe_nat_le_coe_nat_iff` from right to left.
* `zify` should fail if no `zify` lemma applies (i.e. it was unable to shift any proposition to ℤ).
  However, once this succeeds, it does not necessarily need to rewrite with any `push_cast` rules.
-/

namespace zify


/--
The `zify` attribute is used by the `zify` tactic. It applies to lemmas that shift propositions
between `nat` and `int`.

`zify` lemmas should have the form `∀ a₁ ... aₙ : ℕ, Pz (a₁ : ℤ) ... (aₙ : ℤ) ↔ Pn a₁ ... aₙ`.
For example, `int.coe_nat_le_coe_nat_iff : ∀ (m n : ℕ), ↑m ≤ ↑n ↔ m ≤ n` is a `zify` lemma.
-/
/--
Given an expression `e`, `lift_to_z e` looks for subterms of `e` that are propositions "about"
natural numbers and change them to propositions about integers.

Returns an expression `e'` and a proof that `e = e'`.

Includes `ge_iff_le` and `gt_iff_lt` in the simp set. These can't be tagged with `zify` as we
want to use them in the "forward", not "backward", direction.
-/
end zify


theorem int.coe_nat_ne_coe_nat_iff (a : ℕ) (b : ℕ) : ↑a ≠ ↑b ↔ a ≠ b := sorry

/--
`zify extra_lems e` is used to shift propositions in `e` from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

The list of extra lemmas is used in the `push_cast` step.

Returns an expression `e'` and a proof that `e = e'`.-/
/--
A variant of `tactic.zify` that takes `h`, a proof of a proposition about natural numbers,
and returns a proof of the zified version of that propositon.
-/
/--
The `zify` tactic is used to shift propositions from `ℕ` to `ℤ`.
This is often useful since `ℤ` has well-behaved subtraction.

```lean
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : c < a + 3*b :=
begin
  zify,
  zify at h,
  /-
  h : ¬↑x * ↑y * ↑z < 0
  ⊢ ↑c < ↑a + 3 * ↑b
  -/
end Mathlib