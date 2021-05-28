/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# The extended reals [-∞, ∞].

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `with_top (with_bot ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.
An addition is derived, but `ereal` is not even a monoid (there is no identity).

`ereal` is a `complete_lattice`; this is now deduced by type class inference from
the fact that `with_top (with_bot L)` is a complete lattice if `L` is
a conditionally complete lattice.

## Tags

real, ereal, complete lattice

## TODO

abs : ereal → ennreal

In Isabelle they define + - * and / (making junk choices for things like -∞ + ∞)
and then prove whatever bits of the ordered ring/field axioms still hold. They
also do some limits stuff (liminf/limsup etc).
See https://isabelle.in.tum.de/dist/library/HOL/HOL-Library/Extended_Real.html
-/

/-- ereal : The type `[-∞, ∞]` -/
def ereal  :=
  with_top (with_bot ℝ)

namespace ereal


protected instance has_coe : has_coe ℝ ereal :=
  has_coe.mk (some ∘ some)

@[simp] protected theorem coe_real_le {x : ℝ} {y : ℝ} : ↑x ≤ ↑y ↔ x ≤ y := sorry

@[simp] protected theorem coe_real_lt {x : ℝ} {y : ℝ} : ↑x < ↑y ↔ x < y := sorry

@[simp] protected theorem coe_real_inj' {x : ℝ} {y : ℝ} : ↑x = ↑y ↔ x = y := sorry

protected instance has_zero : HasZero ereal :=
  { zero := ↑0 }

protected instance inhabited : Inhabited ereal :=
  { default := 0 }

/-! ### Negation -/

/-- negation on ereal -/
protected def neg : ereal → ereal :=
  sorry

protected instance has_neg : Neg ereal :=
  { neg := ereal.neg }

protected theorem neg_def (x : ℝ) : ↑(-x) = -↑x :=
  rfl

/-- - -a = a on ereal -/
protected theorem neg_neg (a : ereal) : --a = a := sorry

theorem neg_inj (a : ereal) (b : ereal) (h : -a = -b) : a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (Eq.symm (ereal.neg_neg a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ( --a = b)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl ( --b = b)) (ereal.neg_neg b))) (Eq.refl b)))

/-- Even though ereal is not an additive group, -a = b ↔ -b = a still holds -/
theorem neg_eq_iff_neg_eq {a : ereal} {b : ereal} : -a = b ↔ -b = a :=
  { mp := fun (h : -a = b) => eq.mpr (id (Eq._oldrec (Eq.refl (-b = a)) (Eq.symm h))) (ereal.neg_neg a),
    mpr := fun (h : -b = a) => eq.mpr (id (Eq._oldrec (Eq.refl (-a = b)) (Eq.symm h))) (ereal.neg_neg b) }

/-- if -a ≤ b then -b ≤ a on ereal -/
protected theorem neg_le_of_neg_le {a : ereal} {b : ereal} (h : -a ≤ b) : -b ≤ a := sorry

/-- -a ≤ b ↔ -b ≤ a on ereal-/
protected theorem neg_le {a : ereal} {b : ereal} : -a ≤ b ↔ -b ≤ a :=
  { mp := ereal.neg_le_of_neg_le, mpr := ereal.neg_le_of_neg_le }

/-- a ≤ -b → b ≤ -a on ereal -/
theorem le_neg_of_le_neg {a : ereal} {b : ereal} (h : a ≤ -b) : b ≤ -a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b ≤ -a)) (Eq.symm (ereal.neg_neg b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ( --b ≤ -a)) (propext ereal.neg_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ( --a ≤ -b)) (ereal.neg_neg a))) h))

