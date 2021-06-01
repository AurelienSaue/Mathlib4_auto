/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.zero
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Shift

A `shift` on a category is nothing more than an automorphism of the category. An example to
keep in mind might be the category of complexes ⋯ → C_{n-1} → C_n → C_{n+1} → ⋯ with the shift
operator re-indexing the terms, so the degree `n` term of `shift C` would be the degree `n+1`
term of `C`.

-/

namespace category_theory


/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift (C : Type u) [category C] where
  shift : C ≌ C

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
def shift (C : Type u) [category C] [has_shift C] : C ≌ C := has_shift.shift

-- Any better notational suggestions?

@[simp] theorem shift_zero_eq_zero (C : Type u) [category C] [has_shift C]
    [limits.has_zero_morphisms C] (X : C) (Y : C) (n : ℤ) :
    functor.map (equivalence.functor (shift C ^ n)) 0 = 0 :=
  limits.equivalence_preserves_zero_morphisms C (shift C ^ n) X Y

end Mathlib