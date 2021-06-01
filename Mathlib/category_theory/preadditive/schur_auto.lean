/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.simple
import Mathlib.category_theory.preadditive.default
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Schur's lemma
We prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

## TODO
If the category is enriched over finite dimensional vector spaces
over an algebraically closed field, then we can further prove that
`dim (X ⟶ Y) ≤ 1`.

(Probably easiest to prove this for endomorphisms first:
some polynomial `p` in `f : X ⟶ X` vanishes by finite dimensionality,
that polynomial factors linearly,
and at least one factor must be non-invertible, hence zero,
so `f` is a scalar multiple of the identity.
Then for any two nonzero `f g : X ⟶ Y`,
observe `f ≫ g⁻¹` is a multiple of the identity.)
-/

namespace category_theory


/--
Schur's Lemma (for a general preadditive category),
that a nonzero morphism between simple objects is an isomorphism.
-/
def is_iso_of_hom_simple {C : Type u} [category C] [preadditive C] [limits.has_kernels C] {X : C}
    {Y : C} [simple X] [simple Y] {f : X ⟶ Y} (w : f ≠ 0) : is_iso f :=
  is_iso_of_mono_of_nonzero w

/--
As a corollary of Schur's lemma,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
def is_iso_equiv_nonzero {C : Type u} [category C] [preadditive C] [limits.has_kernels C] {X : C}
    {Y : C} [simple X] [simple Y] {f : X ⟶ Y} : is_iso f ≃ f ≠ 0 :=
  equiv.mk sorry (fun (w : f ≠ 0) => is_iso_of_hom_simple w) sorry sorry

end Mathlib