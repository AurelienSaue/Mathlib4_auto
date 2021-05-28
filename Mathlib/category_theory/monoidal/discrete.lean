/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.natural_transformation
import Mathlib.category_theory.discrete_category
import Mathlib.algebra.group.hom
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induced monoidal functors.
-/

namespace category_theory


protected instance monoid_discrete (M : Type u) [monoid M] : monoid (discrete M) :=
  id _inst_1

protected instance discrete.monoidal_category (M : Type u) [monoid M] : monoidal_category (discrete M) :=
  monoidal_category.mk (fun (X Y : discrete M) => X * Y)
    (fun (W X Y Z : discrete M) (f : W ⟶ X) (g : Y ⟶ Z) => eq_to_hom sorry) 1
    (fun (X Y Z : discrete M) => eq_to_iso sorry) (fun (X : discrete M) => eq_to_iso sorry)
    fun (X : discrete M) => eq_to_iso sorry

/--
A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[simp] theorem discrete.monoidal_functor_μ_is_iso {M : Type u} [monoid M] {N : Type u} [monoid N] (F : M →* N) (X : discrete M) (Y : discrete M) : monoidal_functor.μ_is_iso (discrete.monoidal_functor F) X Y =
  discrete.category_theory.is_iso
    (lax_monoidal_functor.μ
      (lax_monoidal_functor.mk
        (functor.mk ⇑F fun (X Y : discrete M) (f : X ⟶ Y) => eq_to_hom (discrete.monoidal_functor._proof_1 F X Y f))
        (eq_to_hom (discrete.monoidal_functor._proof_4 F))
        fun (X Y : discrete M) => eq_to_hom (discrete.monoidal_functor._proof_5 F X Y))
      X Y) :=
  Eq.refl (monoidal_functor.μ_is_iso (discrete.monoidal_functor F) X Y)

/--
The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
def discrete.monoidal_functor_comp {M : Type u} [monoid M] {N : Type u} [monoid N] {K : Type u} [monoid K] (F : M →* N) (G : N →* K) : discrete.monoidal_functor F ⊗⋙ discrete.monoidal_functor G ≅ discrete.monoidal_functor (monoid_hom.comp G F) :=
  iso.mk (monoidal_nat_trans.mk (nat_trans.mk fun (X : discrete M) => 𝟙))
    (monoidal_nat_trans.mk (nat_trans.mk fun (X : discrete M) => 𝟙))

