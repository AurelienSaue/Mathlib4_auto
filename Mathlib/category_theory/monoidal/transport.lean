/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.natural_transformation
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ 

namespace Mathlib

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We don't yet prove anything about this transported structure!
The next step would be to show that the original functor can be upgraded
to a monoidal functor with respect to this new structure.
-/

namespace category_theory.monoidal


/--
Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simp] theorem transport_tensor_unit {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : 𝟙_ = functor.obj (equivalence.functor e) 𝟙_ :=
  Eq.refl 𝟙_

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
def transported {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D)  :=
  D

protected instance transported.category_theory.monoidal_category {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : monoidal_category (transported e) :=
  transport e

protected instance transported.inhabited {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : Inhabited (transported e) :=
  { default := 𝟙_ }

/--
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simp] theorem lax_to_transported_to_functor_map {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) {X : C} {Y : C} : ∀ (ᾰ : X ⟶ Y),
  functor.map (lax_monoidal_functor.to_functor (lax_to_transported e)) ᾰ = functor.map (equivalence.functor e) ᾰ :=
  fun (ᾰ : X ⟶ Y) => Eq.refl (functor.map (lax_monoidal_functor.to_functor (lax_to_transported e)) ᾰ)

/--
We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simp] theorem to_transported_ε_is_iso {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : monoidal_functor.ε_is_iso (to_transported e) = id (is_iso.id (functor.obj (equivalence.functor e) 𝟙_)) :=
  Eq.refl (monoidal_functor.ε_is_iso (to_transported e))

/--
We can upgrade `e.inverse` to a lax monoidal functor from `D` with the transported structure to `C`.
-/
def lax_from_transported {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : lax_monoidal_functor (transported e) C :=
  lax_monoidal_functor.mk (functor.mk (functor.obj (equivalence.inverse e)) (functor.map (equivalence.inverse e)))
    (nat_trans.app (equivalence.unit e) 𝟙_)
    fun (X Y : transported e) =>
      nat_trans.app (equivalence.unit e) (functor.obj (equivalence.inverse e) X ⊗ functor.obj (equivalence.inverse e) Y)

/--
We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
def from_transported {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : monoidal_functor (transported e) C :=
  monoidal_functor.mk
    (lax_monoidal_functor.mk (lax_monoidal_functor.to_functor (lax_from_transported e))
      (lax_monoidal_functor.ε (lax_from_transported e)) (lax_monoidal_functor.μ (lax_from_transported e)))

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
def transported_monoidal_unit_iso {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) : lax_monoidal_functor.id C ≅ lax_to_transported e ⊗⋙ lax_from_transported e :=
  monoidal_nat_iso.of_components (fun (X : C) => iso.app (equivalence.unit_iso e) X) sorry sorry sorry

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simp] theorem transported_monoidal_counit_iso_hom_to_nat_trans_app {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] (e : C ≌ D) (X : transported e) : nat_trans.app (monoidal_nat_trans.to_nat_trans (iso.hom (transported_monoidal_counit_iso e))) X =
  nat_trans.app (iso.hom (equivalence.counit_iso e)) X :=
  Eq.refl (nat_trans.app (iso.hom (equivalence.counit_iso e)) X)

