/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.braided
import Mathlib.category_theory.monoidal.Mon_
import Mathlib.PostPort

universes v₁ u₁ l u₂ v₂ u_1 u_2 

namespace Mathlib

/-!
# The category of commutative monoids in a braided monoidal category.
-/

/--
A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ (C : Type u₁) [category_theory.category C] [category_theory.monoidal_category C]
    [category_theory.braided_category C]
    extends Mon_ C where
  mul_comm' :
    autoParam (category_theory.iso.hom β_ ≫ Mon_.mul _to_Mon_ = Mon_.mul _to_Mon_)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem CommMon_.mul_comm {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (c : CommMon_ C) :
    category_theory.iso.hom β_ ≫ Mon_.mul (CommMon_.to_Mon_ c) = Mon_.mul (CommMon_.to_Mon_ c) :=
  sorry

@[simp] theorem CommMon_.mul_comm_assoc {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (c : CommMon_ C)
    {X' : C} (f' : Mon_.X (CommMon_.to_Mon_ c) ⟶ X') :
    category_theory.iso.hom β_ ≫ Mon_.mul (CommMon_.to_Mon_ c) ≫ f' =
        Mon_.mul (CommMon_.to_Mon_ c) ≫ f' :=
  sorry

namespace CommMon_


/--
The trivial commutative monoid object. We later show this is initial in `CommMon_ C`.
-/
def trivial (C : Type u₁) [category_theory.category C] [category_theory.monoidal_category C]
    [category_theory.braided_category C] : CommMon_ C :=
  mk (Mon_.mk (Mon_.X (Mon_.trivial C)) (Mon_.one (Mon_.trivial C)) (Mon_.mul (Mon_.trivial C)))

protected instance inhabited (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] :
    Inhabited (CommMon_ C) :=
  { default := trivial C }

protected instance category_theory.category {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] :
    category_theory.category (CommMon_ C) :=
  category_theory.induced_category.category to_Mon_

@[simp] theorem id_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (A : CommMon_ C) :
    Mon_.hom.hom 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] {R : CommMon_ C}
    {S : CommMon_ C} {T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.hom.hom (f ≫ g) = Mon_.hom.hom f ≫ Mon_.hom.hom g :=
  rfl

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
def forget₂_Mon_ (C : Type u₁) [category_theory.category C] [category_theory.monoidal_category C]
    [category_theory.braided_category C] : CommMon_ C ⥤ Mon_ C :=
  category_theory.induced_functor to_Mon_

@[simp] theorem forget₂_Mon_obj_one (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (A : CommMon_ C) :
    Mon_.one (category_theory.functor.obj (forget₂_Mon_ C) A) = Mon_.one (to_Mon_ A) :=
  rfl

@[simp] theorem forget₂_Mon_obj_mul (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (A : CommMon_ C) :
    Mon_.mul (category_theory.functor.obj (forget₂_Mon_ C) A) = Mon_.mul (to_Mon_ A) :=
  rfl

@[simp] theorem forget₂_Mon_map_hom (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] {A : CommMon_ C}
    {B : CommMon_ C} (f : A ⟶ B) :
    Mon_.hom.hom (category_theory.functor.map (forget₂_Mon_ C) f) = Mon_.hom.hom f :=
  rfl

protected instance unique_hom_from_trivial {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (A : CommMon_ C) :
    unique (trivial C ⟶ A) :=
  Mon_.unique_hom_from_trivial (to_Mon_ A)

protected instance category_theory.limits.has_initial {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] :
    category_theory.limits.has_initial (CommMon_ C) :=
  category_theory.limits.has_initial_of_unique (trivial C)

end CommMon_


namespace category_theory.lax_braided_functor


/--
A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simp] theorem map_CommMon_map {C : Type u₁} [category C] [monoidal_category C]
    [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D]
    (F : lax_braided_functor C D) (A : CommMon_ C) (B : CommMon_ C) (f : A ⟶ B) :
    functor.map (map_CommMon F) f =
        functor.map (lax_monoidal_functor.map_Mon (to_lax_monoidal_functor F)) f :=
  Eq.refl (functor.map (map_CommMon F) f)

/-- `map_CommMon` is functorial in the lax braided functor. -/
def map_CommMon_functor (C : Type u₁) [category C] [monoidal_category C] [braided_category C]
    (D : Type u₂) [category D] [monoidal_category D] [braided_category D] :
    lax_braided_functor C D ⥤ CommMon_ C ⥤ CommMon_ D :=
  functor.mk map_CommMon
    fun (F G : lax_braided_functor C D) (α : F ⟶ G) =>
      nat_trans.mk
        fun (A : CommMon_ C) =>
          Mon_.hom.mk
            (nat_trans.app (monoidal_nat_trans.to_nat_trans α) (Mon_.X (CommMon_.to_Mon_ A)))

end category_theory.lax_braided_functor


namespace CommMon_


namespace equiv_lax_braided_functor_punit


/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simp] theorem lax_braided_to_CommMon_map (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C]
    (F : category_theory.lax_braided_functor (category_theory.discrete PUnit) C)
    (G : category_theory.lax_braided_functor (category_theory.discrete PUnit) C) (α : F ⟶ G) :
    category_theory.functor.map (lax_braided_to_CommMon C) α =
        category_theory.nat_trans.app
          (category_theory.functor.map
            (category_theory.lax_braided_functor.map_CommMon_functor
              (category_theory.discrete PUnit) C)
            α)
          (trivial (category_theory.discrete PUnit)) :=
  Eq.refl (category_theory.functor.map (lax_braided_to_CommMon C) α)

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simp] theorem CommMon_to_lax_braided_obj_to_lax_monoidal_functor_to_functor_obj (C : Type u₁)
    [category_theory.category C] [category_theory.monoidal_category C]
    [category_theory.braided_category C] (A : CommMon_ C) (_x : category_theory.discrete PUnit) :
    category_theory.functor.obj
          (category_theory.lax_monoidal_functor.to_functor
            (category_theory.lax_braided_functor.to_lax_monoidal_functor
              (category_theory.functor.obj (CommMon_to_lax_braided C) A)))
          _x =
        Mon_.X (to_Mon_ A) :=
  sorry

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simp] theorem unit_iso_hom_app_to_nat_trans_app (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C]
    (X : category_theory.lax_braided_functor (category_theory.discrete PUnit) C) :
    ∀ (X_1 : category_theory.discrete PUnit),
        category_theory.nat_trans.app
            (category_theory.monoidal_nat_trans.to_nat_trans
              (category_theory.nat_trans.app (category_theory.iso.hom (unit_iso C)) X))
            X_1 =
          category_theory.eq_to_hom
            (congr_arg
              (category_theory.functor.obj
                (category_theory.lax_monoidal_functor.to_functor
                  (category_theory.lax_braided_functor.to_lax_monoidal_functor X)))
              (unit_iso._proof_1 X_1)) :=
  sorry

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simp] theorem counit_iso_inv_app_hom (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] (X : CommMon_ C) :
    Mon_.hom.hom (category_theory.nat_trans.app (category_theory.iso.inv (counit_iso C)) X) = 𝟙 :=
  Eq.refl 𝟙

end equiv_lax_braided_functor_punit


/--
Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simp] theorem equiv_lax_braided_functor_punit_functor (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] [category_theory.braided_category C] :
    category_theory.equivalence.functor (equiv_lax_braided_functor_punit C) =
        equiv_lax_braided_functor_punit.lax_braided_to_CommMon C :=
  Eq.refl (category_theory.equivalence.functor (equiv_lax_braided_functor_punit C))

end Mathlib