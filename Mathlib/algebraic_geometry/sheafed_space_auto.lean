/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.presheafed_space
import Mathlib.topology.sheaves.sheaf
import Mathlib.PostPort

universes v u l u_1 

namespace Mathlib

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

namespace algebraic_geometry


/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
structure SheafedSpace (C : Type u) [category_theory.category C]
    [category_theory.limits.has_products C]
    extends PresheafedSpace C where
  sheaf_condition : Top.presheaf.sheaf_condition (PresheafedSpace.presheaf _to_PresheafedSpace)

namespace SheafedSpace


protected instance coe_carrier {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] : has_coe (SheafedSpace C) Top :=
  has_coe.mk fun (X : SheafedSpace C) => PresheafedSpace.carrier (to_PresheafedSpace X)

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
def sheaf {C : Type u} [category_theory.category C] [category_theory.limits.has_products C]
    (X : SheafedSpace C) : Top.sheaf C ↑X :=
  Top.sheaf.mk (PresheafedSpace.presheaf (to_PresheafedSpace X)) (sheaf_condition X)

@[simp] theorem as_coe {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] (X : SheafedSpace C) :
    PresheafedSpace.carrier (to_PresheafedSpace X) = ↑X :=
  rfl

@[simp] theorem mk_coe {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] (carrier : Top) (presheaf : Top.presheaf C carrier)
    (h :
      Top.presheaf.sheaf_condition
        (PresheafedSpace.presheaf (PresheafedSpace.mk carrier presheaf))) :
    ↑(mk (PresheafedSpace.mk carrier presheaf) h) = carrier :=
  rfl

protected instance topological_space {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] (X : SheafedSpace C) : topological_space ↥X :=
  category_theory.bundled.str (PresheafedSpace.carrier (to_PresheafedSpace X))

/-- The trivial `punit` valued sheaf on any topological space. -/
def punit (X : Top) : SheafedSpace (category_theory.discrete PUnit) :=
  mk
    (PresheafedSpace.mk (PresheafedSpace.carrier (PresheafedSpace.const X PUnit.unit))
      (PresheafedSpace.presheaf (PresheafedSpace.const X PUnit.unit)))
    (Top.presheaf.sheaf_condition_punit
      (PresheafedSpace.presheaf
        (PresheafedSpace.mk (PresheafedSpace.carrier (PresheafedSpace.const X PUnit.unit))
          (PresheafedSpace.presheaf (PresheafedSpace.const X PUnit.unit)))))

protected instance inhabited : Inhabited (SheafedSpace (category_theory.discrete PUnit)) :=
  { default := punit (Top.of pempty) }

protected instance category_theory.category {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] : category_theory.category (SheafedSpace C) :=
  (fun
      (this :
      category_theory.category
        (category_theory.induced_category (PresheafedSpace C) to_PresheafedSpace)) =>
      this)
    (category_theory.induced_category.category to_PresheafedSpace)

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
def forget_to_PresheafedSpace {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] : SheafedSpace C ⥤ PresheafedSpace C :=
  category_theory.induced_functor to_PresheafedSpace

@[simp] theorem id_base {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] (X : SheafedSpace C) : PresheafedSpace.hom.base 𝟙 = 𝟙 :=
  rfl

theorem id_c {C : Type u} [category_theory.category C] [category_theory.limits.has_products C]
    (X : SheafedSpace C) :
    PresheafedSpace.hom.c 𝟙 =
        category_theory.iso.inv
            (category_theory.functor.left_unitor
              (PresheafedSpace.presheaf (to_PresheafedSpace X))) ≫
          category_theory.whisker_right
            (category_theory.nat_trans.op
              (category_theory.iso.hom
                (topological_space.opens.map_id (PresheafedSpace.carrier (to_PresheafedSpace X)))))
            (PresheafedSpace.presheaf (to_PresheafedSpace X)) :=
  rfl

@[simp] theorem id_c_app {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] (X : SheafedSpace C)
    (U : topological_space.opens ↥(PresheafedSpace.carrier (to_PresheafedSpace X))ᵒᵖ) :
    category_theory.nat_trans.app (PresheafedSpace.hom.c 𝟙) U =
        category_theory.eq_to_hom
          (opposite.op_induction
            (fun (U : topological_space.opens ↥(PresheafedSpace.carrier (to_PresheafedSpace X))) =>
              subtype.cases_on U
                fun (U_val : set ↥(PresheafedSpace.carrier (to_PresheafedSpace X)))
                  (U_property : is_open U_val) =>
                  Eq.refl
                    (category_theory.functor.obj (PresheafedSpace.presheaf (to_PresheafedSpace X))
                      (opposite.op { val := U_val, property := U_property })))
            U) :=
  sorry

@[simp] theorem comp_base {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] {X : SheafedSpace C} {Y : SheafedSpace C}
    {Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    PresheafedSpace.hom.base (f ≫ g) = PresheafedSpace.hom.base f ≫ PresheafedSpace.hom.base g :=
  rfl

@[simp] theorem comp_c_app {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] {X : SheafedSpace C} {Y : SheafedSpace C}
    {Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z)
    (U : topological_space.opens ↥(PresheafedSpace.carrier (to_PresheafedSpace Z))ᵒᵖ) :
    category_theory.nat_trans.app (PresheafedSpace.hom.c (α ≫ β)) U =
        category_theory.nat_trans.app (PresheafedSpace.hom.c β) U ≫
          category_theory.nat_trans.app (PresheafedSpace.hom.c α)
              (opposite.op
                (category_theory.functor.obj
                  (topological_space.opens.map (PresheafedSpace.hom.base β)) (opposite.unop U))) ≫
            category_theory.nat_trans.app
              (category_theory.iso.inv
                (Top.presheaf.pushforward.comp (PresheafedSpace.presheaf (to_PresheafedSpace X))
                  (PresheafedSpace.hom.base α) (PresheafedSpace.hom.base β)))
              U :=
  rfl

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
def forget (C : Type u) [category_theory.category C] [category_theory.limits.has_products C] :
    SheafedSpace C ⥤ Top :=
  category_theory.functor.mk (fun (X : SheafedSpace C) => ↑X)
    fun (X Y : SheafedSpace C) (f : X ⟶ Y) => PresheafedSpace.hom.base f

/--
The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {C : Type u} [category_theory.category C] [category_theory.limits.has_products C]
    {U : Top} (X : SheafedSpace C) (f : U ⟶ ↑X) (h : open_embedding ⇑f) : SheafedSpace C :=
  sorry

/--
The global sections, notated Gamma.
-/
def Γ {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] :
    SheafedSpace Cᵒᵖ ⥤ C :=
  category_theory.functor.op forget_to_PresheafedSpace ⋙ PresheafedSpace.Γ

theorem Γ_def {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] :
    Γ = category_theory.functor.op forget_to_PresheafedSpace ⋙ PresheafedSpace.Γ :=
  rfl

@[simp] theorem Γ_obj {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] (X : SheafedSpace Cᵒᵖ) :
    category_theory.functor.obj Γ X =
        category_theory.functor.obj
          (PresheafedSpace.presheaf (to_PresheafedSpace (opposite.unop X))) (opposite.op ⊤) :=
  rfl

theorem Γ_obj_op {C : Type u} [category_theory.category C] [category_theory.limits.has_products C]
    (X : SheafedSpace C) :
    category_theory.functor.obj Γ (opposite.op X) =
        category_theory.functor.obj (PresheafedSpace.presheaf (to_PresheafedSpace X))
          (opposite.op ⊤) :=
  rfl

@[simp] theorem Γ_map {C : Type u} [category_theory.category C]
    [category_theory.limits.has_products C] {X : SheafedSpace Cᵒᵖ} {Y : SheafedSpace Cᵒᵖ}
    (f : X ⟶ Y) :
    category_theory.functor.map Γ f =
        category_theory.nat_trans.app (PresheafedSpace.hom.c (category_theory.has_hom.hom.unop f))
            (opposite.op ⊤) ≫
          category_theory.functor.map
            (PresheafedSpace.presheaf (to_PresheafedSpace (opposite.unop Y)))
            (category_theory.has_hom.hom.op
              (topological_space.opens.le_map_top
                (PresheafedSpace.hom.base (category_theory.has_hom.hom.unop f)) ⊤)) :=
  rfl

theorem Γ_map_op {C : Type u} [category_theory.category C] [category_theory.limits.has_products C]
    {X : SheafedSpace C} {Y : SheafedSpace C} (f : X ⟶ Y) :
    category_theory.functor.map Γ (category_theory.has_hom.hom.op f) =
        category_theory.nat_trans.app (PresheafedSpace.hom.c f) (opposite.op ⊤) ≫
          category_theory.functor.map (PresheafedSpace.presheaf (to_PresheafedSpace X))
            (category_theory.has_hom.hom.op
              (topological_space.opens.le_map_top (PresheafedSpace.hom.base f) ⊤)) :=
  rfl

end Mathlib