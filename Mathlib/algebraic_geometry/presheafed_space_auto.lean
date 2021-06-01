/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.presheaf
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

namespace algebraic_geometry


/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
structure PresheafedSpace (C : Type u) [category_theory.category C] where
  carrier : Top
  presheaf : Top.presheaf C carrier

namespace PresheafedSpace


protected instance coe_carrier {C : Type u} [category_theory.category C] :
    has_coe (PresheafedSpace C) Top :=
  has_coe.mk fun (X : PresheafedSpace C) => carrier X

@[simp] theorem as_coe {C : Type u} [category_theory.category C] (X : PresheafedSpace C) :
    carrier X = ↑X :=
  rfl

@[simp] theorem mk_coe {C : Type u} [category_theory.category C] (carrier : Top)
    (presheaf : Top.presheaf C carrier) : ↑(mk carrier presheaf) = carrier :=
  rfl

protected instance topological_space {C : Type u} [category_theory.category C]
    (X : PresheafedSpace C) : topological_space ↥X :=
  category_theory.bundled.str (carrier X)

/-- The constant presheaf on `X` with value `Z`. -/
def const {C : Type u} [category_theory.category C] (X : Top) (Z : C) : PresheafedSpace C :=
  mk X
    (category_theory.functor.mk (fun (U : topological_space.opens ↥Xᵒᵖ) => Z)
      fun (U V : topological_space.opens ↥Xᵒᵖ) (f : U ⟶ V) => 𝟙)

protected instance inhabited {C : Type u} [category_theory.category C] [Inhabited C] :
    Inhabited (PresheafedSpace C) :=
  { default := const (Top.of pempty) Inhabited.default }

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
    `f` between the underlying topological spaces, and a (notice contravariant!) map
    from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
structure hom {C : Type u} [category_theory.category C] (X : PresheafedSpace C)
    (Y : PresheafedSpace C)
    where
  base : ↑X ⟶ ↑Y
  c : PresheafedSpace.presheaf Y ⟶ base _* PresheafedSpace.presheaf X

theorem ext {C : Type u} [category_theory.category C] {X : PresheafedSpace C}
    {Y : PresheafedSpace C} (α : hom X Y) (β : hom X Y) (w : hom.base α = hom.base β)
    (h :
      hom.c α ≫
          category_theory.whisker_right
            (category_theory.nat_trans.op
              (category_theory.iso.inv
                (topological_space.opens.map_iso (hom.base α) (hom.base β) w)))
            (PresheafedSpace.presheaf X) =
        hom.c β) :
    α = β :=
  sorry

/-- The identity morphism of a `PresheafedSpace`. -/
def id {C : Type u} [category_theory.category C] (X : PresheafedSpace C) : hom X X :=
  hom.mk 𝟙
    (category_theory.iso.inv (category_theory.functor.left_unitor (PresheafedSpace.presheaf X)) ≫
      category_theory.whisker_right
        (category_theory.nat_trans.op
          (category_theory.iso.hom (topological_space.opens.map_id (carrier X))))
        (PresheafedSpace.presheaf X))

protected instance hom_inhabited {C : Type u} [category_theory.category C] (X : PresheafedSpace C) :
    Inhabited (hom X X) :=
  { default := id X }

/-- Composition of morphisms of `PresheafedSpace`s. -/
def comp {C : Type u} [category_theory.category C] {X : PresheafedSpace C} {Y : PresheafedSpace C}
    {Z : PresheafedSpace C} (α : hom X Y) (β : hom Y Z) : hom X Z :=
  hom.mk (hom.base α ≫ hom.base β)
    (hom.c β ≫
      category_theory.whisker_left
          (category_theory.functor.op (topological_space.opens.map (hom.base β))) (hom.c α) ≫
        category_theory.iso.inv
          (Top.presheaf.pushforward.comp (PresheafedSpace.presheaf X) (hom.base α) (hom.base β)))

/- The proofs below can be done by `tidy`, but it is too slow,
   and we don't have a tactic caching mechanism. -/

/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
    from the presheaf on the target to the pushforward of the presheaf on the source. -/
protected instance category_of_PresheafedSpaces (C : Type u) [category_theory.category C] :
    category_theory.category (PresheafedSpace C) :=
  category_theory.category.mk

@[simp] theorem id_base {C : Type u} [category_theory.category C] (X : PresheafedSpace C) :
    hom.base 𝟙 = 𝟙 :=
  rfl

theorem id_c {C : Type u} [category_theory.category C] (X : PresheafedSpace C) :
    hom.c 𝟙 =
        category_theory.iso.inv (category_theory.functor.left_unitor (PresheafedSpace.presheaf X)) ≫
          category_theory.whisker_right
            (category_theory.nat_trans.op
              (category_theory.iso.hom (topological_space.opens.map_id (carrier X))))
            (PresheafedSpace.presheaf X) :=
  rfl

@[simp] theorem id_c_app {C : Type u} [category_theory.category C] (X : PresheafedSpace C)
    (U : topological_space.opens ↥(carrier X)ᵒᵖ) :
    category_theory.nat_trans.app (hom.c 𝟙) U =
        category_theory.eq_to_hom
          (opposite.op_induction
            (fun (U : topological_space.opens ↥(carrier X)) =>
              subtype.cases_on U
                fun (U_val : set ↥(carrier X)) (U_property : is_open U_val) =>
                  Eq.refl
                    (category_theory.functor.obj (PresheafedSpace.presheaf X)
                      (opposite.op { val := U_val, property := U_property })))
            U) :=
  sorry

@[simp] theorem comp_base {C : Type u} [category_theory.category C] {X : PresheafedSpace C}
    {Y : PresheafedSpace C} {Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    hom.base (f ≫ g) = hom.base f ≫ hom.base g :=
  rfl

@[simp] theorem comp_c_app {C : Type u} [category_theory.category C] {X : PresheafedSpace C}
    {Y : PresheafedSpace C} {Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z)
    (U : topological_space.opens ↥(carrier Z)ᵒᵖ) :
    category_theory.nat_trans.app (hom.c (α ≫ β)) U =
        category_theory.nat_trans.app (hom.c β) U ≫
          category_theory.nat_trans.app (hom.c α)
              (opposite.op
                (category_theory.functor.obj (topological_space.opens.map (hom.base β))
                  (opposite.unop U))) ≫
            category_theory.nat_trans.app
              (category_theory.iso.inv
                (Top.presheaf.pushforward.comp (PresheafedSpace.presheaf X) (hom.base α)
                  (hom.base β)))
              U :=
  rfl

theorem congr_app {C : Type u} [category_theory.category C] {X : PresheafedSpace C}
    {Y : PresheafedSpace C} {α : X ⟶ Y} {β : X ⟶ Y} (h : α = β)
    (U : topological_space.opens ↥(carrier Y)ᵒᵖ) :
    category_theory.nat_trans.app (hom.c α) U =
        category_theory.nat_trans.app (hom.c β) U ≫
          category_theory.functor.map (PresheafedSpace.presheaf X)
            (category_theory.eq_to_hom
              (Eq._oldrec
                (Eq.refl
                  (category_theory.functor.obj
                    (category_theory.functor.op (topological_space.opens.map (hom.base α))) U))
                h)) :=
  sorry

/-- The forgetful functor from `PresheafedSpace` to `Top`. -/
def forget (C : Type u) [category_theory.category C] : PresheafedSpace C ⥤ Top :=
  category_theory.functor.mk (fun (X : PresheafedSpace C) => ↑X)
    fun (X Y : PresheafedSpace C) (f : X ⟶ Y) => hom.base f

/--
The restriction of a presheafed space along an open embedding into the space.
-/
@[simp] theorem restrict_carrier {C : Type u} [category_theory.category C] {U : Top}
    (X : PresheafedSpace C) (f : U ⟶ ↑X) (h : open_embedding ⇑f) : carrier (restrict X f h) = U :=
  Eq.refl (carrier (restrict X f h))

/--
The map from the restriction of a presheafed space.
-/
@[simp] theorem of_restrict_c_app {C : Type u} [category_theory.category C] (U : Top)
    (X : PresheafedSpace C) (f : U ⟶ ↑X) (h : open_embedding ⇑f)
    (V : topological_space.opens ↥(carrier X)ᵒᵖ) :
    category_theory.nat_trans.app (hom.c (of_restrict U X f h)) V =
        category_theory.functor.map (PresheafedSpace.presheaf X)
          (category_theory.has_hom.hom.op
            (coe_fn
              (equiv.symm
                (category_theory.adjunction.hom_equiv
                  (is_open_map.adjunction (of_restrict._proof_2 U X f h))
                  (category_theory.functor.obj (topological_space.opens.map f) (opposite.unop V))
                  (opposite.unop V)))
              𝟙)) :=
  Eq.refl (category_theory.nat_trans.app (hom.c (of_restrict U X f h)) V)

/--
The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simp] theorem to_restrict_top_base_to_fun_coe {C : Type u} [category_theory.category C]
    (X : PresheafedSpace C) (x : ↥↑X) : ↑(coe_fn (hom.base (to_restrict_top X)) x) = x :=
  Eq.refl ↑(coe_fn (hom.base (to_restrict_top X)) x)

/--
The isomorphism from the restriction to the top subspace.
-/
def restrict_top_iso {C : Type u} [category_theory.category C] (X : PresheafedSpace C) :
    restrict X (topological_space.opens.inclusion ⊤) (restrict_top_iso._proof_1 X) ≅ X :=
  category_theory.iso.mk
    (of_restrict (category_theory.functor.obj (topological_space.opens.to_Top ↑X) ⊤) X
      (topological_space.opens.inclusion ⊤) sorry)
    (to_restrict_top X)

/--
The global sections, notated Gamma.
-/
@[simp] theorem Γ_obj {C : Type u} [category_theory.category C] (X : PresheafedSpace Cᵒᵖ) :
    category_theory.functor.obj Γ X =
        category_theory.functor.obj (PresheafedSpace.presheaf (opposite.unop X)) (opposite.op ⊤) :=
  Eq.refl (category_theory.functor.obj Γ X)

theorem Γ_obj_op {C : Type u} [category_theory.category C] (X : PresheafedSpace C) :
    category_theory.functor.obj Γ (opposite.op X) =
        category_theory.functor.obj (PresheafedSpace.presheaf X) (opposite.op ⊤) :=
  rfl

theorem Γ_map_op {C : Type u} [category_theory.category C] {X : PresheafedSpace C}
    {Y : PresheafedSpace C} (f : X ⟶ Y) :
    category_theory.functor.map Γ (category_theory.has_hom.hom.op f) =
        category_theory.nat_trans.app (hom.c f) (opposite.op ⊤) ≫
          category_theory.functor.map (PresheafedSpace.presheaf X)
            (category_theory.has_hom.hom.op (topological_space.opens.le_map_top (hom.base f) ⊤)) :=
  rfl

end PresheafedSpace


end algebraic_geometry


namespace category_theory


namespace functor


/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
    giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
def map_presheaf {C : Type u} [category C] {D : Type u} [category D] (F : C ⥤ D) :
    algebraic_geometry.PresheafedSpace C ⥤ algebraic_geometry.PresheafedSpace D :=
  mk
    (fun (X : algebraic_geometry.PresheafedSpace C) =>
      algebraic_geometry.PresheafedSpace.mk (algebraic_geometry.PresheafedSpace.carrier X)
        (algebraic_geometry.PresheafedSpace.presheaf X ⋙ F))
    fun (X Y : algebraic_geometry.PresheafedSpace C) (f : X ⟶ Y) =>
      algebraic_geometry.PresheafedSpace.hom.mk (algebraic_geometry.PresheafedSpace.hom.base f)
        (whisker_right (algebraic_geometry.PresheafedSpace.hom.c f) F)

@[simp] theorem map_presheaf_obj_X {C : Type u} [category C] {D : Type u} [category D] (F : C ⥤ D)
    (X : algebraic_geometry.PresheafedSpace C) : ↑(obj (map_presheaf F) X) = ↑X :=
  rfl

@[simp] theorem map_presheaf_obj_presheaf {C : Type u} [category C] {D : Type u} [category D]
    (F : C ⥤ D) (X : algebraic_geometry.PresheafedSpace C) :
    algebraic_geometry.PresheafedSpace.presheaf (obj (map_presheaf F) X) =
        algebraic_geometry.PresheafedSpace.presheaf X ⋙ F :=
  rfl

@[simp] theorem map_presheaf_map_f {C : Type u} [category C] {D : Type u} [category D] (F : C ⥤ D)
    {X : algebraic_geometry.PresheafedSpace C} {Y : algebraic_geometry.PresheafedSpace C}
    (f : X ⟶ Y) :
    algebraic_geometry.PresheafedSpace.hom.base (map (map_presheaf F) f) =
        algebraic_geometry.PresheafedSpace.hom.base f :=
  rfl

@[simp] theorem map_presheaf_map_c {C : Type u} [category C] {D : Type u} [category D] (F : C ⥤ D)
    {X : algebraic_geometry.PresheafedSpace C} {Y : algebraic_geometry.PresheafedSpace C}
    (f : X ⟶ Y) :
    algebraic_geometry.PresheafedSpace.hom.c (map (map_presheaf F) f) =
        whisker_right (algebraic_geometry.PresheafedSpace.hom.c f) F :=
  rfl

end functor


namespace nat_trans


/--
A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
def on_presheaf {C : Type u} [category C] {D : Type u} [category D] {F : C ⥤ D} {G : C ⥤ D}
    (α : F ⟶ G) : functor.map_presheaf G ⟶ functor.map_presheaf F :=
  mk
    fun (X : algebraic_geometry.PresheafedSpace C) =>
      algebraic_geometry.PresheafedSpace.hom.mk 𝟙
        (whisker_left (algebraic_geometry.PresheafedSpace.presheaf X) α ≫
          iso.inv (functor.left_unitor (algebraic_geometry.PresheafedSpace.presheaf X ⋙ G)) ≫
            whisker_right
              (nat_trans.op
                (iso.hom
                  (topological_space.opens.map_id (algebraic_geometry.PresheafedSpace.carrier X))))
              (algebraic_geometry.PresheafedSpace.presheaf X ⋙ G))

end Mathlib