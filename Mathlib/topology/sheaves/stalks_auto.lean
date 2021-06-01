/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.category.Top.open_nhds
import Mathlib.topology.sheaves.presheaf
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.limits.types
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

namespace Top.presheaf


/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (C : Type u) [category_theory.category C] [category_theory.limits.has_colimits C]
    {X : Top} (x : ↥X) : presheaf C X ⥤ C :=
  category_theory.functor.obj
      (category_theory.whiskering_left (topological_space.open_nhds xᵒᵖ)
        (topological_space.opens ↥Xᵒᵖ) C)
      (category_theory.functor.op (topological_space.open_nhds.inclusion x)) ⋙
    category_theory.limits.colim

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk {C : Type u} [category_theory.category C] [category_theory.limits.has_colimits C]
    {X : Top} (ℱ : presheaf C X) (x : ↥X) : C :=
  category_theory.functor.obj (stalk_functor C x) ℱ

@[simp] theorem stalk_functor_obj {C : Type u} [category_theory.category C]
    [category_theory.limits.has_colimits C] {X : Top} (ℱ : presheaf C X) (x : ↥X) :
    category_theory.functor.obj (stalk_functor C x) ℱ = stalk ℱ x :=
  rfl

/--
The germ of a section of a presheaf over an open at a point of that open.
-/
def germ {C : Type u} [category_theory.category C] [category_theory.limits.has_colimits C] {X : Top}
    (F : presheaf C X) {U : topological_space.opens ↥X} (x : ↥U) :
    category_theory.functor.obj F (opposite.op U) ⟶ stalk F ↑x :=
  category_theory.limits.colimit.ι
    (category_theory.functor.op (topological_space.open_nhds.inclusion (subtype.val x)) ⋙ F)
    (opposite.op { val := U, property := sorry })

/-- For a `Type` valued presheaf, every point in a stalk is a germ. -/
theorem germ_exist {X : Top} (F : presheaf (Type v) X) (x : ↥X) (t : stalk F x) :
    ∃ (U : topological_space.opens ↥X),
        ∃ (m : x ∈ U),
          ∃ (s : category_theory.functor.obj F (opposite.op U)),
            germ F { val := x, property := m } s = t :=
  sorry

theorem germ_eq {X : Top} (F : presheaf (Type v) X) {U : topological_space.opens ↥X}
    {V : topological_space.opens ↥X} (x : ↥X) (mU : x ∈ U) (mV : x ∈ V)
    (s : category_theory.functor.obj F (opposite.op U))
    (t : category_theory.functor.obj F (opposite.op V))
    (h : germ F { val := x, property := mU } s = germ F { val := x, property := mV } t) :
    ∃ (W : topological_space.opens ↥X),
        ∃ (m : x ∈ W),
          ∃ (iU : W ⟶ U),
            ∃ (iV : W ⟶ V),
              category_theory.functor.map F (category_theory.has_hom.hom.op iU) s =
                category_theory.functor.map F (category_theory.has_hom.hom.op iV) t :=
  sorry

@[simp] theorem germ_res {C : Type u} [category_theory.category C]
    [category_theory.limits.has_colimits C] {X : Top} (F : presheaf C X)
    {U : topological_space.opens ↥X} {V : topological_space.opens ↥X} (i : U ⟶ V) (x : ↥U) :
    category_theory.functor.map F (category_theory.has_hom.hom.op i) ≫ germ F x =
        germ F (coe_fn i x) :=
  sorry

@[simp] theorem germ_res_apply {X : Top} (F : presheaf (Type v) X) {U : topological_space.opens ↥X}
    {V : topological_space.opens ↥X} (i : U ⟶ V) (x : ↥U)
    (f : category_theory.functor.obj F (opposite.op V)) :
    germ F x (category_theory.functor.map F (category_theory.has_hom.hom.op i) f) =
        germ F (coe_fn i x) f :=
  sorry

/-- A variant when the open sets are written in `(opens X)ᵒᵖ`. -/
@[simp] theorem germ_res_apply' {X : Top} (F : presheaf (Type v) X)
    {U : topological_space.opens ↥Xᵒᵖ} {V : topological_space.opens ↥Xᵒᵖ} (i : V ⟶ U)
    (x : ↥(opposite.unop U)) (f : category_theory.functor.obj F V) :
    germ F x (category_theory.functor.map F i f) =
        germ F (coe_fn (category_theory.has_hom.hom.unop i) x) f :=
  sorry

theorem germ_ext {X : Top} {D : Type u} [category_theory.category D]
    [category_theory.concrete_category D] [category_theory.limits.has_colimits D] (F : presheaf D X)
    {U : topological_space.opens ↥X} {V : topological_space.opens ↥X} {x : ↥X} {hxU : x ∈ U}
    {hxV : x ∈ V} (W : topological_space.opens ↥X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V)
    {sU : ↥(category_theory.functor.obj F (opposite.op U))}
    {sV : ↥(category_theory.functor.obj F (opposite.op V))}
    (ih :
      coe_fn (category_theory.functor.map F (category_theory.has_hom.hom.op iWU)) sU =
        coe_fn (category_theory.functor.map F (category_theory.has_hom.hom.op iWV)) sV) :
    coe_fn (germ F { val := x, property := hxU }) sU =
        coe_fn (germ F { val := x, property := hxV }) sV :=
  sorry

theorem stalk_hom_ext {C : Type u} [category_theory.category C]
    [category_theory.limits.has_colimits C] {X : Top} (F : presheaf C X) {x : ↥X} {Y : C}
    {f₁ : stalk F x ⟶ Y} {f₂ : stalk F x ⟶ Y}
    (ih :
      ∀ (U : topological_space.opens ↥X) (hxU : x ∈ U),
        germ F { val := x, property := hxU } ≫ f₁ = germ F { val := x, property := hxU } ≫ f₂) :
    f₁ = f₂ :=
  sorry

def stalk_pushforward (C : Type u) [category_theory.category C]
    [category_theory.limits.has_colimits C] {X : Top} {Y : Top} (f : X ⟶ Y) (ℱ : presheaf C X)
    (x : ↥X) : stalk (f _* ℱ) (coe_fn f x) ⟶ stalk ℱ x :=
  category_theory.functor.map category_theory.limits.colim
      (category_theory.whisker_right
        (category_theory.nat_trans.op
          (category_theory.iso.inv (topological_space.open_nhds.inclusion_map_iso f x)))
        ℱ) ≫
    category_theory.limits.colimit.pre
      (category_theory.functor.obj
        (category_theory.functor.obj
          (category_theory.whiskering_left (topological_space.open_nhds xᵒᵖ)
            (topological_space.opens ↥Xᵒᵖ) C)
          (category_theory.functor.op (topological_space.open_nhds.inclusion x)))
        ℱ)
      (category_theory.functor.op (topological_space.open_nhds.map f x))

-- Here are two other potential solutions, suggested by @fpvandoorn at

-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>

-- However, I can't get the subsequent two proofs to work with either one.

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=

-- colim.map ((functor.associator _ _ _).inv ≫

--   whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) ≫

-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) : (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=

-- (colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) :

--   colim.obj ((open_nhds.inclusion (f x) ⋙ opens.map f).op ⋙ ℱ) ⟶ _) ≫

-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

namespace stalk_pushforward


@[simp] theorem id (C : Type u) [category_theory.category C] [category_theory.limits.has_colimits C]
    {X : Top} (ℱ : presheaf C X) (x : ↥X) :
    stalk_pushforward C 𝟙 ℱ x =
        category_theory.functor.map (stalk_functor C x)
          (category_theory.iso.hom (pushforward.id ℱ)) :=
  sorry

-- This proof is sadly not at all robust:

-- having to use `erw` at all is a bad sign.

@[simp] theorem comp (C : Type u) [category_theory.category C]
    [category_theory.limits.has_colimits C] {X : Top} {Y : Top} {Z : Top} (ℱ : presheaf C X)
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) :
    stalk_pushforward C (f ≫ g) ℱ x =
        stalk_pushforward C g (f _* ℱ) (coe_fn f x) ≫ stalk_pushforward C f ℱ x :=
  sorry

end Mathlib