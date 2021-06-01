/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.category.Top.opens
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Presheaves on a topological space

We define `presheaf C X` simply as `(opens X)ᵒᵖ ⥤ C`,
and inherit the category structure with natural transformations as morphisms.

We define
* `pushforward_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C`
with notation `f _* ℱ`
and for `ℱ : X.presheaf C` provide the natural isomorphisms
* `pushforward.id : (𝟙 X) _* ℱ ≅ ℱ``
* `pushforward.comp : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ)`
along with their `@[simp]` lemmas.
-/

namespace Top


def presheaf (C : Type u) [category_theory.category C] (X : Top) := topological_space.opens ↥Xᵒᵖ ⥤ C

namespace presheaf


/-- Pushforward a presheaf on `X` along a continuous map `f : X ⟶ Y`, obtaining a presheaf on `Y`. -/
def pushforward_obj {C : Type u} [category_theory.category C] {X : Top} {Y : Top} (f : X ⟶ Y)
    (ℱ : presheaf C X) : presheaf C Y :=
  category_theory.functor.op (topological_space.opens.map f) ⋙ ℱ

infixl:80 " _* " => Mathlib.Top.presheaf.pushforward_obj

@[simp] theorem pushforward_obj_obj {C : Type u} [category_theory.category C] {X : Top} {Y : Top}
    (f : X ⟶ Y) (ℱ : presheaf C X) (U : topological_space.opens ↥Yᵒᵖ) :
    category_theory.functor.obj (f _* ℱ) U =
        category_theory.functor.obj ℱ
          (category_theory.functor.obj (category_theory.functor.op (topological_space.opens.map f))
            U) :=
  rfl

@[simp] theorem pushforward_obj_map {C : Type u} [category_theory.category C] {X : Top} {Y : Top}
    (f : X ⟶ Y) (ℱ : presheaf C X) {U : topological_space.opens ↥Yᵒᵖ}
    {V : topological_space.opens ↥Yᵒᵖ} (i : U ⟶ V) :
    category_theory.functor.map (f _* ℱ) i =
        category_theory.functor.map ℱ
          (category_theory.functor.map (category_theory.functor.op (topological_space.opens.map f))
            i) :=
  rfl

def pushforward_eq {C : Type u} [category_theory.category C] {X : Top} {Y : Top} {f : X ⟶ Y}
    {g : X ⟶ Y} (h : f = g) (ℱ : presheaf C X) : f _* ℱ ≅ g _* ℱ :=
  category_theory.iso_whisker_right
    (category_theory.nat_iso.op (category_theory.iso.symm (topological_space.opens.map_iso f g h)))
    ℱ

@[simp] theorem pushforward_eq_hom_app {C : Type u} [category_theory.category C] {X : Top} {Y : Top}
    {f : X ⟶ Y} {g : X ⟶ Y} (h : f = g) (ℱ : presheaf C X) (U : topological_space.opens ↥Yᵒᵖ) :
    category_theory.nat_trans.app (category_theory.iso.hom (pushforward_eq h ℱ)) U =
        category_theory.functor.map ℱ
          (id
            (category_theory.has_hom.hom.op
              (category_theory.eq_to_hom
                (eq.mpr
                  (id
                    (Eq._oldrec
                      (Eq.refl
                        (category_theory.functor.obj (topological_space.opens.map g)
                            (opposite.unop U) =
                          category_theory.functor.obj (topological_space.opens.map f)
                            (opposite.unop U)))
                      h))
                  (Eq.refl
                    (category_theory.functor.obj (topological_space.opens.map g)
                      (opposite.unop U))))))) :=
  rfl

@[simp] theorem pushforward_eq_rfl {C : Type u} [category_theory.category C] {X : Top} {Y : Top}
    (f : X ⟶ Y) (ℱ : presheaf C X) (U : topological_space.opens ↥Y) :
    category_theory.nat_trans.app (category_theory.iso.hom (pushforward_eq rfl ℱ)) (opposite.op U) =
        𝟙 :=
  sorry

theorem pushforward_eq_eq {C : Type u} [category_theory.category C] {X : Top} {Y : Top} {f : X ⟶ Y}
    {g : X ⟶ Y} (h₁ : f = g) (h₂ : f = g) (ℱ : presheaf C X) :
    pushforward_eq h₁ ℱ = pushforward_eq h₂ ℱ :=
  rfl

namespace pushforward


def id {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X) : 𝟙 _* ℱ ≅ ℱ :=
  category_theory.iso_whisker_right
      (category_theory.nat_iso.op (category_theory.iso.symm (topological_space.opens.map_id X)))
      ℱ ≪≫
    category_theory.functor.left_unitor ℱ

@[simp] theorem id_hom_app' {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X)
    (U : set ↥X) (p : is_open U) :
    category_theory.nat_trans.app (category_theory.iso.hom (id ℱ))
          (opposite.op { val := U, property := p }) =
        category_theory.functor.map ℱ 𝟙 :=
  sorry

@[simp] theorem id_hom_app {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X)
    (U : topological_space.opens ↥Xᵒᵖ) :
    category_theory.nat_trans.app (category_theory.iso.hom (id ℱ)) U =
        category_theory.functor.map ℱ
          (category_theory.eq_to_hom (topological_space.opens.op_map_id_obj U)) :=
  sorry

@[simp] theorem id_inv_app' {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X)
    (U : set ↥X) (p : is_open U) :
    category_theory.nat_trans.app (category_theory.iso.inv (id ℱ))
          (opposite.op { val := U, property := p }) =
        category_theory.functor.map ℱ 𝟙 :=
  sorry

def comp {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X) {Y : Top} {Z : Top}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
  category_theory.iso_whisker_right
    (category_theory.nat_iso.op (category_theory.iso.symm (topological_space.opens.map_comp f g))) ℱ

@[simp] theorem comp_hom_app {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X)
    {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : topological_space.opens ↥Zᵒᵖ) :
    category_theory.nat_trans.app (category_theory.iso.hom (comp ℱ f g)) U = 𝟙 :=
  sorry

@[simp] theorem comp_inv_app {C : Type u} [category_theory.category C] {X : Top} (ℱ : presheaf C X)
    {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (U : topological_space.opens ↥Zᵒᵖ) :
    category_theory.nat_trans.app (category_theory.iso.inv (comp ℱ f g)) U = 𝟙 :=
  sorry

end pushforward


/--
A morphism of presheaves gives rise to a morphisms of the pushforwards of those presheaves.
-/
def pushforward_map {C : Type u} [category_theory.category C] {X : Top} {Y : Top} (f : X ⟶ Y)
    {ℱ : presheaf C X} {𝒢 : presheaf C X} (α : ℱ ⟶ 𝒢) : f _* ℱ ⟶ f _* 𝒢 :=
  category_theory.nat_trans.mk
    fun (U : topological_space.opens ↥Yᵒᵖ) =>
      category_theory.nat_trans.app α
        (category_theory.functor.obj (category_theory.functor.op (topological_space.opens.map f)) U)

end Mathlib