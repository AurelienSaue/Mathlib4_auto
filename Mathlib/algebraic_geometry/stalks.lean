/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.presheafed_space
import Mathlib.topology.sheaves.stalks
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Stalks for presheaved spaces

This file lifts constructions of stalks and pushforwards of stalks to work with
the category of presheafed spaces.
-/

namespace algebraic_geometry.PresheafedSpace


/--
The stalk at `x` of a `PresheafedSpace`.
-/
def stalk {C : Type u} [category_theory.category C] [category_theory.limits.has_colimits C] (X : PresheafedSpace C) (x : ↥X) : C :=
  Top.presheaf.stalk (PresheafedSpace.presheaf X) x

/--
A morphism of presheafed spaces induces a morphism of stalks.
-/
def stalk_map {C : Type u} [category_theory.category C] [category_theory.limits.has_colimits C] {X : PresheafedSpace C} {Y : PresheafedSpace C} (α : X ⟶ Y) (x : ↥X) : stalk Y (coe_fn (hom.base α) x) ⟶ stalk X x :=
  category_theory.functor.map (Top.presheaf.stalk_functor C (coe_fn (hom.base α) x)) (hom.c α) ≫
    Top.presheaf.stalk_pushforward C (hom.base α) (PresheafedSpace.presheaf X) x

-- PROJECT: restriction preserves stalks.

-- We'll want to define cofinal functors, show precomposing with a cofinal functor preserves colimits,

-- and (easily) verify that "open neighbourhoods of x within U" is cofinal in "open neighbourhoods of x".

/-
def restrict_stalk_iso {U : Top} (X : PresheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) (x : U) :
  (X.restrict f h).stalk x ≅ X.stalk (f x) :=
begin
  dsimp only [stalk, Top.presheaf.stalk, stalk_functor],
  dsimp [colim],
  sorry
end

-- TODO `restrict_stalk_iso` is compatible with `germ`.

-- TODO `restrict_stalk_iso` is compatible with `germ`.
-/

namespace stalk_map


@[simp] theorem id {C : Type u} [category_theory.category C] [category_theory.limits.has_colimits C] (X : PresheafedSpace C) (x : ↥X) : stalk_map 𝟙 x = 𝟙 := sorry

-- TODO understand why this proof is still gross (i.e. requires using `erw`)

@[simp] theorem comp {C : Type u} [category_theory.category C] [category_theory.limits.has_colimits C] {X : PresheafedSpace C} {Y : PresheafedSpace C} {Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : ↥X) : stalk_map (α ≫ β) x = stalk_map β (coe_fn (hom.base α) x) ≫ stalk_map α x := sorry

