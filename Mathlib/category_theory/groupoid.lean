/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.epi_mono
import Mathlib.PostPort

universes v u l u₂ 

namespace Mathlib

namespace category_theory


/-- A `groupoid` is a category such that all morphisms are isomorphisms. -/
class groupoid (obj : Type u) 
extends category obj
where
  inv : {X Y : obj} → (X ⟶ Y) → (Y ⟶ X)
  inv_comp' : autoParam (∀ {X Y : obj} (f : X ⟶ Y), inv f ≫ f = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  comp_inv' : autoParam (∀ {X Y : obj} (f : X ⟶ Y), f ≫ inv f = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem groupoid.inv_comp {obj : Type u} [c : groupoid obj] {X : obj} {Y : obj} (f : X ⟶ Y) : groupoid.inv f ≫ f = 𝟙 := sorry

@[simp] theorem groupoid.comp_inv {obj : Type u} [c : groupoid obj] {X : obj} {Y : obj} (f : X ⟶ Y) : f ≫ groupoid.inv f = 𝟙 := sorry

/--
A `large_groupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
/--
def large_groupoid (C : Type (u + 1))  :=
  groupoid C

A `small_groupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
def small_groupoid (C : Type u)  :=
  groupoid C

protected instance is_iso.of_groupoid {C : Type u} [groupoid C] {X : C} {Y : C} (f : X ⟶ Y) : is_iso f :=
  is_iso.mk (groupoid.inv f)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def groupoid.iso_equiv_hom {C : Type u} [groupoid C] (X : C) (Y : C) : (X ≅ Y) ≃ (X ⟶ Y) :=
  equiv.mk iso.hom (fun (f : X ⟶ Y) => as_iso f) sorry sorry

/-- A category where every morphism `is_iso` is a groupoid. -/
def groupoid.of_is_iso {C : Type u} [category C] (all_is_iso : {X Y : C} → (f : X ⟶ Y) → is_iso f) : groupoid C :=
  groupoid.mk fun (X Y : C) (f : X ⟶ Y) => inv f

/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
def groupoid.of_trunc_split_mono {C : Type u} [category C] (all_split_mono : {X Y : C} → (f : X ⟶ Y) → trunc (split_mono f)) : groupoid C :=
  groupoid.of_is_iso
    fun (X Y : C) (f : X ⟶ Y) =>
      trunc.rec_on_subsingleton (all_split_mono f)
        fun (a : split_mono f) =>
          trunc.rec_on_subsingleton (all_split_mono (retraction f))
            fun (a_1 : split_mono (retraction f)) => is_iso.of_mono_retraction

protected instance induced_category.groupoid {C : Type u} (D : Type u₂) [groupoid D] (F : C → D) : groupoid (induced_category D F) :=
  groupoid.mk fun (X Y : induced_category D F) (f : X ⟶ Y) => groupoid.inv f

