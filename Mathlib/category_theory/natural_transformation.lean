/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn

Defines natural transformations between functors.

Introduces notations
  `τ.app X` for the components of natural transformations,
  `F ⟶ G` for the type of natural transformations between functors `F` and `G`,
  `σ ≫ τ` for vertical compositions, and
  `σ ◫ τ` for horizontal compositions.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.functor
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l 

namespace Mathlib

namespace category_theory


/--
`nat_trans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality_lemma`.
-/
structure nat_trans {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (G : C ⥤ D) 
where
  app : (X : C) → functor.obj F X ⟶ functor.obj G X
  naturality' : autoParam (∀ {X Y : C} (f : X ⟶ Y), functor.map F f ≫ app Y = app X ≫ functor.map G f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- Rather arbitrarily, we say that the 'simpler' form is

@[simp] theorem nat_trans.naturality {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (c : nat_trans F G) {X : C} {Y : C} (f : X ⟶ Y) : functor.map F f ≫ nat_trans.app c Y = nat_trans.app c X ≫ functor.map G f := sorry

-- components of natural transfomations moving earlier.

@[simp] theorem nat_trans.naturality_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (c : nat_trans F G) {X : C} {Y : C} (f : X ⟶ Y) {X' : D} (f' : functor.obj G Y ⟶ X') : functor.map F f ≫ nat_trans.app c Y ≫ f' = nat_trans.app c X ≫ functor.map G f ≫ f' := sorry

theorem congr_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {α : nat_trans F G} {β : nat_trans F G} (h : α = β) (X : C) : nat_trans.app α X = nat_trans.app β X :=
  congr_fun (congr_arg nat_trans.app h) X

namespace nat_trans


/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : nat_trans F F :=
  mk fun (X : C) => 𝟙

@[simp] theorem id_app' {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (X : C) : app (nat_trans.id F) X = 𝟙 :=
  rfl

protected instance inhabited {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : Inhabited (nat_trans F F) :=
  { default := nat_trans.id F }

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
  mk fun (X : C) => app α X ≫ app β X

-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a

-- suitable simp lemma.  We will declare the variant vcomp_app' there.

theorem vcomp_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} (α : nat_trans F G) (β : nat_trans G H) (X : C) : app (vcomp α β) X = app α X ≫ app β X :=
  rfl

