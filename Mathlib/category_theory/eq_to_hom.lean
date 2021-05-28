/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.opposites
import Mathlib.PostPort

universes u₁ v₁ v₂ u₂ 

namespace Mathlib

namespace category_theory


/--
An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eq_to_hom {C : Type u₁} [category C] {X : C} {Y : C} (p : X = Y) : X ⟶ Y :=
  eq.mpr sorry 𝟙

@[simp] theorem eq_to_hom_refl {C : Type u₁} [category C] (X : C) (p : X = X) : eq_to_hom p = 𝟙 :=
  rfl

@[simp] theorem eq_to_hom_trans {C : Type u₁} [category C] {X : C} {Y : C} {Z : C} (p : X = Y) (q : Y = Z) : eq_to_hom p ≫ eq_to_hom q = eq_to_hom (Eq.trans p q) := sorry

/--
An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `iso.refl _`
which usually leads to dependent type theory hell.
-/
def eq_to_iso {C : Type u₁} [category C] {X : C} {Y : C} (p : X = Y) : X ≅ Y :=
  iso.mk (eq_to_hom p) (eq_to_hom (Eq.symm p))

@[simp] theorem eq_to_iso.hom {C : Type u₁} [category C] {X : C} {Y : C} (p : X = Y) : iso.hom (eq_to_iso p) = eq_to_hom p :=
  rfl

@[simp] theorem eq_to_iso.inv {C : Type u₁} [category C] {X : C} {Y : C} (p : X = Y) : iso.inv (eq_to_iso p) = eq_to_hom (Eq.symm p) :=
  rfl

@[simp] theorem eq_to_iso_refl {C : Type u₁} [category C] {X : C} (p : X = X) : eq_to_iso p = iso.refl X :=
  rfl

@[simp] theorem eq_to_iso_trans {C : Type u₁} [category C] {X : C} {Y : C} {Z : C} (p : X = Y) (q : Y = Z) : eq_to_iso p ≪≫ eq_to_iso q = eq_to_iso (Eq.trans p q) := sorry

@[simp] theorem eq_to_hom_op {C : Type u₁} [category C] {X : C} {Y : C} (h : X = Y) : has_hom.hom.op (eq_to_hom h) = eq_to_hom (congr_arg opposite.op (Eq.symm h)) := sorry

@[simp] theorem eq_to_hom_unop {C : Type u₁} [category C] {X : Cᵒᵖ} {Y : Cᵒᵖ} (h : X = Y) : has_hom.hom.unop (eq_to_hom h) = eq_to_hom (congr_arg opposite.unop (Eq.symm h)) := sorry

protected instance eq_to_hom.is_iso {C : Type u₁} [category C] {X : C} {Y : C} (h : X = Y) : is_iso (eq_to_hom h) :=
  is_iso.mk (iso.inv (eq_to_iso h))

@[simp] theorem inv_eq_to_hom {C : Type u₁} [category C] {X : C} {Y : C} (h : X = Y) : inv (eq_to_hom h) = eq_to_hom (Eq.symm h) :=
  rfl

namespace functor


/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
theorem ext {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h_obj : ∀ (X : C), obj F X = obj G X) (h_map : ∀ (X Y : C) (f : X ⟶ Y), map F f = eq_to_hom (h_obj X) ≫ map G f ≫ eq_to_hom (Eq.symm (h_obj Y))) : F = G := sorry

/-- Proving equality between functors using heterogeneous equality. -/
theorem hext {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h_obj : ∀ (X : C), obj F X = obj G X) (h_map : ∀ (X Y : C) (f : X ⟶ Y), map F f == map G f) : F = G := sorry

-- Using equalities between functors.

theorem congr_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F = G) (X : C) : obj F X = obj G X :=
  Eq._oldrec (Eq.refl (obj F X)) h

theorem congr_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F = G) {X : C} {Y : C} (f : X ⟶ Y) : map F f = eq_to_hom (congr_obj h X) ≫ map G f ≫ eq_to_hom (Eq.symm (congr_obj h Y)) := sorry

end functor


@[simp] theorem eq_to_hom_map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C} {Y : C} (p : X = Y) : functor.map F (eq_to_hom p) = eq_to_hom (congr_arg (functor.obj F) p) := sorry

@[simp] theorem eq_to_iso_map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) {X : C} {Y : C} (p : X = Y) : functor.map_iso F (eq_to_iso p) = eq_to_iso (congr_arg (functor.obj F) p) := sorry

@[simp] theorem eq_to_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F = G) (X : C) : nat_trans.app (eq_to_hom h) X = eq_to_hom (functor.congr_obj h X) :=
  eq.drec (Eq.refl (nat_trans.app (eq_to_hom (Eq.refl F)) X)) h

theorem nat_trans.congr {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ⟶ G) {X : C} {Y : C} (h : X = Y) : nat_trans.app α X = functor.map F (eq_to_hom h) ≫ nat_trans.app α Y ≫ functor.map G (eq_to_hom (Eq.symm h)) := sorry

