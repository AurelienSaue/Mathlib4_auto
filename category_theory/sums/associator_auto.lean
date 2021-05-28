/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.sums.basic
import PostPort

universes u v 

namespace Mathlib

/-#
The associator functor `((C ⊕ D) ⊕ E) ⥤ (C ⊕ (D ⊕ E))` and its inverse form an equivalence.
-/

namespace category_theory.sum


/--
The associator functor `(C ⊕ D) ⊕ E ⥤ C ⊕ (D ⊕ E)` for sums of categories.
-/
def associator (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] : (C ⊕ D) ⊕ E ⥤ C ⊕ D ⊕ E :=
  functor.mk (fun (X : (C ⊕ D) ⊕ E) => sorry) fun (X Y : (C ⊕ D) ⊕ E) (f : X ⟶ Y) => sorry

@[simp] theorem associator_obj_inl_inl (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] (X : C) : functor.obj (associator C D E) (sum.inl (sum.inl X)) = sum.inl X :=
  rfl

@[simp] theorem associator_obj_inl_inr (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] (X : D) : functor.obj (associator C D E) (sum.inl (sum.inr X)) = sum.inr (sum.inl X) :=
  rfl

@[simp] theorem associator_obj_inr (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] (X : E) : functor.obj (associator C D E) (sum.inr X) = sum.inr (sum.inr X) :=
  rfl

@[simp] theorem associator_map_inl_inl (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] {X : C} {Y : C} (f : sum.inl (sum.inl X) ⟶ sum.inl (sum.inl Y)) : functor.map (associator C D E) f = f :=
  rfl

@[simp] theorem associator_map_inl_inr (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] {X : D} {Y : D} (f : sum.inl (sum.inr X) ⟶ sum.inl (sum.inr Y)) : functor.map (associator C D E) f = f :=
  rfl

@[simp] theorem associator_map_inr (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] {X : E} {Y : E} (f : sum.inr X ⟶ sum.inr Y) : functor.map (associator C D E) f = f :=
  rfl

/--
The inverse associator functor `C ⊕ (D ⊕ E) ⥤ (C ⊕ D) ⊕ E` for sums of categories.
-/
def inverse_associator (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] : C ⊕ D ⊕ E ⥤ (C ⊕ D) ⊕ E :=
  functor.mk (fun (X : C ⊕ D ⊕ E) => sorry) fun (X Y : C ⊕ D ⊕ E) (f : X ⟶ Y) => sorry

@[simp] theorem inverse_associator_obj_inl (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] (X : C) : functor.obj (inverse_associator C D E) (sum.inl X) = sum.inl (sum.inl X) :=
  rfl

@[simp] theorem inverse_associator_obj_inr_inl (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] (X : D) : functor.obj (inverse_associator C D E) (sum.inr (sum.inl X)) = sum.inl (sum.inr X) :=
  rfl

@[simp] theorem inverse_associator_obj_inr_inr (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] (X : E) : functor.obj (inverse_associator C D E) (sum.inr (sum.inr X)) = sum.inr X :=
  rfl

@[simp] theorem inverse_associator_map_inl (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] {X : C} {Y : C} (f : sum.inl X ⟶ sum.inl Y) : functor.map (inverse_associator C D E) f = f :=
  rfl

@[simp] theorem inverse_associator_map_inr_inl (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] {X : D} {Y : D} (f : sum.inr (sum.inl X) ⟶ sum.inr (sum.inl Y)) : functor.map (inverse_associator C D E) f = f :=
  rfl

@[simp] theorem inverse_associator_map_inr_inr (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] {X : E} {Y : E} (f : sum.inr (sum.inr X) ⟶ sum.inr (sum.inr Y)) : functor.map (inverse_associator C D E) f = f :=
  rfl

/--
The equivalence of categories expressing associativity of sums of categories.
-/
def associativity (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] : (C ⊕ D) ⊕ E ≌ C ⊕ D ⊕ E :=
  equivalence.mk (associator C D E) (inverse_associator C D E)
    (nat_iso.of_components (fun (X : (C ⊕ D) ⊕ E) => eq_to_iso sorry) sorry)
    (nat_iso.of_components (fun (X : C ⊕ D ⊕ E) => eq_to_iso sorry) sorry)

protected instance associator_is_equivalence (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] : is_equivalence (associator C D E) :=
  is_equivalence.of_equivalence (associativity C D E)

protected instance inverse_associator_is_equivalence (C : Type u) [category C] (D : Type u) [category D] (E : Type u) [category E] : is_equivalence (inverse_associator C D E) :=
  is_equivalence.of_equivalence_inverse (associativity C D E)

