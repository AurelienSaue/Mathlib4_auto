/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.products.bifunctor
import Mathlib.PostPort

universes u₁ u₂ u₃ v₁ v₂ v₃ 

namespace Mathlib

namespace category_theory


/--
The uncurrying functor, taking a functor `C ⥤ (D ⥤ E)` and producing a functor `(C × D) ⥤ E`.
-/
def uncurry {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] :
    (C ⥤ D ⥤ E) ⥤ C × D ⥤ E :=
  functor.mk
    (fun (F : C ⥤ D ⥤ E) =>
      functor.mk (fun (X : C × D) => functor.obj (functor.obj F (prod.fst X)) (prod.snd X))
        fun (X Y : C × D) (f : X ⟶ Y) =>
          nat_trans.app (functor.map F (prod.fst f)) (prod.snd X) ≫
            functor.map (functor.obj F (prod.fst Y)) (prod.snd f))
    fun (F G : C ⥤ D ⥤ E) (T : F ⟶ G) =>
      nat_trans.mk fun (X : C × D) => nat_trans.app (nat_trans.app T (prod.fst X)) (prod.snd X)

/--
The object level part of the currying functor. (See `curry` for the functorial version.)
-/
def curry_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E]
    (F : C × D ⥤ E) : C ⥤ D ⥤ E :=
  functor.mk
    (fun (X : C) =>
      functor.mk (fun (Y : D) => functor.obj F (X, Y))
        fun (Y Y' : D) (g : Y ⟶ Y') => functor.map F (𝟙, g))
    fun (X X' : C) (f : X ⟶ X') => nat_trans.mk fun (Y : D) => functor.map F (f, 𝟙)

/--
The currying functor, taking a functor `(C × D) ⥤ E` and producing a functor `C ⥤ (D ⥤ E)`.
-/
def curry {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] :
    (C × D ⥤ E) ⥤ C ⥤ D ⥤ E :=
  functor.mk (fun (F : C × D ⥤ E) => curry_obj F)
    fun (F G : C × D ⥤ E) (T : F ⟶ G) =>
      nat_trans.mk fun (X : C) => nat_trans.mk fun (Y : D) => nat_trans.app T (X, Y)

@[simp] theorem uncurry.obj_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D ⥤ E} {X : C × D} :
    functor.obj (functor.obj uncurry F) X = functor.obj (functor.obj F (prod.fst X)) (prod.snd X) :=
  rfl

@[simp] theorem uncurry.obj_map {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D ⥤ E} {X : C × D} {Y : C × D} {f : X ⟶ Y} :
    functor.map (functor.obj uncurry F) f =
        nat_trans.app (functor.map F (prod.fst f)) (prod.snd X) ≫
          functor.map (functor.obj F (prod.fst Y)) (prod.snd f) :=
  rfl

@[simp] theorem uncurry.map_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D ⥤ E} {G : C ⥤ D ⥤ E} {α : F ⟶ G} {X : C × D} :
    nat_trans.app (functor.map uncurry α) X =
        nat_trans.app (nat_trans.app α (prod.fst X)) (prod.snd X) :=
  rfl

@[simp] theorem curry.obj_obj_obj {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {F : C × D ⥤ E} {X : C} {Y : D} :
    functor.obj (functor.obj (functor.obj curry F) X) Y = functor.obj F (X, Y) :=
  rfl

@[simp] theorem curry.obj_obj_map {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {F : C × D ⥤ E} {X : C} {Y : D} {Y' : D} {g : Y ⟶ Y'} :
    functor.map (functor.obj (functor.obj curry F) X) g = functor.map F (𝟙, g) :=
  rfl

@[simp] theorem curry.obj_map_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {F : C × D ⥤ E} {X : C} {X' : C} {f : X ⟶ X'} {Y : D} :
    nat_trans.app (functor.map (functor.obj curry F) f) Y = functor.map F (f, 𝟙) :=
  rfl

@[simp] theorem curry.map_app_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {F : C × D ⥤ E} {G : C × D ⥤ E} {α : F ⟶ G} {X : C} {Y : D} :
    nat_trans.app (nat_trans.app (functor.map curry α) X) Y = nat_trans.app α (X, Y) :=
  rfl

/--
The equivalence of functor categories given by currying/uncurrying.
-/
@[simp] theorem currying_unit_iso_inv_app_app_app {C : Type u₁} [category C] {D : Type u₂}
    [category D] {E : Type u₃} [category E] (X : C ⥤ D ⥤ E) :
    ∀ (X_1 : C) (X_2 : D),
        nat_trans.app
            (nat_trans.app (nat_trans.app (iso.inv (equivalence.unit_iso currying)) X) X_1) X_2 =
          𝟙 :=
  sorry

end Mathlib