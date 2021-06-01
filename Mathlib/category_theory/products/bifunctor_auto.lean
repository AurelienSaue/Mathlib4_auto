/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.products.basic
import Mathlib.PostPort

universes v₁ v₂ v₃ u₁ u₂ u₃ 

namespace Mathlib

namespace category_theory.bifunctor


@[simp] theorem map_id {C : Type u₁} {D : Type u₂} {E : Type u₃} [category C] [category D]
    [category E] (F : C × D ⥤ E) (X : C) (Y : D) : functor.map F (𝟙, 𝟙) = 𝟙 :=
  functor.map_id F (X, Y)

@[simp] theorem map_id_comp {C : Type u₁} {D : Type u₂} {E : Type u₃} [category C] [category D]
    [category E] (F : C × D ⥤ E) (W : C) {X : D} {Y : D} {Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    functor.map F (𝟙, f ≫ g) = functor.map F (𝟙, f) ≫ functor.map F (𝟙, g) :=
  sorry

@[simp] theorem map_comp_id {C : Type u₁} {D : Type u₂} {E : Type u₃} [category C] [category D]
    [category E] (F : C × D ⥤ E) (X : C) (Y : C) (Z : C) (W : D) (f : X ⟶ Y) (g : Y ⟶ Z) :
    functor.map F (f ≫ g, 𝟙) = functor.map F (f, 𝟙) ≫ functor.map F (g, 𝟙) :=
  sorry

@[simp] theorem diagonal {C : Type u₁} {D : Type u₂} {E : Type u₃} [category C] [category D]
    [category E] (F : C × D ⥤ E) (X : C) (X' : C) (f : X ⟶ X') (Y : D) (Y' : D) (g : Y ⟶ Y') :
    functor.map F (𝟙, g) ≫ functor.map F (f, 𝟙) = functor.map F (f, g) :=
  sorry

@[simp] theorem diagonal' {C : Type u₁} {D : Type u₂} {E : Type u₃} [category C] [category D]
    [category E] (F : C × D ⥤ E) (X : C) (X' : C) (f : X ⟶ X') (Y : D) (Y' : D) (g : Y ⟶ Y') :
    functor.map F (f, 𝟙) ≫ functor.map F (𝟙, g) = functor.map F (f, g) :=
  sorry

end Mathlib