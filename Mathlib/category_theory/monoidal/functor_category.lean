/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.braided
import Mathlib.category_theory.functor_category
import Mathlib.category_theory.const
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ 

namespace Mathlib

/-!
# Monoidal structure on `C ⥤ D` when `D` is monoidal.

When `C` is any category, and `D` is a monoidal category,
there is a natural "pointwise" monoidal structure on `C ⥤ D`.

The initial intended application is tensor product of presheaves.
-/

namespace category_theory.monoidal


namespace functor_category


/--
(An auxiliary definition for `functor_category_monoidal`.)
Tensor product of functors `C ⥤ D`, when `D` is monoidal.
 -/
def tensor_obj {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] (F : C ⥤ D) (G : C ⥤ D) : C ⥤ D :=
  functor.mk (fun (X : C) => functor.obj F X ⊗ functor.obj G X)
    fun (X Y : C) (f : X ⟶ Y) => functor.map F f ⊗ functor.map G f

/--
(An auxiliary definition for `functor_category_monoidal`.)
Tensor product of natural transformations into `D`, when `D` is monoidal.
-/
def tensor_hom {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {G : C ⥤ D} {F' : C ⥤ D} {G' : C ⥤ D} (α : F ⟶ G) (β : F' ⟶ G') : tensor_obj F F' ⟶ tensor_obj G G' :=
  nat_trans.mk fun (X : C) => nat_trans.app α X ⊗ nat_trans.app β X

end functor_category


/--
When `C` is any category, and `D` is a monoidal category,
the functor category `C ⥤ D` has a natural pointwise monoidal structure,
where `(F ⊗ G).obj X = F.obj X ⊗ G.obj X`.
-/
protected instance functor_category_monoidal {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] : monoidal_category (C ⥤ D) :=
  monoidal_category.mk (fun (F G : C ⥤ D) => functor_category.tensor_obj F G)
    (fun (F G F' G' : C ⥤ D) (α : F ⟶ G) (β : F' ⟶ G') => functor_category.tensor_hom α β)
    (functor.obj (functor.const C) 𝟙_) (fun (F G H : C ⥤ D) => nat_iso.of_components (fun (X : C) => α_) sorry)
    (fun (F : C ⥤ D) => nat_iso.of_components (fun (X : C) => λ_) sorry)
    fun (F : C ⥤ D) => nat_iso.of_components (fun (X : C) => ρ_) sorry

@[simp] theorem tensor_unit_obj {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {X : C} : functor.obj 𝟙_ X = 𝟙_ :=
  rfl

@[simp] theorem tensor_unit_map {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {X : C} {Y : C} {f : X ⟶ Y} : functor.map 𝟙_ f = 𝟙 :=
  rfl

@[simp] theorem tensor_obj_obj {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {G : C ⥤ D} {X : C} : functor.obj (F ⊗ G) X = functor.obj F X ⊗ functor.obj G X :=
  rfl

@[simp] theorem tensor_obj_map {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {G : C ⥤ D} {X : C} {Y : C} {f : X ⟶ Y} : functor.map (F ⊗ G) f = functor.map F f ⊗ functor.map G f :=
  rfl

@[simp] theorem tensor_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {G : C ⥤ D} {F' : C ⥤ D} {G' : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G'} {X : C} : nat_trans.app (α ⊗ β) X = nat_trans.app α X ⊗ nat_trans.app β X :=
  rfl

@[simp] theorem left_unitor_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {X : C} : nat_trans.app (iso.hom λ_) X = iso.hom λ_ :=
  rfl

@[simp] theorem left_unitor_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {X : C} : nat_trans.app (iso.inv λ_) X = iso.inv λ_ :=
  rfl

@[simp] theorem right_unitor_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {X : C} : nat_trans.app (iso.hom ρ_) X = iso.hom ρ_ :=
  rfl

@[simp] theorem right_unitor_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {X : C} : nat_trans.app (iso.inv ρ_) X = iso.inv ρ_ :=
  rfl

@[simp] theorem associator_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} {X : C} : nat_trans.app (iso.hom α_) X = iso.hom α_ :=
  rfl

@[simp] theorem associator_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} {X : C} : nat_trans.app (iso.inv α_) X = iso.inv α_ :=
  rfl

/--
When `C` is any category, and `D` is a braided monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also braided.
-/
protected instance functor_category_braided {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] : braided_category (C ⥤ D) :=
  braided_category.mk fun (F G : C ⥤ D) => nat_iso.of_components (fun (X : C) => β_) sorry

/--
When `C` is any category, and `D` is a symmetric monoidal category,
the natural pointwise monoidal structure on the functor category `C ⥤ D`
is also symmetric.
-/
protected instance functor_category_symmetric {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] [symmetric_category D] : symmetric_category (C ⥤ D) :=
  symmetric_category.mk

