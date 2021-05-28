/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.Mon_
import Mathlib.PostPort

universes v₁ u₁ l 

namespace Mathlib

/-!
# The category of module objects over a monoid object.
-/

/-- A module object for a monoid object, all internal to some monoidal category. -/
structure Mod {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] (A : Mon_ C) 
where
  X : C
  act : Mon_.X A ⊗ X ⟶ X
  one_act' : autoParam ((Mon_.one A ⊗ 𝟙) ≫ act = category_theory.iso.hom λ_)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  assoc' : autoParam ((Mon_.mul A ⊗ 𝟙) ≫ act = category_theory.iso.hom α_ ≫ (𝟙 ⊗ act) ≫ act)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem Mod.one_act {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (c : Mod A) : (Mon_.one A ⊗ 𝟙) ≫ Mod.act c = category_theory.iso.hom λ_ := sorry

@[simp] theorem Mod.assoc {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (c : Mod A) : (Mon_.mul A ⊗ 𝟙) ≫ Mod.act c = category_theory.iso.hom α_ ≫ (𝟙 ⊗ Mod.act c) ≫ Mod.act c := sorry

@[simp] theorem Mod.one_act_assoc {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (c : Mod A) {X' : C} (f' : Mod.X c ⟶ X') : (Mon_.one A ⊗ 𝟙) ≫ Mod.act c ≫ f' = category_theory.iso.hom λ_ ≫ f' := sorry

namespace Mod


theorem assoc_flip {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (M : Mod A) : (𝟙 ⊗ act M) ≫ act M = category_theory.iso.inv α_ ≫ (Mon_.mul A ⊗ 𝟙) ≫ act M := sorry

/-- A morphism of module objects. -/
structure hom {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (M : Mod A) (N : Mod A) 
where
  hom : X M ⟶ X N
  act_hom' : autoParam (act M ≫ hom = (𝟙 ⊗ hom) ≫ act N)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem hom.act_hom {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} {M : Mod A} {N : Mod A} (c : hom M N) : act M ≫ hom.hom c = (𝟙 ⊗ hom.hom c) ≫ act N := sorry

@[simp] theorem hom.act_hom_assoc {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} {M : Mod A} {N : Mod A} (c : hom M N) {X' : C} (f' : X N ⟶ X') : act M ≫ hom.hom c ≫ f' = (𝟙 ⊗ hom.hom c) ≫ act N ≫ f' := sorry

/-- The identity morphism on a module object. -/
def id {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (M : Mod A) : hom M M :=
  hom.mk 𝟙

protected instance hom_inhabited {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (M : Mod A) : Inhabited (hom M M) :=
  { default := id M }

/-- Composition of module object morphisms. -/
def comp {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} {M : Mod A} {N : Mod A} {O : Mod A} (f : hom M N) (g : hom N O) : hom M O :=
  hom.mk (hom.hom f ≫ hom.hom g)

protected instance category_theory.category {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} : category_theory.category (Mod A) :=
  category_theory.category.mk

@[simp] theorem id_hom' {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} (M : Mod A) : hom.hom 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_hom' {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} {M : Mod A} {N : Mod A} {K : Mod A} (f : M ⟶ N) (g : N ⟶ K) : hom.hom (f ≫ g) = hom.hom f ≫ hom.hom g :=
  rfl

/-- A monoid object as a module over itself. -/
@[simp] theorem regular_X {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] (A : Mon_ C) : X (regular A) = Mon_.X A :=
  Eq.refl (X (regular A))

protected instance inhabited {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] (A : Mon_ C) : Inhabited (Mod A) :=
  { default := regular A }

/-- The forgetful functor from module objects to the ambient category. -/
def forget {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] (A : Mon_ C) : Mod A ⥤ C :=
  category_theory.functor.mk (fun (A_1 : Mod A) => X A_1) fun (A_1 B : Mod A) (f : A_1 ⟶ B) => hom.hom f

/--
A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simp] theorem comap_obj_act {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} {B : Mon_ C} (f : A ⟶ B) (M : Mod B) : act (category_theory.functor.obj (comap f) M) = (Mon_.hom.hom f ⊗ 𝟙) ≫ act M :=
  Eq.refl (act (category_theory.functor.obj (comap f) M))

