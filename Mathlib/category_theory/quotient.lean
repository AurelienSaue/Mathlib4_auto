/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import Mathlib.PostPort

universes v u l u_1 u_2 

namespace Mathlib

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'.
-/

namespace category_theory


/-- A type synonom for `C`, thought of as the objects of the quotient category. -/
structure quotient {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) 
where
  as : C

protected instance quotient.inhabited {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) [Inhabited C] : Inhabited (quotient r) :=
  { default := quotient.mk Inhabited.default }

namespace quotient


/-- Generates the closure of a family of relations w.r.t. composition from left and right. -/
inductive comp_closure {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {s : C} {t : C} : (s ⟶ t) → (s ⟶ t) → Prop
where
| intro : ∀ {a b : C} (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t), r m₁ m₂ → comp_closure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

theorem comp_left {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {a : C} {b : C} {c : C} (f : a ⟶ b) (g₁ : b ⟶ c) (g₂ : b ⟶ c) (h : comp_closure r g₁ g₂) : comp_closure r (f ≫ g₁) (f ≫ g₂) := sorry

theorem comp_right {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {a : C} {b : C} {c : C} (g : b ⟶ c) (f₁ : a ⟶ b) (f₂ : a ⟶ b) (h : comp_closure r f₁ f₂) : comp_closure r (f₁ ≫ g) (f₂ ≫ g) := sorry

/-- Hom-sets of the quotient category. -/
def hom {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) (s : quotient r) (t : quotient r) :=
  Quot (comp_closure r)

protected instance hom.inhabited {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) (a : quotient r) : Inhabited (hom r a a) :=
  { default := Quot.mk (comp_closure r) 𝟙 }

/-- Composition in the quotient category. -/
def comp {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {a : quotient r} {b : quotient r} {c : quotient r} : hom r a b → hom r b c → hom r a c :=
  fun (hf : hom r a b) (hg : hom r b c) =>
    quot.lift_on hf
      (fun (f : as a ⟶ as b) => quot.lift_on hg (fun (g : as b ⟶ as c) => Quot.mk (comp_closure r) (f ≫ g)) sorry) sorry

@[simp] theorem comp_mk {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {a : quotient r} {b : quotient r} {c : quotient r} (f : as a ⟶ as b) (g : as b ⟶ as c) : comp r (Quot.mk (comp_closure r) f) (Quot.mk (comp_closure r) g) = Quot.mk (comp_closure r) (f ≫ g) :=
  rfl

protected instance category {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) : category (quotient r) :=
  category.mk

/-- The functor from a category to its quotient. -/
@[simp] theorem functor_map {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) (_x : C) : ∀ (_x_1 : C) (f : _x ⟶ _x_1), functor.map (functor r) f = Quot.mk (comp_closure r) f :=
  fun (_x_1 : C) (f : _x ⟶ _x_1) => Eq.refl (functor.map (functor r) f)

protected theorem induction {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {P : {a b : quotient r} → (a ⟶ b) → Prop} (h : ∀ {x y : C} (f : x ⟶ y), P (functor.map (functor r) f)) {a : quotient r} {b : quotient r} (f : a ⟶ b) : P f := sorry

protected theorem sound {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {a : C} {b : C} {f₁ : a ⟶ b} {f₂ : a ⟶ b} (h : r f₁ f₂) : functor.map (functor r) f₁ = functor.map (functor r) f₂ := sorry

/-- The induced functor on the quotient category. -/
def lift {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {D : Type u_1} [category D] (F : C ⥤ D) (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → functor.map F f₁ = functor.map F f₂) : quotient r ⥤ D :=
  functor.mk (fun (a : quotient r) => functor.obj F (as a))
    fun (a b : quotient r) (hf : a ⟶ b) => quot.lift_on hf (fun (f : as a ⟶ as b) => functor.map F f) sorry

/-- The original functor factors through the induced functor. -/
def lift.is_lift {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {D : Type u_1} [category D] (F : C ⥤ D) (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → functor.map F f₁ = functor.map F f₂) : functor r ⋙ lift r F H ≅ F :=
  nat_iso.of_components (fun (X : C) => iso.refl (functor.obj (functor r ⋙ lift r F H) X)) sorry

@[simp] theorem lift.is_lift_hom {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {D : Type u_1} [category D] (F : C ⥤ D) (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → functor.map F f₁ = functor.map F f₂) (X : C) : nat_trans.app (iso.hom (lift.is_lift r F H)) X = 𝟙 :=
  rfl

@[simp] theorem lift.is_lift_inv {C : Type u} [category C] (r : {a b : C} → (a ⟶ b) → (a ⟶ b) → Prop) {D : Type u_1} [category D] (F : C ⥤ D) (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → functor.map F f₁ = functor.map F f₂) (X : C) : nat_trans.app (iso.inv (lift.is_lift r F H)) X = 𝟙 :=
  rfl

