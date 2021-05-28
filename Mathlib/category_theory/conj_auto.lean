/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.endomorphism
import Mathlib.algebra.group_power.default
import PostPort

universes u v v₁ u₁ 

namespace Mathlib

/-!
# Conjugate morphisms by isomorphisms

An isomorphism `α : X ≅ Y` defines
- a monoid isomorphism `conj : End X ≃* End Y` by `α.conj f = α.inv ≫ f ≫ α.hom`;
- a group isomorphism `conj_Aut : Aut X ≃* Aut Y` by `α.conj_Aut f = α.symm ≪≫ f ≪≫ α`.

For completeness, we also define `hom_congr : (X ≅ X₁) → (Y ≅ Y₁) → (X ⟶ Y) ≃ (X₁ ⟶ Y₁)`, cf. `equiv.arrow_congr`.
-/

namespace category_theory


namespace iso


/-- If `X` is isomorphic to `X₁` and `Y` is isomorphic to `Y₁`, then
there is a natural bijection between `X ⟶ Y` and `X₁ ⟶ Y₁`. See also `equiv.arrow_congr`. -/
def hom_congr {C : Type u} [category C] {X : C} {Y : C} {X₁ : C} {Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) : (X ⟶ Y) ≃ (X₁ ⟶ Y₁) :=
  equiv.mk (fun (f : X ⟶ Y) => inv α ≫ f ≫ hom β) (fun (f : X₁ ⟶ Y₁) => hom α ≫ f ≫ inv β) sorry sorry

@[simp] theorem hom_congr_apply {C : Type u} [category C] {X : C} {Y : C} {X₁ : C} {Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) : coe_fn (hom_congr α β) f = inv α ≫ f ≫ hom β :=
  rfl

theorem hom_congr_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {X₁ : C} {Y₁ : C} {Z₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (γ : Z ≅ Z₁) (f : X ⟶ Y) (g : Y ⟶ Z) : coe_fn (hom_congr α γ) (f ≫ g) = coe_fn (hom_congr α β) f ≫ coe_fn (hom_congr β γ) g := sorry

@[simp] theorem hom_congr_refl {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : coe_fn (hom_congr (refl X) (refl Y)) f = f := sorry

@[simp] theorem hom_congr_trans {C : Type u} [category C] {X₁ : C} {Y₁ : C} {X₂ : C} {Y₂ : C} {X₃ : C} {Y₃ : C} (α₁ : X₁ ≅ X₂) (β₁ : Y₁ ≅ Y₂) (α₂ : X₂ ≅ X₃) (β₂ : Y₂ ≅ Y₃) (f : X₁ ⟶ Y₁) : coe_fn (hom_congr (α₁ ≪≫ α₂) (β₁ ≪≫ β₂)) f = coe_fn (equiv.trans (hom_congr α₁ β₁) (hom_congr α₂ β₂)) f := sorry

@[simp] theorem hom_congr_symm {C : Type u} [category C] {X₁ : C} {Y₁ : C} {X₂ : C} {Y₂ : C} (α : X₁ ≅ X₂) (β : Y₁ ≅ Y₂) : equiv.symm (hom_congr α β) = hom_congr (symm α) (symm β) :=
  rfl

/-- An isomorphism between two objects defines a monoid isomorphism between their
monoid of endomorphisms. -/
def conj {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) : End X ≃* End Y :=
  mul_equiv.mk (equiv.to_fun (hom_congr α α)) (equiv.inv_fun (hom_congr α α)) sorry sorry sorry

theorem conj_apply {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : End X) : coe_fn (conj α) f = inv α ≫ f ≫ hom α :=
  rfl

@[simp] theorem conj_comp {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : End X) (g : End X) : coe_fn (conj α) (f ≫ g) = coe_fn (conj α) f ≫ coe_fn (conj α) g :=
  mul_equiv.map_mul (conj α) g f

@[simp] theorem conj_id {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) : coe_fn (conj α) 𝟙 = 𝟙 :=
  mul_equiv.map_one (conj α)

@[simp] theorem refl_conj {C : Type u} [category C] {X : C} (f : End X) : coe_fn (conj (refl X)) f = f := sorry

@[simp] theorem trans_conj {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) {Z : C} (β : Y ≅ Z) (f : End X) : coe_fn (conj (α ≪≫ β)) f = coe_fn (conj β) (coe_fn (conj α) f) :=
  hom_congr_trans α α β β f

@[simp] theorem symm_self_conj {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : End X) : coe_fn (conj (symm α)) (coe_fn (conj α) f) = f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (conj (symm α)) (coe_fn (conj α) f) = f)) (Eq.symm (trans_conj α (symm α) f))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (conj (α ≪≫ symm α)) f = f)) (self_symm_id α)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (conj (refl X)) f = f)) (refl_conj f))) (Eq.refl f)))

@[simp] theorem self_symm_conj {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : End Y) : coe_fn (conj α) (coe_fn (conj (symm α)) f) = f :=
  symm_self_conj (symm α) f

@[simp] theorem conj_pow {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : End X) (n : ℕ) : coe_fn (conj α) (f ^ n) = coe_fn (conj α) f ^ n :=
  monoid_hom.map_pow (mul_equiv.to_monoid_hom (conj α)) f n

/-- `conj` defines a group isomorphisms between groups of automorphisms -/
def conj_Aut {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) : Aut X ≃* Aut Y :=
  mul_equiv.trans (mul_equiv.symm (Aut.units_End_equiv_Aut X))
    (mul_equiv.trans (units.map_equiv (conj α)) (Aut.units_End_equiv_Aut Y))

theorem conj_Aut_apply {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) : coe_fn (conj_Aut α) f = symm α ≪≫ f ≪≫ α := sorry

@[simp] theorem conj_Aut_hom {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) : hom (coe_fn (conj_Aut α) f) = coe_fn (conj α) (hom f) :=
  rfl

@[simp] theorem trans_conj_Aut {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) {Z : C} (β : Y ≅ Z) (f : Aut X) : coe_fn (conj_Aut (α ≪≫ β)) f = coe_fn (conj_Aut β) (coe_fn (conj_Aut α) f) := sorry

@[simp] theorem conj_Aut_mul {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) (g : Aut X) : coe_fn (conj_Aut α) (f * g) = coe_fn (conj_Aut α) f * coe_fn (conj_Aut α) g :=
  mul_equiv.map_mul (conj_Aut α) f g

@[simp] theorem conj_Aut_trans {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) (g : Aut X) : coe_fn (conj_Aut α) (f ≪≫ g) = coe_fn (conj_Aut α) f ≪≫ coe_fn (conj_Aut α) g :=
  conj_Aut_mul α g f

@[simp] theorem conj_Aut_pow {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) (n : ℕ) : coe_fn (conj_Aut α) (f ^ n) = coe_fn (conj_Aut α) f ^ n :=
  monoid_hom.map_pow (mul_equiv.to_monoid_hom (conj_Aut α)) f n

@[simp] theorem conj_Aut_gpow {C : Type u} [category C] {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) (n : ℤ) : coe_fn (conj_Aut α) (f ^ n) = coe_fn (conj_Aut α) f ^ n :=
  monoid_hom.map_gpow (mul_equiv.to_monoid_hom (conj_Aut α)) f n

end iso


namespace functor


theorem map_hom_congr {C : Type u} [category C] {D : Type u₁} [category D] (F : C ⥤ D) {X : C} {Y : C} {X₁ : C} {Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) (f : X ⟶ Y) : map F (coe_fn (iso.hom_congr α β) f) = coe_fn (iso.hom_congr (map_iso F α) (map_iso F β)) (map F f) := sorry

theorem map_conj {C : Type u} [category C] {D : Type u₁} [category D] (F : C ⥤ D) {X : C} {Y : C} (α : X ≅ Y) (f : End X) : map F (coe_fn (iso.conj α) f) = coe_fn (iso.conj (map_iso F α)) (map F f) :=
  map_hom_congr F α α f

theorem map_conj_Aut {C : Type u} [category C] {D : Type u₁} [category D] (F : C ⥤ D) {X : C} {Y : C} (α : X ≅ Y) (f : Aut X) : map_iso F (coe_fn (iso.conj_Aut α) f) = coe_fn (iso.conj_Aut (map_iso F α)) (map_iso F f) := sorry

