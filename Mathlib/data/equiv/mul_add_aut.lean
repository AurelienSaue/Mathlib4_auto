/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.mul_add
import Mathlib.group_theory.perm.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Multiplicative and additive group automorphisms

This file defines the automorphism group structure on `add_aut R := add_equiv R R` and
`mul_aut R := mul_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism groups agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/mul_add` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

mul_aut, add_aut
-/

/-- The group of multiplicative automorphisms. -/
def mul_aut (M : Type u_1) [Mul M] :=
  M ≃* M

namespace mul_aut


/--
The group operation on multiplicative automorphisms is defined by
`λ g h, mul_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
protected instance group (M : Type u_2) [Mul M] : group (mul_aut M) :=
  group.mk (fun (g h : M ≃* M) => mul_equiv.trans h g) sorry (mul_equiv.refl M) sorry sorry mul_equiv.symm
    (fun (a b : M ≃* M) => a * mul_equiv.symm b) sorry

protected instance inhabited (M : Type u_2) [Mul M] : Inhabited (mul_aut M) :=
  { default := 1 }

@[simp] theorem coe_mul (M : Type u_2) [Mul M] (e₁ : mul_aut M) (e₂ : mul_aut M) : ⇑(e₁ * e₂) = ⇑e₁ ∘ ⇑e₂ :=
  rfl

@[simp] theorem coe_one (M : Type u_2) [Mul M] : ⇑1 = id :=
  rfl

theorem mul_def (M : Type u_2) [Mul M] (e₁ : mul_aut M) (e₂ : mul_aut M) : e₁ * e₂ = mul_equiv.trans e₂ e₁ :=
  rfl

theorem one_def (M : Type u_2) [Mul M] : 1 = mul_equiv.refl M :=
  rfl

theorem inv_def (M : Type u_2) [Mul M] (e₁ : mul_aut M) : e₁⁻¹ = mul_equiv.symm e₁ :=
  rfl

@[simp] theorem mul_apply (M : Type u_2) [Mul M] (e₁ : mul_aut M) (e₂ : mul_aut M) (m : M) : coe_fn (e₁ * e₂) m = coe_fn e₁ (coe_fn e₂ m) :=
  rfl

@[simp] theorem one_apply (M : Type u_2) [Mul M] (m : M) : coe_fn 1 m = m :=
  rfl

@[simp] theorem apply_inv_self (M : Type u_2) [Mul M] (e : mul_aut M) (m : M) : coe_fn e (coe_fn (e⁻¹) m) = m :=
  mul_equiv.apply_symm_apply e m

@[simp] theorem inv_apply_self (M : Type u_2) [Mul M] (e : mul_aut M) (m : M) : coe_fn (e⁻¹) (coe_fn e m) = m :=
  mul_equiv.apply_symm_apply (e⁻¹) m

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def to_perm (M : Type u_2) [Mul M] : mul_aut M →* equiv.perm M :=
  monoid_hom.mk mul_equiv.to_equiv sorry sorry

/-- group conjugation as a group homomorphism into the automorphism group.
  `conj g h = g * h * g⁻¹` -/
def conj {G : Type u_3} [group G] : G →* mul_aut G :=
  monoid_hom.mk
    (fun (g : G) => mul_equiv.mk (fun (h : G) => g * h * (g⁻¹)) (fun (h : G) => g⁻¹ * h * g) sorry sorry sorry) sorry
    sorry

@[simp] theorem conj_apply {G : Type u_3} [group G] (g : G) (h : G) : coe_fn (coe_fn conj g) h = g * h * (g⁻¹) :=
  rfl

@[simp] theorem conj_symm_apply {G : Type u_3} [group G] (g : G) (h : G) : coe_fn (mul_equiv.symm (coe_fn conj g)) h = g⁻¹ * h * g :=
  rfl

@[simp] theorem conj_inv_apply {G : Type u_1} [group G] (g : G) (h : G) : coe_fn (coe_fn conj g⁻¹) h = g⁻¹ * h * g :=
  rfl

end mul_aut


namespace add_aut


/--
The group operation on additive automorphisms is defined by
`λ g h, add_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
protected instance group (A : Type u_1) [Add A] : group (add_aut A) :=
  group.mk (fun (g h : A ≃+ A) => add_equiv.trans h g) sorry (add_equiv.refl A) sorry sorry add_equiv.symm
    (fun (a b : A ≃+ A) => a * add_equiv.symm b) sorry

protected instance inhabited (A : Type u_1) [Add A] : Inhabited (add_aut A) :=
  { default := 1 }

@[simp] theorem coe_mul (A : Type u_1) [Add A] (e₁ : add_aut A) (e₂ : add_aut A) : ⇑(e₁ * e₂) = ⇑e₁ ∘ ⇑e₂ :=
  rfl

@[simp] theorem coe_one (A : Type u_1) [Add A] : ⇑1 = id :=
  rfl

theorem mul_def (A : Type u_1) [Add A] (e₁ : add_aut A) (e₂ : add_aut A) : e₁ * e₂ = add_equiv.trans e₂ e₁ :=
  rfl

theorem one_def (A : Type u_1) [Add A] : 1 = add_equiv.refl A :=
  rfl

theorem inv_def (A : Type u_1) [Add A] (e₁ : add_aut A) : e₁⁻¹ = add_equiv.symm e₁ :=
  rfl

@[simp] theorem mul_apply (A : Type u_1) [Add A] (e₁ : add_aut A) (e₂ : add_aut A) (a : A) : coe_fn (e₁ * e₂) a = coe_fn e₁ (coe_fn e₂ a) :=
  rfl

@[simp] theorem one_apply (A : Type u_1) [Add A] (a : A) : coe_fn 1 a = a :=
  rfl

@[simp] theorem apply_inv_self (A : Type u_1) [Add A] (e : add_aut A) (a : A) : coe_fn (e⁻¹) (coe_fn e a) = a :=
  add_equiv.apply_symm_apply (e⁻¹) a

@[simp] theorem inv_apply_self (A : Type u_1) [Add A] (e : add_aut A) (a : A) : coe_fn e (coe_fn (e⁻¹) a) = a :=
  add_equiv.apply_symm_apply e a

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def to_perm (A : Type u_1) [Add A] : add_aut A →* equiv.perm A :=
  monoid_hom.mk add_equiv.to_equiv sorry sorry

