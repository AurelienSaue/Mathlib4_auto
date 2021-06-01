/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.algebra.group.basic
import Mathlib.algebra.group.hom
import Mathlib.algebra.group.pi
import Mathlib.algebra.group.prod
import Mathlib.PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
# The group of permutations (self-equivalences) of a type `α`

This file defines the `group` structure on `equiv.perm α`.
-/

namespace equiv


namespace perm


protected instance perm_group {α : Type u} : group (perm α) :=
  group.mk (fun (f g : perm α) => equiv.trans g f) sorry (equiv.refl α) sorry sorry equiv.symm
    (div_inv_monoid.div._default (fun (f g : perm α) => equiv.trans g f) sorry (equiv.refl α) sorry
      sorry equiv.symm)
    sorry

theorem mul_apply {α : Type u} (f : perm α) (g : perm α) (x : α) :
    coe_fn (f * g) x = coe_fn f (coe_fn g x) :=
  trans_apply g f x

theorem one_apply {α : Type u} (x : α) : coe_fn 1 x = x := rfl

@[simp] theorem inv_apply_self {α : Type u} (f : perm α) (x : α) : coe_fn (f⁻¹) (coe_fn f x) = x :=
  symm_apply_apply f x

@[simp] theorem apply_inv_self {α : Type u} (f : perm α) (x : α) : coe_fn f (coe_fn (f⁻¹) x) = x :=
  apply_symm_apply f x

theorem one_def {α : Type u} : 1 = equiv.refl α := rfl

theorem mul_def {α : Type u} (f : perm α) (g : perm α) : f * g = equiv.trans g f := rfl

theorem inv_def {α : Type u} (f : perm α) : f⁻¹ = equiv.symm f := rfl

@[simp] theorem coe_mul {α : Type u} (f : perm α) (g : perm α) : ⇑(f * g) = ⇑f ∘ ⇑g := rfl

@[simp] theorem coe_one {α : Type u} : ⇑1 = id := rfl

theorem eq_inv_iff_eq {α : Type u} {f : perm α} {x : α} {y : α} :
    x = coe_fn (f⁻¹) y ↔ coe_fn f x = y :=
  eq_symm_apply f

theorem inv_eq_iff_eq {α : Type u} {f : perm α} {x : α} {y : α} :
    coe_fn (f⁻¹) x = y ↔ x = coe_fn f y :=
  symm_apply_eq f

/-! Lemmas about mixing `perm` with `equiv`. Because we have multiple ways to express
`equiv.refl`, `equiv.symm`, and `equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/

@[simp] theorem trans_one {α : Sort u_1} {β : Type u_2} (e : α ≃ β) : equiv.trans e 1 = e :=
  trans_refl e

@[simp] theorem mul_refl {α : Type u} (e : perm α) : e * equiv.refl α = e := trans_refl e

@[simp] theorem one_symm {α : Type u} : equiv.symm 1 = 1 := refl_symm

@[simp] theorem refl_inv {α : Type u} : equiv.refl α⁻¹ = 1 := refl_symm

@[simp] theorem one_trans {α : Type u_1} {β : Sort u_2} (e : α ≃ β) : equiv.trans 1 e = e :=
  refl_trans e

@[simp] theorem refl_mul {α : Type u} (e : perm α) : equiv.refl α * e = e := refl_trans e

@[simp] theorem inv_trans {α : Type u} (e : perm α) : equiv.trans (e⁻¹) e = 1 := symm_trans e

@[simp] theorem mul_symm {α : Type u} (e : perm α) : e * equiv.symm e = 1 := symm_trans e

@[simp] theorem trans_inv {α : Type u} (e : perm α) : equiv.trans e (e⁻¹) = 1 := trans_symm e

@[simp] theorem symm_mul {α : Type u} (e : perm α) : equiv.symm e * e = 1 := trans_symm e

/-! Lemmas about `equiv.perm.sum_congr` re-expressed via the group structure. -/

@[simp] theorem sum_congr_mul {α : Type u_1} {β : Type u_2} (e : perm α) (f : perm β) (g : perm α)
    (h : perm β) : sum_congr e f * sum_congr g h = sum_congr (e * g) (f * h) :=
  sum_congr_trans g h e f

@[simp] theorem sum_congr_inv {α : Type u_1} {β : Type u_2} (e : perm α) (f : perm β) :
    sum_congr e f⁻¹ = sum_congr (e⁻¹) (f⁻¹) :=
  sum_congr_symm e f

@[simp] theorem sum_congr_one {α : Type u_1} {β : Type u_2} : sum_congr 1 1 = 1 := sum_congr_refl

/-- `equiv.perm.sum_congr` as a `monoid_hom`, with its two arguments bundled into a single `prod`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
def sum_congr_hom (α : Type u_1) (β : Type u_2) : perm α × perm β →* perm (α ⊕ β) :=
  monoid_hom.mk (fun (a : perm α × perm β) => sum_congr (prod.fst a) (prod.snd a)) sum_congr_one
    sorry

theorem sum_congr_hom_injective {α : Type u_1} {β : Type u_2} :
    function.injective ⇑(sum_congr_hom α β) :=
  sorry

@[simp] theorem sum_congr_swap_one {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    (i : α) (j : α) : sum_congr (swap i j) 1 = swap (sum.inl i) (sum.inl j) :=
  sum_congr_swap_refl i j

@[simp] theorem sum_congr_one_swap {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    (i : β) (j : β) : sum_congr 1 (swap i j) = swap (sum.inr i) (sum.inr j) :=
  sum_congr_refl_swap i j

/-! Lemmas about `equiv.perm.sigma_congr_right` re-expressed via the group structure. -/

@[simp] theorem sigma_congr_right_mul {α : Type u_1} {β : α → Type u_2} (F : (a : α) → perm (β a))
    (G : (a : α) → perm (β a)) :
    sigma_congr_right F * sigma_congr_right G = sigma_congr_right (F * G) :=
  sigma_congr_right_trans G F

@[simp] theorem sigma_congr_right_inv {α : Type u_1} {β : α → Type u_2} (F : (a : α) → perm (β a)) :
    sigma_congr_right F⁻¹ = sigma_congr_right fun (a : α) => F a⁻¹ :=
  sigma_congr_right_symm F

@[simp] theorem sigma_congr_right_one {α : Type u_1} {β : α → Type u_2} : sigma_congr_right 1 = 1 :=
  sigma_congr_right_refl

/-- `equiv.perm.sigma_congr_right` as a `monoid_hom`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
def sigma_congr_right_hom {α : Type u_1} (β : α → Type u_2) :
    ((a : α) → perm (β a)) →* perm (sigma fun (a : α) => β a) :=
  monoid_hom.mk sigma_congr_right sorry sorry

theorem sigma_congr_right_hom_injective {α : Type u_1} {β : α → Type u_2} :
    function.injective ⇑(sigma_congr_right_hom β) :=
  sorry

end perm


@[simp] theorem swap_inv {α : Type u} [DecidableEq α] (x : α) (y : α) : swap x y⁻¹ = swap x y := rfl

@[simp] theorem swap_mul_self {α : Type u} [DecidableEq α] (i : α) (j : α) :
    swap i j * swap i j = 1 :=
  swap_swap i j

theorem swap_mul_eq_mul_swap {α : Type u} [DecidableEq α] (f : perm α) (x : α) (y : α) :
    swap x y * f = f * swap (coe_fn (f⁻¹) x) (coe_fn (f⁻¹) y) :=
  sorry

theorem mul_swap_eq_swap_mul {α : Type u} [DecidableEq α] (f : perm α) (x : α) (y : α) :
    f * swap x y = swap (coe_fn f x) (coe_fn f y) * f :=
  sorry

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp] theorem swap_mul_self_mul {α : Type u} [DecidableEq α] (i : α) (j : α) (σ : perm α) :
    swap i j * (swap i j * σ) = σ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (swap i j * (swap i j * σ) = σ))
        (Eq.symm (mul_assoc (swap i j) (swap i j) σ))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (swap i j * swap i j * σ = σ)) (swap_mul_self i j)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 * σ = σ)) (one_mul σ))) (Eq.refl σ)))

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp] theorem mul_swap_mul_self {α : Type u} [DecidableEq α] (i : α) (j : α) (σ : perm α) :
    σ * swap i j * swap i j = σ :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (σ * swap i j * swap i j = σ)) (mul_assoc σ (swap i j) (swap i j))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (σ * (swap i j * swap i j) = σ)) (swap_mul_self i j)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (σ * 1 = σ)) (mul_one σ))) (Eq.refl σ)))

/-- A stronger version of `mul_right_injective` -/
@[simp] theorem swap_mul_involutive {α : Type u} [DecidableEq α] (i : α) (j : α) :
    function.involutive (Mul.mul (swap i j)) :=
  swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp] theorem mul_swap_involutive {α : Type u} [DecidableEq α] (i : α) (j : α) :
    function.involutive fun (_x : perm α) => _x * swap i j :=
  mul_swap_mul_self i j

theorem swap_mul_eq_iff {α : Type u} [DecidableEq α] {i : α} {j : α} {σ : perm α} :
    swap i j * σ = σ ↔ i = j :=
  sorry

theorem mul_swap_eq_iff {α : Type u} [DecidableEq α] {i : α} {j : α} {σ : perm α} :
    σ * swap i j = σ ↔ i = j :=
  sorry

theorem swap_mul_swap_mul_swap {α : Type u} [DecidableEq α] {x : α} {y : α} {z : α} (hwz : x ≠ y)
    (hxz : x ≠ z) : swap y z * swap x y * swap y z = swap z x :=
  sorry

end Mathlib