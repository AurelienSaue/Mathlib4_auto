/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.perm.sign
import Mathlib.PostPort

universes u_2 u_1 

namespace Mathlib

/-!
# Cyclic permutations

## Main definitions

In the following, `f : equiv.perm β`.

* `equiv.perm.is_cycle`: `f.is_cycle` when two nonfixed points of `β`
  are related by repeated application of `f`.
* `equiv.perm.same_cycle`: `f.same_cycle x y` when `x` and `y` are in the same cycle of `f`.

The following two definitions require that `β` is a `fintype`:

* `equiv.perm.cycle_of`: `f.cycle_of x` is the cycle of `f` that `x` belongs to.
* `equiv.perm.cycle_factors`: `f.cycle_factors` is a list of disjoint cyclic permutations that
  multiply to `f`.

-/

namespace equiv.perm


/-!
### `is_cycle`
-/

/-- A permutation is a cycle when any two nonfixed points of the permutation are related by repeated
  application of the permutation. -/
def is_cycle {β : Type u_2} (f : perm β) :=
  ∃ (x : β), coe_fn f x ≠ x ∧ ∀ (y : β), coe_fn f y ≠ y → ∃ (i : ℤ), coe_fn (f ^ i) x = y

theorem is_cycle.swap {α : Type u_1} [DecidableEq α] {x : α} {y : α} (hxy : x ≠ y) :
    is_cycle (swap x y) :=
  sorry

theorem is_cycle.inv {β : Type u_2} {f : perm β} (hf : is_cycle f) : is_cycle (f⁻¹) := sorry

theorem is_cycle.exists_gpow_eq {β : Type u_2} {f : perm β} (hf : is_cycle f) {x : β} {y : β}
    (hx : coe_fn f x ≠ x) (hy : coe_fn f y ≠ y) : ∃ (i : ℤ), coe_fn (f ^ i) x = y :=
  sorry

theorem is_cycle.exists_pow_eq {β : Type u_2} [fintype β] {f : perm β} (hf : is_cycle f) {x : β}
    {y : β} (hx : coe_fn f x ≠ x) (hy : coe_fn f y ≠ y) : ∃ (i : ℕ), coe_fn (f ^ i) x = y :=
  sorry

theorem is_cycle_swap_mul_aux₁ {α : Type u_1} [DecidableEq α] (n : ℕ) {b : α} {x : α} {f : perm α}
    (hb : coe_fn (swap x (coe_fn f x) * f) b ≠ b) (h : coe_fn (f ^ n) (coe_fn f x) = b) :
    ∃ (i : ℤ), coe_fn ((swap x (coe_fn f x) * f) ^ i) (coe_fn f x) = b :=
  sorry

theorem is_cycle_swap_mul_aux₂ {α : Type u_1} [DecidableEq α] (n : ℤ) {b : α} {x : α} {f : perm α}
    (hb : coe_fn (swap x (coe_fn f x) * f) b ≠ b) (h : coe_fn (f ^ n) (coe_fn f x) = b) :
    ∃ (i : ℤ), coe_fn ((swap x (coe_fn f x) * f) ^ i) (coe_fn f x) = b :=
  sorry

theorem is_cycle.eq_swap_of_apply_apply_eq_self {α : Type u_1} [DecidableEq α] {f : perm α}
    (hf : is_cycle f) {x : α} (hfx : coe_fn f x ≠ x) (hffx : coe_fn f (coe_fn f x) = x) :
    f = swap x (coe_fn f x) :=
  sorry

theorem is_cycle.swap_mul {α : Type u_1} [DecidableEq α] {f : perm α} (hf : is_cycle f) {x : α}
    (hx : coe_fn f x ≠ x) (hffx : coe_fn f (coe_fn f x) ≠ x) : is_cycle (swap x (coe_fn f x) * f) :=
  sorry

theorem is_cycle.sign {α : Type u_1} [DecidableEq α] [fintype α] {f : perm α} (hf : is_cycle f) :
    coe_fn sign f = -(-1) ^ finset.card (support f) :=
  sorry

/-!
### `same_cycle`
-/

/-- The equivalence relation indicating that two points are in the same cycle of a permutation. -/
def same_cycle {β : Type u_2} (f : perm β) (x : β) (y : β) := ∃ (i : ℤ), coe_fn (f ^ i) x = y

theorem same_cycle.refl {β : Type u_2} (f : perm β) (x : β) : same_cycle f x x := Exists.intro 0 rfl

theorem same_cycle.symm {β : Type u_2} (f : perm β) {x : β} {y : β} :
    same_cycle f x y → same_cycle f y x :=
  sorry

theorem same_cycle.trans {β : Type u_2} (f : perm β) {x : β} {y : β} {z : β} :
    same_cycle f x y → same_cycle f y z → same_cycle f x z :=
  sorry

theorem same_cycle.apply_eq_self_iff {β : Type u_2} {f : perm β} {x : β} {y : β} :
    same_cycle f x y → (coe_fn f x = x ↔ coe_fn f y = y) :=
  sorry

theorem is_cycle.same_cycle {β : Type u_2} {f : perm β} (hf : is_cycle f) {x : β} {y : β}
    (hx : coe_fn f x ≠ x) (hy : coe_fn f y ≠ y) : same_cycle f x y :=
  is_cycle.exists_gpow_eq hf hx hy

protected instance same_cycle.decidable_rel {α : Type u_1} [DecidableEq α] [fintype α]
    (f : perm α) : DecidableRel (same_cycle f) :=
  fun (x y : α) =>
    decidable_of_iff (∃ (n : ℕ), ∃ (H : n ∈ list.range (order_of f)), coe_fn (f ^ n) x = y) sorry

theorem same_cycle_apply {β : Type u_2} {f : perm β} {x : β} {y : β} :
    same_cycle f x (coe_fn f y) ↔ same_cycle f x y :=
  sorry

theorem same_cycle_cycle {β : Type u_2} {f : perm β} {x : β} (hx : coe_fn f x ≠ x) :
    is_cycle f ↔ ∀ {y : β}, same_cycle f x y ↔ coe_fn f y ≠ y :=
  sorry

theorem same_cycle_inv {β : Type u_2} (f : perm β) {x : β} {y : β} :
    same_cycle (f⁻¹) x y ↔ same_cycle f x y :=
  sorry

theorem same_cycle_inv_apply {β : Type u_2} {f : perm β} {x : β} {y : β} :
    same_cycle f x (coe_fn (f⁻¹) y) ↔ same_cycle f x y :=
  sorry

/-!
### `cycle_of`
-/

/-- `f.cycle_of x` is the cycle of the permutation `f` to which `x` belongs. -/
def cycle_of {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α) (x : α) : perm α :=
  coe_fn of_subtype (subtype_perm f sorry)

theorem cycle_of_apply {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α) (x : α) (y : α) :
    coe_fn (cycle_of f x) y = ite (same_cycle f x y) (coe_fn f y) y :=
  rfl

theorem cycle_of_inv {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α) (x : α) :
    cycle_of f x⁻¹ = cycle_of (f⁻¹) x :=
  sorry

@[simp] theorem cycle_of_pow_apply_self {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α)
    (x : α) (n : ℕ) : coe_fn (cycle_of f x ^ n) x = coe_fn (f ^ n) x :=
  sorry

@[simp] theorem cycle_of_gpow_apply_self {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α)
    (x : α) (n : ℤ) : coe_fn (cycle_of f x ^ n) x = coe_fn (f ^ n) x :=
  sorry

theorem same_cycle.cycle_of_apply {α : Type u_1} [DecidableEq α] [fintype α] {f : perm α} {x : α}
    {y : α} (h : same_cycle f x y) : coe_fn (cycle_of f x) y = coe_fn f y :=
  dif_pos h

theorem cycle_of_apply_of_not_same_cycle {α : Type u_1} [DecidableEq α] [fintype α] {f : perm α}
    {x : α} {y : α} (h : ¬same_cycle f x y) : coe_fn (cycle_of f x) y = y :=
  dif_neg h

@[simp] theorem cycle_of_apply_self {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α)
    (x : α) : coe_fn (cycle_of f x) x = coe_fn f x :=
  same_cycle.cycle_of_apply (same_cycle.refl f x)

theorem is_cycle.cycle_of_eq {α : Type u_1} [DecidableEq α] [fintype α] {f : perm α}
    (hf : is_cycle f) {x : α} (hx : coe_fn f x ≠ x) : cycle_of f x = f :=
  sorry

theorem cycle_of_one {α : Type u_1} [DecidableEq α] [fintype α] (x : α) : cycle_of 1 x = 1 := sorry

theorem is_cycle_cycle_of {α : Type u_1} [DecidableEq α] [fintype α] (f : perm α) {x : α}
    (hx : coe_fn f x ≠ x) : is_cycle (cycle_of f x) :=
  sorry

/-!
### `cycle_factors`
-/

/-- Given a list `l : list α` and a permutation `f : perm α` whose nonfixed points are all in `l`,
  recursively factors `f` into cycles. -/
def cycle_factors_aux {α : Type u_1} [DecidableEq α] [fintype α] (l : List α) (f : perm α) :
    (∀ {x : α}, coe_fn f x ≠ x → x ∈ l) →
        Subtype
          fun (l : List (perm α)) =>
            list.prod l = f ∧ (∀ (g : perm α), g ∈ l → is_cycle g) ∧ list.pairwise disjoint l :=
  sorry

/-- Factors a permutation `f` into a list of disjoint cyclic permutations that multiply to `f`. -/
def cycle_factors {α : Type u_1} [DecidableEq α] [fintype α] [linear_order α] (f : perm α) :
    Subtype
        fun (l : List (perm α)) =>
          list.prod l = f ∧ (∀ (g : perm α), g ∈ l → is_cycle g) ∧ list.pairwise disjoint l :=
  cycle_factors_aux (finset.sort LessEq finset.univ) f sorry

/-!
### Fixed points
-/

theorem one_lt_nonfixed_point_card_of_ne_one {α : Type u_1} [DecidableEq α] [fintype α] {σ : perm α}
    (h : σ ≠ 1) : 1 < finset.card (finset.filter (fun (x : α) => coe_fn σ x ≠ x) finset.univ) :=
  sorry

theorem fixed_point_card_lt_of_ne_one {α : Type u_1} [DecidableEq α] [fintype α] {σ : perm α}
    (h : σ ≠ 1) :
    finset.card (finset.filter (fun (x : α) => coe_fn σ x = x) finset.univ) < fintype.card α - 1 :=
  sorry

end Mathlib