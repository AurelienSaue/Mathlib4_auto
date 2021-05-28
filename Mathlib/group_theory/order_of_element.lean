/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.order
import Mathlib.group_theory.coset
import Mathlib.data.nat.totient
import Mathlib.data.int.gcd
import Mathlib.data.set.finite
import Mathlib.PostPort

universes u_1 u_2 l 

namespace Mathlib

-- TODO mem_range_iff_mem_finset_range_of_mod_eq should be moved elsewhere.

namespace finset


theorem mem_range_iff_mem_finset_range_of_mod_eq {α : Type u_1} [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ} (hn : 0 < n) (h : ∀ (i : ℤ), f (i % ↑n) = f i) : a ∈ set.range f ↔ a ∈ image (fun (i : ℕ) => f ↑i) (range n) := sorry

end finset


theorem mem_normalizer_fintype {α : Type u_1} [group α] {s : set α} [fintype ↥s] {x : α} (h : ∀ (n : α), n ∈ s → x * n * (x⁻¹) ∈ s) : x ∈ subgroup.set_normalizer s := sorry

protected instance fintype_bot {α : Type u_1} [group α] : fintype ↥⊥ :=
  fintype.mk (singleton 1) sorry

@[simp] theorem card_trivial {α : Type u_1} [group α] : fintype.card ↥⊥ = 1 := sorry

theorem card_eq_card_quotient_mul_card_subgroup {α : Type u_1} [group α] [fintype α] (s : subgroup α) [fintype ↥s] [decidable_pred fun (a : α) => a ∈ s] : fintype.card α = fintype.card (quotient_group.quotient s) * fintype.card ↥s := sorry

theorem card_subgroup_dvd_card {α : Type u_1} [group α] [fintype α] (s : subgroup α) [fintype ↥s] : fintype.card ↥s ∣ fintype.card α := sorry

theorem card_quotient_dvd_card {α : Type u_1} [group α] [fintype α] (s : subgroup α) [decidable_pred fun (a : α) => a ∈ s] [fintype ↥s] : fintype.card (quotient_group.quotient s) ∣ fintype.card α := sorry

theorem exists_gpow_eq_one {α : Type u_1} [group α] [fintype α] (a : α) : ∃ (i : ℤ), ∃ (H : i ≠ 0), a ^ i = 1 := sorry

theorem exists_pow_eq_one {α : Type u_1} [group α] [fintype α] (a : α) : ∃ (i : ℕ), ∃ (H : i > 0), a ^ i = 1 := sorry

/-- `order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `a ^ n = 1` -/
def order_of {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] (a : α) : ℕ :=
  nat.find (exists_pow_eq_one a)

theorem pow_order_of_eq_one {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] (a : α) : a ^ order_of a = 1 := sorry

theorem order_of_pos {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] (a : α) : 0 < order_of a := sorry

theorem pow_injective_of_lt_order_of {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] {n : ℕ} {m : ℕ} (a : α) (hn : n < order_of a) (hm : m < order_of a) (eq : a ^ n = a ^ m) : n = m :=
  or.elim (le_total n m) (fun (h : n ≤ m) => pow_injective_aux a h hn hm eq)
    fun (h : m ≤ n) => Eq.symm (pow_injective_aux a h hm hn (Eq.symm eq))

theorem order_of_le_card_univ {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] : order_of a ≤ fintype.card α :=
  finset.card_le_of_inj_on (pow a) (fun (n : ℕ) (_x : n < order_of a) => fintype.complete (a ^ n))
    fun (i j : ℕ) => pow_injective_of_lt_order_of a

theorem pow_eq_mod_order_of {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] {n : ℕ} : a ^ n = a ^ (n % order_of a) := sorry

theorem gpow_eq_mod_order_of {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] {i : ℤ} : a ^ i = a ^ (i % ↑(order_of a)) := sorry

theorem mem_gpowers_iff_mem_range_order_of {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] {a : α} {a' : α} : a' ∈ subgroup.gpowers a ↔ a' ∈ finset.image (pow a) (finset.range (order_of a)) :=
  finset.mem_range_iff_mem_finset_range_of_mod_eq (order_of_pos a) fun (i : ℤ) => Eq.symm gpow_eq_mod_order_of

protected instance decidable_gpowers {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] : decidable_pred ↑(subgroup.gpowers a) :=
  fun (a' : α) => decidable_of_iff' (a' ∈ finset.image (pow a) (finset.range (order_of a))) sorry

theorem order_of_dvd_of_pow_eq_one {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] {n : ℕ} (h : a ^ n = 1) : order_of a ∣ n := sorry

theorem order_of_dvd_iff_pow_eq_one {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] {n : ℕ} : order_of a ∣ n ↔ a ^ n = 1 := sorry

theorem order_of_le_of_pow_eq_one {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] {n : ℕ} (hn : 0 < n) (h : a ^ n = 1) : order_of a ≤ n :=
  nat.find_min' (exists_pow_eq_one a) (Exists.intro hn h)

theorem sum_card_order_of_eq_card_pow_eq_one {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] {n : ℕ} (hn : 0 < n) : (finset.sum (finset.filter (fun (_x : ℕ) => _x ∣ n) (finset.range (Nat.succ n)))
    fun (m : ℕ) => finset.card (finset.filter (fun (a : α) => order_of a = m) finset.univ)) =
  finset.card (finset.filter (fun (a : α) => a ^ n = 1) finset.univ) := sorry

theorem order_eq_card_gpowers {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] : order_of a = fintype.card ↥↑(subgroup.gpowers a) := sorry

@[simp] theorem order_of_one {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] : order_of 1 = 1 := sorry

@[simp] theorem order_of_eq_one_iff {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] : order_of a = 1 ↔ a = 1 := sorry

theorem order_of_eq_prime {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] {p : ℕ} [hp : fact (nat.prime p)] (hg : a ^ p = 1) (hg1 : a ≠ 1) : order_of a = p :=
  or.resolve_left (and.right hp (order_of a) (order_of_dvd_of_pow_eq_one hg)) (mt (iff.mp order_of_eq_one_iff) hg1)

/- TODO: use cardinal theory, introduce `card : set α → ℕ`, or setup decidability for cosets -/

theorem order_of_dvd_card_univ {α : Type u_1} {a : α} [group α] [fintype α] [dec : DecidableEq α] : order_of a ∣ fintype.card α := sorry

@[simp] theorem pow_card_eq_one {α : Type u_1} [group α] [fintype α] (a : α) : a ^ fintype.card α = 1 := sorry

theorem mem_powers_iff_mem_gpowers {α : Type u_1} [group α] [fintype α] {a : α} {x : α} : x ∈ submonoid.powers a ↔ x ∈ subgroup.gpowers a := sorry

theorem powers_eq_gpowers {α : Type u_1} [group α] [fintype α] (a : α) : ↑(submonoid.powers a) = ↑(subgroup.gpowers a) :=
  set.ext fun (x : α) => mem_powers_iff_mem_gpowers

theorem order_of_pow {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] (a : α) (n : ℕ) : order_of (a ^ n) = order_of a / nat.gcd (order_of a) n := sorry

theorem image_range_order_of {α : Type u_1} [group α] [fintype α] [dec : DecidableEq α] (a : α) : finset.image (fun (i : ℕ) => a ^ i) (finset.range (order_of a)) = set.to_finset ↑(subgroup.gpowers a) := sorry

theorem pow_gcd_card_eq_one_iff {α : Type u_1} [group α] [fintype α] {n : ℕ} {a : α} : a ^ n = 1 ↔ a ^ nat.gcd n (fintype.card α) = 1 := sorry

/-- A group is called *cyclic* if it is generated by a single element. -/
class is_cyclic (α : Type u_2) [group α] 
where
  exists_generator : ∃ (g : α), ∀ (x : α), x ∈ subgroup.gpowers g

/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `comm_group`. -/
def is_cyclic.comm_group {α : Type u_1} [hg : group α] [is_cyclic α] : comm_group α :=
  comm_group.mk group.mul group.mul_assoc group.one group.one_mul group.mul_one group.inv group.div group.mul_left_inv
    sorry

theorem is_cyclic_of_order_of_eq_card {α : Type u_1} [group α] [DecidableEq α] [fintype α] (x : α) (hx : order_of x = fintype.card α) : is_cyclic α := sorry

theorem is_cyclic_of_prime_card {α : Type u_1} [group α] [fintype α] {p : ℕ} [hp : fact (nat.prime p)] (h : fintype.card α = p) : is_cyclic α := sorry

theorem order_of_eq_card_of_forall_mem_gpowers {α : Type u_1} [group α] [DecidableEq α] [fintype α] {g : α} (hx : ∀ (x : α), x ∈ subgroup.gpowers g) : order_of g = fintype.card α := sorry

protected instance bot.is_cyclic {α : Type u_1} [group α] : is_cyclic ↥⊥ :=
  is_cyclic.mk
    (Exists.intro 1 fun (x : ↥⊥) => Exists.intro 0 (subtype.eq (Eq.symm (iff.mp subgroup.mem_bot (subtype.property x)))))

protected instance subgroup.is_cyclic {α : Type u_1} [group α] [is_cyclic α] (H : subgroup α) : is_cyclic ↥H :=
  sorry

theorem is_cyclic.card_pow_eq_one_le {α : Type u_1} [group α] [DecidableEq α] [fintype α] [is_cyclic α] {n : ℕ} (hn0 : 0 < n) : finset.card (finset.filter (fun (a : α) => a ^ n = 1) finset.univ) ≤ n := sorry

theorem is_cyclic.exists_monoid_generator (α : Type u_1) [group α] [fintype α] [is_cyclic α] : ∃ (x : α), ∀ (y : α), y ∈ submonoid.powers x := sorry

theorem is_cyclic.image_range_order_of {α : Type u_1} {a : α} [group α] [DecidableEq α] [fintype α] (ha : ∀ (x : α), x ∈ subgroup.gpowers a) : finset.image (fun (i : ℕ) => a ^ i) (finset.range (order_of a)) = finset.univ := sorry

theorem is_cyclic.image_range_card {α : Type u_1} {a : α} [group α] [DecidableEq α] [fintype α] (ha : ∀ (x : α), x ∈ subgroup.gpowers a) : finset.image (fun (i : ℕ) => a ^ i) (finset.range (fintype.card α)) = finset.univ := sorry

theorem card_pow_eq_one_eq_order_of_aux {α : Type u_1} [group α] [DecidableEq α] [fintype α] (hn : ∀ (n : ℕ), 0 < n → finset.card (finset.filter (fun (a : α) => a ^ n = 1) finset.univ) ≤ n) (a : α) : finset.card (finset.filter (fun (b : α) => b ^ order_of a = 1) finset.univ) = order_of a := sorry

theorem card_order_of_eq_totient_aux₂ {α : Type u_1} [group α] [DecidableEq α] [fintype α] (hn : ∀ (n : ℕ), 0 < n → finset.card (finset.filter (fun (a : α) => a ^ n = 1) finset.univ) ≤ n) {d : ℕ} (hd : d ∣ fintype.card α) : finset.card (finset.filter (fun (a : α) => order_of a = d) finset.univ) = nat.totient d := sorry

theorem is_cyclic_of_card_pow_eq_one_le {α : Type u_1} [group α] [DecidableEq α] [fintype α] (hn : ∀ (n : ℕ), 0 < n → finset.card (finset.filter (fun (a : α) => a ^ n = 1) finset.univ) ≤ n) : is_cyclic α := sorry

theorem is_cyclic.card_order_of_eq_totient {α : Type u_1} [group α] [is_cyclic α] [DecidableEq α] [fintype α] {d : ℕ} (hd : d ∣ fintype.card α) : finset.card (finset.filter (fun (a : α) => order_of a = d) finset.univ) = nat.totient d :=
  card_order_of_eq_totient_aux₂ (fun (n : ℕ) => is_cyclic.card_pow_eq_one_le) hd

