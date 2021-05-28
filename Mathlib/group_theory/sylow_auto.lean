/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.group_action.default
import Mathlib.group_theory.quotient_group
import Mathlib.group_theory.order_of_element
import Mathlib.data.zmod.basic
import Mathlib.data.fintype.card
import Mathlib.data.list.rotate
import PostPort

universes u v u_1 

namespace Mathlib

namespace mul_action


theorem mem_fixed_points_iff_card_orbit_eq_one {G : Type u} {α : Type v} [group G] [mul_action G α] {a : α} [fintype ↥(orbit G a)] : a ∈ fixed_points G α ↔ fintype.card ↥(orbit G a) = 1 := sorry

theorem card_modeq_card_fixed_points {G : Type u} {α : Type v} [group G] [mul_action G α] [fintype α] [fintype G] [fintype ↥(fixed_points G α)] (p : ℕ) {n : ℕ} [hp : fact (nat.prime p)] (h : fintype.card G = p ^ n) : nat.modeq p (fintype.card α) (fintype.card ↥(fixed_points G α)) := sorry

end mul_action


theorem quotient_group.card_preimage_mk {G : Type u} [group G] [fintype G] (s : subgroup G) (t : set (quotient_group.quotient s)) : fintype.card ↥(quotient_group.mk ⁻¹' t) = fintype.card ↥s * fintype.card ↥t := sorry

namespace sylow


/-- Given a vector `v` of length `n`, make a vector of length `n+1` whose product is `1`,
by consing the the inverse of the product of `v`. -/
def mk_vector_prod_eq_one {G : Type u} [group G] (n : ℕ) (v : vector G n) : vector G (n + 1) :=
  list.prod (vector.to_list v)⁻¹::ᵥv

theorem mk_vector_prod_eq_one_injective {G : Type u} [group G] (n : ℕ) : function.injective (mk_vector_prod_eq_one n) := sorry

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectors_prod_eq_one (G : Type u_1) [group G] (n : ℕ) : set (vector G n) :=
  set_of fun (v : vector G n) => list.prod (vector.to_list v) = 1

theorem mem_vectors_prod_eq_one {G : Type u} [group G] {n : ℕ} (v : vector G n) : v ∈ vectors_prod_eq_one G n ↔ list.prod (vector.to_list v) = 1 :=
  iff.rfl

theorem mem_vectors_prod_eq_one_iff {G : Type u} [group G] {n : ℕ} (v : vector G (n + 1)) : v ∈ vectors_prod_eq_one G (n + 1) ↔ v ∈ set.range (mk_vector_prod_eq_one n) := sorry

/-- The rotation action of `zmod n` (viewed as multiplicative group) on
`vectors_prod_eq_one G n`, where `G` is a multiplicative group. -/
def rotate_vectors_prod_eq_one (G : Type u_1) [group G] (n : ℕ) (m : multiplicative (zmod n)) (v : ↥(vectors_prod_eq_one G n)) : ↥(vectors_prod_eq_one G n) :=
  { val := { val := list.rotate (vector.to_list (subtype.val v)) (zmod.val m), property := sorry }, property := sorry }

protected instance rotate_vectors_prod_eq_one.mul_action {G : Type u} [group G] (n : ℕ) [fact (0 < n)] : mul_action (multiplicative (zmod n)) ↥(vectors_prod_eq_one G n) :=
  mul_action.mk sorry sorry

theorem one_mem_vectors_prod_eq_one {G : Type u} [group G] (n : ℕ) : vector.repeat 1 n ∈ vectors_prod_eq_one G n := sorry

theorem one_mem_fixed_points_rotate {G : Type u} [group G] (n : ℕ) [fact (0 < n)] : { val := vector.repeat 1 n, property := one_mem_vectors_prod_eq_one n } ∈
  mul_action.fixed_points (multiplicative (zmod n)) ↥(vectors_prod_eq_one G n) := sorry

/-- Cauchy's theorem -/
theorem exists_prime_order_of_dvd_card {G : Type u} [group G] [fintype G] (p : ℕ) [hp : fact (nat.prime p)] (hdvd : p ∣ fintype.card G) : ∃ (x : G), order_of x = p := sorry

theorem mem_fixed_points_mul_left_cosets_iff_mem_normalizer {G : Type u} [group G] {H : subgroup G} [fintype ↥↑H] {x : G} : ↑x ∈ mul_action.fixed_points (↥H) (quotient_group.quotient H) ↔ x ∈ subgroup.normalizer H := sorry

def fixed_points_mul_left_cosets_equiv_quotient {G : Type u} [group G] (H : subgroup G) [fintype ↥↑H] : ↥(mul_action.fixed_points (↥H) (quotient_group.quotient H)) ≃
  quotient_group.quotient (subgroup.comap (subgroup.subtype (subgroup.normalizer H)) H) :=
  equiv.subtype_quotient_equiv_quotient_subtype (↑(subgroup.normalizer H))
    (mul_action.fixed_points (↥H)
      (quotient (id (setoid.mk (fun (x y : G) => x⁻¹ * y ∈ H) (quotient_group.left_rel._proof_1 H)))))
    sorry sorry

theorem exists_subgroup_card_pow_prime {G : Type u} [group G] [fintype G] (p : ℕ) {n : ℕ} [hp : fact (nat.prime p)] (hdvd : p ^ n ∣ fintype.card G) : ∃ (H : subgroup G), fintype.card ↥H = p ^ n := sorry

