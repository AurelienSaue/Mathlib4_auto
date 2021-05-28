/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.int.modeq
import Mathlib.data.zmod.basic
import Mathlib.linear_algebra.adic_completion
import Mathlib.data.padics.padic_numbers
import Mathlib.ring_theory.discrete_valuation_ring
import Mathlib.topology.metric_space.cau_seq_filter
import PostPort

namespace Mathlib

/-!
# p-adic integers

This file defines the p-adic integers `ℤ_p` as the subtype of `ℚ_p` with norm `≤ 1`.
We show that `ℤ_p`
* is complete
* is nonarchimedean
* is a normed ring
* is a local ring
* is a discrete valuation ring

The relation between `ℤ_[p]` and `zmod p` is established in another file.

## Important definitions

* `padic_int` : the type of p-adic numbers

## Notation

We introduce the notation `ℤ_[p]` for the p-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (nat.prime p)] as a type class argument.

Coercions into `ℤ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

/-- The p-adic integers ℤ_p are the p-adic numbers with norm ≤ 1. -/
def padic_int (p : ℕ) [fact (nat.prime p)]  :=
  Subtype fun (x : padic p) => norm x ≤ 1

namespace padic_int


/-! ### Ring structure and coercion to `ℚ_[p]` -/

protected instance padic.has_coe {p : ℕ} [fact (nat.prime p)] : has_coe (padic_int p) (padic p) :=
  has_coe.mk subtype.val

theorem ext {p : ℕ} [fact (nat.prime p)] {x : padic_int p} {y : padic_int p} : ↑x = ↑y → x = y :=
  iff.mpr subtype.ext_iff_val

/-- Addition on ℤ_p is inherited from ℚ_p. -/
protected instance has_add {p : ℕ} [fact (nat.prime p)] : Add (padic_int p) :=
  { add := fun (_x : padic_int p) => sorry }

/-- Multiplication on ℤ_p is inherited from ℚ_p. -/
protected instance has_mul {p : ℕ} [fact (nat.prime p)] : Mul (padic_int p) :=
  { mul := fun (_x : padic_int p) => sorry }

/-- Negation on ℤ_p is inherited from ℚ_p. -/
protected instance has_neg {p : ℕ} [fact (nat.prime p)] : Neg (padic_int p) :=
  { neg := fun (_x : padic_int p) => sorry }

/-- Subtraction on ℤ_p is inherited from ℚ_p. -/
protected instance has_sub {p : ℕ} [fact (nat.prime p)] : Sub (padic_int p) :=
  { sub := fun (_x : padic_int p) => sorry }

/-- Zero on ℤ_p is inherited from ℚ_p. -/
protected instance has_zero {p : ℕ} [fact (nat.prime p)] : HasZero (padic_int p) :=
  { zero := { val := 0, property := sorry } }

protected instance inhabited {p : ℕ} [fact (nat.prime p)] : Inhabited (padic_int p) :=
  { default := 0 }

/-- One on ℤ_p is inherited from ℚ_p. -/
protected instance has_one {p : ℕ} [fact (nat.prime p)] : HasOne (padic_int p) :=
  { one := { val := 1, property := sorry } }

@[simp] theorem mk_zero {p : ℕ} [fact (nat.prime p)] {h : norm 0 ≤ 1} : { val := 0, property := h } = 0 :=
  rfl

@[simp] theorem val_eq_coe {p : ℕ} [fact (nat.prime p)] (z : padic_int p) : subtype.val z = ↑z :=
  rfl

@[simp] theorem coe_add {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) : ↑(z1 + z2) = ↑z1 + ↑z2 := sorry

@[simp] theorem coe_mul {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) : ↑(z1 * z2) = ↑z1 * ↑z2 := sorry

@[simp] theorem coe_neg {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) : ↑(-z1) = -↑z1 :=
  subtype.cases_on z1
    fun (z1_val : padic p) (z1_property : norm z1_val ≤ 1) =>
      idRhs (↑(-{ val := z1_val, property := z1_property }) = ↑(-{ val := z1_val, property := z1_property })) rfl

@[simp] theorem coe_sub {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) : ↑(z1 - z2) = ↑z1 - ↑z2 := sorry

@[simp] theorem coe_one {p : ℕ} [fact (nat.prime p)] : ↑1 = 1 :=
  rfl

@[simp] theorem coe_coe {p : ℕ} [fact (nat.prime p)] (n : ℕ) : ↑↑n = ↑n := sorry

@[simp] theorem coe_coe_int {p : ℕ} [fact (nat.prime p)] (z : ℤ) : ↑↑z = ↑z := sorry

@[simp] theorem coe_zero {p : ℕ} [fact (nat.prime p)] : ↑0 = 0 :=
  rfl

protected instance ring {p : ℕ} [fact (nat.prime p)] : ring (padic_int p) :=
  ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry

/-- The coercion from ℤ[p] to ℚ[p] as a ring homomorphism. -/
def coe.ring_hom {p : ℕ} [fact (nat.prime p)] : padic_int p →+* padic p :=
  ring_hom.mk coe sorry coe_mul sorry coe_add

@[simp] theorem coe_pow {p : ℕ} [fact (nat.prime p)] (x : padic_int p) (n : ℕ) : ↑(x ^ n) = ↑x ^ n :=
  ring_hom.map_pow coe.ring_hom x n

@[simp] theorem mk_coe {p : ℕ} [fact (nat.prime p)] (k : padic_int p) : { val := ↑k, property := subtype.property k } = k := sorry

/-- The inverse of a p-adic integer with norm equal to 1 is also a p-adic integer. Otherwise, the
inverse is defined to be 0. -/
def inv {p : ℕ} [fact (nat.prime p)] : padic_int p → padic_int p :=
  sorry

protected instance char_zero {p : ℕ} [fact (nat.prime p)] : char_zero (padic_int p) :=
  char_zero.mk
    fun (m n : ℕ) (h : ↑m = ↑n) =>
      nat.cast_injective
        ((fun (this : ↑m = ↑n) => this)
          (eq.mp
            ((fun (a a_1 : padic p) (e_1 : a = a_1) (ᾰ ᾰ_1 : padic p) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (↑↑m) (↑m) (coe_coe m) (↑↑n) (↑n) (coe_coe n))
            (eq.mp (Eq._oldrec (Eq.refl (↑m = ↑n)) (propext subtype.ext_iff)) h)))

@[simp] theorem coe_int_eq {p : ℕ} [fact (nat.prime p)] (z1 : ℤ) (z2 : ℤ) : ↑z1 = ↑z2 ↔ z1 = z2 := sorry

/--
A sequence of integers that is Cauchy with respect to the `p`-adic norm
converges to a `p`-adic integer.
-/
def of_int_seq {p : ℕ} [fact (nat.prime p)] (seq : ℕ → ℤ) (h : is_cau_seq (padic_norm p) fun (n : ℕ) => ↑(seq n)) : padic_int p :=
  { val := quotient.mk { val := fun (n : ℕ) => ↑(seq n), property := h }, property := sorry }

end padic_int


namespace padic_int


/-!
### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

protected instance metric_space (p : ℕ) [fact (nat.prime p)] : metric_space (padic_int p) :=
  subtype.metric_space

protected instance complete_space (p : ℕ) [fact (nat.prime p)] : complete_space (padic_int p) := sorry

protected instance has_norm (p : ℕ) [fact (nat.prime p)] : has_norm (padic_int p) :=
  has_norm.mk fun (z : padic_int p) => norm ↑z

protected theorem mul_comm {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) : z1 * z2 = z2 * z1 := sorry

protected theorem zero_ne_one {p : ℕ} [fact (nat.prime p)] : 0 ≠ 1 :=
  (fun (this : { val := 0, property := has_zero._proof_1 } ≠ { val := 1, property := has_one._proof_1 }) => this)
    (mt (iff.mp subtype.ext_iff_val) zero_ne_one)

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {p : ℕ} [fact (nat.prime p)] (a : padic_int p) (b : padic_int p) : a * b = 0 → a = 0 ∨ b = 0 := sorry

theorem norm_def {p : ℕ} [fact (nat.prime p)] {z : padic_int p} : norm z = norm ↑z :=
  rfl

protected instance normed_comm_ring (p : ℕ) [fact (nat.prime p)] : normed_comm_ring (padic_int p) :=
  normed_comm_ring.mk padic_int.mul_comm

protected instance norm_one_class (p : ℕ) [fact (nat.prime p)] : norm_one_class (padic_int p) :=
  norm_one_class.mk (Eq.trans norm_def norm_one)

protected instance is_absolute_value (p : ℕ) [fact (nat.prime p)] : is_absolute_value fun (z : padic_int p) => norm z :=
  is_absolute_value.mk norm_nonneg (fun (_x : padic_int p) => sorry) (fun (_x : padic_int p) => sorry)
    fun (_x _x_1 : padic_int p) =>
      eq.mpr
        (id
          ((fun (a a_1 : ℝ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℝ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
            (norm (_x * _x_1)) (norm ↑_x * norm ↑_x_1)
            (Eq.trans
              (Eq.trans norm_def
                ((fun (ᾰ ᾰ_1 : padic p) (e_2 : ᾰ = ᾰ_1) => congr_arg norm e_2) (↑(_x * _x_1)) (↑_x * ↑_x_1)
                  (coe_mul _x _x_1)))
              (padic_norm_e.mul ↑_x ↑_x_1))
            (norm _x * norm _x_1) (norm ↑_x * norm ↑_x_1)
            ((fun (ᾰ ᾰ_1 : ℝ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℝ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg Mul.mul e_2) e_3)
              (norm _x) (norm ↑_x) norm_def (norm _x_1) (norm ↑_x_1) norm_def)))
        (Eq.refl (norm ↑_x * norm ↑_x_1))

protected instance integral_domain {p : ℕ} [fact (nat.prime p)] : integral_domain (padic_int p) :=
  integral_domain.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry
    sorry sorry sorry sorry sorry sorry

end padic_int


namespace padic_int


/-! ### Norm -/

theorem norm_le_one {p : ℕ} [fact (nat.prime p)] (z : padic_int p) : norm z ≤ 1 :=
  subtype.cases_on z fun (z_val : padic p) (z_property : norm z_val ≤ 1) => idRhs (norm z_val ≤ 1) z_property

@[simp] theorem norm_mul {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) : norm (z1 * z2) = norm z1 * norm z2 := sorry

@[simp] theorem norm_pow {p : ℕ} [fact (nat.prime p)] (z : padic_int p) (n : ℕ) : norm (z ^ n) = norm z ^ n := sorry

theorem nonarchimedean {p : ℕ} [fact (nat.prime p)] (q : padic_int p) (r : padic_int p) : norm (q + r) ≤ max (norm q) (norm r) := sorry

theorem norm_add_eq_max_of_ne {p : ℕ} [fact (nat.prime p)] {q : padic_int p} {r : padic_int p} : norm q ≠ norm r → norm (q + r) = max (norm q) (norm r) := sorry

theorem norm_eq_of_norm_add_lt_right {p : ℕ} [fact (nat.prime p)] {z1 : padic_int p} {z2 : padic_int p} (h : norm (z1 + z2) < norm z2) : norm z1 = norm z2 := sorry

theorem norm_eq_of_norm_add_lt_left {p : ℕ} [fact (nat.prime p)] {z1 : padic_int p} {z2 : padic_int p} (h : norm (z1 + z2) < norm z1) : norm z1 = norm z2 := sorry

@[simp] theorem padic_norm_e_of_padic_int {p : ℕ} [fact (nat.prime p)] (z : padic_int p) : norm ↑z = norm z := sorry

theorem norm_int_cast_eq_padic_norm {p : ℕ} [fact (nat.prime p)] (z : ℤ) : norm ↑z = norm ↑z := sorry

@[simp] theorem norm_eq_padic_norm {p : ℕ} [fact (nat.prime p)] {q : padic p} (hq : norm q ≤ 1) : norm { val := q, property := hq } = norm q :=
  rfl

@[simp] theorem norm_p {p : ℕ} [fact (nat.prime p)] : norm ↑p = (↑p⁻¹) := sorry

@[simp] theorem norm_p_pow {p : ℕ} [fact (nat.prime p)] (n : ℕ) : norm (↑p ^ n) = ↑p ^ (-↑n) := sorry

protected instance complete (p : ℕ) [fact (nat.prime p)] : cau_seq.is_complete (padic_int p) norm :=
  cau_seq.is_complete.mk sorry

end padic_int


namespace padic_int


theorem exists_pow_neg_lt (p : ℕ) [hp_prime : fact (nat.prime p)] {ε : ℝ} (hε : 0 < ε) : ∃ (k : ℕ), ↑p ^ (-↑k) < ε := sorry

theorem exists_pow_neg_lt_rat (p : ℕ) [hp_prime : fact (nat.prime p)] {ε : ℚ} (hε : 0 < ε) : ∃ (k : ℕ), ↑p ^ (-↑k) < ε := sorry

theorem norm_int_lt_one_iff_dvd {p : ℕ} [hp_prime : fact (nat.prime p)] (k : ℤ) : norm ↑k < 1 ↔ ↑p ∣ k :=
  (fun (this : norm ↑k < 1 ↔ ↑p ∣ k) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (norm ↑k < 1 ↔ ↑p ∣ k)) (norm_int_cast_eq_padic_norm k))) this)
    (padic_norm_e.norm_int_lt_one_iff_dvd k)

theorem norm_int_le_pow_iff_dvd {p : ℕ} [hp_prime : fact (nat.prime p)] {k : ℤ} {n : ℕ} : norm ↑k ≤ ↑p ^ (-↑n) ↔ ↑p ^ n ∣ k := sorry

/-! ### Valuation on `ℤ_[p]` -/

/-- `padic_int.valuation` lifts the p-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) : ℤ :=
  padic.valuation ↑x

theorem norm_eq_pow_val {p : ℕ} [hp_prime : fact (nat.prime p)] {x : padic_int p} (hx : x ≠ 0) : norm x = ↑p ^ (-valuation x) := sorry

@[simp] theorem valuation_zero {p : ℕ} [hp_prime : fact (nat.prime p)] : valuation 0 = 0 :=
  padic.valuation_zero

@[simp] theorem valuation_one {p : ℕ} [hp_prime : fact (nat.prime p)] : valuation 1 = 0 :=
  padic.valuation_one

@[simp] theorem valuation_p {p : ℕ} [hp_prime : fact (nat.prime p)] : valuation ↑p = 1 := sorry

theorem valuation_nonneg {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) : 0 ≤ valuation x := sorry

@[simp] theorem valuation_p_pow_mul {p : ℕ} [hp_prime : fact (nat.prime p)] (n : ℕ) (c : padic_int p) (hc : c ≠ 0) : valuation (↑p ^ n * c) = ↑n + valuation c := sorry

/-! ### Units of `ℤ_[p]` -/

theorem mul_inv {p : ℕ} [hp_prime : fact (nat.prime p)] {z : padic_int p} : norm z = 1 → z * inv z = 1 := sorry

theorem inv_mul {p : ℕ} [hp_prime : fact (nat.prime p)] {z : padic_int p} (hz : norm z = 1) : inv z * z = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (inv z * z = 1)) (mul_comm (inv z) z)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (z * inv z = 1)) (mul_inv hz))) (Eq.refl 1))

theorem is_unit_iff {p : ℕ} [hp_prime : fact (nat.prime p)] {z : padic_int p} : is_unit z ↔ norm z = 1 := sorry

theorem norm_lt_one_add {p : ℕ} [hp_prime : fact (nat.prime p)] {z1 : padic_int p} {z2 : padic_int p} (hz1 : norm z1 < 1) (hz2 : norm z2 < 1) : norm (z1 + z2) < 1 :=
  lt_of_le_of_lt (nonarchimedean z1 z2) (max_lt hz1 hz2)

theorem norm_lt_one_mul {p : ℕ} [hp_prime : fact (nat.prime p)] {z1 : padic_int p} {z2 : padic_int p} (hz2 : norm z2 < 1) : norm (z1 * z2) < 1 := sorry

@[simp] theorem mem_nonunits {p : ℕ} [hp_prime : fact (nat.prime p)] {z : padic_int p} : z ∈ nonunits (padic_int p) ↔ norm z < 1 := sorry

/-- A `p`-adic number `u` with `∥u∥ = 1` is a unit of `ℤ_[p]`. -/
def mk_units {p : ℕ} [hp_prime : fact (nat.prime p)] {u : padic p} (h : norm u = 1) : units (padic_int p) :=
  let z : padic_int p := { val := u, property := sorry };
  units.mk z (inv z) (mul_inv h) (inv_mul h)

@[simp] theorem mk_units_eq {p : ℕ} [hp_prime : fact (nat.prime p)] {u : padic p} (h : norm u = 1) : ↑↑(mk_units h) = u :=
  rfl

@[simp] theorem norm_units {p : ℕ} [hp_prime : fact (nat.prime p)] (u : units (padic_int p)) : norm ↑u = 1 :=
  iff.mp is_unit_iff (eq.mpr (id (propext ((fun {M : Type} (u : units M) => iff_true_intro (is_unit_unit u)) u))) trivial)

/-- `unit_coeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unit_coeff_spec`. -/
def unit_coeff {p : ℕ} [hp_prime : fact (nat.prime p)] {x : padic_int p} (hx : x ≠ 0) : units (padic_int p) :=
  let u : padic p := ↑x * ↑p ^ (-valuation x);
  (fun (hu : norm u = 1) => mk_units hu) sorry

@[simp] theorem unit_coeff_coe {p : ℕ} [hp_prime : fact (nat.prime p)] {x : padic_int p} (hx : x ≠ 0) : ↑(unit_coeff hx) = ↑x * ↑p ^ (-valuation x) :=
  rfl

theorem unit_coeff_spec {p : ℕ} [hp_prime : fact (nat.prime p)] {x : padic_int p} (hx : x ≠ 0) : x = ↑(unit_coeff hx) * ↑p ^ int.nat_abs (valuation x) := sorry

/-! ### Various characterizations of open unit balls -/

theorem norm_le_pow_iff_le_valuation {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) (hx : x ≠ 0) (n : ℕ) : norm x ≤ ↑p ^ (-↑n) ↔ ↑n ≤ valuation x := sorry

theorem mem_span_pow_iff_le_valuation {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) (hx : x ≠ 0) (n : ℕ) : x ∈ ideal.span (singleton (↑p ^ n)) ↔ ↑n ≤ valuation x := sorry

theorem norm_le_pow_iff_mem_span_pow {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) (n : ℕ) : norm x ≤ ↑p ^ (-↑n) ↔ x ∈ ideal.span (singleton (↑p ^ n)) := sorry

theorem norm_le_pow_iff_norm_lt_pow_add_one {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) (n : ℤ) : norm x ≤ ↑p ^ n ↔ norm x < ↑p ^ (n + 1) := sorry

theorem norm_lt_pow_iff_norm_le_pow_sub_one {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) (n : ℤ) : norm x < ↑p ^ n ↔ norm x ≤ ↑p ^ (n - 1) := sorry

theorem norm_lt_one_iff_dvd {p : ℕ} [hp_prime : fact (nat.prime p)] (x : padic_int p) : norm x < 1 ↔ ↑p ∣ x := sorry

@[simp] theorem pow_p_dvd_int_iff {p : ℕ} [hp_prime : fact (nat.prime p)] (n : ℕ) (a : ℤ) : ↑p ^ n ∣ ↑a ↔ ↑p ^ n ∣ a := sorry

/-! ### Discrete valuation ring -/

protected instance local_ring {p : ℕ} [hp_prime : fact (nat.prime p)] : local_ring (padic_int p) :=
  local_of_nonunits_ideal zero_ne_one
    fun (x y : padic_int p) =>
      eq.mpr (id (imp_congr_eq (propext mem_nonunits) (imp_congr_eq (propext mem_nonunits) (propext mem_nonunits))))
        norm_lt_one_add

theorem p_nonnunit {p : ℕ} [hp_prime : fact (nat.prime p)] : ↑p ∈ nonunits (padic_int p) := sorry

theorem maximal_ideal_eq_span_p {p : ℕ} [hp_prime : fact (nat.prime p)] : local_ring.maximal_ideal (padic_int p) = ideal.span (singleton ↑p) := sorry

theorem prime_p {p : ℕ} [hp_prime : fact (nat.prime p)] : prime ↑p := sorry

theorem irreducible_p {p : ℕ} [hp_prime : fact (nat.prime p)] : irreducible ↑p :=
  irreducible_of_prime prime_p

protected instance discrete_valuation_ring {p : ℕ} [hp_prime : fact (nat.prime p)] : discrete_valuation_ring (padic_int p) :=
  discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization
    (Exists.intro ↑p
      { left := irreducible_p,
        right :=
          fun (x : padic_int p) (hx : x ≠ 0) =>
            Exists.intro (int.nat_abs (valuation x))
              (Exists.intro (unit_coeff hx)
                (eq.mpr
                  (id
                    (Eq._oldrec (Eq.refl (↑p ^ int.nat_abs (valuation x) * ↑(unit_coeff hx) = x))
                      (mul_comm (↑p ^ int.nat_abs (valuation x)) ↑(unit_coeff hx))))
                  (eq.mpr
                    (id
                      (Eq._oldrec (Eq.refl (↑(unit_coeff hx) * ↑p ^ int.nat_abs (valuation x) = x))
                        (Eq.symm (unit_coeff_spec hx))))
                    (Eq.refl x)))) })

theorem ideal_eq_span_pow_p {p : ℕ} [hp_prime : fact (nat.prime p)] {s : ideal (padic_int p)} (hs : s ≠ ⊥) : ∃ (n : ℕ), s = ideal.span (singleton (↑p ^ n)) :=
  discrete_valuation_ring.ideal_eq_span_pow_irreducible hs irreducible_p

