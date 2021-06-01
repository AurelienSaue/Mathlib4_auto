/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.modeq
import Mathlib.data.zmod.basic
import Mathlib.linear_algebra.adic_completion
import Mathlib.data.padics.padic_numbers
import Mathlib.ring_theory.discrete_valuation_ring
import Mathlib.topology.metric_space.cau_seq_filter
import Mathlib.PostPort

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
def padic_int (p : ℕ) [fact (nat.prime p)] := Subtype fun (x : padic p) => norm x ≤ 1

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

@[simp] theorem mk_zero {p : ℕ} [fact (nat.prime p)] {h : norm 0 ≤ 1} :
    { val := 0, property := h } = 0 :=
  rfl

@[simp] theorem val_eq_coe {p : ℕ} [fact (nat.prime p)] (z : padic_int p) : subtype.val z = ↑z :=
  rfl

@[simp] theorem coe_add {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) :
    ↑(z1 + z2) = ↑z1 + ↑z2 :=
  sorry

@[simp] theorem coe_mul {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) :
    ↑(z1 * z2) = ↑z1 * ↑z2 :=
  sorry

@[simp] theorem coe_neg {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) : ↑(-z1) = -↑z1 :=
  subtype.cases_on z1
    fun (z1_val : padic p) (z1_property : norm z1_val ≤ 1) =>
      idRhs
        (↑(-{ val := z1_val, property := z1_property }) =
          ↑(-{ val := z1_val, property := z1_property }))
        rfl

@[simp] theorem coe_sub {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) :
    ↑(z1 - z2) = ↑z1 - ↑z2 :=
  sorry

@[simp] theorem coe_one {p : ℕ} [fact (nat.prime p)] : ↑1 = 1 := rfl

@[simp] theorem coe_coe {p : ℕ} [fact (nat.prime p)] (n : ℕ) : ↑↑n = ↑n := sorry

@[simp] theorem coe_coe_int {p : ℕ} [fact (nat.prime p)] (z : ℤ) : ↑↑z = ↑z := sorry

@[simp] theorem coe_zero {p : ℕ} [fact (nat.prime p)] : ↑0 = 0 := rfl

protected instance ring {p : ℕ} [fact (nat.prime p)] : ring (padic_int p) :=
  ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry
    sorry

/-- The coercion from ℤ[p] to ℚ[p] as a ring homomorphism. -/
def coe.ring_hom {p : ℕ} [fact (nat.prime p)] : padic_int p →+* padic p :=
  ring_hom.mk coe sorry coe_mul sorry coe_add

@[simp] theorem coe_pow {p : ℕ} [fact (nat.prime p)] (x : padic_int p) (n : ℕ) :
    ↑(x ^ n) = ↑x ^ n :=
  ring_hom.map_pow coe.ring_hom x n

@[simp] theorem mk_coe {p : ℕ} [fact (nat.prime p)] (k : padic_int p) :
    { val := ↑k, property := subtype.property k } = k :=
  sorry

/-- The inverse of a p-adic integer with norm equal to 1 is also a p-adic integer. Otherwise, the
inverse is defined to be 0. -/
def inv {p : ℕ} [fact (nat.prime p)] : padic_int p → padic_int p := sorry

protected instance char_zero {p : ℕ} [fact (nat.prime p)] : char_zero (padic_int p) :=
  char_zero.mk
    fun (m n : ℕ) (h : ↑m = ↑n) =>
      nat.cast_injective
        ((fun (this : ↑m = ↑n) => this)
          (eq.mp
            ((fun (a a_1 : padic p) (e_1 : a = a_1) (ᾰ ᾰ_1 : padic p) (e_2 : ᾰ = ᾰ_1) =>
                congr (congr_arg Eq e_1) e_2)
              (↑↑m) (↑m) (coe_coe m) (↑↑n) (↑n) (coe_coe n))
            (eq.mp (Eq._oldrec (Eq.refl (↑m = ↑n)) (propext subtype.ext_iff)) h)))

@[simp] theorem coe_int_eq {p : ℕ} [fact (nat.prime p)] (z1 : ℤ) (z2 : ℤ) : ↑z1 = ↑z2 ↔ z1 = z2 :=
  sorry

/--
A sequence of integers that is Cauchy with respect to the `p`-adic norm
converges to a `p`-adic integer.
-/
def of_int_seq {p : ℕ} [fact (nat.prime p)] (seq : ℕ → ℤ)
    (h : is_cau_seq (padic_norm p) fun (n : ℕ) => ↑(seq n)) : padic_int p :=
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

protected instance complete_space (p : ℕ) [fact (nat.prime p)] : complete_space (padic_int p) :=
  sorry

protected instance has_norm (p : ℕ) [fact (nat.prime p)] : has_norm (padic_int p) :=
  has_norm.mk fun (z : padic_int p) => norm ↑z

protected theorem mul_comm {p : ℕ} [fact (nat.prime p)] (z1 : padic_int p) (z2 : padic_int p) :
    z1 * z2 = z2 * z1 :=
  sorry

protected theorem zero_ne_one {p : ℕ} [fact (nat.prime p)] : 0 ≠ 1 :=
  (fun
      (this :
      { val := 0, property := has_zero._proof_1 } ≠ { val := 1, property := has_one._proof_1 }) =>
      this)
    (mt (iff.mp subtype.ext_iff_val) zero_ne_one)

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {p : ℕ} [fact (nat.prime p)] (a : padic_int p)
    (b : padic_int p) : a * b = 0 → a = 0 ∨ b = 0 :=
  sorry

theorem norm_def {p : ℕ} [fact (nat.prime p)] {z : padic_int p} : norm z = norm ↑z := rfl

protected instance normed_comm_ring (p : ℕ) [fact (nat.prime p)] : normed_comm_ring (padic_int p) :=
  normed_comm_ring.mk padic_int.mul_comm

protected instance norm_one_class (p : ℕ) [fact (nat.prime p)] : norm_one_class (padic_int p) :=
  norm_one_class.mk (Eq.trans norm_def norm_one)

protected instance is_absolute_value (p : ℕ) [fact (nat.prime p)] :
    is_absolute_value fun (z : padic_int p) => norm z :=
  is_absolute_value.mk norm_nonneg (fun (_x : padic_int p) => sorry)
    (fun (_x : padic_int p) => sorry)
    fun (_x _x_1 : padic_int p) =>
      eq.mpr
        (id
          ((fun (a a_1 : ℝ) (e_1 : a = a_1) (ᾰ ᾰ_1