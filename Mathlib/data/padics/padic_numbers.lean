/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.padics.padic_norm
import Mathlib.analysis.normed_space.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# p-adic numbers

This file defines the p-adic numbers (rationals) `ℚ_p` as the completion of `ℚ` with respect to the
p-adic norm. We show that the p-adic norm on ℚ extends to `ℚ_p`, that `ℚ` is embedded in `ℚ_p`, and that
`ℚ_p` is Cauchy complete.

## Important definitions

* `padic` : the type of p-adic numbers
* `padic_norm_e` : the rational valued p-adic norm on `ℚ_p`

## Notation

We introduce the notation `ℚ_[p]` for the p-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct ℝ. `ℚ_p` inherits a
field structure from this construction. The extension of the norm on ℚ to `ℚ_p` is *not* analogous to
extending the absolute value to ℝ, and hence the proof that `ℚ_p` is complete is different from the
proof that ℝ is complete.

A small special-purpose simplification tactic, `padic_index_simp`, is used to manipulate sequence
indices in the proof that the norm extends.

`padic_norm_e` is the rational-valued p-adic norm on `ℚ_p`. To instantiate `ℚ_p` as a normed field,
we must cast this into a ℝ-valued norm. The `ℝ`-valued norm, using notation `∥ ∥` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padic_norm` to `padic_norm_e` when possible.
Since `padic_norm_e` and `∥ ∥` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_p` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

/-- The type of Cauchy sequences of rationals with respect to the p-adic norm. -/
def padic_seq (p : ℕ)  :=
  cau_seq ℚ (padic_norm p)

namespace padic_seq


/-- The p-adic norm of the entries of a nonzero Cauchy sequence of rationals is eventually
constant. -/
theorem stationary {p : ℕ} [fact (nat.prime p)] {f : cau_seq ℚ (padic_norm p)} (hf : ¬f ≈ 0) : ∃ (N : ℕ), ∀ (m n : ℕ), N ≤ m → N ≤ n → padic_norm p (coe_fn f n) = padic_norm p (coe_fn f m) := sorry

/-- For all n ≥ stationary_point f hf, the p-adic norm of f n is the same. -/
def stationary_point {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) : ℕ :=
  classical.some (stationary hf)

theorem stationary_point_spec {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) {m : ℕ} {n : ℕ} : stationary_point hf ≤ m → stationary_point hf ≤ n → padic_norm p (coe_fn f n) = padic_norm p (coe_fn f m) :=
  classical.some_spec (stationary hf)

/-- Since the norm of the entries of a Cauchy sequence is eventually stationary, we can lift the norm
to sequences. -/
def norm {p : ℕ} [fact (nat.prime p)] (f : padic_seq p) : ℚ :=
  dite (f ≈ 0) (fun (hf : f ≈ 0) => 0) fun (hf : ¬f ≈ 0) => padic_norm p (coe_fn f (stationary_point hf))

theorem norm_zero_iff {p : ℕ} [fact (nat.prime p)] (f : padic_seq p) : norm f = 0 ↔ f ≈ 0 := sorry

theorem equiv_zero_of_val_eq_of_equiv_zero {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} (h : ∀ (k : ℕ), padic_norm p (coe_fn f k) = padic_norm p (coe_fn g k)) (hf : f ≈ 0) : g ≈ 0 := sorry

theorem norm_nonzero_of_not_equiv_zero {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) : norm f ≠ 0 :=
  hf ∘ iff.mp (norm_zero_iff f)

theorem norm_eq_norm_app_of_nonzero {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) : ∃ (k : ℚ), norm f = padic_norm p k ∧ k ≠ 0 := sorry

theorem not_lim_zero_const_of_nonzero {p : ℕ} [fact (nat.prime p)] {q : ℚ} (hq : q ≠ 0) : ¬cau_seq.lim_zero (cau_seq.const (padic_norm p) q) :=
  fun (h' : cau_seq.lim_zero (cau_seq.const (padic_norm p) q)) => hq (iff.mp cau_seq.const_lim_zero h')

theorem not_equiv_zero_const_of_nonzero {p : ℕ} [fact (nat.prime p)] {q : ℚ} (hq : q ≠ 0) : ¬cau_seq.const (padic_norm p) q ≈ 0 := sorry

theorem norm_nonneg {p : ℕ} [fact (nat.prime p)] (f : padic_seq p) : 0 ≤ norm f := sorry

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_left_left {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) (v2 : ℕ) (v3 : ℕ) : padic_norm p (coe_fn f (stationary_point hf)) = padic_norm p (coe_fn f (max (stationary_point hf) (max v2 v3))) :=
  stationary_point_spec hf (le_max_left (stationary_point hf) (max v2 v3)) (le_refl (stationary_point hf))

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_left {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) (v1 : ℕ) (v3 : ℕ) : padic_norm p (coe_fn f (stationary_point hf)) = padic_norm p (coe_fn f (max v1 (max (stationary_point hf) v3))) :=
  stationary_point_spec hf
    (le_trans (le_max_left (stationary_point hf) v3) (le_max_right v1 (max (stationary_point hf) v3)))
    (le_refl (stationary_point hf))

/-- An auxiliary lemma for manipulating sequence indices. -/
theorem lift_index_right {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) (v1 : ℕ) (v2 : ℕ) : padic_norm p (coe_fn f (stationary_point hf)) = padic_norm p (coe_fn f (max v1 (max v2 (stationary_point hf)))) :=
  stationary_point_spec hf
    (le_trans (le_max_right v2 (stationary_point hf)) (le_max_right v1 (max v2 (stationary_point hf))))
    (le_refl (stationary_point hf))

/-! ### Valuation on `padic_seq` -/

/--
The `p`-adic valuation on `ℚ` lifts to `padic_seq p`.
`valuation f` is defined to be the valuation of the (`ℚ`-valued) stationary point of `f`.
-/
def valuation {p : ℕ} [fact (nat.prime p)] (f : padic_seq p) : ℤ :=
  dite (f ≈ 0) (fun (hf : f ≈ 0) => 0) fun (hf : ¬f ≈ 0) => padic_val_rat p (coe_fn f (stationary_point hf))

theorem norm_eq_pow_val {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} (hf : ¬f ≈ 0) : norm f = ↑p ^ (-valuation f) := sorry

theorem val_eq_iff_norm_eq {p : ℕ} [fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : valuation f = valuation g ↔ norm f = norm g := sorry

end padic_seq


/--
  This is a special-purpose tactic that lifts padic_norm (f (stationary_point f)) to
  padic_norm (f (max _ _ _)).
-/
namespace padic_seq


theorem norm_mul {p : ℕ} [hp : fact (nat.prime p)] (f : padic_seq p) (g : padic_seq p) : norm (f * g) = norm f * norm g := sorry

theorem eq_zero_iff_equiv_zero {p : ℕ} [hp : fact (nat.prime p)] (f : padic_seq p) : cau_seq.completion.mk f = 0 ↔ f ≈ 0 :=
  cau_seq.completion.mk_eq

theorem ne_zero_iff_nequiv_zero {p : ℕ} [hp : fact (nat.prime p)] (f : padic_seq p) : cau_seq.completion.mk f ≠ 0 ↔ ¬f ≈ 0 :=
  iff.mpr not_iff_not (eq_zero_iff_equiv_zero f)

theorem norm_const {p : ℕ} [hp : fact (nat.prime p)] (q : ℚ) : norm (cau_seq.const (padic_norm p) q) = padic_norm p q := sorry

theorem norm_values_discrete {p : ℕ} [hp : fact (nat.prime p)] (a : padic_seq p) (ha : ¬a ≈ 0) : ∃ (z : ℤ), norm a = ↑p ^ (-z) := sorry

theorem norm_one {p : ℕ} [hp : fact (nat.prime p)] : norm 1 = 1 := sorry

theorem norm_equiv {p : ℕ} [hp : fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} (hfg : f ≈ g) : norm f = norm g := sorry

theorem norm_nonarchimedean {p : ℕ} [hp : fact (nat.prime p)] (f : padic_seq p) (g : padic_seq p) : norm (f + g) ≤ max (norm f) (norm g) := sorry

theorem norm_eq {p : ℕ} [hp : fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} (h : ∀ (k : ℕ), padic_norm p (coe_fn f k) = padic_norm p (coe_fn g k)) : norm f = norm g := sorry

theorem norm_neg {p : ℕ} [hp : fact (nat.prime p)] (a : padic_seq p) : norm (-a) = norm a := sorry

theorem norm_eq_of_add_equiv_zero {p : ℕ} [hp : fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} (h : f + g ≈ 0) : norm f = norm g := sorry

theorem add_eq_max_of_ne {p : ℕ} [hp : fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} (hfgne : norm f ≠ norm g) : norm (f + g) = max (norm f) (norm g) := sorry

end padic_seq


/-- The p-adic numbers `Q_[p]` are the Cauchy completion of `ℚ` with respect to the p-adic norm. -/
def padic (p : ℕ) [fact (nat.prime p)]  :=
  cau_seq.completion.Cauchy

namespace padic


/-- The discrete field structure on `ℚ_p` is inherited from the Cauchy completion construction. -/
protected instance field {p : ℕ} [fact (nat.prime p)] : field (padic p) :=
  cau_seq.completion.field

protected instance inhabited {p : ℕ} [fact (nat.prime p)] : Inhabited (padic p) :=
  { default := 0 }

-- short circuits

protected instance has_zero {p : ℕ} [fact (nat.prime p)] : HasZero (padic p) :=
  mul_zero_class.to_has_zero (padic p)

protected instance has_one {p : ℕ} [fact (nat.prime p)] : HasOne (padic p) :=
  monoid.to_has_one (padic p)

protected instance has_add {p : ℕ} [fact (nat.prime p)] : Add (padic p) :=
  distrib.to_has_add (padic p)

protected instance has_mul {p : ℕ} [fact (nat.prime p)] : Mul (padic p) :=
  distrib.to_has_mul (padic p)

protected instance has_sub {p : ℕ} [fact (nat.prime p)] : Sub (padic p) :=
  sub_neg_monoid.to_has_sub (padic p)

protected instance has_neg {p : ℕ} [fact (nat.prime p)] : Neg (padic p) :=
  sub_neg_monoid.to_has_neg (padic p)

protected instance has_div {p : ℕ} [fact (nat.prime p)] : Div (padic p) :=
  div_inv_monoid.to_has_div (padic p)

protected instance add_comm_group {p : ℕ} [fact (nat.prime p)] : add_comm_group (padic p) :=
  ring.to_add_comm_group (padic p)

protected instance comm_ring {p : ℕ} [fact (nat.prime p)] : comm_ring (padic p) :=
  euclidean_domain.to_comm_ring (padic p)

/-- Builds the equivalence class of a Cauchy sequence of rationals. -/
def mk {p : ℕ} [fact (nat.prime p)] : padic_seq p → padic p :=
  quotient.mk

theorem mk_eq (p : ℕ) [fact (nat.prime p)] {f : padic_seq p} {g : padic_seq p} : mk f = mk g ↔ f ≈ g :=
  quotient.eq

/-- Embeds the rational numbers in the p-adic numbers. -/
def of_rat (p : ℕ) [fact (nat.prime p)] : ℚ → padic p :=
  cau_seq.completion.of_rat

@[simp] theorem of_rat_add (p : ℕ) [fact (nat.prime p)] (x : ℚ) (y : ℚ) : of_rat p (x + y) = of_rat p x + of_rat p y :=
  cau_seq.completion.of_rat_add

@[simp] theorem of_rat_neg (p : ℕ) [fact (nat.prime p)] (x : ℚ) : of_rat p (-x) = -of_rat p x :=
  cau_seq.completion.of_rat_neg

@[simp] theorem of_rat_mul (p : ℕ) [fact (nat.prime p)] (x : ℚ) (y : ℚ) : of_rat p (x * y) = of_rat p x * of_rat p y :=
  cau_seq.completion.of_rat_mul

@[simp] theorem of_rat_sub (p : ℕ) [fact (nat.prime p)] (x : ℚ) (y : ℚ) : of_rat p (x - y) = of_rat p x - of_rat p y :=
  cau_seq.completion.of_rat_sub

@[simp] theorem of_rat_div (p : ℕ) [fact (nat.prime p)] (x : ℚ) (y : ℚ) : of_rat p (x / y) = of_rat p x / of_rat p y :=
  cau_seq.completion.of_rat_div

@[simp] theorem of_rat_one (p : ℕ) [fact (nat.prime p)] : of_rat p 1 = 1 :=
  rfl

@[simp] theorem of_rat_zero (p : ℕ) [fact (nat.prime p)] : of_rat p 0 = 0 :=
  rfl

theorem cast_eq_of_rat_of_nat (p : ℕ) [fact (nat.prime p)] (n : ℕ) : ↑n = of_rat p ↑n := sorry

theorem cast_eq_of_rat_of_int (p : ℕ) [fact (nat.prime p)] (n : ℤ) : ↑n = of_rat p ↑n := sorry

theorem cast_eq_of_rat (p : ℕ) [fact (nat.prime p)] (q : ℚ) : ↑q = of_rat p q := sorry

theorem coe_add (p : ℕ) [fact (nat.prime p)] {x : ℚ} {y : ℚ} : ↑(x + y) = ↑x + ↑y := sorry

theorem coe_neg (p : ℕ) [fact (nat.prime p)] {x : ℚ} : ↑(-x) = -↑x := sorry

theorem coe_mul (p : ℕ) [fact (nat.prime p)] {x : ℚ} {y : ℚ} : ↑(x * y) = ↑x * ↑y := sorry

theorem coe_sub (p : ℕ) [fact (nat.prime p)] {x : ℚ} {y : ℚ} : ↑(x - y) = ↑x - ↑y := sorry

theorem coe_div (p : ℕ) [fact (nat.prime p)] {x : ℚ} {y : ℚ} : ↑(x / y) = ↑x / ↑y := sorry

theorem coe_one (p : ℕ) [fact (nat.prime p)] : ↑1 = 1 :=
  rfl

theorem coe_zero (p : ℕ) [fact (nat.prime p)] : ↑0 = 0 :=
  rfl

theorem const_equiv (p : ℕ) [fact (nat.prime p)] {q : ℚ} {r : ℚ} : cau_seq.const (padic_norm p) q ≈ cau_seq.const (padic_norm p) r ↔ q = r := sorry

theorem of_rat_eq (p : ℕ) [fact (nat.prime p)] {q : ℚ} {r : ℚ} : of_rat p q = of_rat p r ↔ q = r :=
  { mp := iff.mp (const_equiv p) ∘ iff.mp quotient.eq,
    mpr := fun (h : q = r) => eq.mpr (id (Eq._oldrec (Eq.refl (of_rat p q = of_rat p r)) h)) (Eq.refl (of_rat p r)) }

theorem coe_inj (p : ℕ) [fact (nat.prime p)] {q : ℚ} {r : ℚ} : ↑q = ↑r ↔ q = r := sorry

protected instance char_zero (p : ℕ) [fact (nat.prime p)] : char_zero (padic p) :=
  char_zero.mk
    fun (m n : ℕ) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (↑m = ↑n → m = n)) (Eq.symm (rat.cast_coe_nat m))))
        (eq.mpr
          (id
            (imp_congr_eq
              (Eq.trans (Eq.trans (congr_arg (Eq ↑↑m) (Eq.symm (rat.cast_coe_nat n))) (propext (coe_inj p)))
                (propext nat.cast_inj))
              (Eq.refl (m = n))))
          id)

end padic


/-- The rational-valued p-adic norm on `ℚ_p` is lifted from the norm on Cauchy sequences. The
canonical form of this function is the normed space instance, with notation `∥ ∥`. -/
def padic_norm_e {p : ℕ} [hp : fact (nat.prime p)] : padic p → ℚ :=
  quotient.lift padic_seq.norm padic_seq.norm_equiv

namespace padic_norm_e


theorem defn {p : ℕ} [fact (nat.prime p)] (f : padic_seq p) {ε : ℚ} (hε : 0 < ε) : ∃ (N : ℕ), ∀ (i : ℕ), i ≥ N → padic_norm_e (quotient.mk f - ↑(coe_fn f i)) < ε := sorry

protected theorem nonneg {p : ℕ} [fact (nat.prime p)] (q : padic p) : 0 ≤ padic_norm_e q :=
  quotient.induction_on q padic_seq.norm_nonneg

theorem zero_def {p : ℕ} [fact (nat.prime p)] : 0 = quotient.mk 0 :=
  rfl

theorem zero_iff {p : ℕ} [fact (nat.prime p)] (q : padic p) : padic_norm_e q = 0 ↔ q = 0 := sorry

@[simp] protected theorem zero {p : ℕ} [fact (nat.prime p)] : padic_norm_e 0 = 0 :=
  iff.mpr (zero_iff 0) rfl

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
@[simp] protected theorem one' {p : ℕ} [fact (nat.prime p)] : padic_norm_e 1 = 1 :=
  padic_seq.norm_one

@[simp] protected theorem neg {p : ℕ} [fact (nat.prime p)] (q : padic p) : padic_norm_e (-q) = padic_norm_e q :=
  quotient.induction_on q padic_seq.norm_neg

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
theorem nonarchimedean' {p : ℕ} [fact (nat.prime p)] (q : padic p) (r : padic p) : padic_norm_e (q + r) ≤ max (padic_norm_e q) (padic_norm_e r) :=
  quotient.induction_on₂ q r padic_seq.norm_nonarchimedean

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
theorem add_eq_max_of_ne' {p : ℕ} [fact (nat.prime p)] {q : padic p} {r : padic p} : padic_norm_e q ≠ padic_norm_e r → padic_norm_e (q + r) = max (padic_norm_e q) (padic_norm_e r) :=
  quotient.induction_on₂ q r fun (_x _x_1 : cau_seq ℚ (padic_norm p)) => padic_seq.add_eq_max_of_ne

theorem triangle_ineq {p : ℕ} [fact (nat.prime p)] (x : padic p) (y : padic p) (z : padic p) : padic_norm_e (x - z) ≤ padic_norm_e (x - y) + padic_norm_e (y - z) := sorry

protected theorem add {p : ℕ} [fact (nat.prime p)] (q : padic p) (r : padic p) : padic_norm_e (q + r) ≤ padic_norm_e q + padic_norm_e r :=
  le_trans (nonarchimedean' q r) (max_le_add_of_nonneg (padic_norm_e.nonneg q) (padic_norm_e.nonneg r))

protected theorem mul' {p : ℕ} [fact (nat.prime p)] (q : padic p) (r : padic p) : padic_norm_e (q * r) = padic_norm_e q * padic_norm_e r :=
  quotient.induction_on₂ q r padic_seq.norm_mul

protected instance is_absolute_value {p : ℕ} [fact (nat.prime p)] : is_absolute_value padic_norm_e :=
  is_absolute_value.mk padic_norm_e.nonneg zero_iff padic_norm_e.add padic_norm_e.mul'

@[simp] theorem eq_padic_norm' {p : ℕ} [fact (nat.prime p)] (q : ℚ) : padic_norm_e (padic.of_rat p q) = padic_norm p q :=
  padic_seq.norm_const q

protected theorem image' {p : ℕ} [fact (nat.prime p)] {q : padic p} : q ≠ 0 → ∃ (n : ℤ), padic_norm_e q = ↑p ^ (-n) :=
  quotient.induction_on q
    fun (f : cau_seq ℚ (padic_norm p)) (hf : quotient.mk f ≠ 0) =>
      (fun (this : ¬f ≈ 0) => padic_seq.norm_values_discrete f this) (iff.mp (padic_seq.ne_zero_iff_nequiv_zero f) hf)

theorem sub_rev {p : ℕ} [fact (nat.prime p)] (q : padic p) (r : padic p) : padic_norm_e (q - r) = padic_norm_e (r - q) := sorry

end padic_norm_e


namespace padic


theorem rat_dense' {p : ℕ} [fact (nat.prime p)] (q : padic p) {ε : ℚ} (hε : 0 < ε) : ∃ (r : ℚ), padic_norm_e (q - ↑r) < ε := sorry

/-- `lim_seq f`, for `f` a Cauchy sequence of `p`-adic numbers,
is a sequence of rationals with the same limit point as `f`. -/
def lim_seq {p : ℕ} [fact (nat.prime p)] (f : cau_seq (padic p) padic_norm_e) : ℕ → ℚ :=
  fun (n : ℕ) => classical.some sorry

theorem exi_rat_seq_conv {p : ℕ} [fact (nat.prime p)] (f : cau_seq (padic p) padic_norm_e) {ε : ℚ} (hε : 0 < ε) : ∃ (N : ℕ), ∀ (i : ℕ), i ≥ N → padic_norm_e (coe_fn f i - ↑(lim_seq f i)) < ε := sorry

theorem exi_rat_seq_conv_cauchy {p : ℕ} [fact (nat.prime p)] (f : cau_seq (padic p) padic_norm_e) : is_cau_seq (padic_norm p) (lim_seq f) := sorry

theorem complete' {p : ℕ} [fact (nat.prime p)] (f : cau_seq (padic p) padic_norm_e) : ∃ (q : padic p), ∀ (ε : ℚ), ε > 0 → ∃ (N : ℕ), ∀ (i : ℕ), i ≥ N → padic_norm_e (q - coe_fn f i) < ε := sorry

protected instance has_dist (p : ℕ) [fact (nat.prime p)] : has_dist (padic p) :=
  has_dist.mk fun (x y : padic p) => ↑(padic_norm_e (x - y))

protected instance metric_space (p : ℕ) [fact (nat.prime p)] : metric_space (padic p) :=
  metric_space.mk sorry sorry sorry sorry
    (fun (x y : padic p) => ennreal.of_real ((fun (x y : padic p) => ↑(padic_norm_e (x - y))) x y))
    (uniform_space_of_dist (fun (x y : padic p) => ↑(padic_norm_e (x - y))) sorry sorry sorry)

protected instance has_norm (p : ℕ) [fact (nat.prime p)] : has_norm (padic p) :=
  has_norm.mk fun (x : padic p) => ↑(padic_norm_e x)

protected instance normed_field (p : ℕ) [fact (nat.prime p)] : normed_field (padic p) :=
  normed_field.mk sorry sorry

protected instance is_absolute_value (p : ℕ) [fact (nat.prime p)] : is_absolute_value fun (a : padic p) => norm a := sorry

theorem rat_dense {p : ℕ} {hp : fact (nat.prime p)} (q : padic p) {ε : ℝ} (hε : 0 < ε) : ∃ (r : ℚ), norm (q - ↑r) < ε := sorry

end padic


namespace padic_norm_e


@[simp] protected theorem mul {p : ℕ} [hp : fact (nat.prime p)] (q : padic p) (r : padic p) : norm (q * r) = norm q * norm r := sorry

protected theorem is_norm {p : ℕ} [hp : fact (nat.prime p)] (q : padic p) : ↑(padic_norm_e q) = norm q :=
  rfl

theorem nonarchimedean {p : ℕ} [hp : fact (nat.prime p)] (q : padic p) (r : padic p) : norm (q + r) ≤ max (norm q) (norm r) := sorry

theorem add_eq_max_of_ne {p : ℕ} [hp : fact (nat.prime p)] {q : padic p} {r : padic p} (h : norm q ≠ norm r) : norm (q + r) = max (norm q) (norm r) := sorry

@[simp] theorem eq_padic_norm {p : ℕ} [hp : fact (nat.prime p)] (q : ℚ) : norm ↑q = ↑(padic_norm p q) := sorry

protected instance padic.nondiscrete_normed_field {p : ℕ} [hp : fact (nat.prime p)] : nondiscrete_normed_field (padic p) :=
  nondiscrete_normed_field.mk sorry

@[simp] theorem norm_p {p : ℕ} [hp : fact (nat.prime p)] : norm ↑p = (↑p⁻¹) := sorry

theorem norm_p_lt_one {p : ℕ} [hp : fact (nat.prime p)] : norm ↑p < 1 := sorry

@[simp] theorem norm_p_pow {p : ℕ} [hp : fact (nat.prime p)] (n : ℤ) : norm (↑p ^ n) = ↑p ^ (-n) := sorry

protected theorem image {p : ℕ} [hp : fact (nat.prime p)] {q : padic p} : q ≠ 0 → ∃ (n : ℤ), norm q = ↑(↑p ^ (-n)) := sorry

protected theorem is_rat {p : ℕ} [hp : fact (nat.prime p)] (q : padic p) : ∃ (q' : ℚ), norm q = ↑q' := sorry

/--`rat_norm q`, for a `p`-adic number `q` is the `p`-adic norm of `q`, as rational number.

The lemma `padic_norm_e.eq_rat_norm` asserts `∥q∥ = rat_norm q`. -/
def rat_norm {p : ℕ} [hp : fact (nat.prime p)] (q : padic p) : ℚ :=
  classical.some (padic_norm_e.is_rat q)

theorem eq_rat_norm {p : ℕ} [hp : fact (nat.prime p)] (q : padic p) : norm q = ↑(rat_norm q) :=
  classical.some_spec (padic_norm_e.is_rat q)

theorem norm_rat_le_one {p : ℕ} [hp : fact (nat.prime p)] {q : ℚ} (hq : ¬p ∣ rat.denom q) : norm ↑q ≤ 1 := sorry

theorem norm_int_le_one {p : ℕ} [hp : fact (nat.prime p)] (z : ℤ) : norm ↑z ≤ 1 := sorry

theorem norm_int_lt_one_iff_dvd {p : ℕ} [hp : fact (nat.prime p)] (k : ℤ) : norm ↑k < 1 ↔ ↑p ∣ k := sorry

theorem norm_int_le_pow_iff_dvd {p : ℕ} [hp : fact (nat.prime p)] (k : ℤ) (n : ℕ) : norm ↑k ≤ ↑p ^ (-↑n) ↔ ↑(p ^ n) ∣ k := sorry

theorem eq_of_norm_add_lt_right {p : ℕ} {hp : fact (nat.prime p)} {z1 : padic p} {z2 : padic p} (h : norm (z1 + z2) < norm z2) : norm z1 = norm z2 := sorry

theorem eq_of_norm_add_lt_left {p : ℕ} {hp : fact (nat.prime p)} {z1 : padic p} {z2 : padic p} (h : norm (z1 + z2) < norm z1) : norm z1 = norm z2 := sorry

end padic_norm_e


namespace padic


protected instance complete {p : ℕ} [fact (nat.prime p)] : cau_seq.is_complete (padic p) norm :=
  cau_seq.is_complete.mk sorry

theorem padic_norm_e_lim_le {p : ℕ} [fact (nat.prime p)] {f : cau_seq (padic p) norm} {a : ℝ} (ha : 0 < a) (hf : ∀ (i : ℕ), norm (coe_fn f i) ≤ a) : norm (cau_seq.lim f) ≤ a := sorry

/-!
### Valuation on `ℚ_[p]`
-/

/--
`padic.valuation` lifts the p-adic valuation on rationals to `ℚ_[p]`.
-/
def valuation {p : ℕ} [fact (nat.prime p)] : padic p → ℤ :=
  quotient.lift padic_seq.valuation sorry

@[simp] theorem valuation_zero {p : ℕ} [fact (nat.prime p)] : valuation 0 = 0 :=
  dif_pos (iff.mpr (const_equiv p) rfl)

@[simp] theorem valuation_one {p : ℕ} [fact (nat.prime p)] : valuation 1 = 0 := sorry

theorem norm_eq_pow_val {p : ℕ} [fact (nat.prime p)] {x : padic p} : x ≠ 0 → norm x = ↑p ^ (-valuation x) := sorry

@[simp] theorem valuation_p {p : ℕ} [fact (nat.prime p)] : valuation ↑p = 1 := sorry

