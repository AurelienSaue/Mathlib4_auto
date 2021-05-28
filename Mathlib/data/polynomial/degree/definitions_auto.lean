/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.coeff
import Mathlib.data.nat.with_bot
import PostPort

universes u v u_1 

namespace Mathlib

/-!
# Theory of univariate polynomials

The definitions include
`degree`, `monic`, `leading_coeff`

Results include
- `degree_mul` : The degree of the product is the sum of degrees
- `leading_coeff_add_of_degree_eq` and `leading_coeff_add_of_degree_lt` :
    The leading_coefficient of a sum is determined by the leading coefficients and degrees
-/

namespace polynomial


/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree {R : Type u} [semiring R] (p : polynomial R) : with_bot ℕ :=
  finset.sup (finsupp.support p) some

theorem degree_lt_wf {R : Type u} [semiring R] : well_founded fun (p q : polynomial R) => degree p < degree q :=
  inv_image.wf degree (with_bot.well_founded_lt nat.lt_wf)

protected instance has_well_founded {R : Type u} [semiring R] : has_well_founded (polynomial R) :=
  has_well_founded.mk (fun (p q : polynomial R) => degree p < degree q) degree_lt_wf

/-- `nat_degree p` forces `degree p` to ℕ, by defining nat_degree 0 = 0. -/
def nat_degree {R : Type u} [semiring R] (p : polynomial R) : ℕ :=
  option.get_or_else (degree p) 0

/-- `leading_coeff p` gives the coefficient of the highest power of `X` in `p`-/
def leading_coeff {R : Type u} [semiring R] (p : polynomial R) : R :=
  coeff p (nat_degree p)

/-- a polynomial is `monic` if its leading coefficient is 1 -/
def monic {R : Type u} [semiring R] (p : polynomial R)  :=
  leading_coeff p = 1

theorem monic_of_subsingleton {R : Type u} [semiring R] [subsingleton R] (p : polynomial R) : monic p :=
  subsingleton.elim (leading_coeff p) 1

theorem monic.def {R : Type u} [semiring R] {p : polynomial R} : monic p ↔ leading_coeff p = 1 :=
  iff.rfl

protected instance monic.decidable {R : Type u} [semiring R] {p : polynomial R} [DecidableEq R] : Decidable (monic p) :=
  eq.mpr sorry (_inst_2 (leading_coeff p) 1)

@[simp] theorem monic.leading_coeff {R : Type u} [semiring R] {p : polynomial R} (hp : monic p) : leading_coeff p = 1 :=
  hp

theorem monic.coeff_nat_degree {R : Type u} [semiring R] {p : polynomial R} (hp : monic p) : coeff p (nat_degree p) = 1 :=
  hp

@[simp] theorem degree_zero {R : Type u} [semiring R] : degree 0 = ⊥ :=
  rfl

@[simp] theorem nat_degree_zero {R : Type u} [semiring R] : nat_degree 0 = 0 :=
  rfl

@[simp] theorem coeff_nat_degree {R : Type u} [semiring R] {p : polynomial R} : coeff p (nat_degree p) = leading_coeff p :=
  rfl

theorem degree_eq_bot {R : Type u} [semiring R] {p : polynomial R} : degree p = ⊥ ↔ p = 0 := sorry

theorem degree_of_subsingleton {R : Type u} [semiring R] {p : polynomial R} [subsingleton R] : degree p = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree p = ⊥)) (subsingleton.elim p 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (degree 0 = ⊥)) degree_zero)) (Eq.refl ⊥))

theorem nat_degree_of_subsingleton {R : Type u} [semiring R] {p : polynomial R} [subsingleton R] : nat_degree p = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree p = 0)) (subsingleton.elim p 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree 0 = 0)) nat_degree_zero)) (Eq.refl 0))

theorem degree_eq_nat_degree {R : Type u} [semiring R] {p : polynomial R} (hp : p ≠ 0) : degree p = ↑(nat_degree p) := sorry

theorem degree_eq_iff_nat_degree_eq {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (hp : p ≠ 0) : degree p = ↑n ↔ nat_degree p = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree p = ↑n ↔ nat_degree p = n)) (degree_eq_nat_degree hp)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nat_degree p) = ↑n ↔ nat_degree p = n)) (propext with_bot.coe_eq_coe)))
      (iff.refl (nat_degree p = n)))

theorem degree_eq_iff_nat_degree_eq_of_pos {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (hn : 0 < n) : degree p = ↑n ↔ nat_degree p = n := sorry

theorem nat_degree_eq_of_degree_eq_some {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (h : degree p = ↑n) : nat_degree p = n := sorry

@[simp] theorem degree_le_nat_degree {R : Type u} [semiring R] {p : polynomial R} : degree p ≤ ↑(nat_degree p) :=
  galois_connection.le_u_l (galois_insertion.gc with_bot.gi_get_or_else_bot) (degree p)

theorem nat_degree_eq_of_degree_eq {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] {q : polynomial S} (h : degree p = degree q) : nat_degree p = nat_degree q := sorry

theorem le_degree_of_ne_zero {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (h : coeff p n ≠ 0) : ↑n ≤ degree p :=
  (fun (this : some n ≤ finset.sup (finsupp.support p) some) => this) (finset.le_sup (iff.mpr finsupp.mem_support_iff h))

theorem le_nat_degree_of_ne_zero {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (h : coeff p n ≠ 0) : n ≤ nat_degree p := sorry

theorem le_nat_degree_of_mem_supp {R : Type u} [semiring R] {p : polynomial R} (a : ℕ) : a ∈ finsupp.support p → a ≤ nat_degree p :=
  le_nat_degree_of_ne_zero ∘ iff.mp mem_support_iff_coeff_ne_zero

theorem supp_subset_range {R : Type u} {m : ℕ} [semiring R] {p : polynomial R} (h : nat_degree p < m) : finsupp.support p ⊆ finset.range m :=
  fun (n : ℕ) (hn : n ∈ finsupp.support p) =>
    iff.mpr finset.mem_range (has_le.le.trans_lt (le_nat_degree_of_mem_supp n hn) h)

theorem supp_subset_range_nat_degree_succ {R : Type u} [semiring R] {p : polynomial R} : finsupp.support p ⊆ finset.range (nat_degree p + 1) :=
  supp_subset_range (nat.lt_succ_self (nat_degree p))

theorem degree_le_degree {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : coeff q (nat_degree p) ≠ 0) : degree p ≤ degree q :=
  dite (p = 0) (fun (hp : p = 0) => eq.mpr (id (Eq._oldrec (Eq.refl (degree p ≤ degree q)) hp)) bot_le)
    fun (hp : ¬p = 0) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (degree p ≤ degree q)) (degree_eq_nat_degree hp))) (le_degree_of_ne_zero h)

theorem degree_ne_of_nat_degree_ne {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : nat_degree p ≠ n → degree p ≠ ↑n := sorry

theorem nat_degree_le_iff_degree_le {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : nat_degree p ≤ n ↔ degree p ≤ ↑n :=
  with_bot.get_or_else_bot_le_iff

theorem degree_le_of_nat_degree_le {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : nat_degree p ≤ n → degree p ≤ ↑n :=
  iff.mp nat_degree_le_iff_degree_le

theorem nat_degree_le_nat_degree {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hpq : degree p ≤ degree q) : nat_degree p ≤ nat_degree q :=
  galois_connection.monotone_l (galois_insertion.gc with_bot.gi_get_or_else_bot) hpq

@[simp] theorem degree_C {R : Type u} {a : R} [semiring R] (ha : a ≠ 0) : degree (coe_fn C a) = 0 :=
  (fun (this : finset.sup (ite (a = 0) ∅ (singleton 0)) some = 0) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (finset.sup (ite (a = 0) ∅ (singleton 0)) some = 0)) (if_neg ha)))
      (Eq.refl (finset.sup (singleton 0) some)))

theorem degree_C_le {R : Type u} {a : R} [semiring R] : degree (coe_fn C a) ≤ 0 := sorry

theorem degree_one_le {R : Type u} [semiring R] : degree 1 ≤ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree 1 ≤ 0)) (Eq.symm C_1))) degree_C_le

@[simp] theorem nat_degree_C {R : Type u} [semiring R] (a : R) : nat_degree (coe_fn C a) = 0 := sorry

@[simp] theorem nat_degree_one {R : Type u} [semiring R] : nat_degree 1 = 0 :=
  nat_degree_C 1

@[simp] theorem nat_degree_nat_cast {R : Type u} [semiring R] (n : ℕ) : nat_degree ↑n = 0 := sorry

@[simp] theorem degree_monomial {R : Type u} {a : R} [semiring R] (n : ℕ) (ha : a ≠ 0) : degree (coe_fn (monomial n) a) = ↑n := sorry

@[simp] theorem degree_C_mul_X_pow {R : Type u} {a : R} [semiring R] (n : ℕ) (ha : a ≠ 0) : degree (coe_fn C a * X ^ n) = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree (coe_fn C a * X ^ n) = ↑n)) (Eq.symm single_eq_C_mul_X)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (degree (coe_fn (monomial n) a) = ↑n)) (degree_monomial n ha))) (Eq.refl ↑n))

theorem degree_monomial_le {R : Type u} [semiring R] (n : ℕ) (a : R) : degree (coe_fn (monomial n) a) ≤ ↑n := sorry

theorem degree_C_mul_X_pow_le {R : Type u} [semiring R] (n : ℕ) (a : R) : degree (coe_fn C a * X ^ n) ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree (coe_fn C a * X ^ n) ≤ ↑n)) (C_mul_X_pow_eq_monomial a n)))
    (degree_monomial_le n a)

@[simp] theorem nat_degree_C_mul_X_pow {R : Type u} [semiring R] (n : ℕ) (a : R) (ha : a ≠ 0) : nat_degree (coe_fn C a * X ^ n) = n :=
  nat_degree_eq_of_degree_eq_some (degree_C_mul_X_pow n ha)

@[simp] theorem nat_degree_C_mul_X {R : Type u} [semiring R] (a : R) (ha : a ≠ 0) : nat_degree (coe_fn C a * X) = 1 := sorry

@[simp] theorem nat_degree_monomial {R : Type u} [semiring R] (i : ℕ) (r : R) (hr : r ≠ 0) : nat_degree (coe_fn (monomial i) r) = i :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree (coe_fn (monomial i) r) = i)) (Eq.symm (C_mul_X_pow_eq_monomial r i))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree (coe_fn C r * X ^ i) = i)) (nat_degree_C_mul_X_pow i r hr))) (Eq.refl i))

theorem coeff_eq_zero_of_degree_lt {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (h : degree p < ↑n) : coeff p n = 0 :=
  iff.mp not_not (mt le_degree_of_ne_zero (not_le_of_gt h))

theorem coeff_eq_zero_of_nat_degree_lt {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (h : nat_degree p < n) : coeff p n = 0 := sorry

@[simp] theorem coeff_nat_degree_succ_eq_zero {R : Type u} [semiring R] {p : polynomial R} : coeff p (nat_degree p + 1) = 0 :=
  coeff_eq_zero_of_nat_degree_lt (lt_add_one (nat_degree p))

-- We need the explicit `decidable` argument here because an exotic one shows up in a moment!

theorem ite_le_nat_degree_coeff {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) (I : Decidable (n < 1 + nat_degree p)) : ite (n < 1 + nat_degree p) (coeff p n) 0 = coeff p n := sorry

theorem as_sum_support {R : Type u} [semiring R] (p : polynomial R) : p = finset.sum (finsupp.support p) fun (i : ℕ) => coe_fn (monomial i) (coeff p i) :=
  Eq.symm (finsupp.sum_single p)

theorem as_sum_support_C_mul_X_pow {R : Type u} [semiring R] (p : polynomial R) : p = finset.sum (finsupp.support p) fun (i : ℕ) => coe_fn C (coeff p i) * X ^ i := sorry

/--
We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
theorem sum_over_range' {R : Type u} {S : Type v} [semiring R] [add_comm_monoid S] (p : polynomial R) {f : ℕ → R → S} (h : ∀ (n : ℕ), f n 0 = 0) (n : ℕ) (w : nat_degree p < n) : finsupp.sum p f = finset.sum (finset.range n) fun (a : ℕ) => f a (coeff p a) :=
  finsupp.sum_of_support_subset p (supp_subset_range w) f fun (n_1 : ℕ) (hn : n_1 ∈ finset.range n) => h n_1

/--
We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
theorem sum_over_range {R : Type u} {S : Type v} [semiring R] [add_comm_monoid S] (p : polynomial R) {f : ℕ → R → S} (h : ∀ (n : ℕ), f n 0 = 0) : finsupp.sum p f = finset.sum (finset.range (nat_degree p + 1)) fun (a : ℕ) => f a (coeff p a) :=
  sum_over_range' p h (nat_degree p + 1) (lt_add_one (nat_degree p))

theorem as_sum_range' {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) (w : nat_degree p < n) : p = finset.sum (finset.range n) fun (i : ℕ) => coe_fn (monomial i) (coeff p i) :=
  Eq.trans (Eq.symm (finsupp.sum_single p)) (sum_over_range' p (fun (n : ℕ) => finsupp.single_zero) n w)

theorem as_sum_range {R : Type u} [semiring R] (p : polynomial R) : p = finset.sum (finset.range (nat_degree p + 1)) fun (i : ℕ) => coe_fn (monomial i) (coeff p i) :=
  Eq.trans (Eq.symm (finsupp.sum_single p)) (sum_over_range p fun (n : ℕ) => finsupp.single_zero)

theorem as_sum_range_C_mul_X_pow {R : Type u} [semiring R] (p : polynomial R) : p = finset.sum (finset.range (nat_degree p + 1)) fun (i : ℕ) => coe_fn C (coeff p i) * X ^ i := sorry

theorem coeff_ne_zero_of_eq_degree {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} (hn : degree p = ↑n) : coeff p n ≠ 0 :=
  fun (h : coeff p n = 0) => iff.mp finsupp.mem_support_iff (finset.mem_of_max hn) h

theorem eq_X_add_C_of_degree_le_one {R : Type u} [semiring R] {p : polynomial R} (h : degree p ≤ 1) : p = coe_fn C (coeff p 1) * X + coe_fn C (coeff p 0) := sorry

theorem eq_X_add_C_of_degree_eq_one {R : Type u} [semiring R] {p : polynomial R} (h : degree p = 1) : p = coe_fn C (leading_coeff p) * X + coe_fn C (coeff p 0) := sorry

theorem eq_X_add_C_of_nat_degree_le_one {R : Type u} [semiring R] {p : polynomial R} (h : nat_degree p ≤ 1) : p = coe_fn C (coeff p 1) * X + coe_fn C (coeff p 0) :=
  eq_X_add_C_of_degree_le_one (degree_le_of_nat_degree_le h)

theorem exists_eq_X_add_C_of_nat_degree_le_one {R : Type u} [semiring R] {p : polynomial R} (h : nat_degree p ≤ 1) : ∃ (a : R), ∃ (b : R), p = coe_fn C a * X + coe_fn C b :=
  Exists.intro (coeff p 1) (Exists.intro (coeff p 0) (eq_X_add_C_of_nat_degree_le_one h))

theorem degree_X_pow_le {R : Type u} [semiring R] (n : ℕ) : degree (X ^ n) ≤ ↑n := sorry

theorem degree_X_le {R : Type u} [semiring R] : degree X ≤ 1 :=
  degree_monomial_le 1 1

theorem nat_degree_X_le {R : Type u} [semiring R] : nat_degree X ≤ 1 :=
  nat_degree_le_of_degree_le degree_X_le

theorem support_C_mul_X_pow {R : Type u} [semiring R] (c : R) (n : ℕ) : finsupp.support (coe_fn C c * X ^ n) ⊆ singleton n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support (coe_fn C c * X ^ n) ⊆ singleton n)) (C_mul_X_pow_eq_monomial c n)))
    finsupp.support_single_subset

theorem mem_support_C_mul_X_pow {R : Type u} [semiring R] {n : ℕ} {a : ℕ} {c : R} (h : a ∈ finsupp.support (coe_fn C c * X ^ n)) : a = n :=
  iff.mp finset.mem_singleton (support_C_mul_X_pow c n h)

theorem card_support_C_mul_X_pow_le_one {R : Type u} [semiring R] {c : R} {n : ℕ} : finset.card (finsupp.support (coe_fn C c * X ^ n)) ≤ 1 := sorry

theorem card_supp_le_succ_nat_degree {R : Type u} [semiring R] (p : polynomial R) : finset.card (finsupp.support p) ≤ nat_degree p + 1 := sorry

theorem le_degree_of_mem_supp {R : Type u} [semiring R] {p : polynomial R} (a : ℕ) : a ∈ finsupp.support p → ↑a ≤ degree p :=
  le_degree_of_ne_zero ∘ iff.mp mem_support_iff_coeff_ne_zero

theorem nonempty_support_iff {R : Type u} [semiring R] {p : polynomial R} : finset.nonempty (finsupp.support p) ↔ p ≠ 0 := sorry

theorem support_C_mul_X_pow_nonzero {R : Type u} [semiring R] {c : R} {n : ℕ} (h : c ≠ 0) : finsupp.support (coe_fn C c * X ^ n) = singleton n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finsupp.support (coe_fn C c * X ^ n) = singleton n)) (C_mul_X_pow_eq_monomial c n)))
    (finsupp.support_single_ne_zero h)

@[simp] theorem degree_one {R : Type u} [semiring R] [nontrivial R] : degree 1 = 0 :=
  degree_C ((fun (this : 1 ≠ 0) => this) (ne.symm zero_ne_one))

@[simp] theorem degree_X {R : Type u} [semiring R] [nontrivial R] : degree X = 1 :=
  degree_monomial 1 one_ne_zero

@[simp] theorem nat_degree_X {R : Type u} [semiring R] [nontrivial R] : nat_degree X = 1 :=
  nat_degree_eq_of_degree_eq_some degree_X

theorem coeff_mul_X_sub_C {R : Type u} [ring R] {p : polynomial R} {r : R} {a : ℕ} : coeff (p * (X - coe_fn C r)) (a + 1) = coeff p a - coeff p (a + 1) * r := sorry

theorem C_eq_int_cast {R : Type u} [ring R] (n : ℤ) : coe_fn C ↑n = ↑n :=
  ring_hom.map_int_cast C n

@[simp] theorem degree_neg {R : Type u} [ring R] (p : polynomial R) : degree (-p) = degree p := sorry

@[simp] theorem nat_degree_neg {R : Type u} [ring R] (p : polynomial R) : nat_degree (-p) = nat_degree p := sorry

@[simp] theorem nat_degree_int_cast {R : Type u} [ring R] (n : ℤ) : nat_degree ↑n = 0 := sorry

/-- The second-highest coefficient, or 0 for constants -/
def next_coeff {R : Type u} [semiring R] (p : polynomial R) : R :=
  ite (nat_degree p = 0) 0 (coeff p (nat_degree p - 1))

@[simp] theorem next_coeff_C_eq_zero {R : Type u} [semiring R] (c : R) : next_coeff (coe_fn C c) = 0 := sorry

theorem next_coeff_of_pos_nat_degree {R : Type u} [semiring R] (p : polynomial R) (hp : 0 < nat_degree p) : next_coeff p = coeff p (nat_degree p - 1) := sorry

theorem coeff_nat_degree_eq_zero_of_degree_lt {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : degree p < degree q) : coeff p (nat_degree q) = 0 :=
  coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h degree_le_nat_degree)

theorem ne_zero_of_degree_gt {R : Type u} [semiring R] {p : polynomial R} {n : with_bot ℕ} (h : n < degree p) : p ≠ 0 :=
  mt (iff.mpr degree_eq_bot) (ne.symm (ne_of_lt (lt_of_le_of_lt bot_le h)))

theorem eq_C_of_degree_le_zero {R : Type u} [semiring R] {p : polynomial R} (h : degree p ≤ 0) : p = coe_fn C (coeff p 0) := sorry

theorem eq_C_of_degree_eq_zero {R : Type u} [semiring R] {p : polynomial R} (h : degree p = 0) : p = coe_fn C (coeff p 0) :=
  eq_C_of_degree_le_zero (h ▸ le_refl (degree p))

theorem degree_le_zero_iff {R : Type u} [semiring R] {p : polynomial R} : degree p ≤ 0 ↔ p = coe_fn C (coeff p 0) :=
  { mp := eq_C_of_degree_le_zero, mpr := fun (h : p = coe_fn C (coeff p 0)) => Eq.symm h ▸ degree_C_le }

theorem degree_add_le {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) : degree (p + q) ≤ max (degree p) (degree q) := sorry

@[simp] theorem leading_coeff_zero {R : Type u} [semiring R] : leading_coeff 0 = 0 :=
  rfl

@[simp] theorem leading_coeff_eq_zero {R : Type u} [semiring R] {p : polynomial R} : leading_coeff p = 0 ↔ p = 0 := sorry

theorem leading_coeff_eq_zero_iff_deg_eq_bot {R : Type u} [semiring R] {p : polynomial R} : leading_coeff p = 0 ↔ degree p = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (leading_coeff p = 0 ↔ degree p = ⊥)) (propext leading_coeff_eq_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (p = 0 ↔ degree p = ⊥)) (propext degree_eq_bot))) (iff.refl (p = 0)))

theorem nat_degree_mem_support_of_nonzero {R : Type u} [semiring R] {p : polynomial R} (H : p ≠ 0) : nat_degree p ∈ finsupp.support p :=
  iff.mpr (finsupp.mem_support_to_fun p (nat_degree p)) (iff.mpr (not_congr leading_coeff_eq_zero) H)

theorem nat_degree_eq_support_max' {R : Type u} [semiring R] {p : polynomial R} (h : p ≠ 0) : nat_degree p = finset.max' (finsupp.support p) (iff.mpr nonempty_support_iff h) := sorry

theorem nat_degree_C_mul_X_pow_le {R : Type u} [semiring R] (a : R) (n : ℕ) : nat_degree (coe_fn C a * X ^ n) ≤ n :=
  iff.mpr nat_degree_le_iff_degree_le (degree_C_mul_X_pow_le n a)

theorem degree_add_eq_left_of_degree_lt {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : degree q < degree p) : degree (p + q) = degree p := sorry

theorem degree_add_eq_right_of_degree_lt {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : degree p < degree q) : degree (p + q) = degree q :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree (p + q) = degree q)) (add_comm p q)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (degree (q + p) = degree q)) (degree_add_eq_left_of_degree_lt h)))
      (Eq.refl (degree q)))

theorem degree_add_C {R : Type u} {a : R} [semiring R] {p : polynomial R} (hp : 0 < degree p) : degree (p + coe_fn C a) = degree p :=
  Eq.subst (add_comm (coe_fn C a) p) degree_add_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hp)

theorem degree_add_eq_of_leading_coeff_add_ne_zero {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : leading_coeff p + leading_coeff q ≠ 0) : degree (p + q) = max (degree p) (degree q) := sorry

theorem degree_erase_le {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) : degree (finsupp.erase n p) ≤ degree p := sorry

theorem degree_erase_lt {R : Type u} [semiring R] {p : polynomial R} (hp : p ≠ 0) : degree (finsupp.erase (nat_degree p) p) < degree p := sorry

theorem degree_sum_le {R : Type u} [semiring R] {ι : Type u_1} (s : finset ι) (f : ι → polynomial R) : degree (finset.sum s fun (i : ι) => f i) ≤ finset.sup s fun (b : ι) => degree (f b) := sorry

theorem degree_mul_le {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) : degree (p * q) ≤ degree p + degree q := sorry

theorem degree_pow_le {R : Type u} [semiring R] (p : polynomial R) (n : ℕ) : degree (p ^ n) ≤ n •ℕ degree p := sorry

@[simp] theorem leading_coeff_monomial {R : Type u} [semiring R] (a : R) (n : ℕ) : leading_coeff (coe_fn (monomial n) a) = a := sorry

theorem leading_coeff_C_mul_X_pow {R : Type u} [semiring R] (a : R) (n : ℕ) : leading_coeff (coe_fn C a * X ^ n) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (leading_coeff (coe_fn C a * X ^ n) = a)) (C_mul_X_pow_eq_monomial a n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (leading_coeff (coe_fn (monomial n) a) = a)) (leading_coeff_monomial a n)))
      (Eq.refl a))

@[simp] theorem leading_coeff_C {R : Type u} [semiring R] (a : R) : leading_coeff (coe_fn C a) = a :=
  leading_coeff_monomial a 0

@[simp] theorem leading_coeff_X_pow {R : Type u} [semiring R] (n : ℕ) : leading_coeff (X ^ n) = 1 := sorry

@[simp] theorem leading_coeff_X {R : Type u} [semiring R] : leading_coeff X = 1 := sorry

@[simp] theorem monic_X_pow {R : Type u} [semiring R] (n : ℕ) : monic (X ^ n) :=
  leading_coeff_X_pow n

@[simp] theorem monic_X {R : Type u} [semiring R] : monic X :=
  leading_coeff_X

@[simp] theorem leading_coeff_one {R : Type u} [semiring R] : leading_coeff 1 = 1 :=
  leading_coeff_C 1

@[simp] theorem monic_one {R : Type u} [semiring R] : monic 1 :=
  leading_coeff_C 1

theorem monic.ne_zero {R : Type u_1} [semiring R] [nontrivial R] {p : polynomial R} (hp : monic p) : p ≠ 0 := sorry

theorem monic.ne_zero_of_ne {R : Type u} [semiring R] (h : 0 ≠ 1) {p : polynomial R} (hp : monic p) : p ≠ 0 :=
  monic.ne_zero hp

theorem monic.ne_zero_of_polynomial_ne {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} {r : polynomial R} (hp : monic p) (hne : q ≠ r) : p ≠ 0 :=
  monic.ne_zero hp

theorem leading_coeff_add_of_degree_lt {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : degree p < degree q) : leading_coeff (p + q) = leading_coeff q := sorry

theorem leading_coeff_add_of_degree_eq {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : degree p = degree q) (hlc : leading_coeff p + leading_coeff q ≠ 0) : leading_coeff (p + q) = leading_coeff p + leading_coeff q := sorry

@[simp] theorem coeff_mul_degree_add_degree {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) : coeff (p * q) (nat_degree p + nat_degree q) = leading_coeff p * leading_coeff q := sorry

theorem degree_mul' {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : leading_coeff p * leading_coeff q ≠ 0) : degree (p * q) = degree p + degree q := sorry

theorem degree_mul_monic {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hq : monic q) : degree (p * q) = degree p + degree q := sorry

theorem nat_degree_mul' {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : leading_coeff p * leading_coeff q ≠ 0) : nat_degree (p * q) = nat_degree p + nat_degree q := sorry

theorem leading_coeff_mul' {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (h : leading_coeff p * leading_coeff q ≠ 0) : leading_coeff (p * q) = leading_coeff p * leading_coeff q := sorry

theorem leading_coeff_pow' {R : Type u} {n : ℕ} [semiring R] {p : polynomial R} : leading_coeff p ^ n ≠ 0 → leading_coeff (p ^ n) = leading_coeff p ^ n := sorry

theorem degree_pow' {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : leading_coeff p ^ n ≠ 0 → degree (p ^ n) = n •ℕ degree p := sorry

theorem nat_degree_pow' {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} (h : leading_coeff p ^ n ≠ 0) : nat_degree (p ^ n) = n * nat_degree p := sorry

theorem leading_coeff_mul_monic {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} (hq : monic q) : leading_coeff (p * q) = leading_coeff p := sorry

@[simp] theorem leading_coeff_mul_X_pow {R : Type u} [semiring R] {p : polynomial R} {n : ℕ} : leading_coeff (p * X ^ n) = leading_coeff p :=
  leading_coeff_mul_monic (monic_X_pow n)

@[simp] theorem leading_coeff_mul_X {R : Type u} [semiring R] {p : polynomial R} : leading_coeff (p * X) = leading_coeff p :=
  leading_coeff_mul_monic monic_X

theorem nat_degree_mul_le {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} : nat_degree (p * q) ≤ nat_degree p + nat_degree q := sorry

theorem subsingleton_of_monic_zero {R : Type u} [semiring R] (h : monic 0) : (∀ (p q : polynomial R), p = q) ∧ ∀ (a b : R), a = b := sorry

theorem zero_le_degree_iff {R : Type u} [semiring R] {p : polynomial R} : 0 ≤ degree p ↔ p ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ degree p ↔ p ≠ 0)) (ne.def p 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ degree p ↔ ¬p = 0)) (Eq.symm (propext degree_eq_bot))))
      (option.cases_on (degree p) (of_as_true trivial) fun (val : ℕ) => of_as_true trivial))

theorem degree_nonneg_iff_ne_zero {R : Type u} [semiring R] {p : polynomial R} : 0 ≤ degree p ↔ p ≠ 0 := sorry

theorem nat_degree_eq_zero_iff_degree_le_zero {R : Type u} [semiring R] {p : polynomial R} : nat_degree p = 0 ↔ degree p ≤ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree p = 0 ↔ degree p ≤ 0)) (Eq.symm (propext nonpos_iff_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree p ≤ 0 ↔ degree p ≤ 0)) (propext nat_degree_le_iff_degree_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (degree p ≤ ↑0 ↔ degree p ≤ 0)) with_bot.coe_zero)) (iff.refl (degree p ≤ 0))))

theorem degree_le_iff_coeff_zero {R : Type u} [semiring R] (f : polynomial R) (n : with_bot ℕ) : degree f ≤ n ↔ ∀ (m : ℕ), n < ↑m → coeff f m = 0 := sorry

theorem degree_lt_iff_coeff_zero {R : Type u} [semiring R] (f : polynomial R) (n : ℕ) : degree f < ↑n ↔ ∀ (m : ℕ), n ≤ m → coeff f m = 0 := sorry

theorem degree_lt_degree_mul_X {R : Type u} [semiring R] {p : polynomial R} (hp : p ≠ 0) : degree p < degree (p * X) := sorry

theorem nat_degree_pos_iff_degree_pos {R : Type u} [semiring R] {p : polynomial R} : 0 < nat_degree p ↔ 0 < degree p :=
  lt_iff_lt_of_le_iff_le nat_degree_le_iff_degree_le

theorem eq_C_of_nat_degree_le_zero {R : Type u} [semiring R] {p : polynomial R} (h : nat_degree p ≤ 0) : p = coe_fn C (coeff p 0) :=
  eq_C_of_degree_le_zero (degree_le_of_nat_degree_le h)

theorem eq_C_of_nat_degree_eq_zero {R : Type u} [semiring R] {p : polynomial R} (h : nat_degree p = 0) : p = coe_fn C (coeff p 0) :=
  eq_C_of_nat_degree_le_zero (eq.le h)

@[simp] theorem degree_X_pow {R : Type u} [semiring R] [nontrivial R] (n : ℕ) : degree (X ^ n) = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (degree (X ^ n) = ↑n)) (X_pow_eq_monomial n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (degree (coe_fn (monomial n) 1) = ↑n)) (degree_monomial n one_ne_zero)))
      (Eq.refl ↑n))

@[simp] theorem nat_degree_X_pow {R : Type u} [semiring R] [nontrivial R] (n : ℕ) : nat_degree (X ^ n) = n :=
  nat_degree_eq_of_degree_eq_some (degree_X_pow n)

theorem not_is_unit_X {R : Type u} [semiring R] [nontrivial R] : ¬is_unit X := sorry

@[simp] theorem degree_mul_X {R : Type u} [semiring R] [nontrivial R] {p : polynomial R} : degree (p * X) = degree p + 1 := sorry

@[simp] theorem degree_mul_X_pow {R : Type u} {n : ℕ} [semiring R] [nontrivial R] {p : polynomial R} : degree (p * X ^ n) = degree p + ↑n := sorry

theorem degree_sub_le {R : Type u} [ring R] (p : polynomial R) (q : polynomial R) : degree (p - q) ≤ max (degree p) (degree q) := sorry

theorem degree_sub_lt {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} (hd : degree p = degree q) (hp0 : p ≠ 0) (hlc : leading_coeff p = leading_coeff q) : degree (p - q) < degree p := sorry

theorem nat_degree_X_sub_C_le {R : Type u} [ring R] {r : R} : nat_degree (X - coe_fn C r) ≤ 1 :=
  iff.mpr nat_degree_le_iff_degree_le
    (le_trans (degree_sub_le X (coe_fn C r))
      (max_le degree_X_le (le_trans degree_C_le (iff.mpr with_bot.coe_le_coe zero_le_one))))

theorem degree_sum_fin_lt {R : Type u} [ring R] {n : ℕ} (f : fin n → R) : degree (finset.sum finset.univ fun (i : fin n) => coe_fn C (f i) * X ^ ↑i) < ↑n := sorry

theorem degree_sub_eq_left_of_degree_lt {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} (h : degree q < degree p) : degree (p - q) = degree p := sorry

theorem degree_sub_eq_right_of_degree_lt {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} (h : degree p < degree q) : degree (p - q) = degree q := sorry

@[simp] theorem degree_X_sub_C {R : Type u} [nontrivial R] [ring R] (a : R) : degree (X - coe_fn C a) = 1 := sorry

@[simp] theorem nat_degree_X_sub_C {R : Type u} [nontrivial R] [ring R] (x : R) : nat_degree (X - coe_fn C x) = 1 :=
  nat_degree_eq_of_degree_eq_some (degree_X_sub_C x)

@[simp] theorem next_coeff_X_sub_C {R : Type u} [nontrivial R] [ring R] (c : R) : next_coeff (X - coe_fn C c) = -c := sorry

theorem degree_X_pow_sub_C {R : Type u} [nontrivial R] [ring R] {n : ℕ} (hn : 0 < n) (a : R) : degree (X ^ n - coe_fn C a) = ↑n := sorry

theorem X_pow_sub_C_ne_zero {R : Type u} [nontrivial R] [ring R] {n : ℕ} (hn : 0 < n) (a : R) : X ^ n - coe_fn C a ≠ 0 := sorry

theorem X_sub_C_ne_zero {R : Type u} [nontrivial R] [ring R] (r : R) : X - coe_fn C r ≠ 0 :=
  pow_one X ▸ X_pow_sub_C_ne_zero zero_lt_one r

theorem nat_degree_X_pow_sub_C {R : Type u} [nontrivial R] [ring R] {n : ℕ} (hn : 0 < n) {r : R} : nat_degree (X ^ n - coe_fn C r) = n := sorry

@[simp] theorem degree_mul {R : Type u} [comm_semiring R] [no_zero_divisors R] {p : polynomial R} {q : polynomial R} : degree (p * q) = degree p + degree q := sorry

@[simp] theorem degree_pow {R : Type u} [comm_semiring R] [no_zero_divisors R] [nontrivial R] (p : polynomial R) (n : ℕ) : degree (p ^ n) = n •ℕ degree p := sorry

@[simp] theorem leading_coeff_mul {R : Type u} [comm_semiring R] [no_zero_divisors R] (p : polynomial R) (q : polynomial R) : leading_coeff (p * q) = leading_coeff p * leading_coeff q := sorry

@[simp] theorem leading_coeff_X_add_C {R : Type u} [comm_semiring R] [no_zero_divisors R] [nontrivial R] (a : R) (b : R) (ha : a ≠ 0) : leading_coeff (coe_fn C a * X + coe_fn C b) = a := sorry

/-- `polynomial.leading_coeff` bundled as a `monoid_hom` when `R` has `no_zero_divisors`, and thus
  `leading_coeff` is multiplicative -/
def leading_coeff_hom {R : Type u} [comm_semiring R] [no_zero_divisors R] : polynomial R →* R :=
  monoid_hom.mk leading_coeff sorry leading_coeff_mul

@[simp] theorem leading_coeff_hom_apply {R : Type u} [comm_semiring R] [no_zero_divisors R] (p : polynomial R) : coe_fn leading_coeff_hom p = leading_coeff p :=
  rfl

@[simp] theorem leading_coeff_pow {R : Type u} [comm_semiring R] [no_zero_divisors R] (p : polynomial R) (n : ℕ) : leading_coeff (p ^ n) = leading_coeff p ^ n :=
  monoid_hom.map_pow leading_coeff_hom p n

