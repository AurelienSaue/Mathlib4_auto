/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.nnreal
import Mathlib.data.set.intervals.default
import Mathlib.PostPort

universes u_1 u_3 

namespace Mathlib

/-!
# Extended non-negative reals

We define `ennreal := with_no ℝ≥0` to be the type of extended nonnegative real numbers, i.e., the
interval `[0, +∞]`. This type is used as the codomain of a `measure_theory.measure`, and of the
extended distance `edist` in a `emetric_space`. In this file we define some algebraic operations and
a linear order on `ennreal` and prove basic properties of these operations, order, and conversions
to/from `ℝ`, `ℝ≥0`, and `ℕ`.

## Main definitions

* `ennreal`: the extended nonnegative real numbers `[0, ∞]`; defined as `with_top ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and `a *
    ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.

  - `a / b` is defined as `a * b⁻¹`.

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ennreal` into a canonically ordered commutative semiring of characteristic zero.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ennreal` is defined as `has_coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ennreal`, and Lean will apply `coe` automatically;

  - `ennreal.to_nnreal` sends `↑p` to `p` and `∞` to `0`;

  - `ennreal.to_real := coe ∘ ennreal.to_nnreal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ennreal.of_real := coe ∘ nnreal.of_real` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ennreal.ne_top_equiv_nnreal` is an equivalence between `{a : ennreal // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `can_lift ennreal ℝ≥0` instance, so one of the ways to prove theorems about an `ennreal`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ennreal) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0`: type of nonnegative real numbers `[0, ∞)`; defined in `data.real.nnreal`;
* `∞`: a localized notation in `ennreal` for `⊤ : ennreal`.

-/

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
def ennreal :=
  with_top nnreal

namespace ennreal


protected instance inhabited : Inhabited ennreal :=
  { default := 0 }

protected instance has_coe : has_coe nnreal ennreal :=
  has_coe.mk some

protected instance nnreal.can_lift : can_lift ennreal nnreal :=
  can_lift.mk coe (fun (r : ennreal) => r ≠ ⊤) sorry

@[simp] theorem none_eq_top : none = ⊤ :=
  rfl

@[simp] theorem some_eq_coe (a : nnreal) : some a = ↑a :=
  rfl

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def to_nnreal : ennreal → nnreal :=
  sorry

/-- `to_real x` returns `x` if it is real, `0` otherwise. -/
protected def to_real (a : ennreal) : ℝ :=
  ↑(ennreal.to_nnreal a)

/-- `of_real x` returns `x` if it is nonnegative, `0` otherwise. -/
protected def of_real (r : ℝ) : ennreal :=
  ↑(nnreal.of_real r)

@[simp] theorem to_nnreal_coe {r : nnreal} : ennreal.to_nnreal ↑r = r :=
  rfl

@[simp] theorem coe_to_nnreal {a : ennreal} : a ≠ ⊤ → ↑(ennreal.to_nnreal a) = a :=
  fun (ᾰ : a ≠ ⊤) =>
    option.cases_on a (fun (ᾰ : none ≠ ⊤) => idRhs (↑(ennreal.to_nnreal none) = none) (false.elim (ᾰ rfl)))
      (fun (a : nnreal) (ᾰ : some a ≠ ⊤) => idRhs (↑(ennreal.to_nnreal (some a)) = ↑(ennreal.to_nnreal (some a))) rfl) ᾰ

@[simp] theorem of_real_to_real {a : ennreal} (h : a ≠ ⊤) : ennreal.of_real (ennreal.to_real a) = a := sorry

@[simp] theorem to_real_of_real {r : ℝ} (h : 0 ≤ r) : ennreal.to_real (ennreal.of_real r) = r := sorry

theorem to_real_of_real' {r : ℝ} : ennreal.to_real (ennreal.of_real r) = max r 0 :=
  rfl

theorem coe_to_nnreal_le_self {a : ennreal} : ↑(ennreal.to_nnreal a) ≤ a := sorry

theorem coe_nnreal_eq (r : nnreal) : ↑r = ennreal.of_real ↑r := sorry

theorem of_real_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) : ennreal.of_real x = ↑{ val := x, property := h } := sorry

@[simp] theorem of_real_coe_nnreal {p : nnreal} : ennreal.of_real ↑p = ↑p :=
  Eq.symm (coe_nnreal_eq p)

@[simp] theorem coe_zero : ↑0 = 0 :=
  rfl

@[simp] theorem coe_one : ↑1 = 1 :=
  rfl

@[simp] theorem to_real_nonneg {a : ennreal} : 0 ≤ ennreal.to_real a := sorry

@[simp] theorem top_to_nnreal : ennreal.to_nnreal ⊤ = 0 :=
  rfl

@[simp] theorem top_to_real : ennreal.to_real ⊤ = 0 :=
  rfl

@[simp] theorem one_to_real : ennreal.to_real 1 = 1 :=
  rfl

@[simp] theorem one_to_nnreal : ennreal.to_nnreal 1 = 1 :=
  rfl

@[simp] theorem coe_to_real (r : nnreal) : ennreal.to_real ↑r = ↑r :=
  rfl

@[simp] theorem zero_to_nnreal : ennreal.to_nnreal 0 = 0 :=
  rfl

@[simp] theorem zero_to_real : ennreal.to_real 0 = 0 :=
  rfl

@[simp] theorem of_real_zero : ennreal.of_real 0 = 0 := sorry

@[simp] theorem of_real_one : ennreal.of_real 1 = 1 := sorry

theorem of_real_to_real_le {a : ennreal} : ennreal.of_real (ennreal.to_real a) ≤ a :=
  dite (a = ⊤) (fun (ha : a = ⊤) => Eq.symm ha ▸ le_top) fun (ha : ¬a = ⊤) => le_of_eq (of_real_to_real ha)

theorem forall_ennreal {p : ennreal → Prop} : (∀ (a : ennreal), p a) ↔ (∀ (r : nnreal), p ↑r) ∧ p ⊤ := sorry

theorem forall_ne_top {p : ennreal → Prop} : (∀ (a : ennreal), a ≠ ⊤ → p a) ↔ ∀ (r : nnreal), p ↑r :=
  option.ball_ne_none

theorem exists_ne_top {p : ennreal → Prop} : (∃ (a : ennreal), ∃ (H : a ≠ ⊤), p a) ↔ ∃ (r : nnreal), p ↑r :=
  option.bex_ne_none

theorem to_nnreal_eq_zero_iff (x : ennreal) : ennreal.to_nnreal x = 0 ↔ x = 0 ∨ x = ⊤ := sorry

theorem to_real_eq_zero_iff (x : ennreal) : ennreal.to_real x = 0 ↔ x = 0 ∨ x = ⊤ := sorry

@[simp] theorem coe_ne_top {r : nnreal} : ↑r ≠ ⊤ :=
  with_top.coe_ne_top

@[simp] theorem top_ne_coe {r : nnreal} : ⊤ ≠ ↑r :=
  with_top.top_ne_coe

@[simp] theorem of_real_ne_top {r : ℝ} : ennreal.of_real r ≠ ⊤ := sorry

@[simp] theorem of_real_lt_top {r : ℝ} : ennreal.of_real r < ⊤ :=
  iff.mpr lt_top_iff_ne_top of_real_ne_top

@[simp] theorem top_ne_of_real {r : ℝ} : ⊤ ≠ ennreal.of_real r := sorry

@[simp] theorem zero_ne_top : 0 ≠ ⊤ :=
  coe_ne_top

@[simp] theorem top_ne_zero : ⊤ ≠ 0 :=
  top_ne_coe

@[simp] theorem one_ne_top : 1 ≠ ⊤ :=
  coe_ne_top

@[simp] theorem top_ne_one : ⊤ ≠ 1 :=
  top_ne_coe

@[simp] theorem coe_eq_coe {r : nnreal} {q : nnreal} : ↑r = ↑q ↔ r = q :=
  with_top.coe_eq_coe

@[simp] theorem coe_le_coe {r : nnreal} {q : nnreal} : ↑r ≤ ↑q ↔ r ≤ q :=
  with_top.coe_le_coe

@[simp] theorem coe_lt_coe {r : nnreal} {q : nnreal} : ↑r < ↑q ↔ r < q :=
  with_top.coe_lt_coe

theorem coe_mono : monotone coe :=
  fun (_x _x_1 : nnreal) => iff.mpr coe_le_coe

@[simp] theorem coe_eq_zero {r : nnreal} : ↑r = 0 ↔ r = 0 :=
  coe_eq_coe

@[simp] theorem zero_eq_coe {r : nnreal} : 0 = ↑r ↔ 0 = r :=
  coe_eq_coe

@[simp] theorem coe_eq_one {r : nnreal} : ↑r = 1 ↔ r = 1 :=
  coe_eq_coe

@[simp] theorem one_eq_coe {r : nnreal} : 1 = ↑r ↔ 1 = r :=
  coe_eq_coe

@[simp] theorem coe_nonneg {r : nnreal} : 0 ≤ ↑r ↔ 0 ≤ r :=
  coe_le_coe

@[simp] theorem coe_pos {r : nnreal} : 0 < ↑r ↔ 0 < r :=
  coe_lt_coe

@[simp] theorem coe_add {r : nnreal} {p : nnreal} : ↑(r + p) = ↑r + ↑p :=
  with_top.coe_add

@[simp] theorem coe_mul {r : nnreal} {p : nnreal} : ↑(r * p) = ↑r * ↑p :=
  with_top.coe_mul

@[simp] theorem coe_bit0 {r : nnreal} : ↑(bit0 r) = bit0 ↑r :=
  coe_add

@[simp] theorem coe_bit1 {r : nnreal} : ↑(bit1 r) = bit1 ↑r := sorry

theorem coe_two : ↑(bit0 1) = bit0 1 := sorry

protected theorem zero_lt_one : 0 < 1 :=
  canonically_ordered_semiring.zero_lt_one

@[simp] theorem one_lt_two : 1 < bit0 1 := sorry

@[simp] theorem zero_lt_two : 0 < bit0 1 :=
  lt_trans ennreal.zero_lt_one one_lt_two

theorem two_ne_zero : bit0 1 ≠ 0 :=
  ne.symm (ne_of_lt zero_lt_two)

theorem two_ne_top : bit0 1 ≠ ⊤ :=
  coe_two ▸ coe_ne_top

/-- The set of `ennreal` numbers that are not equal to `∞` is equivalent to `ℝ≥0`. -/
def ne_top_equiv_nnreal : ↥(set_of fun (a : ennreal) => a ≠ ⊤) ≃ nnreal :=
  equiv.mk (fun (x : ↥(set_of fun (a : ennreal) => a ≠ ⊤)) => ennreal.to_nnreal ↑x)
    (fun (x : nnreal) => { val := ↑x, property := coe_ne_top }) sorry sorry

theorem cinfi_ne_top {α : Type u_1} [has_Inf α] (f : ennreal → α) : (infi fun (x : Subtype fun (x : ennreal) => x ≠ ⊤) => f ↑x) = infi fun (x : nnreal) => f ↑x :=
  Eq.symm
    (infi_congr (⇑(equiv.symm ne_top_equiv_nnreal)) (equiv.surjective (equiv.symm ne_top_equiv_nnreal))
      fun (x : nnreal) => rfl)

theorem infi_ne_top {α : Type u_1} [complete_lattice α] (f : ennreal → α) : (infi fun (x : ennreal) => infi fun (H : x ≠ ⊤) => f x) = infi fun (x : nnreal) => f ↑x := sorry

theorem csupr_ne_top {α : Type u_1} [has_Sup α] (f : ennreal → α) : (supr fun (x : Subtype fun (x : ennreal) => x ≠ ⊤) => f ↑x) = supr fun (x : nnreal) => f ↑x :=
  cinfi_ne_top f

theorem supr_ne_top {α : Type u_1} [complete_lattice α] (f : ennreal → α) : (supr fun (x : ennreal) => supr fun (H : x ≠ ⊤) => f x) = supr fun (x : nnreal) => f ↑x :=
  infi_ne_top fun (x : ennreal) => f x

theorem infi_ennreal {α : Type u_1} [complete_lattice α] {f : ennreal → α} : (infi fun (n : ennreal) => f n) = (infi fun (n : nnreal) => f ↑n) ⊓ f ⊤ := sorry

theorem supr_ennreal {α : Type u_1} [complete_lattice α] {f : ennreal → α} : (supr fun (n : ennreal) => f n) = (supr fun (n : nnreal) => f ↑n) ⊔ f ⊤ :=
  infi_ennreal

@[simp] theorem add_top {a : ennreal} : a + ⊤ = ⊤ :=
  with_top.add_top

@[simp] theorem top_add {a : ennreal} : ⊤ + a = ⊤ :=
  with_top.top_add

/-- Coercion `ℝ≥0 → ennreal` as a `ring_hom`. -/
def of_nnreal_hom : nnreal →+* ennreal :=
  ring_hom.mk coe coe_one sorry coe_zero sorry

@[simp] theorem coe_of_nnreal_hom : ⇑of_nnreal_hom = coe :=
  rfl

@[simp] theorem coe_indicator {α : Type u_1} (s : set α) (f : α → nnreal) (a : α) : ↑(set.indicator s f a) = set.indicator s (fun (x : α) => ↑(f x)) a :=
  add_monoid_hom.map_indicator (↑of_nnreal_hom) s f a

@[simp] theorem coe_pow {r : nnreal} (n : ℕ) : ↑(r ^ n) = ↑r ^ n :=
  ring_hom.map_pow of_nnreal_hom r n

@[simp] theorem add_eq_top {a : ennreal} {b : ennreal} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  with_top.add_eq_top

@[simp] theorem add_lt_top {a : ennreal} {b : ennreal} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
  with_top.add_lt_top

theorem to_nnreal_add {r₁ : ennreal} {r₂ : ennreal} (h₁ : r₁ < ⊤) (h₂ : r₂ < ⊤) : ennreal.to_nnreal (r₁ + r₂) = ennreal.to_nnreal r₁ + ennreal.to_nnreal r₂ := sorry

/- rw has trouble with the generic lt_top_iff_ne_top and bot_lt_iff_ne_bot
(contrary to erw). This is solved with the next lemmas -/

protected theorem lt_top_iff_ne_top {a : ennreal} : a < ⊤ ↔ a ≠ ⊤ :=
  lt_top_iff_ne_top

protected theorem bot_lt_iff_ne_bot {a : ennreal} : 0 < a ↔ a ≠ 0 :=
  bot_lt_iff_ne_bot

theorem not_lt_top {x : ennreal} : ¬x < ⊤ ↔ x = ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬x < ⊤ ↔ x = ⊤)) (propext lt_top_iff_ne_top)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬x ≠ ⊤ ↔ x = ⊤)) (propext not_not))) (iff.refl (x = ⊤)))

theorem add_ne_top {a : ennreal} {b : ennreal} : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := sorry

theorem mul_top {a : ennreal} : a * ⊤ = ite (a = 0) 0 ⊤ := sorry

theorem top_mul {a : ennreal} : ⊤ * a = ite (a = 0) 0 ⊤ := sorry

@[simp] theorem top_mul_top : ⊤ * ⊤ = ⊤ :=
  with_top.top_mul_top

theorem top_pow {n : ℕ} (h : 0 < n) : ⊤ ^ n = ⊤ := sorry

theorem mul_eq_top {a : ennreal} {b : ennreal} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 :=
  with_top.mul_eq_top_iff

theorem mul_lt_top {a : ennreal} {b : ennreal} : a < ⊤ → b < ⊤ → a * b < ⊤ :=
  with_top.mul_lt_top

theorem mul_ne_top {a : ennreal} {b : ennreal} : a ≠ ⊤ → b ≠ ⊤ → a * b ≠ ⊤ := sorry

theorem ne_top_of_mul_ne_top_left {a : ennreal} {b : ennreal} (h : a * b ≠ ⊤) (hb : b ≠ 0) : a ≠ ⊤ := sorry

theorem ne_top_of_mul_ne_top_right {a : ennreal} {b : ennreal} (h : a * b ≠ ⊤) (ha : a ≠ 0) : b ≠ ⊤ :=
  ne_top_of_mul_ne_top_left (eq.mpr (id (Eq._oldrec (Eq.refl (b * a ≠ ⊤)) (mul_comm b a))) h) ha

theorem lt_top_of_mul_lt_top_left {a : ennreal} {b : ennreal} (h : a * b < ⊤) (hb : b ≠ 0) : a < ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < ⊤)) (propext ennreal.lt_top_iff_ne_top)))
    (ne_top_of_mul_ne_top_left (eq.mp (Eq._oldrec (Eq.refl (a * b < ⊤)) (propext ennreal.lt_top_iff_ne_top)) h) hb)

theorem lt_top_of_mul_lt_top_right {a : ennreal} {b : ennreal} (h : a * b < ⊤) (ha : a ≠ 0) : b < ⊤ :=
  lt_top_of_mul_lt_top_left (eq.mpr (id (Eq._oldrec (Eq.refl (b * a < ⊤)) (mul_comm b a))) h) ha

theorem mul_lt_top_iff {a : ennreal} {b : ennreal} : a * b < ⊤ ↔ a < ⊤ ∧ b < ⊤ ∨ a = 0 ∨ b = 0 := sorry

@[simp] theorem mul_pos {a : ennreal} {b : ennreal} : 0 < a * b ↔ 0 < a ∧ 0 < b := sorry

theorem pow_eq_top {a : ennreal} (n : ℕ) : a ^ n = ⊤ → a = ⊤ := sorry

theorem pow_ne_top {a : ennreal} (h : a ≠ ⊤) {n : ℕ} : a ^ n ≠ ⊤ :=
  mt (pow_eq_top n) h

theorem pow_lt_top {a : ennreal} : a < ⊤ → ∀ (n : ℕ), a ^ n < ⊤ :=
  eq.mpr (id (imp_congr_eq (propext lt_top_iff_ne_top) (forall_congr_eq fun (n : ℕ) => propext lt_top_iff_ne_top)))
    (eq.mp (Eq.refl (a ≠ ⊤ → ∀ (n : ℕ), a ^ n ≠ ⊤)) pow_ne_top)

@[simp] theorem coe_finset_sum {α : Type u_1} {s : finset α} {f : α → nnreal} : ↑(finset.sum s fun (a : α) => f a) = finset.sum s fun (a : α) => ↑(f a) :=
  ring_hom.map_sum of_nnreal_hom f s

@[simp] theorem coe_finset_prod {α : Type u_1} {s : finset α} {f : α → nnreal} : ↑(finset.prod s fun (a : α) => f a) = finset.prod s fun (a : α) => ↑(f a) :=
  ring_hom.map_prod of_nnreal_hom f s

@[simp] theorem bot_eq_zero : ⊥ = 0 :=
  rfl

@[simp] theorem coe_lt_top {r : nnreal} : ↑r < ⊤ :=
  with_top.coe_lt_top r

@[simp] theorem not_top_le_coe {r : nnreal} : ¬⊤ ≤ ↑r :=
  with_top.not_top_le_coe r

theorem zero_lt_coe_iff {p : nnreal} : 0 < ↑p ↔ 0 < p :=
  coe_lt_coe

@[simp] theorem one_le_coe_iff {r : nnreal} : 1 ≤ ↑r ↔ 1 ≤ r :=
  coe_le_coe

@[simp] theorem coe_le_one_iff {r : nnreal} : ↑r ≤ 1 ↔ r ≤ 1 :=
  coe_le_coe

@[simp] theorem coe_lt_one_iff {p : nnreal} : ↑p < 1 ↔ p < 1 :=
  coe_lt_coe

@[simp] theorem one_lt_coe_iff {p : nnreal} : 1 < ↑p ↔ 1 < p :=
  coe_lt_coe

@[simp] theorem coe_nat (n : ℕ) : ↑↑n = ↑n :=
  with_top.coe_nat n

@[simp] theorem of_real_coe_nat (n : ℕ) : ennreal.of_real ↑n = ↑n := sorry

@[simp] theorem nat_ne_top (n : ℕ) : ↑n ≠ ⊤ :=
  with_top.nat_ne_top n

@[simp] theorem top_ne_nat (n : ℕ) : ⊤ ≠ ↑n :=
  with_top.top_ne_nat n

@[simp] theorem one_lt_top : 1 < ⊤ :=
  coe_lt_top

theorem le_coe_iff {a : ennreal} {r : nnreal} : a ≤ ↑r ↔ ∃ (p : nnreal), a = ↑p ∧ p ≤ r :=
  with_top.le_coe_iff

theorem coe_le_iff {a : ennreal} {r : nnreal} : ↑r ≤ a ↔ ∀ (p : nnreal), a = ↑p → r ≤ p :=
  with_top.coe_le_iff

theorem lt_iff_exists_coe {a : ennreal} {b : ennreal} : a < b ↔ ∃ (p : nnreal), a = ↑p ∧ ↑p < b :=
  with_top.lt_iff_exists_coe

@[simp] theorem coe_finset_sup {α : Type u_1} {s : finset α} {f : α → nnreal} : ↑(finset.sup s f) = finset.sup s fun (x : α) => ↑(f x) :=
  finset.comp_sup_eq_sup_comp_of_is_total coe coe_mono rfl

theorem pow_le_pow {a : ennreal} {n : ℕ} {m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m := sorry

@[simp] theorem max_eq_zero_iff {a : ennreal} {b : ennreal} : max a b = 0 ↔ a = 0 ∧ b = 0 := sorry

@[simp] theorem max_zero_left {a : ennreal} : max 0 a = a :=
  max_eq_right (zero_le a)

@[simp] theorem max_zero_right {a : ennreal} : max a 0 = a :=
  max_eq_left (zero_le a)

-- TODO: why this is not a `rfl`? There is some hidden diamond here.

@[simp] theorem sup_eq_max {a : ennreal} {b : ennreal} : a ⊔ b = max a b :=
  eq_of_forall_ge_iff fun (c : ennreal) => iff.trans sup_le_iff (iff.symm max_le_iff)

protected theorem pow_pos {a : ennreal} : 0 < a → ∀ (n : ℕ), 0 < a ^ n :=
  canonically_ordered_semiring.pow_pos

protected theorem pow_ne_zero {a : ennreal} : a ≠ 0 → ∀ (n : ℕ), a ^ n ≠ 0 :=
  eq.mpr (id (Eq.refl (a ≠ 0 → ∀ (n : ℕ), a ^ n ≠ 0)))
    (eq.mp (imp_congr_eq (propext pos_iff_ne_zero) (forall_congr_eq fun (n : ℕ) => propext pos_iff_ne_zero))
      ennreal.pow_pos)

@[simp] theorem not_lt_zero {a : ennreal} : ¬a < 0 :=
  eq.mpr (id (Eq.trans (propext not_lt) (propext ((fun {α : Type} (a : α) => iff_true_intro (zero_le a)) a)))) trivial

theorem add_lt_add_iff_left {a : ennreal} {b : ennreal} {c : ennreal} : a < ⊤ → (a + c < a + b ↔ c < b) :=
  with_top.add_lt_add_iff_left

theorem add_lt_add_iff_right {a : ennreal} {b : ennreal} {c : ennreal} : a < ⊤ → (c + a < b + a ↔ c < b) :=
  with_top.add_lt_add_iff_right

theorem lt_add_right {a : ennreal} {b : ennreal} (ha : a < ⊤) (hb : 0 < b) : a < a + b :=
  eq.mp (Eq._oldrec (Eq.refl (a + 0 < a + b)) (add_zero a))
    (eq.mp (Eq._oldrec (Eq.refl (0 < b)) (Eq.symm (propext (add_lt_add_iff_left ha)))) hb)

theorem le_of_forall_pos_le_add {a : ennreal} {b : ennreal} : (∀ (ε : nnreal), 0 < ε → b < ⊤ → a ≤ b + ↑ε) → a ≤ b := sorry

theorem lt_iff_exists_rat_btwn {a : ennreal} {b : ennreal} : a < b ↔ ∃ (q : ℚ), 0 ≤ q ∧ a < ↑(nnreal.of_real ↑q) ∧ ↑(nnreal.of_real ↑q) < b := sorry

theorem lt_iff_exists_real_btwn {a : ennreal} {b : ennreal} : a < b ↔ ∃ (r : ℝ), 0 ≤ r ∧ a < ennreal.of_real r ∧ ennreal.of_real r < b := sorry

theorem lt_iff_exists_nnreal_btwn {a : ennreal} {b : ennreal} : a < b ↔ ∃ (r : nnreal), a < ↑r ∧ ↑r < b :=
  with_top.lt_iff_exists_coe_btwn

theorem lt_iff_exists_add_pos_lt {a : ennreal} {b : ennreal} : a < b ↔ ∃ (r : nnreal), 0 < r ∧ a + ↑r < b := sorry

theorem coe_nat_lt_coe {r : nnreal} {n : ℕ} : ↑n < ↑r ↔ ↑n < r :=
  coe_nat n ▸ coe_lt_coe

theorem coe_lt_coe_nat {r : nnreal} {n : ℕ} : ↑r < ↑n ↔ r < ↑n :=
  coe_nat n ▸ coe_lt_coe

theorem coe_nat_lt_coe_nat {m : ℕ} {n : ℕ} : ↑m < ↑n ↔ m < n :=
  coe_nat n ▸ iff.trans coe_nat_lt_coe nat.cast_lt

theorem coe_nat_ne_top {n : ℕ} : ↑n ≠ ⊤ :=
  coe_nat n ▸ coe_ne_top

theorem coe_nat_mono : strict_mono coe :=
  fun (_x _x_1 : ℕ) => iff.mpr coe_nat_lt_coe_nat

theorem coe_nat_le_coe_nat {m : ℕ} {n : ℕ} : ↑m ≤ ↑n ↔ m ≤ n :=
  strict_mono.le_iff_le coe_nat_mono

protected instance char_zero : char_zero ennreal :=
  char_zero.mk (strict_mono.injective coe_nat_mono)

protected theorem exists_nat_gt {r : ennreal} (h : r ≠ ⊤) : ∃ (n : ℕ), r < ↑n := sorry

theorem add_lt_add {a : ennreal} {b : ennreal} {c : ennreal} {d : ennreal} (ac : a < c) (bd : b < d) : a + b < c + d := sorry

theorem coe_min {r : nnreal} {p : nnreal} : ↑(min r p) = min ↑r ↑p :=
  monotone.map_min coe_mono

theorem coe_max {r : nnreal} {p : nnreal} : ↑(max r p) = max ↑r ↑p :=
  monotone.map_max coe_mono

theorem le_of_top_imp_top_of_to_nnreal_le {a : ennreal} {b : ennreal} (h : a = ⊤ → b = ⊤) (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → ennreal.to_nnreal a ≤ ennreal.to_nnreal b) : a ≤ b := sorry

theorem coe_Sup {s : set nnreal} : bdd_above s → ↑(Sup s) = supr fun (a : nnreal) => supr fun (H : a ∈ s) => ↑a :=
  with_top.coe_Sup

theorem coe_Inf {s : set nnreal} : set.nonempty s → ↑(Inf s) = infi fun (a : nnreal) => infi fun (H : a ∈ s) => ↑a :=
  with_top.coe_Inf

@[simp] theorem top_mem_upper_bounds {s : set ennreal} : ⊤ ∈ upper_bounds s :=
  fun (x : ennreal) (hx : x ∈ s) => le_top

theorem coe_mem_upper_bounds {r : nnreal} {s : set nnreal} : ↑r ∈ upper_bounds (coe '' s) ↔ r ∈ upper_bounds s := sorry

theorem mul_le_mul {a : ennreal} {b : ennreal} {c : ennreal} {d : ennreal} : a ≤ b → c ≤ d → a * c ≤ b * d :=
  canonically_ordered_semiring.mul_le_mul

theorem mul_lt_mul {a : ennreal} {b : ennreal} {c : ennreal} {d : ennreal} (ac : a < c) (bd : b < d) : a * b < c * d := sorry

theorem mul_left_mono {a : ennreal} : monotone (Mul.mul a) :=
  fun (b c : ennreal) => mul_le_mul (le_refl a)

theorem mul_right_mono {a : ennreal} : monotone fun (x : ennreal) => x * a :=
  fun (b c : ennreal) (h : b ≤ c) => mul_le_mul h (le_refl a)

theorem max_mul {a : ennreal} {b : ennreal} {c : ennreal} : max a b * c = max (a * c) (b * c) :=
  monotone.map_max mul_right_mono

theorem mul_max {a : ennreal} {b : ennreal} {c : ennreal} : a * max b c = max (a * b) (a * c) :=
  monotone.map_max mul_left_mono

theorem mul_eq_mul_left {a : ennreal} {b : ennreal} {c : ennreal} : a ≠ 0 → a ≠ ⊤ → (a * b = a * c ↔ b = c) := sorry

theorem mul_eq_mul_right {a : ennreal} {b : ennreal} {c : ennreal} : c ≠ 0 → c ≠ ⊤ → (a * c = b * c ↔ a = b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left

theorem mul_le_mul_left {a : ennreal} {b : ennreal} {c : ennreal} : a ≠ 0 → a ≠ ⊤ → (a * b ≤ a * c ↔ b ≤ c) := sorry

theorem mul_le_mul_right {a : ennreal} {b : ennreal} {c : ennreal} : c ≠ 0 → c ≠ ⊤ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

theorem mul_lt_mul_left {a : ennreal} {b : ennreal} {c : ennreal} : a ≠ 0 → a ≠ ⊤ → (a * b < a * c ↔ b < c) := sorry

theorem mul_lt_mul_right {a : ennreal} {b : ennreal} {c : ennreal} : c ≠ 0 → c ≠ ⊤ → (a * c < b * c ↔ a < b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left

protected instance has_sub : Sub ennreal :=
  { sub := fun (a b : ennreal) => Inf (set_of fun (d : ennreal) => a ≤ d + b) }

theorem coe_sub {r : nnreal} {p : nnreal} : ↑(p - r) = ↑p - ↑r := sorry

@[simp] theorem top_sub_coe {r : nnreal} : ⊤ - ↑r = ⊤ := sorry

@[simp] theorem sub_eq_zero_of_le {a : ennreal} {b : ennreal} (h : a ≤ b) : a - b = 0 :=
  le_antisymm (Inf_le (le_add_left h)) (zero_le (a - b))

@[simp] theorem sub_self {a : ennreal} : a - a = 0 :=
  sub_eq_zero_of_le (le_refl a)

@[simp] theorem zero_sub {a : ennreal} : 0 - a = 0 :=
  le_antisymm (Inf_le (zero_le (0 + a))) (zero_le (0 - a))

@[simp] theorem sub_infty {a : ennreal} : a - ⊤ = 0 := sorry

theorem sub_le_sub {a : ennreal} {b : ennreal} {c : ennreal} {d : ennreal} (h₁ : a ≤ b) (h₂ : d ≤ c) : a - c ≤ b - d :=
  Inf_le_Inf fun (e : ennreal) (h : b ≤ e + d) => le_trans (le_trans h₁ h) (add_le_add (le_refl e) h₂)

@[simp] theorem add_sub_self {a : ennreal} {b : ennreal} : b < ⊤ → a + b - b = a := sorry

@[simp] theorem add_sub_self' {a : ennreal} {b : ennreal} (h : a < ⊤) : a + b - a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b - a = b)) (add_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + a - a = b)) (add_sub_self h))) (Eq.refl b))

theorem add_right_inj {a : ennreal} {b : ennreal} {c : ennreal} (h : a < ⊤) : a + b = a + c ↔ b = c := sorry

theorem add_left_inj {a : ennreal} {b : ennreal} {c : ennreal} (h : a < ⊤) : b + a = c + a ↔ b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b + a = c + a ↔ b = c)) (add_comm b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b = c + a ↔ b = c)) (add_comm c a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a + b = a + c ↔ b = c)) (propext (add_right_inj h)))) (iff.refl (b = c))))

@[simp] theorem sub_add_cancel_of_le {a : ennreal} {b : ennreal} : b ≤ a → a - b + b = a := sorry

@[simp] theorem add_sub_cancel_of_le {a : ennreal} {b : ennreal} (h : b ≤ a) : b + (a - b) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b + (a - b) = a)) (add_comm b (a - b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b + b = a)) (sub_add_cancel_of_le h))) (Eq.refl a))

theorem sub_add_self_eq_max {a : ennreal} {b : ennreal} : a - b + b = max a b := sorry

theorem le_sub_add_self {a : ennreal} {b : ennreal} : a ≤ a - b + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ a - b + b)) sub_add_self_eq_max)) (le_max_left a b)

@[simp] protected theorem sub_le_iff_le_add {a : ennreal} {b : ennreal} {c : ennreal} : a - b ≤ c ↔ a ≤ c + b :=
  { mp := fun (h : a - b ≤ c) => le_trans le_sub_add_self (add_le_add_right h b), mpr := fun (h : a ≤ c + b) => Inf_le h }

protected theorem sub_le_iff_le_add' {a : ennreal} {b : ennreal} {c : ennreal} : a - b ≤ c ↔ a ≤ b + c :=
  add_comm c b ▸ ennreal.sub_le_iff_le_add

theorem sub_eq_of_add_eq {a : ennreal} {b : ennreal} {c : ennreal} : b ≠ ⊤ → a + b = c → c - b = a :=
  fun (hb : b ≠ ⊤) (hc : a + b = c) => hc ▸ add_sub_self (iff.mpr lt_top_iff_ne_top hb)

protected theorem sub_le_of_sub_le {a : ennreal} {b : ennreal} {c : ennreal} (h : a - b ≤ c) : a - c ≤ b :=
  iff.mpr ennreal.sub_le_iff_le_add
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b + c)) (add_comm b c))) (iff.mp ennreal.sub_le_iff_le_add h))

protected theorem sub_lt_self {a : ennreal} {b : ennreal} : a ≠ ⊤ → a ≠ 0 → 0 < b → a - b < a := sorry

@[simp] theorem sub_eq_zero_iff_le {a : ennreal} {b : ennreal} : a - b = 0 ↔ a ≤ b := sorry

@[simp] theorem zero_lt_sub_iff_lt {a : ennreal} {b : ennreal} : 0 < a - b ↔ b < a := sorry

theorem lt_sub_iff_add_lt {a : ennreal} {b : ennreal} {c : ennreal} : a < b - c ↔ a + c < b := sorry

theorem sub_le_self (a : ennreal) (b : ennreal) : a - b ≤ a :=
  iff.mpr ennreal.sub_le_iff_le_add (le_add_right (le_refl a))

@[simp] theorem sub_zero {a : ennreal} : a - 0 = a := sorry

/-- A version of triangle inequality for difference as a "distance". -/
theorem sub_le_sub_add_sub {a : ennreal} {b : ennreal} {c : ennreal} : a - c ≤ a - b + (b - c) :=
  iff.mpr ennreal.sub_le_iff_le_add
    (trans_rel_left LessEq (le_trans le_sub_add_self (add_le_add_left le_sub_add_self (a - b)))
      (Eq.symm (add_assoc (a - b) (b - c) c)))

theorem sub_sub_cancel {a : ennreal} {b : ennreal} (h : a < ⊤) (h2 : b ≤ a) : a - (a - b) = b := sorry

theorem sub_right_inj {a : ennreal} {b : ennreal} {c : ennreal} (ha : a < ⊤) (hb : b ≤ a) (hc : c ≤ a) : a - b = a - c ↔ b = c := sorry

theorem sub_mul {a : ennreal} {b : ennreal} {c : ennreal} (h : 0 < b → b < a → c ≠ ⊤) : (a - b) * c = a * c - b * c := sorry

theorem mul_sub {a : ennreal} {b : ennreal} {c : ennreal} (h : 0 < c → c < b → a ≠ ⊤) : a * (b - c) = a * b - a * c := sorry

theorem sub_mul_ge {a : ennreal} {b : ennreal} {c : ennreal} : a * c - b * c ≤ (a - b) * c := sorry

/-- A product of finite numbers is still finite -/
theorem prod_lt_top {α : Type u_1} {s : finset α} {f : α → ennreal} (h : ∀ (a : α), a ∈ s → f a < ⊤) : (finset.prod s fun (a : α) => f a) < ⊤ :=
  with_top.prod_lt_top h

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top {α : Type u_1} {s : finset α} {f : α → ennreal} : (∀ (a : α), a ∈ s → f a < ⊤) → (finset.sum s fun (a : α) => f a) < ⊤ :=
  with_top.sum_lt_top

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff {α : Type u_1} {s : finset α} {f : α → ennreal} : (finset.sum s fun (a : α) => f a) < ⊤ ↔ ∀ (a : α), a ∈ s → f a < ⊤ :=
  with_top.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff {α : Type u_1} {s : finset α} {f : α → ennreal} : (finset.sum s fun (x : α) => f x) = ⊤ ↔ ∃ (a : α), ∃ (H : a ∈ s), f a = ⊤ :=
  with_top.sum_eq_top_iff

/-- seeing `ennreal` as `ℝ≥0` does not change their sum, unless one of the `ennreal` is
infinity -/
theorem to_nnreal_sum {α : Type u_1} {s : finset α} {f : α → ennreal} (hf : ∀ (a : α), a ∈ s → f a < ⊤) : ennreal.to_nnreal (finset.sum s fun (a : α) => f a) = finset.sum s fun (a : α) => ennreal.to_nnreal (f a) := sorry

/-- seeing `ennreal` as `real` does not change their sum, unless one of the `ennreal` is infinity -/
theorem to_real_sum {α : Type u_1} {s : finset α} {f : α → ennreal} (hf : ∀ (a : α), a ∈ s → f a < ⊤) : ennreal.to_real (finset.sum s fun (a : α) => f a) = finset.sum s fun (a : α) => ennreal.to_real (f a) := sorry

theorem of_real_sum_of_nonneg {α : Type u_1} {s : finset α} {f : α → ℝ} (hf : ∀ (i : α), i ∈ s → 0 ≤ f i) : ennreal.of_real (finset.sum s fun (i : α) => f i) = finset.sum s fun (i : α) => ennreal.of_real (f i) := sorry

protected theorem Ico_eq_Iio {y : ennreal} : set.Ico 0 y = set.Iio y := sorry

theorem mem_Iio_self_add {x : ennreal} {ε : ennreal} : x ≠ ⊤ → 0 < ε → x ∈ set.Iio (x + ε) :=
  fun (xt : x ≠ ⊤) (ε0 : 0 < ε) =>
    lt_add_right (eq.mpr (id (Eq._oldrec (Eq.refl (x < ⊤)) (propext lt_top_iff_ne_top))) xt) ε0

theorem not_mem_Ioo_self_sub {x : ennreal} {y : ennreal} {ε : ennreal} : x = 0 → ¬x ∈ set.Ioo (x - ε) y := sorry

theorem mem_Ioo_self_sub_add {x : ennreal} {ε₁ : ennreal} {ε₂ : ennreal} : x ≠ ⊤ → x ≠ 0 → 0 < ε₁ → 0 < ε₂ → x ∈ set.Ioo (x - ε₁) (x + ε₂) :=
  fun (xt : x ≠ ⊤) (x0 : x ≠ 0) (ε0 : 0 < ε₁) (ε0' : 0 < ε₂) =>
    { left := ennreal.sub_lt_self xt x0 ε0,
      right := lt_add_right (eq.mpr (id (Eq._oldrec (Eq.refl (x < ⊤)) (propext lt_top_iff_ne_top))) xt) ε0' }

@[simp] theorem bit0_inj {a : ennreal} {b : ennreal} : bit0 a = bit0 b ↔ a = b := sorry

@[simp] theorem bit0_eq_zero_iff {a : ennreal} : bit0 a = 0 ↔ a = 0 := sorry

@[simp] theorem bit0_eq_top_iff {a : ennreal} : bit0 a = ⊤ ↔ a = ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bit0 a = ⊤ ↔ a = ⊤)) (bit0.equations._eqn_1 a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + a = ⊤ ↔ a = ⊤)) (propext add_eq_top)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a = ⊤ ∨ a = ⊤ ↔ a = ⊤)) (propext (or_self (a = ⊤))))) (iff.refl (a = ⊤))))

@[simp] theorem bit1_inj {a : ennreal} {b : ennreal} : bit1 a = bit1 b ↔ a = b := sorry

@[simp] theorem bit1_ne_zero {a : ennreal} : bit1 a ≠ 0 := sorry

@[simp] theorem bit1_eq_one_iff {a : ennreal} : bit1 a = 1 ↔ a = 0 := sorry

@[simp] theorem bit1_eq_top_iff {a : ennreal} : bit1 a = ⊤ ↔ a = ⊤ := sorry

protected instance has_inv : has_inv ennreal :=
  has_inv.mk fun (a : ennreal) => Inf (set_of fun (b : ennreal) => 1 ≤ a * b)

protected instance div_inv_monoid : div_inv_monoid ennreal :=
  div_inv_monoid.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv fun (a b : ennreal) => monoid.mul a (b⁻¹)

@[simp] theorem inv_zero : 0⁻¹ = ⊤ := sorry

@[simp] theorem inv_top : ⊤⁻¹ = 0 := sorry

@[simp] theorem coe_inv {r : nnreal} (hr : r ≠ 0) : ↑(r⁻¹) = (↑r⁻¹) := sorry

theorem coe_inv_le {r : nnreal} : ↑(r⁻¹) ≤ (↑r⁻¹) := sorry

theorem coe_inv_two : ↑(bit0 1⁻¹) = (bit0 1⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(bit0 1⁻¹) = (bit0 1⁻¹))) (coe_inv (ne_of_gt zero_lt_two))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(bit0 1)⁻¹ = (bit0 1⁻¹))) coe_two)) (Eq.refl (bit0 1⁻¹)))

@[simp] theorem coe_div {r : nnreal} {p : nnreal} (hr : r ≠ 0) : ↑(p / r) = ↑p / ↑r := sorry

@[simp] theorem inv_one : 1⁻¹ = 1 := sorry

@[simp] theorem div_one {a : ennreal} : a / 1 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / 1 = a)) (div_eq_mul_inv a 1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (1⁻¹) = a)) inv_one))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = a)) (mul_one a))) (Eq.refl a)))

protected theorem inv_pow {a : ennreal} {n : ℕ} : a ^ n⁻¹ = a⁻¹ ^ n := sorry

@[simp] theorem inv_inv {a : ennreal} : a⁻¹⁻¹ = a := sorry

theorem inv_involutive : function.involutive fun (a : ennreal) => a⁻¹ :=
  fun (a : ennreal) => inv_inv

theorem inv_bijective : function.bijective fun (a : ennreal) => a⁻¹ :=
  function.involutive.bijective inv_involutive

@[simp] theorem inv_eq_inv {a : ennreal} {b : ennreal} : a⁻¹ = (b⁻¹) ↔ a = b :=
  function.injective.eq_iff (and.left inv_bijective)

@[simp] theorem inv_eq_top {a : ennreal} : a⁻¹ = ⊤ ↔ a = 0 :=
  inv_zero ▸ inv_eq_inv

theorem inv_ne_top {a : ennreal} : a⁻¹ ≠ ⊤ ↔ a ≠ 0 := sorry

@[simp] theorem inv_lt_top {x : ennreal} : x⁻¹ < ⊤ ↔ 0 < x := sorry

theorem div_lt_top {x : ennreal} {y : ennreal} (h1 : x < ⊤) (h2 : 0 < y) : x / y < ⊤ :=
  mul_lt_top h1 (iff.mpr inv_lt_top h2)

@[simp] theorem inv_eq_zero {a : ennreal} : a⁻¹ = 0 ↔ a = ⊤ :=
  inv_top ▸ inv_eq_inv

theorem inv_ne_zero {a : ennreal} : a⁻¹ ≠ 0 ↔ a ≠ ⊤ := sorry

@[simp] theorem inv_pos {a : ennreal} : 0 < (a⁻¹) ↔ a ≠ ⊤ :=
  iff.trans pos_iff_ne_zero inv_ne_zero

@[simp] theorem inv_lt_inv {a : ennreal} {b : ennreal} : a⁻¹ < (b⁻¹) ↔ b < a := sorry

theorem inv_lt_iff_inv_lt {a : ennreal} {b : ennreal} : a⁻¹ < b ↔ b⁻¹ < a := sorry

theorem lt_inv_iff_lt_inv {a : ennreal} {b : ennreal} : a < (b⁻¹) ↔ b < (a⁻¹) := sorry

@[simp] theorem inv_le_inv {a : ennreal} {b : ennreal} : a⁻¹ ≤ (b⁻¹) ↔ b ≤ a := sorry

theorem inv_le_iff_inv_le {a : ennreal} {b : ennreal} : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := sorry

theorem le_inv_iff_le_inv {a : ennreal} {b : ennreal} : a ≤ (b⁻¹) ↔ b ≤ (a⁻¹) := sorry

@[simp] theorem inv_lt_one {a : ennreal} : a⁻¹ < 1 ↔ 1 < a :=
  iff.trans inv_lt_iff_inv_lt (eq.mpr (id (Eq._oldrec (Eq.refl (1⁻¹ < a ↔ 1 < a)) inv_one)) (iff.refl (1 < a)))

@[simp] theorem div_top {a : ennreal} : a / ⊤ = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / ⊤ = 0)) (div_eq_mul_inv a ⊤)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (⊤⁻¹) = 0)) inv_top))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 0 = 0)) (mul_zero a))) (Eq.refl 0)))

@[simp] theorem top_div_coe {p : nnreal} : ⊤ / ↑p = ⊤ := sorry

theorem top_div_of_ne_top {a : ennreal} (h : a ≠ ⊤) : ⊤ / a = ⊤ := sorry

theorem top_div_of_lt_top {a : ennreal} (h : a < ⊤) : ⊤ / a = ⊤ :=
  top_div_of_ne_top (has_lt.lt.ne h)

theorem top_div {a : ennreal} : ⊤ / a = ite (a = ⊤) 0 ⊤ := sorry

@[simp] theorem zero_div {a : ennreal} : 0 / a = 0 :=
  zero_mul (a⁻¹)

theorem div_eq_top {a : ennreal} {b : ennreal} : a / b = ⊤ ↔ a ≠ 0 ∧ b = 0 ∨ a = ⊤ ∧ b ≠ ⊤ := sorry

theorem le_div_iff_mul_le {a : ennreal} {b : ennreal} {c : ennreal} (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ⊤ ∨ c ≠ ⊤) : a ≤ c / b ↔ a * b ≤ c := sorry

theorem div_le_iff_le_mul {a : ennreal} {b : ennreal} {c : ennreal} (hb0 : b ≠ 0 ∨ c ≠ ⊤) (hbt : b ≠ ⊤ ∨ c ≠ 0) : a / b ≤ c ↔ a ≤ c * b := sorry

theorem div_le_of_le_mul {a : ennreal} {b : ennreal} {c : ennreal} (h : a ≤ b * c) : a / c ≤ b := sorry

protected theorem div_lt_iff {a : ennreal} {b : ennreal} {c : ennreal} (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ⊤ ∨ c ≠ ⊤) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le (le_div_iff_mul_le h0 ht)

theorem mul_lt_of_lt_div {a : ennreal} {b : ennreal} {c : ennreal} (h : a < b / c) : a * c < b := sorry

theorem inv_le_iff_le_mul {a : ennreal} {b : ennreal} : (b = ⊤ → a ≠ 0) → (a = ⊤ → b ≠ 0) → (a⁻¹ ≤ b ↔ 1 ≤ a * b) := sorry

@[simp] theorem le_inv_iff_mul_le {a : ennreal} {b : ennreal} : a ≤ (b⁻¹) ↔ a * b ≤ 1 := sorry

theorem mul_inv_cancel {a : ennreal} (h0 : a ≠ 0) (ht : a ≠ ⊤) : a * (a⁻¹) = 1 := sorry

theorem inv_mul_cancel {a : ennreal} (h0 : a ≠ 0) (ht : a ≠ ⊤) : a⁻¹ * a = 1 :=
  mul_comm a (a⁻¹) ▸ mul_inv_cancel h0 ht

theorem mul_le_iff_le_inv {a : ennreal} {b : ennreal} {r : ennreal} (hr₀ : r ≠ 0) (hr₁ : r ≠ ⊤) : r * a ≤ b ↔ a ≤ r⁻¹ * b := sorry

theorem le_of_forall_nnreal_lt {x : ennreal} {y : ennreal} (h : ∀ (r : nnreal), ↑r < x → ↑r ≤ y) : x ≤ y := sorry

theorem eq_top_of_forall_nnreal_le {x : ennreal} (h : ∀ (r : nnreal), ↑r ≤ x) : x = ⊤ :=
  top_unique (le_of_forall_nnreal_lt fun (r : nnreal) (hr : ↑r < ⊤) => h r)

theorem div_add_div_same {a : ennreal} {b : ennreal} {c : ennreal} : a / c + b / c = (a + b) / c :=
  Eq.symm (right_distrib a b (c⁻¹))

theorem div_self {a : ennreal} (h0 : a ≠ 0) (hI : a ≠ ⊤) : a / a = 1 :=
  mul_inv_cancel h0 hI

theorem mul_div_cancel {a : ennreal} {b : ennreal} (h0 : a ≠ 0) (hI : a ≠ ⊤) : b / a * a = b := sorry

theorem mul_div_cancel' {a : ennreal} {b : ennreal} (h0 : a ≠ 0) (hI : a ≠ ⊤) : a * (b / a) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b / a) = b)) (mul_comm a (b / a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / a * a = b)) (mul_div_cancel h0 hI))) (Eq.refl b))

theorem mul_div_le {a : ennreal} {b : ennreal} : a * (b / a) ≤ b := sorry

theorem inv_two_add_inv_two : bit0 1⁻¹ + (bit0 1⁻¹) = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1⁻¹ + (bit0 1⁻¹) = 1)) (Eq.symm (two_mul (bit0 1⁻¹)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 * (bit0 1⁻¹) = 1)) (Eq.symm (div_eq_mul_inv (bit0 1) (bit0 1)))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 / bit0 1 = 1)) (div_self two_ne_zero two_ne_top))) (Eq.refl 1)))

theorem add_halves (a : ennreal) : a / bit0 1 + a / bit0 1 = a := sorry

@[simp] theorem div_zero_iff {a : ennreal} {b : ennreal} : a / b = 0 ↔ a = 0 ∨ b = ⊤ := sorry

@[simp] theorem div_pos_iff {a : ennreal} {b : ennreal} : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤ := sorry

theorem half_pos {a : ennreal} (h : 0 < a) : 0 < a / bit0 1 := sorry

theorem one_half_lt_one : bit0 1⁻¹ < 1 :=
  iff.mpr inv_lt_one one_lt_two

theorem half_lt_self {a : ennreal} (hz : a ≠ 0) (ht : a ≠ ⊤) : a / bit0 1 < a := sorry

theorem sub_half {a : ennreal} (h : a ≠ ⊤) : a - a / bit0 1 = a / bit0 1 := sorry

theorem one_sub_inv_two : 1 - (bit0 1⁻¹) = (bit0 1⁻¹) := sorry

theorem exists_inv_nat_lt {a : ennreal} (h : a ≠ 0) : ∃ (n : ℕ), ↑n⁻¹ < a := sorry

theorem exists_nat_pos_mul_gt {a : ennreal} {b : ennreal} (ha : a ≠ 0) (hb : b ≠ ⊤) : ∃ (n : ℕ), ∃ (H : n > 0), b < ↑n * a := sorry

theorem exists_nat_mul_gt {a : ennreal} {b : ennreal} (ha : a ≠ 0) (hb : b ≠ ⊤) : ∃ (n : ℕ), b < ↑n * a :=
  Exists.imp (fun (n : ℕ) => Exists.snd) (exists_nat_pos_mul_gt ha hb)

theorem exists_nat_pos_inv_mul_lt {a : ennreal} {b : ennreal} (ha : a ≠ ⊤) (hb : b ≠ 0) : ∃ (n : ℕ), ∃ (H : n > 0), ↑n⁻¹ * a < b := sorry

theorem exists_nnreal_pos_mul_lt {a : ennreal} {b : ennreal} (ha : a ≠ ⊤) (hb : b ≠ 0) : ∃ (n : nnreal), ∃ (H : n > 0), ↑n * a < b := sorry

theorem to_real_add {a : ennreal} {b : ennreal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : ennreal.to_real (a + b) = ennreal.to_real a + ennreal.to_real b := sorry

theorem to_real_add_le {a : ennreal} {b : ennreal} : ennreal.to_real (a + b) ≤ ennreal.to_real a + ennreal.to_real b := sorry

theorem of_real_add {p : ℝ} {q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : ennreal.of_real (p + q) = ennreal.of_real p + ennreal.of_real q := sorry

theorem of_real_add_le {p : ℝ} {q : ℝ} : ennreal.of_real (p + q) ≤ ennreal.of_real p + ennreal.of_real q :=
  iff.mpr coe_le_coe nnreal.of_real_add_le

@[simp] theorem to_real_le_to_real {a : ennreal} {b : ennreal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : ennreal.to_real a ≤ ennreal.to_real b ↔ a ≤ b := sorry

@[simp] theorem to_real_lt_to_real {a : ennreal} {b : ennreal} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : ennreal.to_real a < ennreal.to_real b ↔ a < b := sorry

theorem to_real_max {a : ennreal} {b : ennreal} (hr : a ≠ ⊤) (hp : b ≠ ⊤) : ennreal.to_real (max a b) = max (ennreal.to_real a) (ennreal.to_real b) := sorry

theorem to_nnreal_pos_iff {a : ennreal} : 0 < ennreal.to_nnreal a ↔ 0 < a ∧ a ≠ ⊤ := sorry

theorem to_real_pos_iff {a : ennreal} : 0 < ennreal.to_real a ↔ 0 < a ∧ a ≠ ⊤ :=
  iff.trans nnreal.coe_pos to_nnreal_pos_iff

theorem of_real_le_of_real {p : ℝ} {q : ℝ} (h : p ≤ q) : ennreal.of_real p ≤ ennreal.of_real q := sorry

theorem of_real_le_of_le_to_real {a : ℝ} {b : ennreal} (h : a ≤ ennreal.to_real b) : ennreal.of_real a ≤ b :=
  has_le.le.trans (of_real_le_of_real h) of_real_to_real_le

@[simp] theorem of_real_le_of_real_iff {p : ℝ} {q : ℝ} (h : 0 ≤ q) : ennreal.of_real p ≤ ennreal.of_real q ↔ p ≤ q := sorry

@[simp] theorem of_real_lt_of_real_iff {p : ℝ} {q : ℝ} (h : 0 < q) : ennreal.of_real p < ennreal.of_real q ↔ p < q := sorry

theorem of_real_lt_of_real_iff_of_nonneg {p : ℝ} {q : ℝ} (hp : 0 ≤ p) : ennreal.of_real p < ennreal.of_real q ↔ p < q := sorry

@[simp] theorem of_real_pos {p : ℝ} : 0 < ennreal.of_real p ↔ 0 < p := sorry

@[simp] theorem of_real_eq_zero {p : ℝ} : ennreal.of_real p = 0 ↔ p ≤ 0 := sorry

theorem of_real_le_iff_le_to_real {a : ℝ} {b : ennreal} (hb : b ≠ ⊤) : ennreal.of_real a ≤ b ↔ a ≤ ennreal.to_real b := sorry

theorem of_real_lt_iff_lt_to_real {a : ℝ} {b : ennreal} (ha : 0 ≤ a) (hb : b ≠ ⊤) : ennreal.of_real a < b ↔ a < ennreal.to_real b := sorry

theorem le_of_real_iff_to_real_le {a : ennreal} {b : ℝ} (ha : a ≠ ⊤) (hb : 0 ≤ b) : a ≤ ennreal.of_real b ↔ ennreal.to_real a ≤ b := sorry

theorem to_real_le_of_le_of_real {a : ennreal} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ennreal.of_real b) : ennreal.to_real a ≤ b :=
  (fun (ha : a ≠ ⊤) => iff.mp (le_of_real_iff_to_real_le ha hb) h) (ne_top_of_le_ne_top of_real_ne_top h)

theorem lt_of_real_iff_to_real_lt {a : ennreal} {b : ℝ} (ha : a ≠ ⊤) : a < ennreal.of_real b ↔ ennreal.to_real a < b := sorry

theorem of_real_mul {p : ℝ} {q : ℝ} (hp : 0 ≤ p) : ennreal.of_real (p * q) = ennreal.of_real p * ennreal.of_real q := sorry

theorem of_real_inv_of_pos {x : ℝ} (hx : 0 < x) : ennreal.of_real x⁻¹ = ennreal.of_real (x⁻¹) := sorry

theorem of_real_div_of_pos {x : ℝ} {y : ℝ} (hy : 0 < y) : ennreal.of_real (x / y) = ennreal.of_real x / ennreal.of_real y := sorry

theorem to_real_of_real_mul (c : ℝ) (a : ennreal) (h : 0 ≤ c) : ennreal.to_real (ennreal.of_real c * a) = c * ennreal.to_real a := sorry

@[simp] theorem to_nnreal_mul_top (a : ennreal) : ennreal.to_nnreal (a * ⊤) = 0 := sorry

@[simp] theorem to_nnreal_top_mul (a : ennreal) : ennreal.to_nnreal (⊤ * a) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ennreal.to_nnreal (⊤ * a) = 0)) (mul_comm ⊤ a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ennreal.to_nnreal (a * ⊤) = 0)) (to_nnreal_mul_top a))) (Eq.refl 0))

@[simp] theorem to_real_mul_top (a : ennreal) : ennreal.to_real (a * ⊤) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ennreal.to_real (a * ⊤) = 0)) (to_real.equations._eqn_1 (a * ⊤))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(ennreal.to_nnreal (a * ⊤)) = 0)) (to_nnreal_mul_top a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑0 = 0)) nnreal.coe_zero)) (Eq.refl 0)))

@[simp] theorem to_real_top_mul (a : ennreal) : ennreal.to_real (⊤ * a) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ennreal.to_real (⊤ * a) = 0)) (mul_comm ⊤ a))) (to_real_mul_top a)

theorem to_real_eq_to_real {a : ennreal} {b : ennreal} (ha : a < ⊤) (hb : b < ⊤) : ennreal.to_real a = ennreal.to_real b ↔ a = b := sorry

/-- `ennreal.to_nnreal` as a `monoid_hom`. -/
def to_nnreal_hom : ennreal →* nnreal :=
  monoid_hom.mk ennreal.to_nnreal sorry sorry

theorem to_nnreal_mul {a : ennreal} {b : ennreal} : ennreal.to_nnreal (a * b) = ennreal.to_nnreal a * ennreal.to_nnreal b :=
  monoid_hom.map_mul to_nnreal_hom a b

theorem to_nnreal_pow (a : ennreal) (n : ℕ) : ennreal.to_nnreal (a ^ n) = ennreal.to_nnreal a ^ n :=
  monoid_hom.map_pow to_nnreal_hom a n

theorem to_nnreal_prod {ι : Type u_1} {s : finset ι} {f : ι → ennreal} : ennreal.to_nnreal (finset.prod s fun (i : ι) => f i) = finset.prod s fun (i : ι) => ennreal.to_nnreal (f i) :=
  monoid_hom.map_prod to_nnreal_hom (fun (i : ι) => f i) s

/-- `ennreal.to_real` as a `monoid_hom`. -/
def to_real_hom : ennreal →* ℝ :=
  monoid_hom.comp (↑nnreal.to_real_hom) to_nnreal_hom

theorem to_real_mul {a : ennreal} {b : ennreal} : ennreal.to_real (a * b) = ennreal.to_real a * ennreal.to_real b :=
  monoid_hom.map_mul to_real_hom a b

theorem to_real_pow (a : ennreal) (n : ℕ) : ennreal.to_real (a ^ n) = ennreal.to_real a ^ n :=
  monoid_hom.map_pow to_real_hom a n

theorem to_real_prod {ι : Type u_1} {s : finset ι} {f : ι → ennreal} : ennreal.to_real (finset.prod s fun (i : ι) => f i) = finset.prod s fun (i : ι) => ennreal.to_real (f i) :=
  monoid_hom.map_prod to_real_hom (fun (i : ι) => f i) s

theorem of_real_prod_of_nonneg {α : Type u_1} {s : finset α} {f : α → ℝ} (hf : ∀ (i : α), i ∈ s → 0 ≤ f i) : ennreal.of_real (finset.prod s fun (i : α) => f i) = finset.prod s fun (i : α) => ennreal.of_real (f i) := sorry

theorem infi_add {a : ennreal} {ι : Sort u_3} {f : ι → ennreal} : infi f + a = infi fun (i : ι) => f i + a :=
  le_antisymm (le_infi fun (i : ι) => add_le_add (infi_le f i) (le_refl a))
    (iff.mp ennreal.sub_le_iff_le_add
      (le_infi fun (i : ι) => iff.mpr ennreal.sub_le_iff_le_add (infi_le (fun (i : ι) => f i + a) i)))

theorem supr_sub {a : ennreal} {ι : Sort u_3} {f : ι → ennreal} : (supr fun (i : ι) => f i) - a = supr fun (i : ι) => f i - a := sorry

theorem sub_infi {a : ennreal} {ι : Sort u_3} {f : ι → ennreal} : (a - infi fun (i : ι) => f i) = supr fun (i : ι) => a - f i := sorry

theorem Inf_add {a : ennreal} {s : set ennreal} : Inf s + a = infi fun (b : ennreal) => infi fun (H : b ∈ s) => b + a := sorry

theorem add_infi {ι : Sort u_3} {f : ι → ennreal} {a : ennreal} : a + infi f = infi fun (b : ι) => a + f b := sorry

theorem infi_add_infi {ι : Sort u_3} {f : ι → ennreal} {g : ι → ennreal} (h : ∀ (i j : ι), ∃ (k : ι), f k + g k ≤ f i + g j) : infi f + infi g = infi fun (a : ι) => f a + g a := sorry

theorem infi_sum {α : Type u_1} {ι : Sort u_3} {f : ι → α → ennreal} {s : finset α} [Nonempty ι] (h : ∀ (t : finset α) (i j : ι), ∃ (k : ι), ∀ (a : α), a ∈ t → f k a ≤ f i a ∧ f k a ≤ f j a) : (infi fun (i : ι) => finset.sum s fun (a : α) => f i a) = finset.sum s fun (a : α) => infi fun (i : ι) => f i a := sorry

theorem infi_mul {ι : Sort u_1} [Nonempty ι] {f : ι → ennreal} {x : ennreal} (h : x ≠ ⊤) : infi f * x = infi fun (i : ι) => f i * x := sorry

theorem mul_infi {ι : Sort u_1} [Nonempty ι] {f : ι → ennreal} {x : ennreal} (h : x ≠ ⊤) : x * infi f = infi fun (i : ι) => x * f i := sorry

/-! `supr_mul`, `mul_supr` and variants are in `topology.instances.ennreal`. -/

theorem supr_coe_nat : (supr fun (n : ℕ) => ↑n) = ⊤ :=
  iff.mpr (supr_eq_top fun (n : ℕ) => ↑n)
    fun (b : ennreal) (hb : b < ⊤) => ennreal.exists_nat_gt (iff.mp lt_top_iff_ne_top hb)

/-- `le_of_add_le_add_left` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds in `ennreal` with the additional assumption that `a < ∞`. -/
theorem le_of_add_le_add_left {a : ennreal} {b : ennreal} {c : ennreal} : a < ⊤ → a + b ≤ a + c → b ≤ c := sorry

