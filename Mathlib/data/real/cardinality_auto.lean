/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.set_theory.cardinal_ordinal
import Mathlib.analysis.specific_limits
import Mathlib.data.rat.denumerable
import Mathlib.data.set.intervals.image_preimage
import PostPort

namespace Mathlib

/-!
# The cardinality of the reals

This file shows that the real numbers have cardinality continuum, i.e. `#ℝ = 2^ω`.

We shows that `#ℝ ≤ 2^ω` by noting that every real number is determined by a Cauchy-sequence of the
form `ℕ → ℚ`, which has cardinality `2^ω`. To show that `#ℝ ≥ 2^ω` we define an injection from
`{0, 1} ^ ℕ` to `ℝ` with `f ↦ Σ n, f n * (1 / 3) ^ n`.

We conclude that all intervals with distinct endpoints have cardinality continuum.

## Main definitions

* `cardinal.cantor_function` is the function that sends `f` in `{0, 1} ^ ℕ` to `ℝ` by
  `f ↦ Σ' n, f n * (1 / 3) ^ n`

## Main statements

* `cardinal.mk_real : #ℝ = 2 ^ omega`: the reals have cardinality continuum.
* `cardinal.not_countable_real`: the universal set of real numbers is not countable. We can use this same
  proof to show that all the other sets in this file are not countable.
* 8 lemmas of the form `mk_Ixy_real` for `x,y ∈ {i,o,c}` state that intervals on the reals
  have cardinality continuum.

## Tags
continuum, cardinality, reals, cardinality of the reals
-/

namespace cardinal


/-- The body of the sum in `cantor_function`.
`cantor_function_aux c f n = c ^ n` if `f n = tt`;
`cantor_function_aux c f n = 0` if `f n = ff`. -/
def cantor_function_aux (c : ℝ) (f : ℕ → Bool) (n : ℕ) : ℝ :=
  cond (f n) (c ^ n) 0

@[simp] theorem cantor_function_aux_tt {c : ℝ} {f : ℕ → Bool} {n : ℕ} (h : f n = tt) : cantor_function_aux c f n = c ^ n := sorry

@[simp] theorem cantor_function_aux_ff {c : ℝ} {f : ℕ → Bool} {n : ℕ} (h : f n = false) : cantor_function_aux c f n = 0 := sorry

theorem cantor_function_aux_nonneg {c : ℝ} {f : ℕ → Bool} {n : ℕ} (h : 0 ≤ c) : 0 ≤ cantor_function_aux c f n := sorry

theorem cantor_function_aux_eq {c : ℝ} {f : ℕ → Bool} {g : ℕ → Bool} {n : ℕ} (h : f n = g n) : cantor_function_aux c f n = cantor_function_aux c g n := sorry

theorem cantor_function_aux_succ {c : ℝ} (f : ℕ → Bool) : (fun (n : ℕ) => cantor_function_aux c f (n + 1)) = fun (n : ℕ) => c * cantor_function_aux c (fun (n : ℕ) => f (n + 1)) n := sorry

theorem summable_cantor_function {c : ℝ} (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) : summable (cantor_function_aux c f) := sorry

/-- `cantor_function c (f : ℕ → bool)` is `Σ n, f n * c ^ n`, where `tt` is interpreted as `1` and
`ff` is interpreted as `0`. It is implemented using `cantor_function_aux`. -/
def cantor_function (c : ℝ) (f : ℕ → Bool) : ℝ :=
  tsum fun (n : ℕ) => cantor_function_aux c f n

theorem cantor_function_le {c : ℝ} {f : ℕ → Bool} {g : ℕ → Bool} (h1 : 0 ≤ c) (h2 : c < 1) (h3 : ∀ (n : ℕ), ↥(f n) → ↥(g n)) : cantor_function c f ≤ cantor_function c g := sorry

theorem cantor_function_succ {c : ℝ} (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) : cantor_function c f = cond (f 0) 1 0 + c * cantor_function c fun (n : ℕ) => f (n + 1) := sorry

/-- `cantor_function c` is strictly increasing with if `0 < c < 1/2`, if we endow `ℕ → bool` with a
lexicographic order. The lexicographic order doesn't exist for these infinitary products, so we
explicitly write out what it means. -/
theorem increasing_cantor_function {c : ℝ} (h1 : 0 < c) (h2 : c < 1 / bit0 1) {n : ℕ} {f : ℕ → Bool} {g : ℕ → Bool} (hn : ∀ (k : ℕ), k < n → f k = g k) (fn : f n = false) (gn : g n = tt) : cantor_function c f < cantor_function c g := sorry

/-- `cantor_function c` is injective if `0 < c < 1/2`. -/
theorem cantor_function_injective {c : ℝ} (h1 : 0 < c) (h2 : c < 1 / bit0 1) : function.injective (cantor_function c) := sorry

/-- The cardinality of the reals, as a type. -/
theorem mk_real : mk ℝ = bit0 1 ^ omega := sorry

/-- The cardinality of the reals, as a set. -/
theorem mk_univ_real : mk ↥set.univ = bit0 1 ^ omega :=
  eq.mpr (id (Eq._oldrec (Eq.refl (mk ↥set.univ = bit0 1 ^ omega)) mk_univ))
    (eq.mpr (id (Eq._oldrec (Eq.refl (mk ℝ = bit0 1 ^ omega)) mk_real)) (Eq.refl (bit0 1 ^ omega)))

/-- The reals are not countable. -/
theorem not_countable_real : ¬set.countable set.univ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬set.countable set.univ)) (propext (countable_iff set.univ))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬mk ↥set.univ ≤ omega)) (propext not_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (omega < mk ↥set.univ)) mk_univ_real)) (cantor omega)))

/-- The cardinality of the interval (a, ∞). -/
theorem mk_Ioi_real (a : ℝ) : mk ↥(set.Ioi a) = bit0 1 ^ omega := sorry

/-- The cardinality of the interval [a, ∞). -/
theorem mk_Ici_real (a : ℝ) : mk ↥(set.Ici a) = bit0 1 ^ omega :=
  le_antisymm (mk_real ▸ mk_set_le (set.Ici a)) (mk_Ioi_real a ▸ mk_le_mk_of_subset set.Ioi_subset_Ici_self)

/-- The cardinality of the interval (-∞, a). -/
theorem mk_Iio_real (a : ℝ) : mk ↥(set.Iio a) = bit0 1 ^ omega := sorry

/-- The cardinality of the interval (-∞, a]. -/
theorem mk_Iic_real (a : ℝ) : mk ↥(set.Iic a) = bit0 1 ^ omega :=
  le_antisymm (mk_real ▸ mk_set_le (set.Iic a)) (mk_Iio_real a ▸ mk_le_mk_of_subset set.Iio_subset_Iic_self)

/-- The cardinality of the interval (a, b). -/
theorem mk_Ioo_real {a : ℝ} {b : ℝ} (h : a < b) : mk ↥(set.Ioo a b) = bit0 1 ^ omega := sorry

/-- The cardinality of the interval [a, b). -/
theorem mk_Ico_real {a : ℝ} {b : ℝ} (h : a < b) : mk ↥(set.Ico a b) = bit0 1 ^ omega :=
  le_antisymm (mk_real ▸ mk_set_le (set.Ico a b)) (mk_Ioo_real h ▸ mk_le_mk_of_subset set.Ioo_subset_Ico_self)

/-- The cardinality of the interval [a, b]. -/
theorem mk_Icc_real {a : ℝ} {b : ℝ} (h : a < b) : mk ↥(set.Icc a b) = bit0 1 ^ omega :=
  le_antisymm (mk_real ▸ mk_set_le (set.Icc a b)) (mk_Ioo_real h ▸ mk_le_mk_of_subset set.Ioo_subset_Icc_self)

/-- The cardinality of the interval (a, b]. -/
theorem mk_Ioc_real {a : ℝ} {b : ℝ} (h : a < b) : mk ↥(set.Ioc a b) = bit0 1 ^ omega :=
  le_antisymm (mk_real ▸ mk_set_le (set.Ioc a b)) (mk_Ioo_real h ▸ mk_le_mk_of_subset set.Ioo_subset_Ioc_self)

