/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.multilinear
import Mathlib.ring_theory.power_series.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `times_cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
def formal_multilinear_series (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (E : Type u_2) [normed_group E] [normed_space 𝕜 E] (F : Type u_3) [normed_group F] [normed_space 𝕜 F]  :=
  (n : ℕ) → continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F

protected instance formal_multilinear_series.inhabited {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : Inhabited (formal_multilinear_series 𝕜 E F) :=
  { default := 0 }

/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/

protected instance formal_multilinear_series.module {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] : module 𝕜 (formal_multilinear_series 𝕜 E F) :=
  let _inst : (n : ℕ) → module 𝕜 (continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F) :=
    fun (n : ℕ) => continuous_multilinear_map.semimodule;
  pi.semimodule ℕ (fun (n : ℕ) => continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F) 𝕜

namespace formal_multilinear_series


/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) : formal_multilinear_series 𝕜 E (continuous_linear_map 𝕜 E F) :=
  fun (n : ℕ) => continuous_multilinear_map.curry_right (p (Nat.succ n))

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (q : formal_multilinear_series 𝕜 E (continuous_linear_map 𝕜 E F)) (z : F) : formal_multilinear_series 𝕜 E F :=
  sorry

/-- Killing the zeroth coefficient in a formal multilinear series -/
def remove_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) : formal_multilinear_series 𝕜 E F :=
  sorry

@[simp] theorem remove_zero_coeff_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) : remove_zero p 0 = 0 :=
  rfl

@[simp] theorem remove_zero_coeff_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) (n : ℕ) : remove_zero p (n + 1) = p (n + 1) :=
  rfl

theorem remove_zero_of_pos {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (h : 0 < n) : remove_zero p n = p n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (remove_zero p n = p n)) (Eq.symm (nat.succ_pred_eq_of_pos h))))
    (Eq.refl (remove_zero p (Nat.succ (Nat.pred n))))

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
theorem congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (p : formal_multilinear_series 𝕜 E F) {m : ℕ} {n : ℕ} {v : fin m → E} {w : fin n → E} (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v { val := i, property := him } = w { val := i, property := hin }) : coe_fn (p m) v = coe_fn (p n) w := sorry

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def comp_continuous_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (p : formal_multilinear_series 𝕜 F G) (u : continuous_linear_map 𝕜 E F) : formal_multilinear_series 𝕜 E G :=
  fun (n : ℕ) => continuous_multilinear_map.comp_continuous_linear_map (p n) fun (i : fin n) => u

@[simp] theorem comp_continuous_linear_map_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] (p : formal_multilinear_series 𝕜 F G) (u : continuous_linear_map 𝕜 E F) (n : ℕ) (v : fin n → E) : coe_fn (comp_continuous_linear_map p u n) v = coe_fn (p n) (⇑u ∘ v) :=
  rfl

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series, where `𝕜'` is a
normed algebra over `𝕜`. -/
@[simp] protected def restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {𝕜' : Type u_5} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] (p : formal_multilinear_series 𝕜' E F) : formal_multilinear_series 𝕜 E F :=
  fun (n : ℕ) => continuous_multilinear_map.restrict_scalars 𝕜 (p n)

