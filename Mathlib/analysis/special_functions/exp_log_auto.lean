/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.complex.exponential
import Mathlib.analysis.calculus.mean_value
import Mathlib.measure_theory.borel_space
import Mathlib.analysis.complex.real_deriv
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Complex and real exponential, real logarithm

## Main statements

This file establishes the basic analytical properties of the complex and real exponential functions
(continuity, differentiability, computation of the derivative).

It also contains the definition of the real logarithm function (as the inverse of the
exponential on `(0, +∞)`, extended to `ℝ` by setting `log (-x) = log x`) and its basic
properties (continuity, differentiability, formula for the derivative).

The complex logarithm is *not* defined in this file as it relies on trigonometric functions. See
instead `trigonometric.lean`.

## Tags

exp, log
-/

namespace complex


/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
theorem has_deriv_at_exp (x : ℂ) : has_deriv_at exp (exp x) x := sorry

theorem differentiable_exp : differentiable ℂ exp :=
  fun (x : ℂ) => has_deriv_at.differentiable_at (has_deriv_at_exp x)

theorem differentiable_at_exp {x : ℂ} : differentiable_at ℂ exp x := differentiable_exp x

@[simp] theorem deriv_exp : deriv exp = exp :=
  funext fun (x : ℂ) => has_deriv_at.deriv (has_deriv_at_exp x)

@[simp] theorem iter_deriv_exp (n : ℕ) : nat.iterate deriv n exp = exp := sorry

theorem continuous_exp : continuous exp := differentiable.continuous differentiable_exp

theorem times_cont_diff_exp {n : with_top ℕ} : times_cont_diff ℂ n exp := sorry

theorem measurable_exp : measurable exp := continuous.measurable continuous_exp

end complex


theorem has_deriv_at.cexp {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} (hf : has_deriv_at f f' x) :
    has_deriv_at (fun (x : ℂ) => complex.exp (f x)) (complex.exp (f x) * f') x :=
  has_deriv_at.comp x (complex.has_deriv_at_exp (f x)) hf

theorem has_deriv_within_at.cexp {f : ℂ → ℂ} {f' : ℂ} {x : ℂ} {s : set ℂ}
    (hf : has_deriv_within_at f f' s x) :
    has_deriv_within_at (fun (x : ℂ) => complex.exp (f x)) (complex.exp (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (complex.has_deriv_at_exp (f x)) hf

theorem deriv_within_cexp {f : ℂ → ℂ} {x : ℂ} {s : set ℂ} (hf : differentiable_within_at ℂ f s x)
    (hxs : unique_diff_within_at ℂ s x) :
    deriv_within (fun (x : ℂ) => complex.exp (f x)) s x = complex.exp (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within
    (has_deriv_within_at.cexp (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_cexp {f : ℂ → ℂ} {x : ℂ} (hc : differentiable_at ℂ f x) :
    deriv (fun (x : ℂ) => complex.exp (f x)) x = complex.exp (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.cexp (differentiable_at.has_deriv_at hc))

theorem measurable.cexp {α : Type u_1} [measurable_space α] {f : α → ℂ} (hf : measurable f) :
    measurable fun (x : α) => complex.exp (f x) :=
  measurable.comp complex.measurable_exp hf

theorem has_fderiv_within_at.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {f' : continuous_linear_map ℂ E ℂ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) :
    has_fderiv_within_at (fun (x : E) => complex.exp (f x)) (complex.exp (f x) • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (complex.has_deriv_at_exp (f x)) hf

theorem has_fderiv_at.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {f' : continuous_linear_map ℂ E ℂ} {x : E} (hf : has_fderiv_at f f' x) :
    has_fderiv_at (fun (x : E) => complex.exp (f x)) (complex.exp (f x) • f') x :=
  iff.mp has_fderiv_within_at_univ
    (has_fderiv_within_at.cexp (has_fderiv_at.has_fderiv_within_at hf))

theorem differentiable_within_at.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {x : E} {s : set E} (hf : differentiable_within_at ℂ f s x) :
    differentiable_within_at ℂ (fun (x : E) => complex.exp (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.cexp (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E]
    {f : E → ℂ} {x : E} (hc : differentiable_at ℂ f x) :
    differentiable_at ℂ (fun (x : E) => complex.exp (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.cexp (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {s : set E} (hc : differentiable_on ℂ f s) :
    differentiable_on ℂ (fun (x : E) => complex.exp (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.cexp (hc x h)

@[simp] theorem differentiable.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    (hc : differentiable ℂ f) : differentiable ℂ fun (x : E) => complex.exp (f x) :=
  fun (x : E) => differentiable_at.cexp (hc x)

theorem times_cont_diff.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {n : with_top ℕ} (h : times_cont_diff ℂ n f) :
    times_cont_diff ℂ n fun (x : E) => complex.exp (f x) :=
  times_cont_diff.comp complex.times_cont_diff_exp h

theorem times_cont_diff_at.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℂ n f x) :
    times_cont_diff_at ℂ n (fun (x : E) => complex.exp (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at complex.times_cont_diff_exp) hf

theorem times_cont_diff_on.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E] {f : E → ℂ}
    {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℂ n f s) :
    times_cont_diff_on ℂ n (fun (x : E) => complex.exp (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on complex.times_cont_diff_exp hf

theorem times_cont_diff_within_at.cexp {E : Type u_1} [normed_group E] [normed_space ℂ E]
    {f : E → ℂ} {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℂ n f s x) :
    times_cont_diff_within_at ℂ n (fun (x : E) => complex.exp (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x
    (times_cont_diff.times_cont_diff_at complex.times_cont_diff_exp) hf

namespace real


theorem has_deriv_at_exp (x : ℝ) : has_deriv_at exp (exp x) x :=
  has_deriv_at.real_of_complex (complex.has_deriv_at_exp ↑x)

theorem times_cont_diff_exp {n : with_top ℕ} : times_cont_diff ℝ n exp :=
  times_cont_diff.real_of_complex complex.times_cont_diff_exp

theorem differentiable_exp : differentiable ℝ exp :=
  fun (x : ℝ) => has_deriv_at.differentiable_at (has_deriv_at_exp x)

theorem differentiable_at_exp {x : ℝ} : differentiable_at ℝ exp x := differentiable_exp x

@[simp] theorem deriv_exp : deriv exp = exp :=
  funext fun (x : ℝ) => has_deriv_at.deriv (has_deriv_at_exp x)

@[simp] theorem iter_deriv_exp (n : ℕ) : nat.iterate deriv n exp = exp := sorry

theorem continuous_exp : continuous exp := differentiable.continuous differentiable_exp

theorem measurable_exp : measurable exp := continuous.measurable continuous_exp

end real


/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

theorem has_deriv_at.exp {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} (hf : has_deriv_at f f' x) :
    has_deriv_at (fun (x : ℝ) => real.exp (f x)) (real.exp (f x) * f') x :=
  has_deriv_at.comp x (real.has_deriv_at_exp (f x)) hf

theorem has_deriv_within_at.exp {f : ℝ → ℝ} {f' : ℝ} {x : ℝ} {s : set ℝ}
    (hf : has_deriv_within_at f f' s x) :
    has_deriv_within_at (fun (x : ℝ) => real.exp (f x)) (real.exp (f x) * f') s x :=
  has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_exp (f x)) hf

theorem deriv_within_exp {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x)
    (hxs : unique_diff_within_at ℝ s x) :
    deriv_within (fun (x : ℝ) => real.exp (f x)) s x = real.exp (f x) * deriv_within f s x :=
  has_deriv_within_at.deriv_within
    (has_deriv_within_at.exp (differentiable_within_at.has_deriv_within_at hf)) hxs

@[simp] theorem deriv_exp {f : ℝ → ℝ} {x : ℝ} (hc : differentiable_at ℝ f x) :
    deriv (fun (x : ℝ) => real.exp (f x)) x = real.exp (f x) * deriv f x :=
  has_deriv_at.deriv (has_deriv_at.exp (differentiable_at.has_deriv_at hc))

/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

theorem measurable.exp {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) :
    measurable fun (x : α) => real.exp (f x) :=
  measurable.comp real.measurable_exp hf

theorem times_cont_diff.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {n : with_top ℕ} (hf : times_cont_diff ℝ n f) :
    times_cont_diff ℝ n fun (x : E) => real.exp (f x) :=
  times_cont_diff.comp real.times_cont_diff_exp hf

theorem times_cont_diff_at.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} {n : with_top ℕ} (hf : times_cont_diff_at ℝ n f x) :
    times_cont_diff_at ℝ n (fun (x : E) => real.exp (f x)) x :=
  times_cont_diff_at.comp x (times_cont_diff.times_cont_diff_at real.times_cont_diff_exp) hf

theorem times_cont_diff_on.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {s : set E} {n : with_top ℕ} (hf : times_cont_diff_on ℝ n f s) :
    times_cont_diff_on ℝ n (fun (x : E) => real.exp (f x)) s :=
  times_cont_diff.comp_times_cont_diff_on real.times_cont_diff_exp hf

theorem times_cont_diff_within_at.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} {s : set E} {n : with_top ℕ} (hf : times_cont_diff_within_at ℝ n f s x) :
    times_cont_diff_within_at ℝ n (fun (x : E) => real.exp (f x)) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x
    (times_cont_diff.times_cont_diff_at real.times_cont_diff_exp) hf

theorem has_fderiv_within_at.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {f' : continuous_linear_map ℝ E ℝ} {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) :
    has_fderiv_within_at (fun (x : E) => real.exp (f x)) (real.exp (f x) • f') s x :=
  sorry

theorem has_fderiv_at.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {f' : continuous_linear_map ℝ E ℝ} {x : E} (hf : has_fderiv_at f f' x) :
    has_fderiv_at (fun (x : E) => real.exp (f x)) (real.exp (f x) • f') x :=
  iff.mp has_fderiv_within_at_univ
    (has_fderiv_within_at.exp (has_fderiv_at.has_fderiv_within_at hf))

theorem differentiable_within_at.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) :
    differentiable_within_at ℝ (fun (x : E) => real.exp (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.exp (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} (hc : differentiable_at ℝ f x) :
    differentiable_at ℝ (fun (x : E) => real.exp (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.exp (differentiable_at.has_fderiv_at hc))

theorem differentiable_on.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {s : set E} (hc : differentiable_on ℝ f s) :
    differentiable_on ℝ (fun (x : E) => real.exp (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.exp (hc x h)

@[simp] theorem differentiable.exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    (hc : differentiable ℝ f) : differentiable ℝ fun (x : E) => real.exp (f x) :=
  fun (x : E) => differentiable_at.exp (hc x)

theorem fderiv_within_exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E}
    {s : set E} (hf : differentiable_within_at ℝ f s x) (hxs : unique_diff_within_at ℝ s x) :
    fderiv_within ℝ (fun (x : E) => real.exp (f x)) s x = real.exp (f x) • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.exp (differentiable_within_at.has_fderiv_within_at hf)) hxs

@[simp] theorem fderiv_exp {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E}
    (hc : differentiable_at ℝ f x) :
    fderiv ℝ (fun (x : E) => real.exp (f x)) x = real.exp (f x) • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.exp (differentiable_at.has_fderiv_at hc))

namespace real


/-- The real exponential function tends to `+∞` at `+∞`. -/
theorem tendsto_exp_at_top : filter.tendsto exp filter.at_top filter.at_top :=
  filter.tendsto_at_top_mono' filter.at_top
    (iff.mpr filter.eventually_at_top
      (Exists.intro 0 fun (x : ℝ) (hx : x ≥ 0) => add_one_le_exp_of_nonneg hx))
    (filter.tendsto_at_top_add_const_right filter.at_top 1 filter.tendsto_id)

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
theorem tendsto_exp_neg_at_top_nhds_0 :
    filter.tendsto (fun (x : ℝ) => exp (-x)) filter.at_top (nhds 0) :=
  filter.tendsto.congr (fun (x : ℝ) => Eq.symm (exp_neg x))
    (filter.tendsto.comp tendsto_inv_at_top_zero tendsto_exp_at_top)

/-- The real exponential function tends to `1` at `0`. -/
theorem tendsto_exp_nhds_0_nhds_1 : filter.tendsto exp (nhds 0) (nhds 1) := sorry

theorem tendsto_exp_at_bot : filter.tendsto exp filter.at_bot (nhds 0) :=
  filter.tendsto.congr (fun (x : ℝ) => congr_arg exp (neg_neg x))
    (filter.tendsto.comp tendsto_exp_neg_at_top_nhds_0 filter.tendsto_neg_at_bot_at_top)

theorem tendsto_exp_at_bot_nhds_within :
    filter.tendsto exp filter.at_bot (nhds_within 0 (set.Ioi 0)) :=
  iff.mpr filter.tendsto_inf
    { left := tendsto_exp_at_bot,
      right := iff.mpr filter.tendsto_principal (filter.eventually_of_forall exp_pos) }

/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def exp_order_iso : ℝ ≃o ↥(set.Ioi 0) :=
  strict_mono.order_iso_of_surjective (set.cod_restrict exp (set.Ioi 0) exp_pos) sorry sorry

@[simp] theorem coe_exp_order_iso_apply (x : ℝ) : ↑(coe_fn exp_order_iso x) = exp x := rfl

@[simp] theorem coe_comp_exp_order_iso : coe ∘ ⇑exp_order_iso = exp := rfl

@[simp] theorem range_exp : set.range exp = set.Ioi 0 := sorry

@[simp] theorem map_exp_at_top : filter.map exp filter.at_top = filter.at_top := sorry

@[simp] theorem comap_exp_at_top : filter.comap exp filter.at_top = filter.at_top := sorry

@[simp] theorem tendsto_exp_comp_at_top {α : Type u_1} {l : filter α} {f : α → ℝ} :
    filter.tendsto (fun (x : α) => exp (f x)) l filter.at_top ↔ filter.tendsto f l filter.at_top :=
  sorry

theorem tendsto_comp_exp_at_top {α : Type u_1} {l : filter α} {f : ℝ → α} :
    filter.tendsto (fun (x : ℝ) => f (exp x)) filter.at_top l ↔ filter.tendsto f filter.at_top l :=
  sorry

@[simp] theorem map_exp_at_bot : filter.map exp filter.at_bot = nhds_within 0 (set.Ioi 0) := sorry

theorem comap_exp_nhds_within_Ioi_zero :
    filter.comap exp (nhds_within 0 (set.Ioi 0)) = filter.at_bot :=
  sorry

theorem tendsto_comp_exp_at_bot {α : Type u_1} {l : filter α} {f : ℝ → α} :
    filter.tendsto (fun (x : ℝ) => f (exp x)) filter.at_bot l ↔
        filter.tendsto f (nhds_within 0 (set.Ioi 0)) l :=
  sorry

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
def log (x : ℝ) : ℝ :=
  dite (x = 0) (fun (hx : x = 0) => 0)
    fun (hx : ¬x = 0) => coe_fn (order_iso.symm exp_order_iso) { val := abs x, property := sorry }

theorem log_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    log x =
        coe_fn (order_iso.symm exp_order_iso) { val := abs x, property := iff.mpr abs_pos hx } :=
  dif_neg hx

theorem log_of_pos {x : ℝ} (hx : 0 < x) :
    log x = coe_fn (order_iso.symm exp_order_iso) { val := x, property := hx } :=
  sorry

theorem exp_log_eq_abs {x : ℝ} (hx : x ≠ 0) : exp (log x) = abs x := sorry

theorem exp_log {x : ℝ} (hx : 0 < x) : exp (log x) = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp (log x) = x)) (exp_log_eq_abs (has_lt.lt.ne' hx))))
    (abs_of_pos hx)

theorem exp_log_of_neg {x : ℝ} (hx : x < 0) : exp (log x) = -x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp (log x) = -x)) (exp_log_eq_abs (ne_of_lt hx))))
    (abs_of_neg hx)

@[simp] theorem log_exp (x : ℝ) : log (exp x) = x := exp_injective (exp_log (exp_pos x))

theorem surj_on_log : set.surj_on log (set.Ioi 0) set.univ :=
  fun (x : ℝ) (_x : x ∈ set.univ) => Exists.intro (exp x) { left := exp_pos x, right := log_exp x }

theorem log_surjective : function.surjective log := fun (x : ℝ) => Exists.intro (exp x) (log_exp x)

@[simp] theorem range_log : set.range log = set.univ := function.surjective.range_eq log_surjective

@[simp] theorem log_zero : log 0 = 0 := dif_pos rfl

@[simp] theorem log_one : log 1 = 0 :=
  exp_injective
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp (log 1) = exp 0)) (exp_log zero_lt_one)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 = exp 0)) exp_zero)) (Eq.refl 1)))

@[simp] theorem log_abs (x : ℝ) : log (abs x) = log x := sorry

@[simp] theorem log_neg_eq_log (x : ℝ) : log (-x) = log x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (log (-x) = log x)) (Eq.symm (log_abs x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (log (-x) = log (abs x))) (Eq.symm (log_abs (-x)))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (log (abs (-x)) = log (abs x))) (abs_neg x)))
        (Eq.refl (log (abs x)))))

theorem surj_on_log' : set.surj_on log (set.Iio 0) set.univ := sorry

theorem log_mul {x : ℝ} {y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y := sorry

@[simp] theorem log_inv (x : ℝ) : log (x⁻¹) = -log x := sorry

theorem log_le_log {x : ℝ} {y : ℝ} (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (log x ≤ log y ↔ x ≤ y)) (Eq.symm (propext exp_le_exp))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp (log x) ≤ exp (log y) ↔ x ≤ y)) (exp_log h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ exp (log y) ↔ x ≤ y)) (exp_log h₁)))
        (iff.refl (x ≤ y))))

theorem log_lt_log {x : ℝ} {y : ℝ} (hx : 0 < x) : x < y → log x < log y := sorry

theorem log_lt_log_iff {x : ℝ} {y : ℝ} (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (log x < log y ↔ x < y)) (Eq.symm (propext exp_lt_exp))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp (log x) < exp (log y) ↔ x < y)) (exp_log hx)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (x < exp (log y) ↔ x < y)) (exp_log hy)))
        (iff.refl (x < y))))

theorem log_pos_iff {x : ℝ} (hx : 0 < x) : 0 < log x ↔ 1 < x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < log x ↔ 1 < x)) (Eq.symm log_one)))
    (log_lt_log_iff zero_lt_one hx)

theorem log_pos {x : ℝ} (hx : 1 < x) : 0 < log x :=
  iff.mpr (log_pos_iff (lt_trans zero_lt_one hx)) hx

theorem log_neg_iff {x : ℝ} (h : 0 < x) : log x < 0 ↔ x < 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (log x < 0 ↔ x < 1)) (Eq.symm log_one)))
    (log_lt_log_iff h zero_lt_one)

theorem log_neg {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : log x < 0 := iff.mpr (log_neg_iff h0) h1

theorem log_nonneg_iff {x : ℝ} (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ log x ↔ 1 ≤ x)) (Eq.symm (propext not_lt))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬log x < 0 ↔ 1 ≤ x)) (propext (log_neg_iff hx))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬x < 1 ↔ 1 ≤ x)) (propext not_lt))) (iff.refl (1 ≤ x))))

theorem log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log x :=
  iff.mpr (log_nonneg_iff (has_lt.lt.trans_le zero_lt_one hx)) hx

theorem log_nonpos_iff {x : ℝ} (hx : 0 < x) : log x ≤ 0 ↔ x ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (log x ≤ 0 ↔ x ≤ 1)) (Eq.symm (propext not_lt))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬0 < log x ↔ x ≤ 1)) (propext (log_pos_iff hx))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬1 < x ↔ x ≤ 1)) (propext not_lt))) (iff.refl (x ≤ 1))))

theorem log_nonpos_iff' {x : ℝ} (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 := sorry

theorem log_nonpos {x : ℝ} (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
  iff.mpr (log_nonpos_iff' hx) h'x

theorem strict_mono_incr_on_log : strict_mono_incr_on log (set.Ioi 0) :=
  fun (x : ℝ) (hx : x ∈ set.Ioi 0) (y : ℝ) (hy : y ∈ set.Ioi 0) (hxy : x < y) => log_lt_log hx hxy

theorem strict_mono_decr_on_log : strict_mono_decr_on log (set.Iio 0) := sorry

/-- The real logarithm function tends to `+∞` at `+∞`. -/
theorem tendsto_log_at_top : filter.tendsto log filter.at_top filter.at_top := sorry

theorem tendsto_log_nhds_within_zero :
    filter.tendsto log (nhds_within 0 (singleton 0ᶜ)) filter.at_bot :=
  sorry

theorem continuous_on_log : continuous_on log (singleton 0ᶜ) := sorry

theorem continuous_log' : continuous fun (x : Subtype fun (x : ℝ) => 0 < x) => log ↑x := sorry

theorem continuous_at_log {x : ℝ} (hx : x ≠ 0) : continuous_at log x :=
  continuous_within_at.continuous_at (continuous_on_log x hx)
    (mem_nhds_sets is_open_compl_singleton hx)

@[simp] theorem continuous_at_log_iff {x : ℝ} : continuous_at log x ↔ x ≠ 0 := sorry

theorem has_deriv_at_log_of_pos {x : ℝ} (hx : 0 < x) : has_deriv_at log (x⁻¹) x := sorry

theorem has_deriv_at_log {x : ℝ} (hx : x ≠ 0) : has_deriv_at log (x⁻¹) x := sorry

theorem differentiable_at_log {x : ℝ} (hx : x ≠ 0) : differentiable_at ℝ log x :=
  has_deriv_at.differentiable_at (has_deriv_at_log hx)

theorem differentiable_on_log : differentiable_on ℝ log (singleton 0ᶜ) :=
  fun (x : ℝ) (hx : x ∈ (singleton 0ᶜ)) =>
    differentiable_at.differentiable_within_at (differentiable_at_log hx)

@[simp] theorem differentiable_at_log_iff {x : ℝ} : differentiable_at ℝ log x ↔ x ≠ 0 :=
  { mp :=
      fun (h : differentiable_at ℝ log x) =>
        iff.mp continuous_at_log_iff (differentiable_at.continuous_at h),
    mpr := differentiable_at_log }

theorem deriv_log (x : ℝ) : deriv log x = (x⁻¹) := sorry

@[simp] theorem deriv_log' : deriv log = has_inv.inv := funext deriv_log

theorem measurable_log : measurable log :=
  measurable_of_measurable_on_compl_singleton 0
    (continuous.measurable (iff.mp continuous_on_iff_continuous_restrict continuous_on_log))

theorem times_cont_diff_on_log {n : with_top ℕ} : times_cont_diff_on ℝ n log (singleton 0ᶜ) := sorry

theorem times_cont_diff_at_log {x : ℝ} (hx : x ≠ 0) {n : with_top ℕ} :
    times_cont_diff_at ℝ n log x :=
  times_cont_diff_within_at.times_cont_diff_at (times_cont_diff_on_log x hx)
    (mem_nhds_sets is_open_compl_singleton hx)

end real


theorem filter.tendsto.log {α : Type u_1} {f : α → ℝ} {l : filter α} {x : ℝ}
    (h : filter.tendsto f l (nhds x)) (hx : x ≠ 0) :
    filter.tendsto (fun (x : α) => real.log (f x)) l (nhds (real.log x)) :=
  filter.tendsto.comp (continuous_at.tendsto (real.continuous_at_log hx)) h

theorem continuous.log {α : Type u_1} [topological_space α] {f : α → ℝ} (hf : continuous f)
    (h₀ : ∀ (x : α), f x ≠ 0) : continuous fun (x : α) => real.log (f x) :=
  continuous_on.comp_continuous real.continuous_on_log hf h₀

theorem continuous_at.log {α : Type u_1} [topological_space α] {f : α → ℝ} {a : α}
    (hf : continuous_at f a) (h₀ : f a ≠ 0) : continuous_at (fun (x : α) => real.log (f x)) a :=
  filter.tendsto.log hf h₀

theorem continuous_within_at.log {α : Type u_1} [topological_space α] {f : α → ℝ} {s : set α}
    {a : α} (hf : continuous_within_at f s a) (h₀ : f a ≠ 0) :
    continuous_within_at (fun (x : α) => real.log (f x)) s a :=
  filter.tendsto.log hf h₀

theorem continuous_on.log {α : Type u_1} [topological_space α] {f : α → ℝ} {s : set α}
    (hf : continuous_on f s) (h₀ : ∀ (x : α), x ∈ s → f x ≠ 0) :
    continuous_on (fun (x : α) => real.log (f x)) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.log (hf x hx) (h₀ x hx)

theorem measurable.log {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) :
    measurable fun (x : α) => real.log (f x) :=
  measurable.comp real.measurable_log hf

theorem has_deriv_within_at.log {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} {s : set ℝ}
    (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
    has_deriv_within_at (fun (y : ℝ) => real.log (f y)) (f' / f x) s x :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (has_deriv_within_at (fun (y : ℝ) => real.log (f y)) (f' / f x) s x))
        div_eq_inv_mul))
    (has_deriv_at.comp_has_deriv_within_at x (real.has_deriv_at_log hx) hf)

theorem has_deriv_at.log {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
    has_deriv_at (fun (y : ℝ) => real.log (f y)) (f' / f x) x :=
  sorry

theorem deriv_within.log {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x)
    (hx : f x ≠ 0) (hxs : unique_diff_within_at ℝ s x) :
    deriv_within (fun (x : ℝ) => real.log (f x)) s x = deriv_within f s x / f x :=
  has_deriv_within_at.deriv_within
    (has_deriv_within_at.log (differentiable_within_at.has_deriv_within_at hf) hx) hxs

@[simp] theorem deriv.log {f : ℝ → ℝ} {x : ℝ} (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
    deriv (fun (x : ℝ) => real.log (f x)) x = deriv f x / f x :=
  has_deriv_at.deriv (has_deriv_at.log (differentiable_at.has_deriv_at hf) hx)

theorem has_fderiv_within_at.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} {f' : continuous_linear_map ℝ E ℝ} {s : set E} (hf : has_fderiv_within_at f f' s x)
    (hx : f x ≠ 0) : has_fderiv_within_at (fun (x : E) => real.log (f x)) (f x⁻¹ • f') s x :=
  has_deriv_at.comp_has_fderiv_within_at x (real.has_deriv_at_log hx) hf

theorem has_fderiv_at.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E}
    {f' : continuous_linear_map ℝ E ℝ} (hf : has_fderiv_at f f' x) (hx : f x ≠ 0) :
    has_fderiv_at (fun (x : E) => real.log (f x)) (f x⁻¹ • f') x :=
  has_deriv_at.comp_has_fderiv_at x (real.has_deriv_at_log hx) hf

theorem differentiable_within_at.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} {s : set E} (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
    differentiable_within_at ℝ (fun (x : E) => real.log (f x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.log (differentiable_within_at.has_fderiv_within_at hf) hx)

@[simp] theorem differentiable_at.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {x : E} (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
    differentiable_at ℝ (fun (x : E) => real.log (f x)) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.log (differentiable_at.has_fderiv_at hf) hx)

theorem differentiable_on.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    {s : set E} (hf : differentiable_on ℝ f s) (hx : ∀ (x : E), x ∈ s → f x ≠ 0) :
    differentiable_on ℝ (fun (x : E) => real.log (f x)) s :=
  fun (x : E) (h : x ∈ s) => differentiable_within_at.log (hf x h) (hx x h)

@[simp] theorem differentiable.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ}
    (hf : differentiable ℝ f) (hx : ∀ (x : E), f x ≠ 0) :
    differentiable ℝ fun (x : E) => real.log (f x) :=
  fun (x : E) => differentiable_at.log (hf x) (hx x)

theorem fderiv_within.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E}
    {s : set E} (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
    (hxs : unique_diff_within_at ℝ s x) :
    fderiv_within ℝ (fun (x : E) => real.log (f x)) s x = f x⁻¹ • fderiv_within ℝ f s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.log (differentiable_within_at.has_fderiv_within_at hf) hx) hxs

@[simp] theorem fderiv.log {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E}
    (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun (x : E) => real.log (f x)) x = f x⁻¹ • fderiv ℝ f x :=
  has_fderiv_at.fderiv (has_fderiv_at.log (differentiable_at.has_fderiv_at hf) hx)

namespace real


/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
theorem tendsto_exp_div_pow_at_top (n : ℕ) :
    filter.tendsto (fun (x : ℝ) => exp x / x ^ n) filter.at_top filter.at_top :=
  sorry

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
theorem tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) :
    filter.tendsto (fun (x : ℝ) => x ^ n * exp (-x)) filter.at_top (nhds 0) :=
  sorry

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
theorem tendsto_mul_exp_add_div_pow_at_top (b : ℝ) (c : ℝ) (n : ℕ) (hb : 0 < b) (hn : 1 ≤ n) :
    filter.tendsto (fun (x : ℝ) => (b * exp x + c) / x ^ n) filter.at_top filter.at_top :=
  sorry

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
theorem tendsto_div_pow_mul_exp_add_at_top (b : ℝ) (c : ℝ) (n : ℕ) (hb : 0 ≠ b) (hn : 1 ≤ n) :
    filter.tendsto (fun (x : ℝ) => x ^ n / (b * exp x + c)) filter.at_top (nhds 0) :=
  sorry

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : abs x < 1) (n : ℕ) :
    abs ((finset.sum (finset.range n) fun (i : ℕ) => x ^ (i + 1) / (↑i + 1)) + log (1 - x)) ≤
        abs x ^ (n + 1) / (1 - abs x) :=
  sorry

/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : abs x < 1) :
    has_sum (fun (n : ℕ) => x ^ (n + 1) / (↑n + 1)) (-log (1 - x)) :=
  sorry

end Mathlib