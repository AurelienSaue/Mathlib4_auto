/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.mean_value
import Mathlib.analysis.special_functions.exp_log
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwall_bound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `∥f a∥ ≤ δ`
and `∀ x ∈ [a, b), ∥f' x∥ ≤ K * ∥f x∥ + ε`, then for all `x ∈ [a, b]` we have `∥f x∥ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwall_bound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `∥f' x∥ ≤ K x * ∥f x∥ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/

/-! ### Technical lemmas about `gronwall_bound` -/

/-- Upper bound used in several Grönwall-like inequalities. -/
def gronwall_bound (δ : ℝ) (K : ℝ) (ε : ℝ) (x : ℝ) : ℝ :=
  ite (K = 0) (δ + ε * x) (δ * real.exp (K * x) + ε / K * (real.exp (K * x) - 1))

theorem gronwall_bound_K0 (δ : ℝ) (ε : ℝ) : gronwall_bound δ 0 ε = fun (x : ℝ) => δ + ε * x :=
  funext fun (x : ℝ) => if_pos rfl

theorem gronwall_bound_of_K_ne_0 {δ : ℝ} {K : ℝ} {ε : ℝ} (hK : K ≠ 0) : gronwall_bound δ K ε = fun (x : ℝ) => δ * real.exp (K * x) + ε / K * (real.exp (K * x) - 1) :=
  funext fun (x : ℝ) => if_neg hK

theorem has_deriv_at_gronwall_bound (δ : ℝ) (K : ℝ) (ε : ℝ) (x : ℝ) : has_deriv_at (gronwall_bound δ K ε) (K * gronwall_bound δ K ε x + ε) x := sorry

theorem has_deriv_at_gronwall_bound_shift (δ : ℝ) (K : ℝ) (ε : ℝ) (x : ℝ) (a : ℝ) : has_deriv_at (fun (y : ℝ) => gronwall_bound δ K ε (y - a)) (K * gronwall_bound δ K ε (x - a) + ε) x := sorry

theorem gronwall_bound_x0 (δ : ℝ) (K : ℝ) (ε : ℝ) : gronwall_bound δ K ε 0 = δ := sorry

theorem gronwall_bound_ε0 (δ : ℝ) (K : ℝ) (x : ℝ) : gronwall_bound δ K 0 x = δ * real.exp (K * x) := sorry

theorem gronwall_bound_ε0_δ0 (K : ℝ) (x : ℝ) : gronwall_bound 0 K 0 x = 0 := sorry

theorem gronwall_bound_continuous_ε (δ : ℝ) (K : ℝ) (x : ℝ) : continuous fun (ε : ℝ) => gronwall_bound δ K ε x := sorry

/-! ### Inequality and corollaries -/

/-- A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfies
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwall_bound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwall_bound_of_norm_deriv_right_le` for a version bounding `∥f x∥`,
`f : ℝ → E`. -/
theorem le_gronwall_bound_of_liminf_deriv_right_le {f : ℝ → ℝ} {f' : ℝ → ℝ} {δ : ℝ} {K : ℝ} {ε : ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ),
  x ∈ set.Ico a b →
    ∀ (r : ℝ), f' x < r → filter.frequently (fun (z : ℝ) => z - x⁻¹ * (f z - f x) < r) (nhds_within x (set.Ioi x))) (ha : f a ≤ δ) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → f' x ≤ K * f x + ε) (x : ℝ) (H : x ∈ set.Icc a b) : f x ≤ gronwall_bound δ K ε (x - a) := sorry

/-- A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `∥f a∥ ≤ δ`,
`∀ x ∈ [a, b), ∥f' x∥ ≤ K * ∥f x∥ + ε`, then `∥f x∥` is bounded by `gronwall_bound δ K ε (x - a)`
on `[a, b]`. -/
theorem norm_le_gronwall_bound_of_norm_deriv_right_le {E : Type u_1} [normed_group E] [normed_space ℝ E] {f : ℝ → E} {f' : ℝ → E} {δ : ℝ} {K : ℝ} {ε : ℝ} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (x : ℝ), x ∈ set.Ico a b → has_deriv_within_at f (f' x) (set.Ici x) x) (ha : norm (f a) ≤ δ) (bound : ∀ (x : ℝ), x ∈ set.Ico a b → norm (f' x) ≤ K * norm (f x) + ε) (x : ℝ) (H : x ∈ set.Icc a b) : norm (f x) ≤ gronwall_bound δ K ε (x - a) := sorry

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem_set {E : Type u_1} [normed_group E] [normed_space ℝ E] {v : ℝ → E → E} {s : ℝ → set E} {K : ℝ} (hv : ∀ (t : ℝ) (x y : E), x ∈ s t → y ∈ s t → dist (v t x) (v t y) ≤ K * dist x y) {f : ℝ → E} {g : ℝ → E} {f' : ℝ → E} {g' : ℝ → E} {a : ℝ} {b : ℝ} {εf : ℝ} {εg : ℝ} {δ : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at f (f' t) (set.Ici t) t) (f_bound : ∀ (t : ℝ), t ∈ set.Ico a b → dist (f' t) (v t (f t)) ≤ εf) (hfs : ∀ (t : ℝ), t ∈ set.Ico a b → f t ∈ s t) (hg : continuous_on g (set.Icc a b)) (hg' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at g (g' t) (set.Ici t) t) (g_bound : ∀ (t : ℝ), t ∈ set.Ico a b → dist (g' t) (v t (g t)) ≤ εg) (hgs : ∀ (t : ℝ), t ∈ set.Ico a b → g t ∈ s t) (ha : dist (f a) (g a) ≤ δ) (t : ℝ) (H : t ∈ set.Icc a b) : dist (f t) (g t) ≤ gronwall_bound δ K (εf + εg) (t - a) := sorry

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_approx_trajectories_ODE {E : Type u_1} [normed_group E] [normed_space ℝ E] {v : ℝ → E → E} {K : nnreal} (hv : ∀ (t : ℝ), lipschitz_with K (v t)) {f : ℝ → E} {g : ℝ → E} {f' : ℝ → E} {g' : ℝ → E} {a : ℝ} {b : ℝ} {εf : ℝ} {εg : ℝ} {δ : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at f (f' t) (set.Ici t) t) (f_bound : ∀ (t : ℝ), t ∈ set.Ico a b → dist (f' t) (v t (f t)) ≤ εf) (hg : continuous_on g (set.Icc a b)) (hg' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at g (g' t) (set.Ici t) t) (g_bound : ∀ (t : ℝ), t ∈ set.Ico a b → dist (g' t) (v t (g t)) ≤ εg) (ha : dist (f a) (g a) ≤ δ) (t : ℝ) (H : t ∈ set.Icc a b) : dist (f t) (g t) ≤ gronwall_bound δ (↑K) (εf + εg) (t - a) := sorry

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_trajectories_ODE_of_mem_set {E : Type u_1} [normed_group E] [normed_space ℝ E] {v : ℝ → E → E} {s : ℝ → set E} {K : ℝ} (hv : ∀ (t : ℝ) (x y : E), x ∈ s t → y ∈ s t → dist (v t x) (v t y) ≤ K * dist x y) {f : ℝ → E} {g : ℝ → E} {a : ℝ} {b : ℝ} {δ : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at f (v t (f t)) (set.Ici t) t) (hfs : ∀ (t : ℝ), t ∈ set.Ico a b → f t ∈ s t) (hg : continuous_on g (set.Icc a b)) (hg' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at g (v t (g t)) (set.Ici t) t) (hgs : ∀ (t : ℝ), t ∈ set.Ico a b → g t ∈ s t) (ha : dist (f a) (g a) ≤ δ) (t : ℝ) (H : t ∈ set.Icc a b) : dist (f t) (g t) ≤ δ * real.exp (K * (t - a)) := sorry

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_trajectories_ODE {E : Type u_1} [normed_group E] [normed_space ℝ E] {v : ℝ → E → E} {K : nnreal} (hv : ∀ (t : ℝ), lipschitz_with K (v t)) {f : ℝ → E} {g : ℝ → E} {a : ℝ} {b : ℝ} {δ : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at f (v t (f t)) (set.Ici t) t) (hg : continuous_on g (set.Icc a b)) (hg' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at g (v t (g t)) (set.Ici t) t) (ha : dist (f a) (g a) ≤ δ) (t : ℝ) (H : t ∈ set.Icc a b) : dist (f t) (g t) ≤ δ * real.exp (↑K * (t - a)) := sorry

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) in a set `s ⊆ ℝ × E` with
a given initial value provided that RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`. -/
theorem ODE_solution_unique_of_mem_set {E : Type u_1} [normed_group E] [normed_space ℝ E] {v : ℝ → E → E} {s : ℝ → set E} {K : ℝ} (hv : ∀ (t : ℝ) (x y : E), x ∈ s t → y ∈ s t → dist (v t x) (v t y) ≤ K * dist x y) {f : ℝ → E} {g : ℝ → E} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at f (v t (f t)) (set.Ici t) t) (hfs : ∀ (t : ℝ), t ∈ set.Ico a b → f t ∈ s t) (hg : continuous_on g (set.Icc a b)) (hg' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at g (v t (g t)) (set.Ici t) t) (hgs : ∀ (t : ℝ), t ∈ set.Ico a b → g t ∈ s t) (ha : f a = g a) (t : ℝ) (H : t ∈ set.Icc a b) : f t = g t :=
  eq.mp (Eq._oldrec (Eq.refl (dist (f t) (g t) ≤ 0)) (propext dist_le_zero))
    (eq.mp (Eq._oldrec (Eq.refl (dist (f t) (g t) ≤ 0 * real.exp (K * (t - a)))) (zero_mul (real.exp (K * (t - a)))))
      (dist_le_of_trajectories_ODE_of_mem_set hv hf hf' hfs hg hg' hgs (iff.mpr dist_le_zero ha) t ht))

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique {E : Type u_1} [normed_group E] [normed_space ℝ E] {v : ℝ → E → E} {K : nnreal} (hv : ∀ (t : ℝ), lipschitz_with K (v t)) {f : ℝ → E} {g : ℝ → E} {a : ℝ} {b : ℝ} (hf : continuous_on f (set.Icc a b)) (hf' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at f (v t (f t)) (set.Ici t) t) (hg : continuous_on g (set.Icc a b)) (hg' : ∀ (t : ℝ), t ∈ set.Ico a b → has_deriv_within_at g (v t (g t)) (set.Ici t) t) (ha : f a = g a) (t : ℝ) (H : t ∈ set.Icc a b) : f t = g t := sorry

