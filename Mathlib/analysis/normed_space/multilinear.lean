/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.operator_norm
import Mathlib.topology.algebra.multilinear
import Mathlib.PostPort

universes u v w₁ w₂ wG u_1 w 

namespace Mathlib

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `∥f∥` as the
smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `∥f m∥ ≤ C * ∏ i, ∥m i∥` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mk_continuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `∥f∥` is its norm, i.e., the smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for
  all `m`.
* `le_op_norm f m` asserts the fundamental inequality `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥`.
* `norm_image_sub_le f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `∥f∥` and `∥m₁ - m₂∥`.

We also register isomorphisms corresponding to currying or uncurrying variables, transforming a
continuous multilinear function `f` in `n+1` variables into a continuous linear function taking
values in continuous multilinear functions in `n` variables, and also into a continuous multilinear
function in `n` variables taking values in continuous linear functions. These operations are called
`f.curry_left` and `f.curry_right` respectively (with inverses `f.uncurry_left` and
`f.uncurry_right`). They induce continuous linear equivalences between spaces of
continuous multilinear functions in `n+1` variables and spaces of continuous linear functions into
continuous multilinear functions in `n` variables (resp. continuous multilinear functions in `n`
variables taking values in continuous linear functions), called respectively
`continuous_multilinear_curry_left_equiv` and `continuous_multilinear_curry_right_equiv`.

## Implementation notes

We mostly follow the API (and the proofs) of `operator_norm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables. The currying/uncurrying
constructions are based on those in `multilinear.lean`.

From the mathematical point of view, all the results follow from the results on operator norm in
one variable, by applying them to one variable after the other through currying. However, this
is only well defined when there is an order on the variables (for instance on `fin n`) although
the final result is independent of the order. While everything could be done following this
approach, it turns out that direct proofs are easier and more efficient.
-/

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, in
both directions. Along the way, we prove useful bounds on the difference `∥f m₁ - f m₂∥`.
-/

namespace multilinear_map


/-- If a multilinear map in finitely many variables on normed spaces satisfies the inequality
`∥f m∥ ≤ C * ∏ i, ∥m i∥` on a shell `ε i / ∥c i∥ < ∥m i∥ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ∥c i∥`, then it satisfies this inequality for all `m`. -/
theorem bound_of_shell {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) {ε : ι → ℝ} {C : ℝ} (hε : ∀ (i : ι), 0 < ε i) {c : ι → 𝕜} (hc : ∀ (i : ι), 1 < norm (c i)) (hf : ∀ (m : (i : ι) → E₁ i),
  (∀ (i : ι), ε i / norm (c i) ≤ norm (m i)) →
    (∀ (i : ι), norm (m i) < ε i) → norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) (m : (i : ι) → E₁ i) : norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i) := sorry

/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, for some `C` which can be chosen to be
positive. -/
theorem exists_bound_of_continuous {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) (hf : continuous ⇑f) : ∃ (C : ℝ), 0 < C ∧ ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i) := sorry

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a precise but hard to use version. See
`norm_image_sub_le_of_bound` for a less precise but more usable version. The bound reads
`∥f m - f m'∥ ≤
  C * ∥m 1 - m' 1∥ * max ∥m 2∥ ∥m' 2∥ * max ∥m 3∥ ∥m' 3∥ * ... * max ∥m n∥ ∥m' n∥ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
theorem norm_image_sub_le_of_bound' {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) {C : ℝ} (hC : 0 ≤ C) (H : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) (m₁ : (i : ι) → E₁ i) (m₂ : (i : ι) → E₁ i) : norm (coe_fn f m₁ - coe_fn f m₂) ≤
  C *
    finset.sum finset.univ
      fun (i : ι) =>
        finset.prod finset.univ fun (j : ι) => ite (j = i) (norm (m₁ i - m₂ i)) (max (norm (m₁ j)) (norm (m₂ j))) := sorry

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bound is
`∥f m - f m'∥ ≤ C * card ι * ∥m - m'∥ * (max ∥m∥ ∥m'∥) ^ (card ι - 1)`. -/
theorem norm_image_sub_le_of_bound {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) {C : ℝ} (hC : 0 ≤ C) (H : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) (m₁ : (i : ι) → E₁ i) (m₂ : (i : ι) → E₁ i) : norm (coe_fn f m₁ - coe_fn f m₂) ≤
  C * ↑(fintype.card ι) * max (norm m₁) (norm m₂) ^ (fintype.card ι - 1) * norm (m₁ - m₂) := sorry

/-- If a multilinear map satisfies an inequality `∥f m∥ ≤ C * ∏ i, ∥m i∥`, then it is
continuous. -/
theorem continuous_of_bound {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) (C : ℝ) (H : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) : continuous ⇑f := sorry

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
def mk_continuous {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) (C : ℝ) (H : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) : continuous_multilinear_map 𝕜 E₁ E₂ :=
  continuous_multilinear_map.mk (mk (to_fun f) sorry sorry) sorry

@[simp] theorem coe_mk_continuous {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) (C : ℝ) (H : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) : ⇑(mk_continuous f C H) = ⇑f :=
  rfl

/-- Given a multilinear map in `n` variables, if one restricts it to `k` variables putting `z` on
the other coordinates, then the resulting restricted function satisfies an inequality
`∥f.restr v∥ ≤ C * ∥z∥^(n-k) * Π ∥v i∥` if the original function satisfies `∥f v∥ ≤ C * Π ∥v i∥`. -/
theorem restr_norm_le {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] {k : ℕ} {n : ℕ} (f : multilinear_map 𝕜 (fun (i : fin n) => G) E₂) (s : finset (fin n)) (hk : finset.card s = k) (z : G) {C : ℝ} (H : ∀ (m : (i : fin n) → (fun (i : fin n) => G) i),
  norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : fin n) => norm (m i)) (v : fin k → G) : norm (coe_fn (restr f s hk z) v) ≤ C * norm z ^ (n - k) * finset.prod finset.univ fun (i : fin k) => norm (v i) := sorry

end multilinear_map


/-!
### Continuous multilinear maps

We define the norm `∥f∥` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `∥f m∥ ≤ ∥f∥ * ∏ i, ∥m i∥` for all `m`. We show that this
defines a normed space structure on `continuous_multilinear_map 𝕜 E₁ E₂`.
-/

namespace continuous_multilinear_map


theorem bound {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) : ∃ (C : ℝ), 0 < C ∧ ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i) :=
  multilinear_map.exists_bound_of_continuous (to_multilinear_map f) (cont f)

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
def op_norm {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) : ℝ :=
  Inf
    (set_of
      fun (c : ℝ) =>
        0 ≤ c ∧ ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ c * finset.prod finset.univ fun (i : ι) => norm (m i))

protected instance has_op_norm {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] : has_norm (continuous_multilinear_map 𝕜 E₁ E₂) :=
  has_norm.mk op_norm

theorem norm_def {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) : norm f =
  Inf
    (set_of
      fun (c : ℝ) =>
        0 ≤ c ∧ ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ c * finset.prod finset.univ fun (i : ι) => norm (m i)) :=
  rfl

-- So that invocations of `real.Inf_le` make sense: we show that the set of

-- bounds is nonempty and bounded below.

theorem bounds_nonempty {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] {f : continuous_multilinear_map 𝕜 E₁ E₂} : ∃ (c : ℝ),
  c ∈
    set_of
      fun (c : ℝ) =>
        0 ≤ c ∧ ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ c * finset.prod finset.univ fun (i : ι) => norm (m i) := sorry

theorem bounds_bdd_below {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] {f : continuous_multilinear_map 𝕜 E₁ E₂} : bdd_below
  (set_of
    fun (c : ℝ) =>
      0 ≤ c ∧ ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ c * finset.prod finset.univ fun (i : ι) => norm (m i)) := sorry

theorem op_norm_nonneg {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) : 0 ≤ norm f := sorry

/-- The fundamental property of the operator norm of a continuous multilinear map:
`∥f m∥` is bounded by `∥f∥` times the product of the `∥m i∥`. -/
theorem le_op_norm {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) (m : (i : ι) → E₁ i) : norm (coe_fn f m) ≤ norm f * finset.prod finset.univ fun (i : ι) => norm (m i) := sorry

theorem ratio_le_op_norm {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) (m : (i : ι) → E₁ i) : (norm (coe_fn f m) / finset.prod finset.univ fun (i : ι) => norm (m i)) ≤ norm f := sorry

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
theorem unit_le_op_norm {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) (m : (i : ι) → E₁ i) (h : norm m ≤ 1) : norm (coe_fn f m) ≤ norm f := sorry

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem op_norm_le_bound {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ M * finset.prod finset.univ fun (i : ι) => norm (m i)) : norm f ≤ M := sorry

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) (g : continuous_multilinear_map 𝕜 E₁ E₂) : norm (f + g) ≤ norm f + norm g := sorry

/-- A continuous linear map is zero iff its norm vanishes. -/
theorem op_norm_zero_iff {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) : norm f = 0 ↔ f = 0 := sorry

theorem op_norm_smul_le {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) {𝕜' : Type u_1} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜] [normed_space 𝕜' E₂] [is_scalar_tower 𝕜' 𝕜 E₂] (c : 𝕜') : norm (c • f) ≤ norm c * norm f := sorry

theorem op_norm_neg {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) : norm (-f) = norm f := sorry

/-- Continuous multilinear maps themselves form a normed space with respect to
    the operator norm. -/
protected instance to_normed_group {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] : normed_group (continuous_multilinear_map 𝕜 E₁ E₂) :=
  normed_group.of_core (continuous_multilinear_map 𝕜 E₁ E₂) sorry

protected instance to_normed_space {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] {𝕜' : Type u_1} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜] [normed_space 𝕜' E₂] [is_scalar_tower 𝕜' 𝕜 E₂] : normed_space 𝕜' (continuous_multilinear_map 𝕜 E₁ E₂) :=
  normed_space.mk sorry

@[simp] theorem norm_restrict_scalars {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) {𝕜' : Type u_1} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜] [normed_space 𝕜' E₂] [is_scalar_tower 𝕜' 𝕜 E₂] [(i : ι) → normed_space 𝕜' (E₁ i)] [∀ (i : ι), is_scalar_tower 𝕜' 𝕜 (E₁ i)] : norm (restrict_scalars 𝕜' f) = norm f := sorry

/-- `continuous_multilinear_map.restrict_scalars` as a `continuous_multilinear_map`. -/
def restrict_scalars_linear {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (𝕜' : Type u_1) [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜] [normed_space 𝕜' E₂] [is_scalar_tower 𝕜' 𝕜 E₂] [(i : ι) → normed_space 𝕜' (E₁ i)] [∀ (i : ι), is_scalar_tower 𝕜' 𝕜 (E₁ i)] : continuous_linear_map 𝕜' (continuous_multilinear_map 𝕜 E₁ E₂) (continuous_multilinear_map 𝕜' E₁ E₂) :=
  linear_map.mk_continuous (linear_map.mk (restrict_scalars 𝕜') sorry sorry) 1 sorry

theorem continuous_restrict_scalars {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] {𝕜' : Type u_1} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜' 𝕜] [normed_space 𝕜' E₂] [is_scalar_tower 𝕜' 𝕜 E₂] [(i : ι) → normed_space 𝕜' (E₁ i)] [∀ (i : ι), is_scalar_tower 𝕜' 𝕜 (E₁ i)] : continuous (restrict_scalars 𝕜') :=
  continuous_linear_map.continuous (restrict_scalars_linear 𝕜')

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`∥f m - f m'∥ ≤
  ∥f∥ * ∥m 1 - m' 1∥ * max ∥m 2∥ ∥m' 2∥ * max ∥m 3∥ ∥m' 3∥ * ... * max ∥m n∥ ∥m' n∥ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`.-/
theorem norm_image_sub_le' {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) (m₁ : (i : ι) → E₁ i) (m₂ : (i : ι) → E₁ i) : norm (coe_fn f m₁ - coe_fn f m₂) ≤
  norm f *
    finset.sum finset.univ
      fun (i : ι) =>
        finset.prod finset.univ fun (j : ι) => ite (j = i) (norm (m₁ i - m₂ i)) (max (norm (m₁ j)) (norm (m₂ j))) :=
  multilinear_map.norm_image_sub_le_of_bound' (to_multilinear_map f) (norm_nonneg f) (le_op_norm f) m₁ m₂

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `∥f m - f m'∥ ≤ ∥f∥ * card ι * ∥m - m'∥ * (max ∥m∥ ∥m'∥) ^ (card ι - 1)`.-/
theorem norm_image_sub_le {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E₁ E₂) (m₁ : (i : ι) → E₁ i) (m₂ : (i : ι) → E₁ i) : norm (coe_fn f m₁ - coe_fn f m₂) ≤
  norm f * ↑(fintype.card ι) * max (norm m₁) (norm m₂) ^ (fintype.card ι - 1) * norm (m₁ - m₂) :=
  multilinear_map.norm_image_sub_le_of_bound (to_multilinear_map f) (norm_nonneg f) (le_op_norm f) m₁ m₂

/-- Applying a multilinear map to a vector is continuous in both coordinates. -/
theorem continuous_eval {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] : continuous fun (p : continuous_multilinear_map 𝕜 E₁ E₂ × ((i : ι) → E₁ i)) => coe_fn (prod.fst p) (prod.snd p) := sorry

theorem continuous_eval_left {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (m : (i : ι) → E₁ i) : continuous fun (p : continuous_multilinear_map 𝕜 E₁ E₂) => coe_fn p m :=
  continuous.comp continuous_eval (continuous.prod_mk continuous_id continuous_const)

theorem has_sum_eval {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] {α : Type u_1} {p : α → continuous_multilinear_map 𝕜 E₁ E₂} {q : continuous_multilinear_map 𝕜 E₁ E₂} (h : has_sum p q) (m : (i : ι) → E₁ i) : has_sum (fun (a : α) => coe_fn (p a) m) (coe_fn q m) := sorry

/-- If the target space is complete, the space of continuous multilinear maps with its norm is also
complete. The proof is essentially the same as for the space of continuous linear maps (modulo the
addition of `finset.prod` where needed. The duplication could be avoided by deducing the linear
case from the multilinear case via a currying isomorphism. However, this would mess up imports,
and it is more satisfactory to have the simplest case as a standalone proof. -/
protected instance complete_space {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] [complete_space E₂] : complete_space (continuous_multilinear_map 𝕜 E₁ E₂) := sorry

end continuous_multilinear_map


/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem multilinear_map.mk_continuous_norm_le {𝕜 : Type u} {ι : Type v} {E₁ : ι → Type w₁} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [(i : ι) → normed_group (E₁ i)] [normed_group E₂] [(i : ι) → normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂] (f : multilinear_map 𝕜 E₁ E₂) {C : ℝ} (hC : 0 ≤ C) (H : ∀ (m : (i : ι) → E₁ i), norm (coe_fn f m) ≤ C * finset.prod finset.univ fun (i : ι) => norm (m i)) : norm (multilinear_map.mk_continuous f C H) ≤ C :=
  continuous_multilinear_map.op_norm_le_bound (multilinear_map.mk_continuous f C H) hC fun (m : (i : ι) → E₁ i) => H m

namespace continuous_multilinear_map


/-- Given a continuous multilinear map `f` on `n` variables (parameterized by `fin n`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `fin k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is denoted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The implicit
identification between `fin k` and `s` that we use is the canonical (increasing) bijection. -/
def restr {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] {k : ℕ} {n : ℕ} (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => G) E₂) (s : finset (fin n)) (hk : finset.card s = k) (z : G) : continuous_multilinear_map 𝕜 (fun (i : fin k) => G) E₂ :=
  multilinear_map.mk_continuous (multilinear_map.restr (to_multilinear_map f) s hk z) (norm f * norm z ^ (n - k)) sorry

theorem norm_restr {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] {k : ℕ} {n : ℕ} (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => G) E₂) (s : finset (fin n)) (hk : finset.card s = k) (z : G) : norm (restr f s hk z) ≤ norm f * norm z ^ (n - k) :=
  multilinear_map.mk_continuous_norm_le (multilinear_map.restr (to_multilinear_map f) s hk z)
    (mul_nonneg (norm_nonneg f) (pow_nonneg (norm_nonneg z) (n - k))) (restr._proof_1 f s hk z)

/-- The continuous multilinear map on `A^ι`, where `A` is a normed commutative algebra
over `𝕜`, associating to `m` the product of all the `m i`.

See also `continuous_multilinear_map.mk_pi_algebra_fin`. -/
protected def mk_pi_algebra (𝕜 : Type u) (ι : Type v) [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] (A : Type u_1) [normed_comm_ring A] [normed_algebra 𝕜 A] : continuous_multilinear_map 𝕜 (fun (i : ι) => A) A :=
  multilinear_map.mk_continuous (multilinear_map.mk_pi_algebra 𝕜 ι A) (ite (Nonempty ι) 1 (norm 1)) sorry

@[simp] theorem mk_pi_algebra_apply {𝕜 : Type u} {ι : Type v} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_comm_ring A] [normed_algebra 𝕜 A] (m : ι → A) : coe_fn (continuous_multilinear_map.mk_pi_algebra 𝕜 ι A) m = finset.prod finset.univ fun (i : ι) => m i :=
  rfl

theorem norm_mk_pi_algebra_le {𝕜 : Type u} {ι : Type v} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_comm_ring A] [normed_algebra 𝕜 A] [Nonempty ι] : norm (continuous_multilinear_map.mk_pi_algebra 𝕜 ι A) ≤ 1 := sorry

theorem norm_mk_pi_algebra_of_empty {𝕜 : Type u} {ι : Type v} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_comm_ring A] [normed_algebra 𝕜 A] (h : ¬Nonempty ι) : norm (continuous_multilinear_map.mk_pi_algebra 𝕜 ι A) = norm 1 := sorry

@[simp] theorem norm_mk_pi_algebra {𝕜 : Type u} {ι : Type v} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_comm_ring A] [normed_algebra 𝕜 A] [norm_one_class A] : norm (continuous_multilinear_map.mk_pi_algebra 𝕜 ι A) = 1 := sorry

/-- The continuous multilinear map on `A^n`, where `A` is a normed algebra over `𝕜`, associating to
`m` the product of all the `m i`.

See also: `multilinear_map.mk_pi_algebra`. -/
protected def mk_pi_algebra_fin (𝕜 : Type u) (n : ℕ) [nondiscrete_normed_field 𝕜] (A : Type u_1) [normed_ring A] [normed_algebra 𝕜 A] : continuous_multilinear_map 𝕜 (fun (i : fin n) => A) A :=
  multilinear_map.mk_continuous (multilinear_map.mk_pi_algebra_fin 𝕜 n A) (nat.cases_on n (norm 1) fun (_x : ℕ) => 1)
    sorry

@[simp] theorem mk_pi_algebra_fin_apply {𝕜 : Type u} {n : ℕ} [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_ring A] [normed_algebra 𝕜 A] (m : fin n → A) : coe_fn (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 n A) m = list.prod (list.of_fn m) :=
  rfl

theorem norm_mk_pi_algebra_fin_succ_le {𝕜 : Type u} {n : ℕ} [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_ring A] [normed_algebra 𝕜 A] : norm (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 (Nat.succ n) A) ≤ 1 :=
  multilinear_map.mk_continuous_norm_le (multilinear_map.mk_pi_algebra_fin 𝕜 (Nat.succ n) A) zero_le_one
    (mk_pi_algebra_fin._proof_1 𝕜 (Nat.succ n) A)

theorem norm_mk_pi_algebra_fin_le_of_pos {𝕜 : Type u} {n : ℕ} [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_ring A] [normed_algebra 𝕜 A] (hn : 0 < n) : norm (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 n A) ≤ 1 :=
  nat.cases_on n (fun (hn : 0 < 0) => false.elim (has_lt.lt.false hn))
    (fun (n : ℕ) (hn : 0 < Nat.succ n) => norm_mk_pi_algebra_fin_succ_le) hn

theorem norm_mk_pi_algebra_fin_zero {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_ring A] [normed_algebra 𝕜 A] : norm (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 0 A) = norm 1 := sorry

theorem norm_mk_pi_algebra_fin {𝕜 : Type u} {n : ℕ} [nondiscrete_normed_field 𝕜] {A : Type u_1} [normed_ring A] [normed_algebra 𝕜 A] [norm_one_class A] : norm (continuous_multilinear_map.mk_pi_algebra_fin 𝕜 n A) = 1 := sorry

/-- The canonical continuous multilinear map on `𝕜^ι`, associating to `m` the product of all the
`m i` (multiplied by a fixed reference element `z` in the target module) -/
protected def mk_pi_field (𝕜 : Type u) (ι : Type v) {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [normed_group E₂] [normed_space 𝕜 E₂] (z : E₂) : continuous_multilinear_map 𝕜 (fun (i : ι) => 𝕜) E₂ :=
  multilinear_map.mk_continuous (multilinear_map.mk_pi_ring 𝕜 ι z) (norm z) sorry

@[simp] theorem mk_pi_field_apply {𝕜 : Type u} {ι : Type v} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [normed_group E₂] [normed_space 𝕜 E₂] (z : E₂) (m : ι → 𝕜) : coe_fn (continuous_multilinear_map.mk_pi_field 𝕜 ι z) m = (finset.prod finset.univ fun (i : ι) => m i) • z :=
  rfl

theorem mk_pi_field_apply_one_eq_self {𝕜 : Type u} {ι : Type v} {E₂ : Type w₂} [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [normed_group E₂] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : ι) => 𝕜) E₂) : continuous_multilinear_map.mk_pi_field 𝕜 ι (coe_fn f fun (i : ι) => 1) = f :=
  to_multilinear_map_inj (multilinear_map.mk_pi_ring_apply_one_eq_self (to_multilinear_map f))

/-- Continuous multilinear maps on `𝕜^n` with values in `E₂` are in bijection with `E₂`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear equivalence in
`continuous_multilinear_map.pi_field_equiv_aux`. The continuous linear equivalence is
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv_aux (𝕜 : Type u) (ι : Type v) (E₂ : Type w₂) [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [normed_group E₂] [normed_space 𝕜 E₂] : linear_equiv 𝕜 E₂ (continuous_multilinear_map 𝕜 (fun (i : ι) => 𝕜) E₂) :=
  linear_equiv.mk (fun (z : E₂) => continuous_multilinear_map.mk_pi_field 𝕜 ι z) sorry sorry
    (fun (f : continuous_multilinear_map 𝕜 (fun (i : ι) => 𝕜) E₂) => coe_fn f fun (i : ι) => 1) sorry sorry

/-- Continuous multilinear maps on `𝕜^n` with values in `E₂` are in bijection with `E₂`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a continuous linear equivalence in
`continuous_multilinear_map.pi_field_equiv`. -/
protected def pi_field_equiv (𝕜 : Type u) (ι : Type v) (E₂ : Type w₂) [DecidableEq ι] [fintype ι] [nondiscrete_normed_field 𝕜] [normed_group E₂] [normed_space 𝕜 E₂] : continuous_linear_equiv 𝕜 E₂ (continuous_multilinear_map 𝕜 (fun (i : ι) => 𝕜) E₂) :=
  continuous_linear_equiv.mk
    (linear_equiv.mk (linear_equiv.to_fun (continuous_multilinear_map.pi_field_equiv_aux 𝕜 ι E₂)) sorry sorry
      (linear_equiv.inv_fun (continuous_multilinear_map.pi_field_equiv_aux 𝕜 ι E₂)) sorry sorry)

end continuous_multilinear_map


/-!
### Currying

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `fin n.succ`) two
curried functions, named `f.curry_left` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curry_right` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register continuous linear equiv versions of these correspondences, in
`continuous_multilinear_curry_left_equiv` and `continuous_multilinear_curry_right_equiv`.
-/

theorem continuous_linear_map.norm_map_tail_le {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂)) (m : (i : fin (Nat.succ n)) → E i) : norm (coe_fn (coe_fn f (m 0)) (fin.tail m)) ≤ norm f * finset.prod finset.univ fun (i : fin (Nat.succ n)) => norm (m i) := sorry

theorem continuous_multilinear_map.norm_map_init_le {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂)) (m : (i : fin (Nat.succ n)) → E i) : norm (coe_fn (coe_fn f (fin.init m)) (m (fin.last n))) ≤
  norm f * finset.prod finset.univ fun (i : fin (Nat.succ n)) => norm (m i) := sorry

theorem continuous_multilinear_map.norm_map_cons_le {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (m : (i : fin n) → E (fin.succ i)) : norm (coe_fn f (fin.cons x m)) ≤ norm f * norm x * finset.prod finset.univ fun (i : fin n) => norm (m i) := sorry

theorem continuous_multilinear_map.norm_map_snoc_le {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) (m : (i : fin n) → E (coe_fn fin.cast_succ i)) (x : E (fin.last n)) : norm (coe_fn f (fin.snoc m x)) ≤ (norm f * finset.prod finset.univ fun (i : fin n) => norm (m i)) * norm x := sorry

/-! #### Left currying -/

/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def continuous_linear_map.uncurry_left {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂)) : continuous_multilinear_map 𝕜 E E₂ :=
  multilinear_map.mk_continuous
    (linear_map.uncurry_left
      (linear_map.comp continuous_multilinear_map.to_multilinear_map_linear (continuous_linear_map.to_linear_map f)))
    (norm f) sorry

@[simp] theorem continuous_linear_map.uncurry_left_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂)) (m : (i : fin (Nat.succ n)) → E i) : coe_fn (continuous_linear_map.uncurry_left f) m = coe_fn (coe_fn f (m 0)) (fin.tail m) :=
  rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
def continuous_multilinear_map.curry_left {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂) :=
  linear_map.mk_continuous
    (linear_map.mk
      (fun (x : E 0) =>
        multilinear_map.mk_continuous
          (coe_fn (multilinear_map.curry_left (continuous_multilinear_map.to_multilinear_map f)) x) (norm f * norm x)
          sorry)
      sorry sorry)
    (norm f) sorry

@[simp] theorem continuous_multilinear_map.curry_left_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (m : (i : fin n) → E (fin.succ i)) : coe_fn (coe_fn (continuous_multilinear_map.curry_left f) x) m = coe_fn f (fin.cons x m) :=
  rfl

@[simp] theorem continuous_linear_map.curry_uncurry_left {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂)) : continuous_multilinear_map.curry_left (continuous_linear_map.uncurry_left f) = f := sorry

@[simp] theorem continuous_multilinear_map.uncurry_curry_left {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) : continuous_linear_map.uncurry_left (continuous_multilinear_map.curry_left f) = f := sorry

@[simp] theorem continuous_multilinear_map.curry_left_norm {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) : norm (continuous_multilinear_map.curry_left f) = norm f := sorry

@[simp] theorem continuous_linear_map.uncurry_left_norm {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂)) : norm (continuous_linear_map.uncurry_left f) = norm f := sorry

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism as a
linear isomorphism in `continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂`.
The algebraic version (without continuity assumption on the maps) is
`multilinear_curry_left_equiv 𝕜 E E₂`, and the topological isomorphism (registering
additionally that the isomorphism is continuous) is
`continuous_multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear equivs. -/
def continuous_multilinear_curry_left_equiv_aux (𝕜 : Type u) {n : ℕ} (E : fin (Nat.succ n) → Type w) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] : linear_equiv 𝕜 (continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂))
  (continuous_multilinear_map 𝕜 E E₂) :=
  linear_equiv.mk continuous_linear_map.uncurry_left sorry sorry continuous_multilinear_map.curry_left
    continuous_linear_map.curry_uncurry_left sorry

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism in
`continuous_multilinear_curry_left_equiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of continuous linear equivs. -/
def continuous_multilinear_curry_left_equiv (𝕜 : Type u) {n : ℕ} (E : fin (Nat.succ n) → Type w) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] : continuous_linear_equiv 𝕜
  (continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂))
  (continuous_multilinear_map 𝕜 E E₂) :=
  continuous_linear_equiv.mk
    (linear_equiv.mk (linear_equiv.to_fun (continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂)) sorry sorry
      (linear_equiv.inv_fun (continuous_multilinear_curry_left_equiv_aux 𝕜 E E₂)) sorry sorry)

@[simp] theorem continuous_multilinear_curry_left_equiv_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 (E 0) (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (fin.succ i)) E₂)) (v : (i : fin (Nat.succ n)) → E i) : coe_fn (coe_fn (continuous_multilinear_curry_left_equiv 𝕜 E E₂) f) v = coe_fn (coe_fn f (v 0)) (fin.tail v) :=
  rfl

@[simp] theorem continuous_multilinear_curry_left_equiv_symm_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (v : (i : fin n) → E (fin.succ i)) : coe_fn (coe_fn (coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_left_equiv 𝕜 E E₂)) f) x) v =
  coe_fn f (fin.cons x v) :=
  rfl

/-! #### Right currying -/

/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
def continuous_multilinear_map.uncurry_right {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂)) : continuous_multilinear_map 𝕜 E E₂ :=
  let f' : multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i)) (linear_map 𝕜 (E (fin.last n)) E₂) :=
    multilinear_map.mk
      (fun (m : (i : fin n) → E (coe_fn fin.cast_succ i)) => continuous_linear_map.to_linear_map (coe_fn f m)) sorry
      sorry;
  multilinear_map.mk_continuous (multilinear_map.uncurry_right f') (norm f) sorry

@[simp] theorem continuous_multilinear_map.uncurry_right_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂)) (m : (i : fin (Nat.succ n)) → E i) : coe_fn (continuous_multilinear_map.uncurry_right f) m = coe_fn (coe_fn f (fin.init m)) (m (fin.last n)) :=
  rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def continuous_multilinear_map.curry_right {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂) :=
  let f' :
    multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i)) (continuous_linear_map 𝕜 (E (fin.last n)) E₂) :=
    multilinear_map.mk
      (fun (m : (i : fin n) → E (coe_fn fin.cast_succ i)) =>
        linear_map.mk_continuous
          (coe_fn (multilinear_map.curry_right (continuous_multilinear_map.to_multilinear_map f)) m)
          (norm f * finset.prod finset.univ fun (i : fin n) => norm (m i)) sorry)
      sorry sorry;
  multilinear_map.mk_continuous f' (norm f) sorry

@[simp] theorem continuous_multilinear_map.curry_right_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) (m : (i : fin n) → E (coe_fn fin.cast_succ i)) (x : E (fin.last n)) : coe_fn (coe_fn (continuous_multilinear_map.curry_right f) m) x = coe_fn f (fin.snoc m x) :=
  rfl

@[simp] theorem continuous_multilinear_map.curry_uncurry_right {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂)) : continuous_multilinear_map.curry_right (continuous_multilinear_map.uncurry_right f) = f := sorry

@[simp] theorem continuous_multilinear_map.uncurry_curry_right {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) : continuous_multilinear_map.uncurry_right (continuous_multilinear_map.curry_right f) = f := sorry

@[simp] theorem continuous_multilinear_map.curry_right_norm {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) : norm (continuous_multilinear_map.curry_right f) = norm f := sorry

@[simp] theorem continuous_multilinear_map.uncurry_right_norm {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂)) : norm (continuous_multilinear_map.uncurry_right f) = norm f := sorry

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), E i.cast_succ` with values in the space
of continuous linear maps on `E (last n)`, by separating the last variable. We register this
isomorphism as a linear equiv in `continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂`.
The algebraic version (without continuity assumption on the maps) is
`multilinear_curry_right_equiv 𝕜 E E₂`, and the topological isomorphism (registering
additionally that the isomorphism is continuous) is
`continuous_multilinear_curry_right_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear equivs. -/
def continuous_multilinear_curry_right_equiv_aux (𝕜 : Type u) {n : ℕ} (E : fin (Nat.succ n) → Type w) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] : linear_equiv 𝕜
  (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
    (continuous_linear_map 𝕜 (E (fin.last n)) E₂))
  (continuous_multilinear_map 𝕜 E E₂) :=
  linear_equiv.mk continuous_multilinear_map.uncurry_right sorry sorry continuous_multilinear_map.curry_right
    continuous_multilinear_map.curry_uncurry_right sorry

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), E i.cast_succ` with values in the space
of continuous linear maps on `E (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv 𝕜 E E₂`.
The algebraic version (without topology) is given in `multilinear_curry_right_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of continuous linear equivs. -/
def continuous_multilinear_curry_right_equiv (𝕜 : Type u) {n : ℕ} (E : fin (Nat.succ n) → Type w) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] : continuous_linear_equiv 𝕜
  (continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
    (continuous_linear_map 𝕜 (E (fin.last n)) E₂))
  (continuous_multilinear_map 𝕜 E E₂) :=
  continuous_linear_equiv.mk
    (linear_equiv.mk (linear_equiv.to_fun (continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂)) sorry sorry
      (linear_equiv.inv_fun (continuous_multilinear_curry_right_equiv_aux 𝕜 E E₂)) sorry sorry)

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), G` is canonically isomorphic to
the space of continuous multilinear maps on `Π(i : fin n), G` with values in the space
of continuous linear maps on `G`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_multilinear_curry_right_equiv' 𝕜 n G E₂`.
For a version allowing dependent types, see `continuous_multilinear_curry_right_equiv`. When there
are no dependent types, use the primed version as it helps Lean a lot for unification.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of continuous linear equivs. -/
def continuous_multilinear_curry_right_equiv' (𝕜 : Type u) (n : ℕ) (G : Type wG) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] : continuous_linear_equiv 𝕜 (continuous_multilinear_map 𝕜 (fun (i : fin n) => G) (continuous_linear_map 𝕜 G E₂))
  (continuous_multilinear_map 𝕜 (fun (i : fin (Nat.succ n)) => G) E₂) :=
  continuous_multilinear_curry_right_equiv 𝕜 (fun (i : fin (Nat.succ n)) => G) E₂

@[simp] theorem continuous_multilinear_curry_right_equiv_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => E (coe_fn fin.cast_succ i))
  (continuous_linear_map 𝕜 (E (fin.last n)) E₂)) (v : (i : fin (Nat.succ n)) → E i) : coe_fn (coe_fn (continuous_multilinear_curry_right_equiv 𝕜 E E₂) f) v = coe_fn (coe_fn f (fin.init v)) (v (fin.last n)) :=
  rfl

@[simp] theorem continuous_multilinear_curry_right_equiv_symm_apply {𝕜 : Type u} {n : ℕ} {E : fin (Nat.succ n) → Type w} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [(i : fin (Nat.succ n)) → normed_group (E i)] [normed_group E₂] [(i : fin (Nat.succ n)) → normed_space 𝕜 (E i)] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 E E₂) (v : (i : fin n) → E (coe_fn fin.cast_succ i)) (x : E (fin.last n)) : coe_fn (coe_fn (coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_right_equiv 𝕜 E E₂)) f) v) x =
  coe_fn f (fin.snoc v x) :=
  rfl

@[simp] theorem continuous_multilinear_curry_right_equiv_apply' {𝕜 : Type u} {n : ℕ} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin n) => G) (continuous_linear_map 𝕜 G E₂)) (v : fin (Nat.succ n) → G) : coe_fn (coe_fn (continuous_multilinear_curry_right_equiv' 𝕜 n G E₂) f) v =
  coe_fn (coe_fn f (fin.init v)) (v (fin.last n)) :=
  rfl

@[simp] theorem continuous_multilinear_curry_right_equiv_symm_apply' {𝕜 : Type u} {n : ℕ} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin (Nat.succ n)) => G) E₂) (v : fin n → G) (x : G) : coe_fn (coe_fn (coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_right_equiv' 𝕜 n G E₂)) f) v) x =
  coe_fn f (fin.snoc v x) :=
  rfl

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
def continuous_multilinear_map.uncurry0 {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) : E₂ :=
  coe_fn f 0

/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
def continuous_multilinear_map.curry0 (𝕜 : Type u) (G : Type wG) {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (x : E₂) : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂ :=
  continuous_multilinear_map.mk (multilinear_map.mk (fun (m : fin 0 → G) => x) sorry sorry) sorry

@[simp] theorem continuous_multilinear_map.curry0_apply (𝕜 : Type u) {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (x : E₂) (m : fin 0 → G) : coe_fn (continuous_multilinear_map.curry0 𝕜 G x) m = x :=
  rfl

@[simp] theorem continuous_multilinear_map.uncurry0_apply {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) : continuous_multilinear_map.uncurry0 f = coe_fn f 0 :=
  rfl

@[simp] theorem continuous_multilinear_map.apply_zero_curry0 {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) {x : fin 0 → G} : continuous_multilinear_map.curry0 𝕜 G (coe_fn f x) = f := sorry

theorem continuous_multilinear_map.uncurry0_curry0 {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) : continuous_multilinear_map.curry0 𝕜 G (continuous_multilinear_map.uncurry0 f) = f := sorry

@[simp] theorem continuous_multilinear_map.curry0_uncurry0 (𝕜 : Type u) (G : Type wG) {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (x : E₂) : continuous_multilinear_map.uncurry0 (continuous_multilinear_map.curry0 𝕜 G x) = x :=
  rfl

@[simp] theorem continuous_multilinear_map.uncurry0_norm (𝕜 : Type u) (G : Type wG) {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (x : E₂) : norm (continuous_multilinear_map.curry0 𝕜 G x) = norm x := sorry

@[simp] theorem continuous_multilinear_map.fin0_apply_norm {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) {x : fin 0 → G} : norm (coe_fn f x) = norm f := sorry

theorem continuous_multilinear_map.curry0_norm {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) : norm (continuous_multilinear_map.uncurry0 f) = norm f := sorry

/-- The linear isomorphism between elements of a normed space, and continuous multilinear maps in
`0` variables with values in this normed space. The continuous version is given in
`continuous_multilinear_curry_fin0`.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear equivs. -/
def continuous_multilinear_curry_fin0_aux (𝕜 : Type u) (G : Type wG) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] : linear_equiv 𝕜 (continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) E₂ :=
  linear_equiv.mk
    (fun (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) => continuous_multilinear_map.uncurry0 f) sorry
    sorry (fun (f : E₂) => continuous_multilinear_map.curry0 𝕜 G f) continuous_multilinear_map.uncurry0_curry0
    (continuous_multilinear_map.curry0_uncurry0 𝕜 G)

/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of continuous linear equivs. -/
def continuous_multilinear_curry_fin0 (𝕜 : Type u) (G : Type wG) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] : continuous_linear_equiv 𝕜 (continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) E₂ :=
  continuous_linear_equiv.mk
    (linear_equiv.mk (linear_equiv.to_fun (continuous_multilinear_curry_fin0_aux 𝕜 G E₂)) sorry sorry
      (linear_equiv.inv_fun (continuous_multilinear_curry_fin0_aux 𝕜 G E₂)) sorry sorry)

@[simp] theorem continuous_multilinear_curry_fin0_apply {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 0) => G) E₂) : coe_fn (continuous_multilinear_curry_fin0 𝕜 G E₂) f = coe_fn f 0 :=
  rfl

@[simp] theorem continuous_multilinear_curry_fin0_symm_apply {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (x : E₂) (v : fin 0 → G) : coe_fn (coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_fin0 𝕜 G E₂)) x) v = x :=
  rfl

/-! #### With 1 variable -/

/-- Continuous multilinear maps from `G^1` to `E₂` are isomorphic with continuous linear maps from
`G` to `E₂`. -/
def continuous_multilinear_curry_fin1 (𝕜 : Type u) (G : Type wG) (E₂ : Type w₂) [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] : continuous_linear_equiv 𝕜 (continuous_multilinear_map 𝕜 (fun (i : fin 1) => G) E₂) (continuous_linear_map 𝕜 G E₂) :=
  continuous_linear_equiv.trans
    (continuous_linear_equiv.symm (continuous_multilinear_curry_right_equiv 𝕜 (fun (i : fin 1) => G) E₂))
    (continuous_multilinear_curry_fin0 𝕜 G (continuous_linear_map 𝕜 G E₂))

@[simp] theorem continuous_multilinear_curry_fin1_apply {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_multilinear_map 𝕜 (fun (i : fin 1) => G) E₂) (x : G) : coe_fn (coe_fn (continuous_multilinear_curry_fin1 𝕜 G E₂) f) x = coe_fn f (fin.snoc 0 x) :=
  rfl

@[simp] theorem continuous_multilinear_curry_fin1_symm_apply {𝕜 : Type u} {G : Type wG} {E₂ : Type w₂} [nondiscrete_normed_field 𝕜] [normed_group G] [normed_group E₂] [normed_space 𝕜 G] [normed_space 𝕜 E₂] (f : continuous_linear_map 𝕜 G E₂) (v : fin 1 → G) : coe_fn (coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_fin1 𝕜 G E₂)) f) v = coe_fn f (v 0) :=
  rfl

