/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.analysis.normed_space.linear_isometry
import Mathlib.analysis.normed_space.riesz_lemma
import Mathlib.analysis.asymptotics
import Mathlib.PostPort

universes u_2 u_3 u_1 u_4 u_5 u_6 u_7 u_8 

namespace Mathlib

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous linear maps between normed spaces, and prove
its basic properties. In particular, show that this space is itself a normed space.
-/

theorem exists_pos_bound_of_bound {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    {f : E → F} (M : ℝ) (h : ∀ (x : E), norm (f x) ≤ M * norm x) :
    ∃ (N : ℝ), 0 < N ∧ ∀ (x : E), norm (f x) ≤ N * norm x :=
  Exists.intro (max M 1)
    { left := lt_of_lt_of_le zero_lt_one (le_max_right M 1),
      right :=
        fun (x : E) =>
          le_trans (h x) (mul_le_mul_of_nonneg_right (le_max_left M 1) (norm_nonneg x)) }

/- Most statements in this file require the field to be non-discrete, as this is necessary
to deduce an inequality `∥f x∥ ≤ C ∥x∥` from the continuity of f. However, the other direction always
holds. In this section, we just assume that `𝕜` is a normed field. In the remainder of the file,
it will be non-discrete. -/

theorem linear_map.lipschitz_of_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : linear_map 𝕜 E F)
    (C : ℝ) (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) :
    lipschitz_with (nnreal.of_real C) ⇑f :=
  sorry

theorem linear_map.antilipschitz_of_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) {K : nnreal} (h : ∀ (x : E), norm x ≤ ↑K * norm (coe_fn f x)) :
    antilipschitz_with K ⇑f :=
  sorry

theorem linear_map.bound_of_antilipschitz {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) {K : nnreal} (h : antilipschitz_with K ⇑f) (x : E) :
    norm x ≤ ↑K * norm (coe_fn f x) :=
  sorry

theorem linear_map.uniform_continuous_of_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) (C : ℝ) (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) :
    uniform_continuous ⇑f :=
  lipschitz_with.uniform_continuous (linear_map.lipschitz_of_bound f C h)

theorem linear_map.continuous_of_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : linear_map 𝕜 E F)
    (C : ℝ) (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) : continuous ⇑f :=
  lipschitz_with.continuous (linear_map.lipschitz_of_bound f C h)

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : linear_map 𝕜 E F)
    (C : ℝ) (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) : continuous_linear_map 𝕜 E F :=
  continuous_linear_map.mk f

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def linear_map.to_continuous_linear_map₁ {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [normed_field 𝕜] [normed_space 𝕜 E] (f : linear_map 𝕜 𝕜 E) : continuous_linear_map 𝕜 𝕜 E :=
  linear_map.mk_continuous f (norm (coe_fn f 1)) sorry

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous_of_exists_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) (h : ∃ (C : ℝ), ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) :
    continuous_linear_map 𝕜 E F :=
  continuous_linear_map.mk f

theorem continuous_of_linear_of_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] {f : E → F}
    (h_add : ∀ (x y : E), f (x + y) = f x + f y) (h_smul : ∀ (c : 𝕜) (x : E), f (c • x) = c • f x)
    {C : ℝ} (h_bound : ∀ (x : E), norm (f x) ≤ C * norm x) : continuous f :=
  let φ : linear_map 𝕜 E F := linear_map.mk f h_add h_smul;
  linear_map.continuous_of_bound φ C h_bound

@[simp] theorem linear_map.mk_continuous_coe {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) (C : ℝ) (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) :
    ↑(linear_map.mk_continuous f C h) = f :=
  rfl

@[simp] theorem linear_map.mk_continuous_apply {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) (C : ℝ) (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) (x : E) :
    coe_fn (linear_map.mk_continuous f C h) x = coe_fn f x :=
  rfl

@[simp] theorem linear_map.mk_continuous_of_exists_bound_coe {𝕜 : Type u_1} {E : Type u_2}
    {F : Type u_3} [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] (f : linear_map 𝕜 E F)
    (h : ∃ (C : ℝ), ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) :
    ↑(linear_map.mk_continuous_of_exists_bound f h) = f :=
  rfl

@[simp] theorem linear_map.mk_continuous_of_exists_bound_apply {𝕜 : Type u_1} {E : Type u_2}
    {F : Type u_3} [normed_group E] [normed_group F] [normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] (f : linear_map 𝕜 E F)
    (h : ∃ (C : ℝ), ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) (x : E) :
    coe_fn (linear_map.mk_continuous_of_exists_bound f h) x = coe_fn f x :=
  rfl

@[simp] theorem linear_map.to_continuous_linear_map₁_coe {𝕜 : Type u_1} {E : Type u_2}
    [normed_group E] [normed_field 𝕜] [normed_space 𝕜 E] (f : linear_map 𝕜 𝕜 E) :
    ↑(linear_map.to_continuous_linear_map₁ f) = f :=
  rfl

@[simp] theorem linear_map.to_continuous_linear_map₁_apply {𝕜 : Type u_1} {E : Type u_2}
    [normed_group E] [normed_field 𝕜] [normed_space 𝕜 E] (f : linear_map 𝕜 𝕜 E) (x : 𝕜) :
    coe_fn (linear_map.to_continuous_linear_map₁ f) x = coe_fn f x :=
  rfl

theorem linear_map.continuous_iff_is_closed_ker {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [normed_field 𝕜] [normed_space 𝕜 E] {f : linear_map 𝕜 E 𝕜} :
    continuous ⇑f ↔ is_closed ↑(linear_map.ker f) :=
  sorry

theorem linear_map.bound_of_shell {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < norm c)
    (hf : ∀ (x : E), ε / norm c ≤ norm x → norm x < ε → norm (coe_fn f x) ≤ C * norm x) (x : E) :
    norm (coe_fn f x) ≤ C * norm x :=
  sorry

/-- A continuous linear map between normed spaces is bounded when the field is nondiscrete. The
continuity ensures boundedness on a ball of some radius `ε`. The nondiscreteness is then used to
rescale any element into an element of norm in `[ε/C, ε]`, whose image has a controlled norm. The
norm control for the original element follows by rescaling. -/
theorem linear_map.bound_of_continuous {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : linear_map 𝕜 E F) (hf : continuous ⇑f) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (x : E), norm (coe_fn f x) ≤ C * norm x :=
  sorry

namespace continuous_linear_map


theorem bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (x : E), norm (coe_fn f x) ≤ C * norm x :=
  linear_map.bound_of_continuous (to_linear_map f) (cont f)

theorem is_O_id {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) (l : filter E) : asymptotics.is_O (⇑f) (fun (x : E) => x) l :=
  sorry

theorem is_O_comp {𝕜 : Type u_1} {F : Type u_3} {G : Type u_4} [normed_group F] [normed_group G]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 F] [normed_space 𝕜 G] {α : Type u_2}
    (g : continuous_linear_map 𝕜 F G) (f : α → F) (l : filter α) :
    asymptotics.is_O (fun (x' : α) => coe_fn g (f x')) f l :=
  asymptotics.is_O.comp_tendsto (is_O_id g ⊤) le_top

theorem is_O_sub {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) (l : filter E) (x : E) :
    asymptotics.is_O (fun (x' : E) => coe_fn f (x' - x)) (fun (x' : E) => x' - x) l :=
  is_O_comp f (fun (x' : E) => x' - x) l

/-- A linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def of_homothety {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : linear_map 𝕜 E F)
    (a : ℝ) (hf : ∀ (x : E), norm (coe_fn f x) = a * norm x) : continuous_linear_map 𝕜 E F :=
  linear_map.mk_continuous f a sorry

theorem to_span_singleton_homothety (𝕜 : Type u_1) {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] (x : E) (c : 𝕜) :
    norm (coe_fn (linear_map.to_span_singleton 𝕜 E x) c) = norm x * norm c :=
  sorry

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `E` to the span of `x`.-/
def to_span_singleton (𝕜 : Type u_1) {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] (x : E) : continuous_linear_map 𝕜 𝕜 E :=
  of_homothety (linear_map.to_span_singleton 𝕜 E x) (norm x) (to_span_singleton_homothety 𝕜 x)

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) : ℝ :=
  Inf (set_of fun (c : ℝ) => 0 ≤ c ∧ ∀ (x : E), norm (coe_fn f x) ≤ c * norm x)

protected instance has_op_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] :
    has_norm (continuous_linear_map 𝕜 E F) :=
  has_norm.mk op_norm

theorem norm_def {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) :
    norm f = Inf (set_of fun (c : ℝ) => 0 ≤ c ∧ ∀ (x : E), norm (coe_fn f x) ≤ c * norm x) :=
  rfl

-- So that invocations of `real.Inf_le` make sense: we show that the set of

-- bounds is nonempty and bounded below.

theorem bounds_nonempty {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} :
    ∃ (c : ℝ), c ∈ set_of fun (c : ℝ) => 0 ≤ c ∧ ∀ (x : E), norm (coe_fn f x) ≤ c * norm x :=
  sorry

theorem bounds_bdd_below {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} :
    bdd_below (set_of fun (c : ℝ) => 0 ≤ c ∧ ∀ (x : E), norm (coe_fn f x) ≤ c * norm x) :=
  sorry

theorem op_norm_nonneg {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) : 0 ≤ norm f :=
  sorry

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) (x : E) : norm (coe_fn f x) ≤ norm f * norm x :=
  sorry

theorem le_op_norm_of_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) {c : ℝ} {x : E} (h : norm x ≤ c) :
    norm (coe_fn f x) ≤ norm f * c :=
  le_trans (le_op_norm f x) (mul_le_mul_of_nonneg_left h (op_norm_nonneg f))

theorem le_of_op_norm_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) {c : ℝ} (h : norm f ≤ c) (x : E) :
    norm (coe_fn f x) ≤ c * norm x :=
  has_le.le.trans (le_op_norm f x) (mul_le_mul_of_nonneg_right h (norm_nonneg x))

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) :
    lipschitz_with { val := norm f, property := op_norm_nonneg f } ⇑f :=
  sorry

theorem ratio_le_op_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) (x : E) : norm (coe_fn f x) / norm x ≤ norm f :=
  div_le_of_nonneg_of_le_mul (norm_nonneg x) (op_norm_nonneg f) (le_op_norm f x)

/-- The image of the unit ball under a continuous linear map is bounded. -/
theorem unit_le_op_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) (x : E) : norm x ≤ 1 → norm (coe_fn f x) ≤ norm f :=
  mul_one (norm f) ▸ le_op_norm_of_le f

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem op_norm_le_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ (x : E), norm (coe_fn f x) ≤ M * norm x) : norm f ≤ M :=
  real.Inf_le (set_of fun (c : ℝ) => 0 ≤ c ∧ ∀ (x : E), norm (coe_fn f x) ≤ c * norm x)
    bounds_bdd_below { left := hMp, right := hM }

theorem op_norm_le_of_lipschitz {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} {K : nnreal} (hf : lipschitz_with K ⇑f) : norm f ≤ ↑K :=
  sorry

theorem op_norm_le_of_shell {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : 1 < norm c)
    (hf : ∀ (x : E), ε / norm c ≤ norm x → norm x < ε → norm (coe_fn f x) ≤ C * norm x) :
    norm f ≤ C :=
  op_norm_le_bound f hC (linear_map.bound_of_shell (↑f) ε_pos hc hf)

theorem op_norm_le_of_ball {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C)
    (hf : ∀ (x : E), x ∈ metric.ball 0 ε → norm (coe_fn f x) ≤ C * norm x) : norm f ≤ C :=
  sorry

theorem op_norm_le_of_nhds_zero {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} {C : ℝ} (hC : 0 ≤ C)
    (hf : filter.eventually (fun (x : E) => norm (coe_fn f x) ≤ C * norm x) (nhds 0)) :
    norm f ≤ C :=
  sorry

theorem op_norm_le_of_shell' {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {f : continuous_linear_map 𝕜 E F} {ε : ℝ} {C : ℝ} (ε_pos : 0 < ε) (hC : 0 ≤ C) {c : 𝕜}
    (hc : norm c < 1)
    (hf : ∀ (x : E), ε * norm c ≤ norm x → norm x < ε → norm (coe_fn f x) ≤ C * norm x) :
    norm f ≤ C :=
  sorry

theorem op_norm_eq_of_bounds {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    {φ : continuous_linear_map 𝕜 E F} {M : ℝ} (M_nonneg : 0 ≤ M)
    (h_above : ∀ (x : E), norm (coe_fn φ x) ≤ M * norm x)
    (h_below : ∀ (N : ℝ), N ≥ 0 → (∀ (x : E), norm (coe_fn φ x) ≤ N * norm x) → M ≤ N) :
    norm φ = M :=
  sorry

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) (g : continuous_linear_map 𝕜 E F) :
    norm (f + g) ≤ norm f + norm g :=
  sorry

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) : norm f = 0 ↔ f = 0 :=
  sorry

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
theorem norm_id_le {𝕜 : Type u_1} {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] : norm (id 𝕜 E) ≤ 1 :=
  sorry

/-- If a space is non-trivial, then the norm of the identity equals `1`. -/
theorem norm_id {𝕜 : Type u_1} {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] [nontrivial E] : norm (id 𝕜 E) = 1 :=
  sorry

@[simp] theorem norm_id_field {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] : norm (id 𝕜 𝕜) = 1 :=
  norm_id

@[simp] theorem norm_id_field' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] : norm 1 = 1 :=
  norm_id_field

theorem op_norm_smul_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (c : 𝕜)
    (f : continuous_linear_map 𝕜 E F) : norm (c • f) ≤ norm c * norm f :=
  sorry

theorem op_norm_neg {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) : norm (-f) = norm f :=
  sorry

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
protected instance to_normed_group {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] :
    normed_group (continuous_linear_map 𝕜 E F) :=
  normed_group.of_core (continuous_linear_map 𝕜 E F) sorry

protected instance to_normed_space {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] :
    normed_space 𝕜 (continuous_linear_map 𝕜 E F) :=
  normed_space.mk op_norm_smul_le

/-- The operator norm is submultiplicative. -/
theorem op_norm_comp_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [normed_group E]
    [normed_group F] [normed_group G] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] [normed_space 𝕜 G] (h : continuous_linear_map 𝕜 F G)
    (f : continuous_linear_map 𝕜 E F) : norm (comp h f) ≤ norm h * norm f :=
  sorry

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
protected instance to_normed_ring {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] : normed_ring (continuous_linear_map 𝕜 E E) :=
  normed_ring.mk sorry op_norm_comp_le

/-- For a nonzero normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
protected instance to_normed_algebra {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [nontrivial E] :
    normed_algebra 𝕜 (continuous_linear_map 𝕜 E E) :=
  normed_algebra.mk sorry

/-- A continuous linear map is automatically uniformly continuous. -/
protected theorem uniform_continuous {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) : uniform_continuous ⇑f :=
  lipschitz_with.uniform_continuous (lipschitz f)

/-- A continuous linear map is an isometry if and only if it preserves the norm. -/
theorem isometry_iff_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) : isometry ⇑f ↔ ∀ (x : E), norm (coe_fn f x) = norm x :=
  add_monoid_hom.isometry_iff_norm (linear_map.to_add_monoid_hom (to_linear_map f))

theorem homothety_norm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    [nontrivial E] (f : continuous_linear_map 𝕜 E F) {a : ℝ}
    (hf : ∀ (x : E), norm (coe_fn f x) = a * norm x) : norm f = a :=
  sorry

theorem to_span_singleton_norm {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] (x : E) :
    norm (to_span_singleton 𝕜 x) = norm x :=
  homothety_norm (to_span_singleton 𝕜 x) (to_span_singleton_homothety 𝕜 x)

theorem uniform_embedding_of_bound {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (f : continuous_linear_map 𝕜 E F) {K : nnreal}
    (hf : ∀ (x : E), norm x ≤ ↑K * norm (coe_fn f x)) : uniform_embedding ⇑f :=
  antilipschitz_with.uniform_embedding (linear_map.antilipschitz_of_bound (to_linear_map f) hf)
    (continuous_linear_map.uniform_continuous f)

/-- If a continuous linear map is a uniform embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_uniform_embedding {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] (f : continuous_linear_map 𝕜 E F) (hf : uniform_embedding ⇑f) :
    ∃ (K : nnreal), antilipschitz_with K ⇑f :=
  sorry

/-- If the target space is complete, the space of continuous linear maps with its norm is also
complete. -/
protected instance complete_space {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    [complete_space F] : complete_space (continuous_linear_map 𝕜 E F) :=
  sorry

/-- Extension of a continuous linear map `f : E →L[𝕜] F`, with `E` a normed space and `F` a complete
    normed space, along a uniform and dense embedding `e : E →L[𝕜] G`.  -/
/- extension of `f` is continuous -/

def extend {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [normed_group E]
    [normed_group F] [normed_group G] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] [normed_space 𝕜 G] (f : continuous_linear_map 𝕜 E F) [complete_space F]
    (e : continuous_linear_map 𝕜 E G) (h_dense : dense_range ⇑e) (h_e : uniform_inducing ⇑e) :
    continuous_linear_map 𝕜 G F :=
  (fun (cont : continuous (dense_inducing.extend sorry ⇑f)) =>
      (fun (eq : ∀ (b : E), dense_inducing.extend sorry (⇑f) (coe_fn e b) = coe_fn f b) =>
          mk (linear_map.mk (dense_inducing.extend sorry ⇑f) sorry sorry))
        sorry)
    sorry

/- extension of `f` agrees with `f` on the domain of the embedding `e` -/

theorem extend_unique {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [normed_group E]
    [normed_group F] [normed_group G] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] [normed_space 𝕜 G] (f : continuous_linear_map 𝕜 E F) [complete_space F]
    (e : continuous_linear_map 𝕜 E G) (h_dense : dense_range ⇑e) (h_e : uniform_inducing ⇑e)
    (g : continuous_linear_map 𝕜 G F) (H : comp g e = f) : extend f e h_dense h_e = g :=
  injective_coe_fn
    (uniformly_extend_unique h_e h_dense (iff.mp ext_iff H) (continuous_linear_map.continuous g))

@[simp] theorem extend_zero {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4}
    [normed_group E] [normed_group F] [normed_group G] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] [normed_space 𝕜 F] [normed_space 𝕜 G] [complete_space F]
    (e : continuous_linear_map 𝕜 E G) (h_dense : dense_range ⇑e) (h_e : uniform_inducing ⇑e) :
    extend 0 e h_dense h_e = 0 :=
  extend_unique 0 e h_dense h_e 0 (zero_comp e)

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the norm
    of the extension of `f` along `e` is bounded by `N * ∥f∥`. -/
theorem op_norm_extend_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4}
    [normed_group E] [normed_group F] [normed_group G] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] [normed_space 𝕜 F] [normed_space 𝕜 G] (f : continuous_linear_map 𝕜 E F)
    [complete_space F] (e : continuous_linear_map 𝕜 E G) (h_dense : dense_range ⇑e) {N : nnreal}
    (h_e : ∀ (x : E), norm x ≤ ↑N * norm (coe_fn e x)) :
    norm
          (extend f e h_dense
            (uniform_embedding.to_uniform_inducing (uniform_embedding_of_bound e h_e))) ≤
        ↑N * norm f :=
  sorry

end continuous_linear_map


theorem linear_isometry.norm_to_continuous_linear_map {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] [nontrivial E] (f : linear_isometry 𝕜 E F) :
    norm (linear_isometry.to_continuous_linear_map f) = 1 :=
  sorry

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
theorem linear_map.mk_continuous_norm_le {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] (f : linear_map 𝕜 E F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (x : E), norm (coe_fn f x) ≤ C * norm x) : norm (linear_map.mk_continuous f C h) ≤ C :=
  continuous_linear_map.op_norm_le_bound (linear_map.mk_continuous f C h) hC h

namespace continuous_linear_map


/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp] theorem norm_smul_right_apply {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (c : continuous_linear_map 𝕜 E 𝕜) (f : F) : norm (smul_right c f) = norm c * norm f :=
  sorry

/-- Given `c : c : E →L[𝕜] 𝕜`, `c.smul_rightL` is the continuous linear map from `F` to `E →L[𝕜] F`
sending `f` to `λ e, c e • f`. -/
def smul_rightL {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (c : continuous_linear_map 𝕜 E 𝕜) : continuous_linear_map 𝕜 F (continuous_linear_map 𝕜 E F) :=
  linear_map.mk_continuous (smul_rightₗ c) (norm c) sorry

@[simp] theorem norm_smul_rightL_apply {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (c : continuous_linear_map 𝕜 E 𝕜) (f : F) : norm (coe_fn (smul_rightL c) f) = norm c * norm f :=
  sorry

@[simp] theorem norm_smul_rightL {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (c : continuous_linear_map 𝕜 E 𝕜) [nontrivial F] : norm (smul_rightL c) = norm c :=
  homothety_norm (smul_rightL c) (norm_smul_right_apply c)

/-- The linear map obtained by applying a continuous linear map at a given vector. -/
def applyₗ (𝕜 : Type u_1) {E : Type u_2} (F : Type u_3) [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (v : E) :
    linear_map 𝕜 (continuous_linear_map 𝕜 E F) F :=
  linear_map.mk (fun (f : continuous_linear_map 𝕜 E F) => coe_fn f v) sorry sorry

theorem continuous_applyₗ (𝕜 : Type u_1) {E : Type u_2} (F : Type u_3) [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (v : E) :
    continuous ⇑(applyₗ 𝕜 F v) :=
  sorry

/-- The continuous linear map obtained by applying a continuous linear map at a given vector. -/
def apply (𝕜 : Type u_1) {E : Type u_2} (F : Type u_3) [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (v : E) :
    continuous_linear_map 𝕜 (continuous_linear_map 𝕜 E F) F :=
  mk (applyₗ 𝕜 F v)

@[simp] theorem apply_apply {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (v : E)
    (f : continuous_linear_map 𝕜 E F) : coe_fn (apply 𝕜 F v) f = coe_fn f v :=
  rfl

/-- Left-multiplication in a normed algebra, considered as a continuous linear map. -/
def lmul_left (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5) [normed_ring 𝕜']
    [normed_algebra 𝕜 𝕜'] : 𝕜' → continuous_linear_map 𝕜 𝕜' 𝕜' :=
  fun (x : 𝕜') => linear_map.mk_continuous (algebra.lmul_left 𝕜 x) (norm x) sorry

/-- Right-multiplication in a normed algebra, considered as a continuous linear map. -/
def lmul_right (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5) [normed_ring 𝕜']
    [normed_algebra 𝕜 𝕜'] : 𝕜' → continuous_linear_map 𝕜 𝕜' 𝕜' :=
  fun (x : 𝕜') => linear_map.mk_continuous (algebra.lmul_right 𝕜 x) (norm x) sorry

/-- Simultaneous left- and right-multiplication in a normed algebra, considered as a continuous
linear map. -/
def lmul_left_right (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5) [normed_ring 𝕜']
    [normed_algebra 𝕜 𝕜'] (vw : 𝕜' × 𝕜') : continuous_linear_map 𝕜 𝕜' 𝕜' :=
  comp (lmul_right 𝕜 𝕜' (prod.snd vw)) (lmul_left 𝕜 𝕜' (prod.fst vw))

@[simp] theorem lmul_left_apply (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5)
    [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] (x : 𝕜') (y : 𝕜') :
    coe_fn (lmul_left 𝕜 𝕜' x) y = x * y :=
  rfl

@[simp] theorem lmul_right_apply (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5)
    [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] (x : 𝕜') (y : 𝕜') :
    coe_fn (lmul_right 𝕜 𝕜' x) y = y * x :=
  rfl

@[simp] theorem lmul_left_right_apply (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5)
    [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] (vw : 𝕜' × 𝕜') (x : 𝕜') :
    coe_fn (lmul_left_right 𝕜 𝕜' vw) x = prod.fst vw * x * prod.snd vw :=
  rfl

/-- `𝕜`-linear continuous function induced by a `𝕜'`-linear continuous function when `𝕜'` is a
normed algebra over `𝕜`. -/
def restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {𝕜' : Type u_5} [normed_field 𝕜']
    [normed_algebra 𝕜 𝕜'] {E' : Type u_6} [normed_group E'] [normed_space 𝕜 E'] [normed_space 𝕜' E']
    [is_scalar_tower 𝕜 𝕜' E'] {F' : Type u_7} [normed_group F'] [normed_space 𝕜 F']
    [normed_space 𝕜' F'] [is_scalar_tower 𝕜 𝕜' F'] (f : continuous_linear_map 𝕜' E' F') :
    continuous_linear_map 𝕜 E' F' :=
  mk
    (linear_map.mk (linear_map.to_fun (linear_map.restrict_scalars 𝕜 (to_linear_map f))) sorry
      sorry)

@[simp] theorem restrict_scalars_coe_eq_coe (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_5} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E' : Type u_6} [normed_group E']
    [normed_space 𝕜 E'] [normed_space 𝕜' E'] [is_scalar_tower 𝕜 𝕜' E'] {F' : Type u_7}
    [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F'] [is_scalar_tower 𝕜 𝕜' F']
    (f : continuous_linear_map 𝕜' E' F') :
    ↑(restrict_scalars 𝕜 f) = linear_map.restrict_scalars 𝕜 ↑f :=
  rfl

@[simp] theorem restrict_scalars_coe_eq_coe' (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_5} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E' : Type u_6} [normed_group E']
    [normed_space 𝕜 E'] [normed_space 𝕜' E'] [is_scalar_tower 𝕜 𝕜' E'] {F' : Type u_7}
    [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F'] [is_scalar_tower 𝕜 𝕜' F']
    (f : continuous_linear_map 𝕜' E' F') : ⇑(restrict_scalars 𝕜 f) = ⇑f :=
  rfl

protected instance has_scalar_extend_scalars {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] {𝕜' : Type u_5} [normed_field 𝕜']
    [normed_algebra 𝕜 𝕜'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F']
    [is_scalar_tower 𝕜 𝕜' F'] : has_scalar 𝕜' (continuous_linear_map 𝕜 E F') :=
  has_scalar.mk
    fun (c : 𝕜') (f : continuous_linear_map 𝕜 E F') =>
      linear_map.mk_continuous (c • to_linear_map f) (norm c * norm f) sorry

protected instance module_extend_scalars {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] {𝕜' : Type u_5} [normed_field 𝕜']
    [normed_algebra 𝕜 𝕜'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F']
    [is_scalar_tower 𝕜 𝕜' F'] : module 𝕜' (continuous_linear_map 𝕜 E F') :=
  semimodule.mk sorry sorry

protected instance normed_space_extend_scalars {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] {𝕜' : Type u_5} [normed_field 𝕜']
    [normed_algebra 𝕜 𝕜'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F']
    [is_scalar_tower 𝕜 𝕜' F'] : normed_space 𝕜' (continuous_linear_map 𝕜 E F') :=
  normed_space.mk sorry

/-- When `f` is a continuous linear map taking values in `S`, then `λb, f b • x` is a
continuous linear map. -/
def smul_algebra_right {𝕜 : Type u_1} {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] {𝕜' : Type u_5} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {F' : Type u_6}
    [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F'] [is_scalar_tower 𝕜 𝕜' F']
    (f : continuous_linear_map 𝕜 E 𝕜') (x : F') : continuous_linear_map 𝕜 E F' :=
  mk
    (linear_map.mk (linear_map.to_fun (linear_map.smul_algebra_right (to_linear_map f) x)) sorry
      sorry)

@[simp] theorem smul_algebra_right_apply {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] {𝕜' : Type u_5} [normed_field 𝕜']
    [normed_algebra 𝕜 𝕜'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] [normed_space 𝕜' F']
    [is_scalar_tower 𝕜 𝕜' F'] (f : continuous_linear_map 𝕜 E 𝕜') (x : F') (c : E) :
    coe_fn (smul_algebra_right f x) c = coe_fn f c • x :=
  rfl

end continuous_linear_map


/-- The continuous linear map of inclusion from a submodule of `K` into `E`. -/
def submodule.subtype_continuous {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] (K : submodule 𝕜 E) :
    continuous_linear_map 𝕜 (↥K) E :=
  linear_map.mk_continuous (submodule.subtype K) 1 sorry

@[simp] theorem submodule.subtype_continuous_apply {𝕜 : Type u_1} {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] (K : submodule 𝕜 E) (v : ↥K) :
    coe_fn (submodule.subtype_continuous K) v = ↑v :=
  rfl

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we

-- don't have bundled continuous additive homomorphisms.

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem continuous_linear_map.has_sum {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] {f : ι → M}
    (φ : continuous_linear_map R M M₂) {x : M} (hf : has_sum f x) :
    has_sum (fun (b : ι) => coe_fn φ (f b)) (coe_fn φ x) :=
  sorry

theorem has_sum.mapL {ι : Type u_5} {R : Type u_6} {M : Type u_7} {M₂ : Type u_8} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂]
    [topological_space M] [topological_space M₂] {f : ι → M} (φ : continuous_linear_map R M M₂)
    {x : M} (hf : has_sum f x) : has_sum (fun (b : ι) => coe_fn φ (f b)) (coe_fn φ x) :=
  continuous_linear_map.has_sum

protected theorem continuous_linear_map.summable {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] {f : ι → M}
    (φ : continuous_linear_map R M M₂) (hf : summable f) : summable fun (b : ι) => coe_fn φ (f b) :=
  has_sum.summable (has_sum.mapL φ (summable.has_sum hf))

theorem summable.mapL {ι : Type u_5} {R : Type u_6} {M : Type u_7} {M₂ : Type u_8} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂] [semimodule R M₂]
    [topological_space M] [topological_space M₂] {f : ι → M} (φ : continuous_linear_map R M M₂)
    (hf : summable f) : summable fun (b : ι) => coe_fn φ (f b) :=
  continuous_linear_map.summable

protected theorem continuous_linear_map.map_tsum {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] [t2_space M₂] {f : ι → M}
    (φ : continuous_linear_map R M M₂) (hf : summable f) :
    coe_fn φ (tsum fun (z : ι) => f z) = tsum fun (z : ι) => coe_fn φ (f z) :=
  Eq.symm (has_sum.tsum_eq (has_sum.mapL φ (summable.has_sum hf)))

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem continuous_linear_equiv.has_sum {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] {f : ι → M}
    (e : continuous_linear_equiv R M M₂) {y : M₂} :
    has_sum (fun (b : ι) => coe_fn e (f b)) y ↔
        has_sum f (coe_fn (continuous_linear_equiv.symm e) y) :=
  sorry

protected theorem continuous_linear_equiv.summable {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] {f : ι → M}
    (e : continuous_linear_equiv R M M₂) : (summable fun (b : ι) => coe_fn e (f b)) ↔ summable f :=
  sorry

theorem continuous_linear_equiv.tsum_eq_iff {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] [t2_space M] [t2_space M₂]
    {f : ι → M} (e : continuous_linear_equiv R M M₂) {y : M₂} :
    (tsum fun (z : ι) => coe_fn e (f z)) = y ↔
        (tsum fun (z : ι) => f z) = coe_fn (continuous_linear_equiv.symm e) y :=
  sorry

protected theorem continuous_linear_equiv.map_tsum {ι : Type u_5} {R : Type u_6} {M : Type u_7}
    {M₂ : Type u_8} [semiring R] [add_comm_monoid M] [semimodule R M] [add_comm_monoid M₂]
    [semimodule R M₂] [topological_space M] [topological_space M₂] [t2_space M] [t2_space M₂]
    {f : ι → M} (e : continuous_linear_equiv R M M₂) :
    coe_fn e (tsum fun (z : ι) => f z) = tsum fun (z : ι) => coe_fn e (f z) :=
  sorry

namespace continuous_linear_equiv


protected theorem lipschitz {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) : lipschitz_with (nnnorm ↑e) ⇑e :=
  continuous_linear_map.lipschitz ↑e

protected theorem antilipschitz {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) :
    antilipschitz_with (nnnorm ↑(continuous_linear_equiv.symm e)) ⇑e :=
  lipschitz_with.to_right_inverse
    (continuous_linear_equiv.lipschitz (continuous_linear_equiv.symm e))
    (linear_equiv.left_inv (to_linear_equiv e))

theorem is_O_comp {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) {α : Type u_4} (f : α → E) (l : filter α) :
    asymptotics.is_O (fun (x' : α) => coe_fn e (f x')) f l :=
  continuous_linear_map.is_O_comp (↑e) f l

theorem is_O_sub {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) (l : filter E) (x : E) :
    asymptotics.is_O (fun (x' : E) => coe_fn e (x' - x)) (fun (x' : E) => x' - x) l :=
  continuous_linear_map.is_O_sub (↑e) l x

theorem is_O_comp_rev {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) {α : Type u_4} (f : α → E) (l : filter α) :
    asymptotics.is_O f (fun (x' : α) => coe_fn e (f x')) l :=
  asymptotics.is_O.congr_left (fun (_x : α) => symm_apply_apply e (f _x))
    (is_O_comp (continuous_linear_equiv.symm e) (fun (x' : α) => coe_fn e (f x')) l)

theorem is_O_sub_rev {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) (l : filter E) (x : E) :
    asymptotics.is_O (fun (x' : E) => x' - x) (fun (x' : E) => coe_fn e (x' - x)) l :=
  is_O_comp_rev e (fun (x' : E) => x' - x) l

/-- A continuous linear equiv is a uniform embedding. -/
theorem uniform_embedding {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) : uniform_embedding ⇑e :=
  antilipschitz_with.uniform_embedding (continuous_linear_equiv.antilipschitz e)
    (lipschitz_with.uniform_continuous (continuous_linear_equiv.lipschitz e))

theorem one_le_norm_mul_norm_symm {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) [nontrivial E] :
    1 ≤ norm ↑e * norm ↑(continuous_linear_equiv.symm e) :=
  sorry

theorem norm_pos {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) [nontrivial E] : 0 < norm ↑e :=
  pos_of_mul_pos_right (lt_of_lt_of_le zero_lt_one (one_le_norm_mul_norm_symm e))
    (norm_nonneg ↑(continuous_linear_equiv.symm e))

theorem norm_symm_pos {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) [nontrivial E] :
    0 < norm ↑(continuous_linear_equiv.symm e) :=
  pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one (one_le_norm_mul_norm_symm e)) (norm_nonneg ↑e)

theorem subsingleton_or_norm_symm_pos {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : continuous_linear_equiv 𝕜 E F) :
    subsingleton E ∨ 0 < norm ↑(continuous_linear_equiv.symm e) :=
  or.dcases_on (subsingleton_or_nontrivial E) (fun (_i : subsingleton E) => Or.inl _i)
    fun (_i : nontrivial E) => Or.inr (norm_symm_pos e)

theorem subsingleton_or_nnnorm_symm_pos {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] (e : continuous_linear_equiv 𝕜 E F) :
    subsingleton E ∨ 0 < nnnorm ↑(continuous_linear_equiv.symm e) :=
  subsingleton_or_norm_symm_pos e

theorem homothety_inverse {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (a : ℝ)
    (ha : 0 < a) (f : linear_equiv 𝕜 E F) :
    (∀ (x : E), norm (coe_fn f x) = a * norm x) →
        ∀ (y : F), norm (coe_fn (linear_equiv.symm f) y) = a⁻¹ * norm y :=
  sorry

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
def of_homothety (𝕜 : Type u_1) {E : Type u_2} {F : Type u_3} [normed_group E] [normed_group F]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : linear_equiv 𝕜 E F)
    (a : ℝ) (ha : 0 < a) (hf : ∀ (x : E), norm (coe_fn f x) = a * norm x) :
    continuous_linear_equiv 𝕜 E F :=
  mk f

theorem to_span_nonzero_singleton_homothety (𝕜 : Type u_1) {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] (x : E) (h : x ≠ 0) (c : 𝕜) :
    norm (coe_fn (linear_equiv.to_span_nonzero_singleton 𝕜 E x h) c) = norm x * norm c :=
  continuous_linear_map.to_span_singleton_homothety 𝕜 x c

/-- Given a nonzero element `x` of a normed space `E` over a field `𝕜`, the natural
    continuous linear equivalence from `E` to the span of `x`.-/
def to_span_nonzero_singleton (𝕜 : Type u_1) {E : Type u_2} [normed_group E]
    [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] (x : E) (h : x ≠ 0) :
    continuous_linear_equiv 𝕜 𝕜 ↥(submodule.span 𝕜 (singleton x)) :=
  of_homothety 𝕜 (linear_equiv.to_span_nonzero_singleton 𝕜 E x h) (norm x) sorry
    (to_span_nonzero_singleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
def coord (𝕜 : Type u_1) {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] (x : E) (h : x ≠ 0) :
    continuous_linear_map 𝕜 (↥(submodule.span 𝕜 (singleton x))) 𝕜 :=
  ↑(continuous_linear_equiv.symm (to_span_nonzero_singleton 𝕜 x h))

theorem coord_norm (𝕜 : Type u_1) {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] (x : E) (h : x ≠ 0) : norm (coord 𝕜 x h) = (norm x⁻¹) :=
  sorry

theorem coord_self (𝕜 : Type u_1) {E : Type u_2} [normed_group E] [nondiscrete_normed_field 𝕜]
    [normed_space 𝕜 E] (x : E) (h : x ≠ 0) :
    coe_fn (coord 𝕜 x h) { val := x, property := submodule.mem_span_singleton_self x } = 1 :=
  linear_equiv.coord_self 𝕜 E x h

end continuous_linear_equiv


theorem linear_equiv.uniform_embedding {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [normed_group E]
    [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
    (e : linear_equiv 𝕜 E F) (h₁ : continuous ⇑e) (h₂ : continuous ⇑(linear_equiv.symm e)) :
    uniform_embedding ⇑e :=
  sorry

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def linear_equiv.to_continuous_linear_equiv_of_bounds {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
    [normed_group E] [normed_group F] [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
    [normed_space 𝕜 F] (e : linear_equiv 𝕜 E F) (C_to : ℝ) (C_inv : ℝ)
    (h_to : ∀ (x : E), norm (coe_fn e x) ≤ C_to * norm x)
    (h_inv : ∀ (x : F), norm (coe_fn (linear_equiv.symm e) x) ≤ C_inv * norm x) :
    continuous_linear_equiv 𝕜 E F :=
  continuous_linear_equiv.mk e

namespace continuous_linear_map


@[simp] theorem lmul_left_norm (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5)
    [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] (v : 𝕜') : norm (lmul_left 𝕜 𝕜' v) = norm v :=
  sorry

@[simp] theorem lmul_right_norm (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5)
    [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] (v : 𝕜') : norm (lmul_right 𝕜 𝕜' v) = norm v :=
  sorry

theorem lmul_left_right_norm_le (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] (𝕜' : Type u_5)
    [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] (vw : 𝕜' × 𝕜') :
    norm (lmul_left_right 𝕜 𝕜' vw) ≤ norm (prod.fst vw) * norm (prod.snd vw) :=
  sorry

end Mathlib