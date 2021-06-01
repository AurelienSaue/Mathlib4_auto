/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.tangent_cone
import Mathlib.analysis.normed_space.units
import Mathlib.analysis.asymptotic_equivalent
import Mathlib.analysis.analytic.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# The Fréchet derivative

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

Finally,

  `has_strict_fderiv_at f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`is_bounded_bilinear_map.has_fderiv_at` twice: first for `has_fderiv_at`, then for
`has_strict_fderiv_at`.

## Main results

In addition to the definition and basic properties of the derivative, this file contains the
usual formulas (and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps
* bounded bilinear maps
* sum of two functions
* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
* multiplication of a function by a scalar function
* multiplication of two scalar functions
* composition of functions (the chain rule)
* inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `analysis.special_functions.trigonometric`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `deriv.lean`.

## Implementation details

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at 𝕜 f x`,
`differentiable_on 𝕜 f s` and `differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s`, defined in `tangent_cone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

Tests for this ability of the simplifier (with more examples) are provided in
`tests/differentiable.lean`.

## Tags

derivative, differentiable, Fréchet, calculus

-/

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L`. This definition
is designed to be specialized for `L = 𝓝 x` (in `has_fderiv_at`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `has_fderiv_within_at`), giving rise to
the notion of Fréchet derivative along the set `s`. -/
def has_fderiv_at_filter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) (x : E) (L : filter E) :=
  asymptotics.is_o (fun (x' : E) => f x' - f x - coe_fn f' (x' - x)) (fun (x' : E) => x' - x) L

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
def has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) (s : set E) (x : E) :=
  has_fderiv_at_filter f f' x (nhds_within x s)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
def has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) (x : E) :=
  has_fderiv_at_filter f f' x (nhds x)

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
def has_strict_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F)
    (f' : continuous_linear_map 𝕜 E F) (x : E) :=
  asymptotics.is_o
    (fun (p : E × E) => f (prod.fst p) - f (prod.snd p) - coe_fn f' (prod.fst p - prod.snd p))
    (fun (p : E × E) => prod.fst p - prod.snd p) (nhds (x, x))

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
def differentiable_within_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    (f : E → F) (s : set E) (x : E) :=
  ∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_within_at f f' s x

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
def differentiable_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (x : E) :=
  ∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_at f f' x

/-- If `f` has a derivative at `x` within `s`, then `fderiv_within 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. -/
def fderiv_within (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (s : set E)
    (x : E) : continuous_linear_map 𝕜 E F :=
  dite (∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_within_at f f' s x)
    (fun (h : ∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_within_at f f' s x) =>
      classical.some h)
    fun (h : ¬∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_within_at f f' s x) => 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
def fderiv (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (x : E) :
    continuous_linear_map 𝕜 E F :=
  dite (∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_at f f' x)
    (fun (h : ∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_at f f' x) => classical.some h)
    fun (h : ¬∃ (f' : continuous_linear_map 𝕜 E F), has_fderiv_at f f' x) => 0

/-- `differentiable_on 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
def differentiable_on (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (s : set E) :=
  ∀ (x : E), x ∈ s → differentiable_within_at 𝕜 f s x

/-- `differentiable 𝕜 f` means that `f` is differentiable at any point. -/
def differentiable (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) :=
  ∀ (x : E), differentiable_at 𝕜 f x

theorem fderiv_within_zero_of_not_differentiable_within_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E}
    (h : ¬differentiable_within_at 𝕜 f s x) : fderiv_within 𝕜 f s x = 0 :=
  sorry

theorem fderiv_zero_of_not_differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (h : ¬differentiable_at 𝕜 f x) : fderiv 𝕜 f x = 0 :=
  sorry

/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `unique_diff_within_at` and `unique_diff_on` indeed imply the
uniqueness of the derivative. -/

/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem has_fderiv_within_at.lim {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) {α : Type u_4} (l : filter α) {c : α → 𝕜} {d : α → E}
    {v : E} (dtop : filter.eventually (fun (n : α) => x + d n ∈ s) l)
    (clim : filter.tendsto (fun (n : α) => norm (c n)) l filter.at_top)
    (cdlim : filter.tendsto (fun (n : α) => c n • d n) l (nhds v)) :
    filter.tendsto (fun (n : α) => c n • (f (x + d n) - f x)) l (nhds (coe_fn f' v)) :=
  sorry

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem has_fderiv_within_at.unique_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {f₁' : continuous_linear_map 𝕜 E F} {x : E}
    {s : set E} (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at f f₁' s x) :
    set.eq_on (⇑f') (⇑f₁') (tangent_cone_at 𝕜 s x) :=
  sorry

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_diff_within_at.eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {f₁' : continuous_linear_map 𝕜 E F} {x : E}
    {s : set E} (H : unique_diff_within_at 𝕜 s x) (hf : has_fderiv_within_at f f' s x)
    (hg : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
  continuous_linear_map.ext_on (and.left H) (has_fderiv_within_at.unique_on hf hg)

theorem unique_diff_on.eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {f₁' : continuous_linear_map 𝕜 E F} {x : E}
    {s : set E} (H : unique_diff_on 𝕜 s) (hx : x ∈ s) (h : has_fderiv_within_at f f' s x)
    (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
  unique_diff_within_at.eq (H x hx) h h₁

/-! ### Basic properties of the derivative -/

theorem has_fderiv_at_filter_iff_tendsto {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E} :
    has_fderiv_at_filter f f' x L ↔
        filter.tendsto (fun (x' : E) => norm (x' - x)⁻¹ * norm (f x' - f x - coe_fn f' (x' - x))) L
          (nhds 0) :=
  sorry

theorem has_fderiv_within_at_iff_tendsto {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} :
    has_fderiv_within_at f f' s x ↔
        filter.tendsto (fun (x' : E) => norm (x' - x)⁻¹ * norm (f x' - f x - coe_fn f' (x' - x)))
          (nhds_within x s) (nhds 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} :
    has_fderiv_at f f' x ↔
        filter.tendsto (fun (x' : E) => norm (x' - x)⁻¹ * norm (f x' - f x - coe_fn f' (x' - x)))
          (nhds x) (nhds 0) :=
  has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_is_o_nhds_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} :
    has_fderiv_at f f' x ↔
        asymptotics.is_o (fun (h : E) => f (x + h) - f x - coe_fn f' h) (fun (h : E) => h)
          (nhds 0) :=
  sorry

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. -/
theorem has_fderiv_at.le_of_lip {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x₀ : E} (hf : has_fderiv_at f f' x₀) {s : set E}
    (hs : s ∈ nhds x₀) {C : nnreal} (hlip : lipschitz_on_with C f s) : norm f' ≤ ↑C :=
  sorry

theorem has_fderiv_at_filter.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L₁ : filter E} {L₂ : filter E}
    (h : has_fderiv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) : has_fderiv_at_filter f f' x L₁ :=
  asymptotics.is_o.mono h hst

theorem has_fderiv_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {t : set E}
    (h : has_fderiv_within_at f f' t x) (hst : s ⊆ t) : has_fderiv_within_at f f' s x :=
  has_fderiv_at_filter.mono h (nhds_within_mono x hst)

theorem has_fderiv_at.has_fderiv_at_filter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (h : has_fderiv_at f f' x) (hL : L ≤ nhds x) : has_fderiv_at_filter f f' x L :=
  has_fderiv_at_filter.mono h hL

theorem has_fderiv_at.has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_at f f' x) : has_fderiv_within_at f f' s x :=
  has_fderiv_at.has_fderiv_at_filter h inf_le_left

theorem has_fderiv_within_at.differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) : differentiable_within_at 𝕜 f s x :=
  Exists.intro f' h

theorem has_fderiv_at.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_fderiv_at f f' x) :
    differentiable_at 𝕜 f x :=
  Exists.intro f' h

@[simp] theorem has_fderiv_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} :
    has_fderiv_within_at f f' set.univ x ↔ has_fderiv_at f f' x :=
  sorry

theorem has_strict_fderiv_at.is_O_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_strict_fderiv_at f f' x) :
    asymptotics.is_O (fun (p : E × E) => f (prod.fst p) - f (prod.snd p))
        (fun (p : E × E) => prod.fst p - prod.snd p) (nhds (x, x)) :=
  iff.mpr (asymptotics.is_O.congr_of_sub (asymptotics.is_o.is_O hf))
    (continuous_linear_map.is_O_comp f' (fun (p : E × E) => prod.fst p - prod.snd p) (nhds (x, x)))

theorem has_fderiv_at_filter.is_O_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (h : has_fderiv_at_filter f f' x L) :
    asymptotics.is_O (fun (x' : E) => f x' - f x) (fun (x' : E) => x' - x) L :=
  iff.mpr (asymptotics.is_O.congr_of_sub (asymptotics.is_o.is_O h))
    (continuous_linear_map.is_O_sub f' L x)

protected theorem has_strict_fderiv_at.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (hf : has_strict_fderiv_at f f' x) : has_fderiv_at f f' x :=
  sorry

protected theorem has_strict_fderiv_at.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (hf : has_strict_fderiv_at f f' x) : differentiable_at 𝕜 f x :=
  has_fderiv_at.differentiable_at (has_strict_fderiv_at.has_fderiv_at hf)

/-- Directional derivative agrees with `has_fderiv`. -/
theorem has_fderiv_at.lim {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_fderiv_at f f' x) (v : E)
    {α : Type u_4} {c : α → 𝕜} {l : filter α}
    (hc : filter.tendsto (fun (n : α) => norm (c n)) l filter.at_top) :
    filter.tendsto (fun (n : α) => c n • (f (x + c n⁻¹ • v) - f x)) l (nhds (coe_fn f' v)) :=
  sorry

theorem has_fderiv_at_unique {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₀' : continuous_linear_map 𝕜 E F} {f₁' : continuous_linear_map 𝕜 E F} {x : E}
    (h₀ : has_fderiv_at f f₀' x) (h₁ : has_fderiv_at f f₁' x) : f₀' = f₁' :=
  unique_diff_within_at.eq unique_diff_within_at_univ
    (eq.mp
      (Eq._oldrec (Eq.refl (has_fderiv_at f f₀' x)) (Eq.symm (propext has_fderiv_within_at_univ)))
      h₀)
    (eq.mp
      (Eq._oldrec (Eq.refl (has_fderiv_at f f₁' x)) (Eq.symm (propext has_fderiv_within_at_univ)))
      h₁)

theorem has_fderiv_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {t : set E}
    (h : t ∈ nhds_within x s) :
    has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
  sorry

theorem has_fderiv_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {t : set E}
    (h : t ∈ nhds x) : has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
  sorry

theorem has_fderiv_within_at.union {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {t : set E}
    (hs : has_fderiv_within_at f f' s x) (ht : has_fderiv_within_at f f' t x) :
    has_fderiv_within_at f f' (s ∪ t) x :=
  sorry

theorem has_fderiv_within_at.nhds_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {t : set E}
    (h : has_fderiv_within_at f f' s x) (ht : s ∈ nhds_within x t) :
    has_fderiv_within_at f f' t x :=
  iff.mp (has_fderiv_within_at_inter' ht) (has_fderiv_within_at.mono h (set.inter_subset_right t s))

theorem has_fderiv_within_at.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) (hs : s ∈ nhds x) : has_fderiv_at f f' x :=
  eq.mp
    (Eq._oldrec (Eq.refl (has_fderiv_within_at f f' set.univ x))
      (propext has_fderiv_within_at_univ))
    (eq.mp
      (Eq._oldrec (Eq.refl (has_fderiv_within_at f f' (set.univ ∩ s) x))
        (propext (has_fderiv_within_at_inter hs)))
      (eq.mp (Eq._oldrec (Eq.refl (has_fderiv_within_at f f' s x)) (Eq.symm (set.univ_inter s))) h))

theorem differentiable_within_at.has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : differentiable_within_at 𝕜 f s x) :
    has_fderiv_within_at f (fderiv_within 𝕜 f s x) s x :=
  sorry

theorem differentiable_at.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : differentiable_at 𝕜 f x) : has_fderiv_at f (fderiv 𝕜 f x) x :=
  sorry

theorem has_fderiv_at.fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_fderiv_at f f' x) :
    fderiv 𝕜 f x = f' :=
  sorry

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
theorem fderiv_at.le_of_lip {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x₀ : E} (hf : differentiable_at 𝕜 f x₀) {s : set E} (hs : s ∈ nhds x₀) {C : nnreal}
    (hlip : lipschitz_on_with C f s) : norm (fderiv 𝕜 f x₀) ≤ ↑C :=
  has_fderiv_at.le_of_lip (differentiable_at.has_fderiv_at hf) hs hlip

theorem has_fderiv_within_at.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 f s x = f' :=
  Eq.symm
    (unique_diff_within_at.eq hxs h
      (differentiable_within_at.has_fderiv_within_at
        (has_fderiv_within_at.differentiable_within_at h)))

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem has_fderiv_within_at_of_not_mem_closure {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : ¬x ∈ closure s) : has_fderiv_within_at f f' s x :=
  sorry

theorem differentiable_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {t : set E} (h : differentiable_within_at 𝕜 f t x)
    (st : s ⊆ t) : differentiable_within_at 𝕜 f s x :=
  Exists.dcases_on h
    fun (f' : continuous_linear_map 𝕜 E F) (hf' : has_fderiv_within_at f f' t x) =>
      Exists.intro f' (has_fderiv_within_at.mono hf' st)

theorem differentiable_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} : differentiable_within_at 𝕜 f set.univ x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {t : set E} (ht : t ∈ nhds x) :
    differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {t : set E} (ht : t ∈ nhds_within x s) :
    differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_at.differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : differentiable_at 𝕜 f x) :
    differentiable_within_at 𝕜 f s x :=
  differentiable_within_at.mono (iff.mpr differentiable_within_at_univ h) (set.subset_univ s)

theorem differentiable.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : differentiable 𝕜 f) : differentiable_at 𝕜 f x :=
  h x

theorem differentiable_within_at.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : differentiable_within_at 𝕜 f s x)
    (hs : s ∈ nhds x) : differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_at.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (h : differentiable_at 𝕜 f x)
    (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_at.has_fderiv_within_at (differentiable_at.has_fderiv_at h)) hxs

theorem differentiable_on.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} {t : set E} (h : differentiable_on 𝕜 f t) (st : s ⊆ t) :
    differentiable_on 𝕜 f s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.mono (h x (st hx)) st

theorem differentiable_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} : differentiable_on 𝕜 f set.univ ↔ differentiable 𝕜 f :=
  sorry

theorem differentiable.differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (h : differentiable 𝕜 f) : differentiable_on 𝕜 f s :=
  differentiable_on.mono (iff.mpr differentiable_on_univ h) (set.subset_univ s)

theorem differentiable_on_of_locally_differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E}
    (h : ∀ (x : E), x ∈ s → ∃ (u : set E), is_open u ∧ x ∈ u ∧ differentiable_on 𝕜 f (s ∩ u)) :
    differentiable_on 𝕜 f s :=
  sorry

theorem fderiv_within_subset {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {t : set E} (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
    (h : differentiable_within_at 𝕜 f t x) : fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.mono (differentiable_within_at.has_fderiv_within_at h) st) ht

@[simp] theorem fderiv_within_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} : fderiv_within 𝕜 f set.univ = fderiv 𝕜 f :=
  sorry

theorem fderiv_within_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {t : set E} (ht : t ∈ nhds x)
    (hs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 f (s ∩ t) x = fderiv_within 𝕜 f s x :=
  sorry

theorem fderiv_within_of_mem_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (h : s ∈ nhds x) : fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
  sorry

theorem fderiv_within_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hs : is_open s) (hx : x ∈ s) :
    fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
  fderiv_within_of_mem_nhds (mem_nhds_sets hs hx)

theorem fderiv_within_eq_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hs : unique_diff_within_at 𝕜 s x)
    (h : differentiable_at 𝕜 f x) : fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (fderiv_within 𝕜 f s x = fderiv 𝕜 f x)) (Eq.symm fderiv_within_univ)))
    (fderiv_within_subset (set.subset_univ s) hs (differentiable_at.differentiable_within_at h))

theorem fderiv_mem_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F}
    {s : set (continuous_linear_map 𝕜 E F)} {x : E} :
    fderiv 𝕜 f x ∈ s ↔
        differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ s ∨ 0 ∈ s ∧ ¬differentiable_at 𝕜 f x :=
  sorry

/-! ### Deducing continuity from differentiability -/

theorem has_fderiv_at_filter.tendsto_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E} (hL : L ≤ nhds x)
    (h : has_fderiv_at_filter f f' x L) : filter.tendsto f L (nhds (f x)) :=
  sorry

theorem has_fderiv_within_at.continuous_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) : continuous_within_at f s x :=
  has_fderiv_at_filter.tendsto_nhds inf_le_left h

theorem has_fderiv_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_fderiv_at f f' x) :
    continuous_at f x :=
  has_fderiv_at_filter.tendsto_nhds (le_refl (nhds x)) h

theorem differentiable_within_at.continuous_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : differentiable_within_at 𝕜 f s x) :
    continuous_within_at f s x :=
  sorry

theorem differentiable_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : differentiable_at 𝕜 f x) : continuous_at f x :=
  sorry

theorem differentiable_on.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (h : differentiable_on 𝕜 f s) : continuous_on f s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.continuous_within_at (h x hx)

theorem differentiable.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (h : differentiable 𝕜 f) : continuous f :=
  iff.mpr continuous_iff_continuous_at fun (x : E) => differentiable_at.continuous_at (h x)

protected theorem has_strict_fderiv_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (hf : has_strict_fderiv_at f f' x) : continuous_at f x :=
  has_fderiv_at.continuous_at (has_strict_fderiv_at.has_fderiv_at hf)

theorem has_strict_fderiv_at.is_O_sub_rev {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {f' : continuous_linear_equiv 𝕜 E F} (hf : has_strict_fderiv_at f (↑f') x) :
    asymptotics.is_O (fun (p : E × E) => prod.fst p - prod.snd p)
        (fun (p : E × E) => f (prod.fst p) - f (prod.snd p)) (nhds (x, x)) :=
  sorry

theorem has_fderiv_at_filter.is_O_sub_rev {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {L : filter E} {f' : continuous_linear_equiv 𝕜 E F}
    (hf : has_fderiv_at_filter f (↑f') x L) :
    asymptotics.is_O (fun (x' : E) => x' - x) (fun (x' : E) => f x' - f x) L :=
  asymptotics.is_O.congr (fun (_x : E) => rfl)
    (fun (_x : E) => sub_add_cancel (f _x - f x) (coe_fn (↑f') (_x - x)))
    (asymptotics.is_O.trans (continuous_linear_equiv.is_O_sub_rev f' L x)
      (asymptotics.is_o.right_is_O_add
        (asymptotics.is_o.trans_is_O hf (continuous_linear_equiv.is_O_sub_rev f' L x))))

/-! ### congr properties of the derivative -/

theorem filter.eventually_eq.has_strict_fderiv_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f₀ : E → F} {f₁ : E → F} {f₀' : continuous_linear_map 𝕜 E F}
    {f₁' : continuous_linear_map 𝕜 E F} {x : E} (h : filter.eventually_eq (nhds x) f₀ f₁)
    (h' : ∀ (y : E), coe_fn f₀' y = coe_fn f₁' y) :
    has_strict_fderiv_at f₀ f₀' x ↔ has_strict_fderiv_at f₁ f₁' x :=
  sorry

theorem has_strict_fderiv_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (h : has_strict_fderiv_at f f' x) (h₁ : filter.eventually_eq (nhds x) f f₁) :
    has_strict_fderiv_at f₁ f' x :=
  iff.mp (filter.eventually_eq.has_strict_fderiv_at_iff h₁ fun (_x : E) => rfl) h

theorem filter.eventually_eq.has_fderiv_at_filter_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f₀ : E → F} {f₁ : E → F} {f₀' : continuous_linear_map 𝕜 E F}
    {f₁' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E} (h₀ : filter.eventually_eq L f₀ f₁)
    (hx : f₀ x = f₁ x) (h₁ : ∀ (x : E), coe_fn f₀' x = coe_fn f₁' x) :
    has_fderiv_at_filter f₀ f₀' x L ↔ has_fderiv_at_filter f₁ f₁' x L :=
  sorry

theorem has_fderiv_at_filter.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    {L : filter E} (h : has_fderiv_at_filter f f' x L) (hL : filter.eventually_eq L f₁ f)
    (hx : f₁ x = f x) : has_fderiv_at_filter f₁ f' x L :=
  iff.mpr (filter.eventually_eq.has_fderiv_at_filter_iff hL hx fun (_x : E) => rfl) h

theorem has_fderiv_within_at.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {t : set E}
    (h : has_fderiv_within_at f f' s x) (ht : ∀ (x : E), x ∈ t → f₁ x = f x) (hx : f₁ x = f x)
    (h₁ : t ⊆ s) : has_fderiv_within_at f₁ f' t x :=
  has_fderiv_at_filter.congr_of_eventually_eq (has_fderiv_within_at.mono h h₁)
    (filter.mem_inf_sets_of_right ht) hx

theorem has_fderiv_within_at.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) (hs : ∀ (x : E), x ∈ s → f₁ x = f x) (hx : f₁ x = f x) :
    has_fderiv_within_at f₁ f' s x :=
  has_fderiv_within_at.congr_mono h hs hx (set.subset.refl s)

theorem has_fderiv_within_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    {s : set E} (h : has_fderiv_within_at f f' s x)
    (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) :
    has_fderiv_within_at f₁ f' s x :=
  has_fderiv_at_filter.congr_of_eventually_eq h h₁ hx

theorem has_fderiv_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (h : has_fderiv_at f f' x) (h₁ : filter.eventually_eq (nhds x) f₁ f) : has_fderiv_at f₁ f' x :=
  has_fderiv_at_filter.congr_of_eventually_eq h h₁ (mem_of_nhds h₁)

theorem differentiable_within_at.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {x : E} {s : set E} {t : set E}
    (h : differentiable_within_at 𝕜 f s x) (ht : ∀ (x : E), x ∈ t → f₁ x = f x) (hx : f₁ x = f x)
    (h₁ : t ⊆ s) : differentiable_within_at 𝕜 f₁ t x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.congr_mono (differentiable_within_at.has_fderiv_within_at h) ht hx h₁)

theorem differentiable_within_at.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {x : E} {s : set E} (h : differentiable_within_at 𝕜 f s x)
    (ht : ∀ (x : E), x ∈ s → f₁ x = f x) (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
  differentiable_within_at.congr_mono h ht hx (set.subset.refl s)

theorem differentiable_within_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {x : E} {s : set E}
    (h : differentiable_within_at 𝕜 f s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f)
    (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.congr_of_eventually_eq (differentiable_within_at.has_fderiv_within_at h)
      h₁ hx)

theorem differentiable_on.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {s : set E} {t : set E} (h : differentiable_on 𝕜 f s)
    (h' : ∀ (x : E), x ∈ t → f₁ x = f x) (h₁ : t ⊆ s) : differentiable_on 𝕜 f₁ t :=
  fun (x : E) (hx : x ∈ t) => differentiable_within_at.congr_mono (h x (h₁ hx)) h' (h' x hx) h₁

theorem differentiable_on.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {s : set E} (h : differentiable_on 𝕜 f s)
    (h' : ∀ (x : E), x ∈ s → f₁ x = f x) : differentiable_on 𝕜 f₁ s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.congr (h x hx) h' (h' x hx)

theorem differentiable_on_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {s : set E} (h' : ∀ (x : E), x ∈ s → f₁ x = f x) :
    differentiable_on 𝕜 f₁ s ↔ differentiable_on 𝕜 f s :=
  { mp :=
      fun (h : differentiable_on 𝕜 f₁ s) =>
        differentiable_on.congr h fun (y : E) (hy : y ∈ s) => Eq.symm (h' y hy),
    mpr := fun (h : differentiable_on 𝕜 f s) => differentiable_on.congr h h' }

theorem differentiable_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {x : E} (h : differentiable_at 𝕜 f x)
    (hL : filter.eventually_eq (nhds x) f₁ f) : differentiable_at 𝕜 f₁ x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at_filter.congr_of_eventually_eq (differentiable_at.has_fderiv_at h) hL
      (mem_of_nhds hL))

theorem differentiable_within_at.fderiv_within_congr_mono {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {x : E} {s : set E} {t : set E}
    (h : differentiable_within_at 𝕜 f s x) (hs : ∀ (x : E), x ∈ t → f₁ x = f x) (hx : f₁ x = f x)
    (hxt : unique_diff_within_at 𝕜 t x) (h₁ : t ⊆ s) :
    fderiv_within 𝕜 f₁ t x = fderiv_within 𝕜 f s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.congr_mono (differentiable_within_at.has_fderiv_within_at h) hs hx h₁) hxt

theorem filter.eventually_eq.fderiv_within_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {x : E} {s : set E}
    (hs : unique_diff_within_at 𝕜 s x) (hL : filter.eventually_eq (nhds_within x s) f₁ f)
    (hx : f₁ x = f x) : fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
  sorry

theorem fderiv_within_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {x : E} {s : set E} (hs : unique_diff_within_at 𝕜 s x)
    (hL : ∀ (y : E), y ∈ s → f₁ y = f y) (hx : f₁ x = f x) :
    fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
  filter.eventually_eq.fderiv_within_eq hs (filter.mem_sets_of_superset self_mem_nhds_within hL) hx

theorem filter.eventually_eq.fderiv_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f₁ : E → F} {x : E} (hL : filter.eventually_eq (nhds x) f₁ f) :
    fderiv 𝕜 f₁ x = fderiv 𝕜 f x :=
  sorry

/-! ### Derivative of the identity -/

theorem has_strict_fderiv_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] (x : E) :
    has_strict_fderiv_at id (continuous_linear_map.id 𝕜 E) x :=
  sorry

theorem has_fderiv_at_filter_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] (x : E) (L : filter E) :
    has_fderiv_at_filter id (continuous_linear_map.id 𝕜 E) x L :=
  sorry

theorem has_fderiv_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] (x : E) (s : set E) :
    has_fderiv_within_at id (continuous_linear_map.id 𝕜 E) s x :=
  has_fderiv_at_filter_id x (nhds_within x s)

theorem has_fderiv_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] (x : E) : has_fderiv_at id (continuous_linear_map.id 𝕜 E) x :=
  has_fderiv_at_filter_id x (nhds x)

@[simp] theorem differentiable_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} : differentiable_at 𝕜 id x :=
  has_fderiv_at.differentiable_at (has_fderiv_at_id x)

@[simp] theorem differentiable_at_id' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} : differentiable_at 𝕜 (fun (x : E) => x) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at_id x)

theorem differentiable_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} : differentiable_within_at 𝕜 id s x :=
  differentiable_at.differentiable_within_at differentiable_at_id

@[simp] theorem differentiable_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] : differentiable 𝕜 id :=
  fun (x : E) => differentiable_at_id

@[simp] theorem differentiable_id' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] : differentiable 𝕜 fun (x : E) => x :=
  fun (x : E) => differentiable_at_id

theorem differentiable_on_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {s : set E} : differentiable_on 𝕜 id s :=
  differentiable.differentiable_on differentiable_id

theorem fderiv_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {x : E} : fderiv 𝕜 id x = continuous_linear_map.id 𝕜 E :=
  has_fderiv_at.fderiv (has_fderiv_at_id x)

@[simp] theorem fderiv_id' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} :
    fderiv 𝕜 (fun (x : E) => x) x = continuous_linear_map.id 𝕜 E :=
  fderiv_id

theorem fderiv_within_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 id s x = continuous_linear_map.id 𝕜 E :=
  sorry

theorem fderiv_within_id' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (fun (x : E) => x) s x = continuous_linear_map.id 𝕜 E :=
  fderiv_within_id hxs

/-! ### derivative of a constant function -/

theorem has_strict_fderiv_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (c : F)
    (x : E) : has_strict_fderiv_at (fun (_x : E) => c) 0 x :=
  sorry

theorem has_fderiv_at_filter_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (c : F)
    (x : E) (L : filter E) : has_fderiv_at_filter (fun (x : E) => c) 0 x L :=
  sorry

theorem has_fderiv_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (c : F)
    (x : E) (s : set E) : has_fderiv_within_at (fun (x : E) => c) 0 s x :=
  has_fderiv_at_filter_const c x (nhds_within x s)

theorem has_fderiv_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (c : F)
    (x : E) : has_fderiv_at (fun (x : E) => c) 0 x :=
  has_fderiv_at_filter_const c x (nhds x)

@[simp] theorem differentiable_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    (c : F) : differentiable_at 𝕜 (fun (x : E) => c) x :=
  Exists.intro 0 (has_fderiv_at_const c x)

theorem differentiable_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} (c : F) : differentiable_within_at 𝕜 (fun (x : E) => c) s x :=
  differentiable_at.differentiable_within_at (differentiable_at_const c)

theorem fderiv_const_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    (c : F) : fderiv 𝕜 (fun (y : E) => c) x = 0 :=
  has_fderiv_at.fderiv (has_fderiv_at_const c x)

@[simp] theorem fderiv_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (c : F) :
    (fderiv 𝕜 fun (y : E) => c) = 0 :=
  sorry

theorem fderiv_within_const_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} (c : F) (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (fun (y : E) => c) s x = 0 :=
  sorry

@[simp] theorem differentiable_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (c : F) :
    differentiable 𝕜 fun (x : E) => c :=
  fun (x : E) => differentiable_at_const c

theorem differentiable_on_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {s : set E} (c : F) : differentiable_on 𝕜 (fun (x : E) => c) s :=
  differentiable.differentiable_on (differentiable_const c)

/-!
### Continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `continuous_linear_map`, and denoted `E →L[𝕜] F`), and the unbundled version (with a
predicate `is_bounded_linear_map`). We give statements for both versions. -/

protected theorem continuous_linear_map.has_strict_fderiv_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} :
    has_strict_fderiv_at (⇑e) e x :=
  sorry

protected theorem continuous_linear_map.has_fderiv_at_filter {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} {L : filter E} :
    has_fderiv_at_filter (⇑e) e x L :=
  sorry

protected theorem continuous_linear_map.has_fderiv_within_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} {s : set E} :
    has_fderiv_within_at (⇑e) e s x :=
  continuous_linear_map.has_fderiv_at_filter e

protected theorem continuous_linear_map.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} : has_fderiv_at (⇑e) e x :=
  continuous_linear_map.has_fderiv_at_filter e

@[simp] protected theorem continuous_linear_map.differentiable_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} :
    differentiable_at 𝕜 (⇑e) x :=
  has_fderiv_at.differentiable_at (continuous_linear_map.has_fderiv_at e)

protected theorem continuous_linear_map.differentiable_within_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} {s : set E} :
    differentiable_within_at 𝕜 (⇑e) s x :=
  differentiable_at.differentiable_within_at (continuous_linear_map.differentiable_at e)

@[simp] protected theorem continuous_linear_map.fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} : fderiv 𝕜 (⇑e) x = e :=
  has_fderiv_at.fderiv (continuous_linear_map.has_fderiv_at e)

protected theorem continuous_linear_map.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {x : E} {s : set E}
    (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 (⇑e) s x = e :=
  sorry

@[simp] protected theorem continuous_linear_map.differentiable {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) : differentiable 𝕜 ⇑e :=
  fun (x : E) => continuous_linear_map.differentiable_at e

protected theorem continuous_linear_map.differentiable_on {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] (e : continuous_linear_map 𝕜 E F) {s : set E} :
    differentiable_on 𝕜 (⇑e) s :=
  differentiable.differentiable_on (continuous_linear_map.differentiable e)

theorem is_bounded_linear_map.has_fderiv_at_filter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {L : filter E} (h : is_bounded_linear_map 𝕜 f) :
    has_fderiv_at_filter f (is_bounded_linear_map.to_continuous_linear_map h) x L :=
  continuous_linear_map.has_fderiv_at_filter (is_bounded_linear_map.to_continuous_linear_map h)

theorem is_bounded_linear_map.has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : is_bounded_linear_map 𝕜 f) :
    has_fderiv_within_at f (is_bounded_linear_map.to_continuous_linear_map h) s x :=
  is_bounded_linear_map.has_fderiv_at_filter h

theorem is_bounded_linear_map.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (h : is_bounded_linear_map 𝕜 f) :
    has_fderiv_at f (is_bounded_linear_map.to_continuous_linear_map h) x :=
  is_bounded_linear_map.has_fderiv_at_filter h

theorem is_bounded_linear_map.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (h : is_bounded_linear_map 𝕜 f) :
    differentiable_at 𝕜 f x :=
  has_fderiv_at.differentiable_at (is_bounded_linear_map.has_fderiv_at h)

theorem is_bounded_linear_map.differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : is_bounded_linear_map 𝕜 f) :
    differentiable_within_at 𝕜 f s x :=
  differentiable_at.differentiable_within_at (is_bounded_linear_map.differentiable_at h)

theorem is_bounded_linear_map.fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : is_bounded_linear_map 𝕜 f) :
    fderiv 𝕜 f x = is_bounded_linear_map.to_continuous_linear_map h :=
  has_fderiv_at.fderiv (is_bounded_linear_map.has_fderiv_at h)

theorem is_bounded_linear_map.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : is_bounded_linear_map 𝕜 f)
    (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 f s x = is_bounded_linear_map.to_continuous_linear_map h :=
  sorry

theorem is_bounded_linear_map.differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} (h : is_bounded_linear_map 𝕜 f) : differentiable 𝕜 f :=
  fun (x : E) => is_bounded_linear_map.differentiable_at h

theorem is_bounded_linear_map.differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} (h : is_bounded_linear_map 𝕜 f) :
    differentiable_on 𝕜 f s :=
  differentiable.differentiable_on (is_bounded_linear_map.differentiable h)

theorem has_fpower_series_at.has_strict_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {p : formal_multilinear_series 𝕜 E F}
    (h : has_fpower_series_at f p x) :
    has_strict_fderiv_at f (coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p 1)) x :=
  sorry

theorem has_fpower_series_at.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {p : formal_multilinear_series 𝕜 E F}
    (h : has_fpower_series_at f p x) :
    has_fderiv_at f (coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p 1)) x :=
  has_strict_fderiv_at.has_fderiv_at (has_fpower_series_at.has_strict_fderiv_at h)

theorem has_fpower_series_at.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {p : formal_multilinear_series 𝕜 E F}
    (h : has_fpower_series_at f p x) : differentiable_at 𝕜 f x :=
  has_fderiv_at.differentiable_at (has_fpower_series_at.has_fderiv_at h)

theorem analytic_at.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} : analytic_at 𝕜 f x → differentiable_at 𝕜 f x :=
  sorry

theorem analytic_at.differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : analytic_at 𝕜 f x) :
    differentiable_within_at 𝕜 f s x :=
  differentiable_at.differentiable_within_at (analytic_at.differentiable_at h)

theorem has_fpower_series_at.fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {p : formal_multilinear_series 𝕜 E F} (h : has_fpower_series_at f p x) :
    fderiv 𝕜 f x = coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p 1) :=
  has_fderiv_at.fderiv (has_fpower_series_at.has_fderiv_at h)

theorem has_fpower_series_on_ball.differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {p : formal_multilinear_series 𝕜 E F} {r : ennreal}
    [complete_space F] (h : has_fpower_series_on_ball f p x r) :
    differentiable_on 𝕜 f (emetric.ball x r) :=
  fun (y : E) (hy : y ∈ emetric.ball x r) =>
    analytic_at.differentiable_within_at (has_fpower_series_on_ball.analytic_at_of_mem h hy)

/-!
### Derivative of the composition of two functions

For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/

theorem has_fderiv_at_filter.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} (x : E) {L : filter E} {g : F → G}
    {g' : continuous_linear_map 𝕜 F G} (hg : has_fderiv_at_filter g g' (f x) (filter.map f L))
    (hf : has_fderiv_at_filter f f' x L) :
    has_fderiv_at_filter (g ∘ f) (continuous_linear_map.comp g' f') x L :=
  sorry

/- A readable version of the previous theorem,
   a general form of the chain rule. -/

theorem has_fderiv_within_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} (x : E) {s : set E} {g : F → G}
    {g' : continuous_linear_map 𝕜 F G} {t : set F} (hg : has_fderiv_within_at g g' t (f x))
    (hf : has_fderiv_within_at f f' s x) (hst : s ⊆ f ⁻¹' t) :
    has_fderiv_within_at (g ∘ f) (continuous_linear_map.comp g' f') s x :=
  sorry

/-- The chain rule. -/
theorem has_fderiv_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} (x : E) {g : F → G} {g' : continuous_linear_map 𝕜 F G}
    (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_at f f' x) :
    has_fderiv_at (g ∘ f) (continuous_linear_map.comp g' f') x :=
  has_fderiv_at_filter.comp x (has_fderiv_at_filter.mono hg (has_fderiv_at.continuous_at hf)) hf

theorem has_fderiv_at.comp_has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} (x : E) {s : set E} {g : F → G}
    {g' : continuous_linear_map 𝕜 F G} (hg : has_fderiv_at g g' (f x))
    (hf : has_fderiv_within_at f f' s x) :
    has_fderiv_within_at (g ∘ f) (continuous_linear_map.comp g' f') s x :=
  has_fderiv_within_at.comp x
    (eq.mp
      (Eq._oldrec (Eq.refl (has_fderiv_at g g' (f x)))
        (Eq.symm (propext has_fderiv_within_at_univ)))
      hg)
    hf set.subset_preimage_univ

theorem differentiable_within_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E) {s : set E} {g : F → G}
    {t : set F} (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
    (h : s ⊆ f ⁻¹' t) : differentiable_within_at 𝕜 (g ∘ f) s x :=
  sorry

theorem differentiable_within_at.comp' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E) {s : set E} {g : F → G}
    {t : set F} (hg : differentiable_within_at 𝕜 g t (f x))
    (hf : differentiable_within_at 𝕜 f s x) : differentiable_within_at 𝕜 (g ∘ f) (s ∩ f ⁻¹' t) x :=
  differentiable_within_at.comp x hg
    (differentiable_within_at.mono hf (set.inter_subset_left s (f ⁻¹' t)))
    (set.inter_subset_right s (f ⁻¹' t))

theorem differentiable_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E) {g : F → G}
    (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
    differentiable_at 𝕜 (g ∘ f) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.comp x (differentiable_at.has_fderiv_at hg) (differentiable_at.has_fderiv_at hf))

theorem differentiable_at.comp_differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E)
    {s : set E} {g : F → G} (hg : differentiable_at 𝕜 g (f x))
    (hf : differentiable_within_at 𝕜 f s x) : differentiable_within_at 𝕜 (g ∘ f) s x :=
  sorry

theorem fderiv_within.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E) {s : set E} {g : F → G}
    {t : set F} (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
    (h : set.maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (g ∘ f) s x =
        continuous_linear_map.comp (fderiv_within 𝕜 g t (f x)) (fderiv_within 𝕜 f s x) :=
  sorry

theorem fderiv.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E) {g : F → G}
    (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
    fderiv 𝕜 (g ∘ f) x = continuous_linear_map.comp (fderiv 𝕜 g (f x)) (fderiv 𝕜 f x) :=
  has_fderiv_at.fderiv
    (has_fderiv_at.comp x (differentiable_at.has_fderiv_at hg) (differentiable_at.has_fderiv_at hf))

theorem fderiv.comp_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} (x : E) {s : set E} {g : F → G}
    (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_within_at 𝕜 f s x)
    (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (g ∘ f) s x =
        continuous_linear_map.comp (fderiv 𝕜 g (f x)) (fderiv_within 𝕜 f s x) :=
  sorry

theorem differentiable_on.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} {s : set E} {g : F → G}
    {t : set F} (hg : differentiable_on 𝕜 g t) (hf : differentiable_on 𝕜 f s) (st : s ⊆ f ⁻¹' t) :
    differentiable_on 𝕜 (g ∘ f) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.comp x (hg (f x) (st hx)) (hf x hx) st

theorem differentiable.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} {g : F → G}
    (hg : differentiable 𝕜 g) (hf : differentiable 𝕜 f) : differentiable 𝕜 (g ∘ f) :=
  fun (x : E) => differentiable_at.comp x (hg (f x)) (hf x)

theorem differentiable.comp_differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} {s : set E}
    {g : F → G} (hg : differentiable 𝕜 g) (hf : differentiable_on 𝕜 f s) :
    differentiable_on 𝕜 (g ∘ f) s :=
  sorry

/-- The chain rule for derivatives in the sense of strict differentiability. -/
protected theorem has_strict_fderiv_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F}
    {f' : continuous_linear_map 𝕜 E F} (x : E) {g : F → G} {g' : continuous_linear_map 𝕜 F G}
    (hg : has_strict_fderiv_at g g' (f x)) (hf : has_strict_fderiv_at f f' x) :
    has_strict_fderiv_at (fun (x : E) => g (f x)) (continuous_linear_map.comp g' f') x :=
  sorry

protected theorem differentiable.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {f : E → E} (hf : differentiable 𝕜 f) (n : ℕ) :
    differentiable 𝕜 (nat.iterate f n) :=
  nat.rec_on n differentiable_id
    fun (n : ℕ) (ihn : differentiable 𝕜 (nat.iterate f n)) => differentiable.comp ihn hf

protected theorem differentiable_on.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {f : E → E}
    (hf : differentiable_on 𝕜 f s) (hs : set.maps_to f s s) (n : ℕ) :
    differentiable_on 𝕜 (nat.iterate f n) s :=
  nat.rec_on n differentiable_on_id
    fun (n : ℕ) (ihn : differentiable_on 𝕜 (nat.iterate f n) s) => differentiable_on.comp ihn hf hs

protected theorem has_fderiv_at_filter.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {L : filter E} {f : E → E}
    {f' : continuous_linear_map 𝕜 E E} (hf : has_fderiv_at_filter f f' x L)
    (hL : filter.tendsto f L L) (hx : f x = x) (n : ℕ) :
    has_fderiv_at_filter (nat.iterate f n) (f' ^ n) x L :=
  sorry

protected theorem has_fderiv_at.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {f : E → E} {f' : continuous_linear_map 𝕜 E E}
    (hf : has_fderiv_at f f' x) (hx : f x = x) (n : ℕ) :
    has_fderiv_at (nat.iterate f n) (f' ^ n) x :=
  sorry

protected theorem has_fderiv_within_at.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {f : E → E}
    {f' : continuous_linear_map 𝕜 E E} (hf : has_fderiv_within_at f f' s x) (hx : f x = x)
    (hs : set.maps_to f s s) (n : ℕ) : has_fderiv_within_at (nat.iterate f n) (f' ^ n) s x :=
  sorry

protected theorem has_strict_fderiv_at.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {f : E → E}
    {f' : continuous_linear_map 𝕜 E E} (hf : has_strict_fderiv_at f f' x) (hx : f x = x) (n : ℕ) :
    has_strict_fderiv_at (nat.iterate f n) (f' ^ n) x :=
  sorry

protected theorem differentiable_at.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {f : E → E}
    (hf : differentiable_at 𝕜 f x) (hx : f x = x) (n : ℕ) :
    differentiable_at 𝕜 (nat.iterate f n) x :=
  exists.elim hf
    fun (f' : continuous_linear_map 𝕜 E E) (hf : has_fderiv_at f f' x) =>
      has_fderiv_at.differentiable_at (has_fderiv_at.iterate hf hx n)

protected theorem differentiable_within_at.iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {f : E → E}
    (hf : differentiable_within_at 𝕜 f s x) (hx : f x = x) (hs : set.maps_to f s s) (n : ℕ) :
    differentiable_within_at 𝕜 (nat.iterate f n) s x :=
  exists.elim hf
    fun (f' : continuous_linear_map 𝕜 E E) (hf : has_fderiv_within_at f f' s x) =>
      has_fderiv_within_at.differentiable_within_at (has_fderiv_within_at.iterate hf hx hs n)

/-! ### Derivative of the cartesian product of two functions -/

protected theorem has_strict_fderiv_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F}
    {f₁' : continuous_linear_map 𝕜 E F} {x : E} {f₂ : E → G} {f₂' : continuous_linear_map 𝕜 E G}
    (hf₁ : has_strict_fderiv_at f₁ f₁' x) (hf₂ : has_strict_fderiv_at f₂ f₂' x) :
    has_strict_fderiv_at (fun (x : E) => (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') x :=
  asymptotics.is_o.prod_left hf₁ hf₂

theorem has_fderiv_at_filter.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F}
    {f₁' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E} {f₂ : E → G}
    {f₂' : continuous_linear_map 𝕜 E G} (hf₁ : has_fderiv_at_filter f₁ f₁' x L)
    (hf₂ : has_fderiv_at_filter f₂ f₂' x L) :
    has_fderiv_at_filter (fun (x : E) => (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') x L :=
  asymptotics.is_o.prod_left hf₁ hf₂

theorem has_fderiv_within_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F}
    {f₁' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {f₂ : E → G}
    {f₂' : continuous_linear_map 𝕜 E G} (hf₁ : has_fderiv_within_at f₁ f₁' s x)
    (hf₂ : has_fderiv_within_at f₂ f₂' s x) :
    has_fderiv_within_at (fun (x : E) => (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') s x :=
  has_fderiv_at_filter.prod hf₁ hf₂

theorem has_fderiv_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F}
    {f₁' : continuous_linear_map 𝕜 E F} {x : E} {f₂ : E → G} {f₂' : continuous_linear_map 𝕜 E G}
    (hf₁ : has_fderiv_at f₁ f₁' x) (hf₂ : has_fderiv_at f₂ f₂' x) :
    has_fderiv_at (fun (x : E) => (f₁ x, f₂ x)) (continuous_linear_map.prod f₁' f₂') x :=
  has_fderiv_at_filter.prod hf₁ hf₂

theorem differentiable_within_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F} {x : E} {s : set E} {f₂ : E → G}
    (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x) :
    differentiable_within_at 𝕜 (fun (x : E) => (f₁ x, f₂ x)) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.prod (differentiable_within_at.has_fderiv_within_at hf₁)
      (differentiable_within_at.has_fderiv_within_at hf₂))

@[simp] theorem differentiable_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F} {x : E} {f₂ : E → G}
    (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
    differentiable_at 𝕜 (fun (x : E) => (f₁ x, f₂ x)) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.prod (differentiable_at.has_fderiv_at hf₁) (differentiable_at.has_fderiv_at hf₂))

theorem differentiable_on.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F} {s : set E} {f₂ : E → G}
    (hf₁ : differentiable_on 𝕜 f₁ s) (hf₂ : differentiable_on 𝕜 f₂ s) :
    differentiable_on 𝕜 (fun (x : E) => (f₁ x, f₂ x)) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.prod (hf₁ x hx) (hf₂ x hx)

@[simp] theorem differentiable.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F} {f₂ : E → G}
    (hf₁ : differentiable 𝕜 f₁) (hf₂ : differentiable 𝕜 f₂) :
    differentiable 𝕜 fun (x : E) => (f₁ x, f₂ x) :=
  fun (x : E) => differentiable_at.prod (hf₁ x) (hf₂ x)

theorem differentiable_at.fderiv_prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F} {x : E} {f₂ : E → G}
    (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
    fderiv 𝕜 (fun (x : E) => (f₁ x, f₂ x)) x =
        continuous_linear_map.prod (fderiv 𝕜 f₁ x) (fderiv 𝕜 f₂ x) :=
  has_fderiv_at.fderiv
    (has_fderiv_at.prod (differentiable_at.has_fderiv_at hf₁) (differentiable_at.has_fderiv_at hf₂))

theorem differentiable_at.fderiv_within_prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₁ : E → F} {x : E}
    {s : set E} {f₂ : E → G} (hf₁ : differentiable_within_at 𝕜 f₁ s x)
    (hf₂ : differentiable_within_at 𝕜 f₂ s x) (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (fun (x : E) => (f₁ x, f₂ x)) s x =
        continuous_linear_map.prod (fderiv_within 𝕜 f₁ s x) (fderiv_within 𝕜 f₂ s x) :=
  sorry

theorem has_strict_fderiv_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} : has_strict_fderiv_at prod.fst (continuous_linear_map.fst 𝕜 E F) p :=
  continuous_linear_map.has_strict_fderiv_at (continuous_linear_map.fst 𝕜 E F)

protected theorem has_strict_fderiv_at.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G}
    {f₂' : continuous_linear_map 𝕜 E (F × G)} (h : has_strict_fderiv_at f₂ f₂' x) :
    has_strict_fderiv_at (fun (x : E) => prod.fst (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.fst 𝕜 F G) f₂') x :=
  has_strict_fderiv_at.comp x has_strict_fderiv_at_fst h

theorem has_fderiv_at_filter_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {L : filter (E × F)} :
    has_fderiv_at_filter prod.fst (continuous_linear_map.fst 𝕜 E F) p L :=
  continuous_linear_map.has_fderiv_at_filter (continuous_linear_map.fst 𝕜 E F)

protected theorem has_fderiv_at_filter.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {L : filter E}
    {f₂ : E → F × G} {f₂' : continuous_linear_map 𝕜 E (F × G)}
    (h : has_fderiv_at_filter f₂ f₂' x L) :
    has_fderiv_at_filter (fun (x : E) => prod.fst (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.fst 𝕜 F G) f₂') x L :=
  has_fderiv_at_filter.comp x has_fderiv_at_filter_fst h

theorem has_fderiv_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} : has_fderiv_at prod.fst (continuous_linear_map.fst 𝕜 E F) p :=
  has_fderiv_at_filter_fst

protected theorem has_fderiv_at.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G}
    {f₂' : continuous_linear_map 𝕜 E (F × G)} (h : has_fderiv_at f₂ f₂' x) :
    has_fderiv_at (fun (x : E) => prod.fst (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.fst 𝕜 F G) f₂') x :=
  has_fderiv_at_filter.fst h

theorem has_fderiv_within_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {s : set (E × F)} :
    has_fderiv_within_at prod.fst (continuous_linear_map.fst 𝕜 E F) s p :=
  has_fderiv_at_filter_fst

protected theorem has_fderiv_within_at.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {s : set E}
    {f₂ : E → F × G} {f₂' : continuous_linear_map 𝕜 E (F × G)}
    (h : has_fderiv_within_at f₂ f₂' s x) :
    has_fderiv_within_at (fun (x : E) => prod.fst (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.fst 𝕜 F G) f₂') s x :=
  has_fderiv_at_filter.fst h

theorem differentiable_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} : differentiable_at 𝕜 prod.fst p :=
  has_fderiv_at.differentiable_at has_fderiv_at_fst

@[simp] protected theorem differentiable_at.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G}
    (h : differentiable_at 𝕜 f₂ x) : differentiable_at 𝕜 (fun (x : E) => prod.fst (f₂ x)) x :=
  differentiable_at.comp x differentiable_at_fst h

theorem differentiable_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] :
    differentiable 𝕜 prod.fst :=
  fun (x : E × F) => differentiable_at_fst

@[simp] protected theorem differentiable.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₂ : E → F × G}
    (h : differentiable 𝕜 f₂) : differentiable 𝕜 fun (x : E) => prod.fst (f₂ x) :=
  differentiable.comp differentiable_fst h

theorem differentiable_within_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {s : set (E × F)} : differentiable_within_at 𝕜 prod.fst s p :=
  differentiable_at.differentiable_within_at differentiable_at_fst

protected theorem differentiable_within_at.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {s : set E}
    {f₂ : E → F × G} (h : differentiable_within_at 𝕜 f₂ s x) :
    differentiable_within_at 𝕜 (fun (x : E) => prod.fst (f₂ x)) s x :=
  differentiable_at.comp_differentiable_within_at x differentiable_at_fst h

theorem differentiable_on_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {s : set (E × F)} : differentiable_on 𝕜 prod.fst s :=
  differentiable.differentiable_on differentiable_fst

protected theorem differentiable_on.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f₂ : E → F × G}
    (h : differentiable_on 𝕜 f₂ s) : differentiable_on 𝕜 (fun (x : E) => prod.fst (f₂ x)) s :=
  differentiable.comp_differentiable_on differentiable_fst h

theorem fderiv_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {p : E × F} :
    fderiv 𝕜 prod.fst p = continuous_linear_map.fst 𝕜 E F :=
  has_fderiv_at.fderiv has_fderiv_at_fst

theorem fderiv.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G} (h : differentiable_at 𝕜 f₂ x) :
    fderiv 𝕜 (fun (x : E) => prod.fst (f₂ x)) x =
        continuous_linear_map.comp (continuous_linear_map.fst 𝕜 F G) (fderiv 𝕜 f₂ x) :=
  has_fderiv_at.fderiv (has_fderiv_at.fst (differentiable_at.has_fderiv_at h))

theorem fderiv_within_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {s : set (E × F)} (hs : unique_diff_within_at 𝕜 s p) :
    fderiv_within 𝕜 prod.fst s p = continuous_linear_map.fst 𝕜 E F :=
  has_fderiv_within_at.fderiv_within has_fderiv_within_at_fst hs

theorem fderiv_within.fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {s : set E} {f₂ : E → F × G}
    (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f₂ s x) :
    fderiv_within 𝕜 (fun (x : E) => prod.fst (f₂ x)) s x =
        continuous_linear_map.comp (continuous_linear_map.fst 𝕜 F G) (fderiv_within 𝕜 f₂ s x) :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.fst (differentiable_within_at.has_fderiv_within_at h)) hs

theorem has_strict_fderiv_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} : has_strict_fderiv_at prod.snd (continuous_linear_map.snd 𝕜 E F) p :=
  continuous_linear_map.has_strict_fderiv_at (continuous_linear_map.snd 𝕜 E F)

protected theorem has_strict_fderiv_at.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G}
    {f₂' : continuous_linear_map 𝕜 E (F × G)} (h : has_strict_fderiv_at f₂ f₂' x) :
    has_strict_fderiv_at (fun (x : E) => prod.snd (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.snd 𝕜 F G) f₂') x :=
  has_strict_fderiv_at.comp x has_strict_fderiv_at_snd h

theorem has_fderiv_at_filter_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {L : filter (E × F)} :
    has_fderiv_at_filter prod.snd (continuous_linear_map.snd 𝕜 E F) p L :=
  continuous_linear_map.has_fderiv_at_filter (continuous_linear_map.snd 𝕜 E F)

protected theorem has_fderiv_at_filter.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {L : filter E}
    {f₂ : E → F × G} {f₂' : continuous_linear_map 𝕜 E (F × G)}
    (h : has_fderiv_at_filter f₂ f₂' x L) :
    has_fderiv_at_filter (fun (x : E) => prod.snd (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.snd 𝕜 F G) f₂') x L :=
  has_fderiv_at_filter.comp x has_fderiv_at_filter_snd h

theorem has_fderiv_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} : has_fderiv_at prod.snd (continuous_linear_map.snd 𝕜 E F) p :=
  has_fderiv_at_filter_snd

protected theorem has_fderiv_at.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G}
    {f₂' : continuous_linear_map 𝕜 E (F × G)} (h : has_fderiv_at f₂ f₂' x) :
    has_fderiv_at (fun (x : E) => prod.snd (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.snd 𝕜 F G) f₂') x :=
  has_fderiv_at_filter.snd h

theorem has_fderiv_within_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {s : set (E × F)} :
    has_fderiv_within_at prod.snd (continuous_linear_map.snd 𝕜 E F) s p :=
  has_fderiv_at_filter_snd

protected theorem has_fderiv_within_at.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {s : set E}
    {f₂ : E → F × G} {f₂' : continuous_linear_map 𝕜 E (F × G)}
    (h : has_fderiv_within_at f₂ f₂' s x) :
    has_fderiv_within_at (fun (x : E) => prod.snd (f₂ x))
        (continuous_linear_map.comp (continuous_linear_map.snd 𝕜 F G) f₂') s x :=
  has_fderiv_at_filter.snd h

theorem differentiable_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} : differentiable_at 𝕜 prod.snd p :=
  has_fderiv_at.differentiable_at has_fderiv_at_snd

@[simp] protected theorem differentiable_at.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G}
    (h : differentiable_at 𝕜 f₂ x) : differentiable_at 𝕜 (fun (x : E) => prod.snd (f₂ x)) x :=
  differentiable_at.comp x differentiable_at_snd h

theorem differentiable_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] :
    differentiable 𝕜 prod.snd :=
  fun (x : E × F) => differentiable_at_snd

@[simp] protected theorem differentiable.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f₂ : E → F × G}
    (h : differentiable 𝕜 f₂) : differentiable 𝕜 fun (x : E) => prod.snd (f₂ x) :=
  differentiable.comp differentiable_snd h

theorem differentiable_within_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {s : set (E × F)} : differentiable_within_at 𝕜 prod.snd s p :=
  differentiable_at.differentiable_within_at differentiable_at_snd

protected theorem differentiable_within_at.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {s : set E}
    {f₂ : E → F × G} (h : differentiable_within_at 𝕜 f₂ s x) :
    differentiable_within_at 𝕜 (fun (x : E) => prod.snd (f₂ x)) s x :=
  differentiable_at.comp_differentiable_within_at x differentiable_at_snd h

theorem differentiable_on_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {s : set (E × F)} : differentiable_on 𝕜 prod.snd s :=
  differentiable.differentiable_on differentiable_snd

protected theorem differentiable_on.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f₂ : E → F × G}
    (h : differentiable_on 𝕜 f₂ s) : differentiable_on 𝕜 (fun (x : E) => prod.snd (f₂ x)) s :=
  differentiable.comp_differentiable_on differentiable_snd h

theorem fderiv_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {p : E × F} :
    fderiv 𝕜 prod.snd p = continuous_linear_map.snd 𝕜 E F :=
  has_fderiv_at.fderiv has_fderiv_at_snd

theorem fderiv.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4}
    [normed_group G] [normed_space 𝕜 G] {x : E} {f₂ : E → F × G} (h : differentiable_at 𝕜 f₂ x) :
    fderiv 𝕜 (fun (x : E) => prod.snd (f₂ x)) x =
        continuous_linear_map.comp (continuous_linear_map.snd 𝕜 F G) (fderiv 𝕜 f₂ x) :=
  has_fderiv_at.fderiv (has_fderiv_at.snd (differentiable_at.has_fderiv_at h))

theorem fderiv_within_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {p : E × F} {s : set (E × F)} (hs : unique_diff_within_at 𝕜 s p) :
    fderiv_within 𝕜 prod.snd s p = continuous_linear_map.snd 𝕜 E F :=
  has_fderiv_within_at.fderiv_within has_fderiv_within_at_snd hs

theorem fderiv_within.snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {s : set E} {f₂ : E → F × G}
    (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f₂ s x) :
    fderiv_within 𝕜 (fun (x : E) => prod.snd (f₂ x)) s x =
        continuous_linear_map.comp (continuous_linear_map.snd 𝕜 F G) (fderiv_within 𝕜 f₂ s x) :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.snd (differentiable_within_at.has_fderiv_within_at h)) hs

-- TODO (Lean 3.8): use `prod.map f f₂``

protected theorem has_strict_fderiv_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {G' : Type u_5}
    [normed_group G'] [normed_space 𝕜 G'] {f : E → F} {f' : continuous_linear_map 𝕜 E F}
    {f₂ : G → G'} {f₂' : continuous_linear_map 𝕜 G G'} (p : E × G)
    (hf : has_strict_fderiv_at f f' (prod.fst p)) (hf₂ : has_strict_fderiv_at f₂ f₂' (prod.snd p)) :
    has_strict_fderiv_at (fun (p : E × G) => (f (prod.fst p), f₂ (prod.snd p)))
        (continuous_linear_map.prod_map f' f₂') p :=
  has_strict_fderiv_at.prod (has_strict_fderiv_at.comp p hf has_strict_fderiv_at_fst)
    (has_strict_fderiv_at.comp p hf₂ has_strict_fderiv_at_snd)

protected theorem has_fderiv_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {G' : Type u_5} [normed_group G']
    [normed_space 𝕜 G'] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {f₂ : G → G'}
    {f₂' : continuous_linear_map 𝕜 G G'} (p : E × G) (hf : has_fderiv_at f f' (prod.fst p))
    (hf₂ : has_fderiv_at f₂ f₂' (prod.snd p)) :
    has_fderiv_at (fun (p : E × G) => (f (prod.fst p), f₂ (prod.snd p)))
        (continuous_linear_map.prod_map f' f₂') p :=
  has_fderiv_at.prod (has_fderiv_at.comp p hf has_fderiv_at_fst)
    (has_fderiv_at.comp p hf₂ has_fderiv_at_snd)

@[simp] protected theorem differentiable_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {G' : Type u_5}
    [normed_group G'] [normed_space 𝕜 G'] {f : E → F} {f₂ : G → G'} (p : E × G)
    (hf : differentiable_at 𝕜 f (prod.fst p)) (hf₂ : differentiable_at 𝕜 f₂ (prod.snd p)) :
    differentiable_at 𝕜 (fun (p : E × G) => (f (prod.fst p), f₂ (prod.snd p))) p :=
  differentiable_at.prod (differentiable_at.comp p hf differentiable_at_fst)
    (differentiable_at.comp p hf₂ differentiable_at_snd)

/-! ### Derivative of a function multiplied by a constant -/

theorem has_strict_fderiv_at.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_strict_fderiv_at f f' x)
    (c : 𝕜) : has_strict_fderiv_at (fun (x : E) => c • f x) (c • f') x :=
  has_strict_fderiv_at.comp x (continuous_linear_map.has_strict_fderiv_at (c • 1)) h

theorem has_fderiv_at_filter.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (h : has_fderiv_at_filter f f' x L) (c : 𝕜) :
    has_fderiv_at_filter (fun (x : E) => c • f x) (c • f') x L :=
  has_fderiv_at_filter.comp x (continuous_linear_map.has_fderiv_at_filter (c • 1)) h

theorem has_fderiv_within_at.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) (c : 𝕜) :
    has_fderiv_within_at (fun (x : E) => c • f x) (c • f') s x :=
  has_fderiv_at_filter.const_smul h c

theorem has_fderiv_at.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_fderiv_at f f' x) (c : 𝕜) :
    has_fderiv_at (fun (x : E) => c • f x) (c • f') x :=
  has_fderiv_at_filter.const_smul h c

theorem differentiable_within_at.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (h : differentiable_within_at 𝕜 f s x)
    (c : 𝕜) : differentiable_within_at 𝕜 (fun (y : E) => c • f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.const_smul (differentiable_within_at.has_fderiv_within_at h) c)

theorem differentiable_at.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : differentiable_at 𝕜 f x) (c : 𝕜) :
    differentiable_at 𝕜 (fun (y : E) => c • f y) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.const_smul (differentiable_at.has_fderiv_at h) c)

theorem differentiable_on.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (h : differentiable_on 𝕜 f s) (c : 𝕜) :
    differentiable_on 𝕜 (fun (y : E) => c • f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.const_smul (h x hx) c

theorem differentiable.const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (h : differentiable 𝕜 f) (c : 𝕜) : differentiable 𝕜 fun (y : E) => c • f y :=
  fun (x : E) => differentiable_at.const_smul (h x) c

theorem fderiv_within_const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x)
    (h : differentiable_within_at 𝕜 f s x) (c : 𝕜) :
    fderiv_within 𝕜 (fun (y : E) => c • f y) s x = c • fderiv_within 𝕜 f s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.const_smul (differentiable_within_at.has_fderiv_within_at h) c) hxs

theorem fderiv_const_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : differentiable_at 𝕜 f x) (c : 𝕜) :
    fderiv 𝕜 (fun (y : E) => c • f y) x = c • fderiv 𝕜 f x :=
  has_fderiv_at.fderiv (has_fderiv_at.const_smul (differentiable_at.has_fderiv_at h) c)

/-! ### Derivative of the sum of two functions -/

theorem has_strict_fderiv_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} (hf : has_strict_fderiv_at f f' x) (hg : has_strict_fderiv_at g g' x) :
    has_strict_fderiv_at (fun (y : E) => f y + g y) (f' + g') x :=
  sorry

theorem has_fderiv_at_filter.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} {L : filter E} (hf : has_fderiv_at_filter f f' x L)
    (hg : has_fderiv_at_filter g g' x L) :
    has_fderiv_at_filter (fun (y : E) => f y + g y) (f' + g') x L :=
  sorry

theorem has_fderiv_within_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
    has_fderiv_within_at (fun (y : E) => f y + g y) (f' + g') s x :=
  has_fderiv_at_filter.add hf hg

theorem has_fderiv_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
    has_fderiv_at (fun (x : E) => f x + g x) (f' + g') x :=
  has_fderiv_at_filter.add hf hg

theorem differentiable_within_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {x : E} {s : set E} (hf : differentiable_within_at 𝕜 f s x)
    (hg : differentiable_within_at 𝕜 g s x) :
    differentiable_within_at 𝕜 (fun (y : E) => f y + g y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.add (differentiable_within_at.has_fderiv_within_at hf)
      (differentiable_within_at.has_fderiv_within_at hg))

@[simp] theorem differentiable_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {x : E} (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
    differentiable_at 𝕜 (fun (y : E) => f y + g y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.add (differentiable_at.has_fderiv_at hf) (differentiable_at.has_fderiv_at hg))

theorem differentiable_on.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {s : set E} (hf : differentiable_on 𝕜 f s)
    (hg : differentiable_on 𝕜 g s) : differentiable_on 𝕜 (fun (y : E) => f y + g y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.add (hf x hx) (hg x hx)

@[simp] theorem differentiable.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
    differentiable 𝕜 fun (y : E) => f y + g y :=
  fun (x : E) => differentiable_at.add (hf x) (hg x)

theorem fderiv_within_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x)
    (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
    fderiv_within 𝕜 (fun (y : E) => f y + g y) s x =
        fderiv_within 𝕜 f s x + fderiv_within 𝕜 g s x :=
  sorry

theorem fderiv_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F}
    {x : E} (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
    fderiv 𝕜 (fun (y : E) => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  has_fderiv_at.fderiv
    (has_fderiv_at.add (differentiable_at.has_fderiv_at hf) (differentiable_at.has_fderiv_at hg))

theorem has_strict_fderiv_at.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_strict_fderiv_at f f' x)
    (c : F) : has_strict_fderiv_at (fun (y : E) => f y + c) f' x :=
  add_zero f' ▸ has_strict_fderiv_at.add hf (has_strict_fderiv_at_const c x)

theorem has_fderiv_at_filter.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (hf : has_fderiv_at_filter f f' x L) (c : F) :
    has_fderiv_at_filter (fun (y : E) => f y + c) f' x L :=
  add_zero f' ▸ has_fderiv_at_filter.add hf (has_fderiv_at_filter_const c x L)

theorem has_fderiv_within_at.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (hf : has_fderiv_within_at f f' s x) (c : F) :
    has_fderiv_within_at (fun (y : E) => f y + c) f' s x :=
  has_fderiv_at_filter.add_const hf c

theorem has_fderiv_at.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_fderiv_at f f' x) (c : F) :
    has_fderiv_at (fun (x : E) => f x + c) f' x :=
  has_fderiv_at_filter.add_const hf c

theorem differentiable_within_at.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (hf : differentiable_within_at 𝕜 f s x)
    (c : F) : differentiable_within_at 𝕜 (fun (y : E) => f y + c) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.add_const (differentiable_within_at.has_fderiv_within_at hf) c)

@[simp] theorem differentiable_within_at_add_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (c : F) :
    differentiable_within_at 𝕜 (fun (y : E) => f y + c) s x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_at.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (hf : differentiable_at 𝕜 f x) (c : F) :
    differentiable_at 𝕜 (fun (y : E) => f y + c) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.add_const (differentiable_at.has_fderiv_at hf) c)

@[simp] theorem differentiable_at_add_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (c : F) :
    differentiable_at 𝕜 (fun (y : E) => f y + c) x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_on.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (hf : differentiable_on 𝕜 f s) (c : F) :
    differentiable_on 𝕜 (fun (y : E) => f y + c) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.add_const (hf x hx) c

@[simp] theorem differentiable_on_add_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} (c : F) :
    differentiable_on 𝕜 (fun (y : E) => f y + c) s ↔ differentiable_on 𝕜 f s :=
  sorry

theorem differentiable.add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (hf : differentiable 𝕜 f) (c : F) : differentiable 𝕜 fun (y : E) => f y + c :=
  fun (x : E) => differentiable_at.add_const (hf x) c

@[simp] theorem differentiable_add_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} (c : F) :
    (differentiable 𝕜 fun (y : E) => f y + c) ↔ differentiable 𝕜 f :=
  sorry

theorem fderiv_within_add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
    fderiv_within 𝕜 (fun (y : E) => f y + c) s x = fderiv_within 𝕜 f s x :=
  sorry

theorem fderiv_add_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E}
    (c : F) : fderiv 𝕜 (fun (y : E) => f y + c) x = fderiv 𝕜 f x :=
  sorry

theorem has_strict_fderiv_at.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_strict_fderiv_at f f' x)
    (c : F) : has_strict_fderiv_at (fun (y : E) => c + f y) f' x :=
  zero_add f' ▸ has_strict_fderiv_at.add (has_strict_fderiv_at_const c x) hf

theorem has_fderiv_at_filter.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (hf : has_fderiv_at_filter f f' x L) (c : F) :
    has_fderiv_at_filter (fun (y : E) => c + f y) f' x L :=
  zero_add f' ▸ has_fderiv_at_filter.add (has_fderiv_at_filter_const c x L) hf

theorem has_fderiv_within_at.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (hf : has_fderiv_within_at f f' s x) (c : F) :
    has_fderiv_within_at (fun (y : E) => c + f y) f' s x :=
  has_fderiv_at_filter.const_add hf c

theorem has_fderiv_at.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_fderiv_at f f' x) (c : F) :
    has_fderiv_at (fun (x : E) => c + f x) f' x :=
  has_fderiv_at_filter.const_add hf c

theorem differentiable_within_at.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (hf : differentiable_within_at 𝕜 f s x)
    (c : F) : differentiable_within_at 𝕜 (fun (y : E) => c + f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.const_add (differentiable_within_at.has_fderiv_within_at hf) c)

@[simp] theorem differentiable_within_at_const_add_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (c : F) :
    differentiable_within_at 𝕜 (fun (y : E) => c + f y) s x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_at.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (hf : differentiable_at 𝕜 f x) (c : F) :
    differentiable_at 𝕜 (fun (y : E) => c + f y) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.const_add (differentiable_at.has_fderiv_at hf) c)

@[simp] theorem differentiable_at_const_add_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (c : F) :
    differentiable_at 𝕜 (fun (y : E) => c + f y) x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_on.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (hf : differentiable_on 𝕜 f s) (c : F) :
    differentiable_on 𝕜 (fun (y : E) => c + f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.const_add (hf x hx) c

@[simp] theorem differentiable_on_const_add_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} (c : F) :
    differentiable_on 𝕜 (fun (y : E) => c + f y) s ↔ differentiable_on 𝕜 f s :=
  sorry

theorem differentiable.const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (hf : differentiable 𝕜 f) (c : F) : differentiable 𝕜 fun (y : E) => c + f y :=
  fun (x : E) => differentiable_at.const_add (hf x) c

@[simp] theorem differentiable_const_add_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} (c : F) :
    (differentiable 𝕜 fun (y : E) => c + f y) ↔ differentiable 𝕜 f :=
  sorry

theorem fderiv_within_const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
    fderiv_within 𝕜 (fun (y : E) => c + f y) s x = fderiv_within 𝕜 f s x :=
  sorry

theorem fderiv_const_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E}
    (c : F) : fderiv 𝕜 (fun (y : E) => c + f y) x = fderiv 𝕜 f x :=
  sorry

/-! ### Derivative of a finite sum of functions -/

theorem has_strict_fderiv_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {ι : Type u_6} {u : finset ι} {A : ι → E → F} {A' : ι → continuous_linear_map 𝕜 E F}
    (h : ∀ (i : ι), i ∈ u → has_strict_fderiv_at (A i) (A' i) x) :
    has_strict_fderiv_at (fun (y : E) => finset.sum u fun (i : ι) => A i y)
        (finset.sum u fun (i : ι) => A' i) x :=
  sorry

theorem has_fderiv_at_filter.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {L : filter E} {ι : Type u_6} {u : finset ι} {A : ι → E → F}
    {A' : ι → continuous_linear_map 𝕜 E F}
    (h : ∀ (i : ι), i ∈ u → has_fderiv_at_filter (A i) (A' i) x L) :
    has_fderiv_at_filter (fun (y : E) => finset.sum u fun (i : ι) => A i y)
        (finset.sum u fun (i : ι) => A' i) x L :=
  sorry

theorem has_fderiv_within_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} {ι : Type u_6} {u : finset ι} {A : ι → E → F} {A' : ι → continuous_linear_map 𝕜 E F}
    (h : ∀ (i : ι), i ∈ u → has_fderiv_within_at (A i) (A' i) s x) :
    has_fderiv_within_at (fun (y : E) => finset.sum u fun (i : ι) => A i y)
        (finset.sum u fun (i : ι) => A' i) s x :=
  has_fderiv_at_filter.sum h

theorem has_fderiv_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {ι : Type u_6} {u : finset ι} {A : ι → E → F} {A' : ι → continuous_linear_map 𝕜 E F}
    (h : ∀ (i : ι), i ∈ u → has_fderiv_at (A i) (A' i) x) :
    has_fderiv_at (fun (y : E) => finset.sum u fun (i : ι) => A i y)
        (finset.sum u fun (i : ι) => A' i) x :=
  has_fderiv_at_filter.sum h

theorem differentiable_within_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} {ι : Type u_6} {u : finset ι} {A : ι → E → F}
    (h : ∀ (i : ι), i ∈ u → differentiable_within_at 𝕜 (A i) s x) :
    differentiable_within_at 𝕜 (fun (y : E) => finset.sum u fun (i : ι) => A i y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.sum
      fun (i : ι) (hi : i ∈ u) => differentiable_within_at.has_fderiv_within_at (h i hi))

@[simp] theorem differentiable_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {ι : Type u_6} {u : finset ι} {A : ι → E → F}
    (h : ∀ (i : ι), i ∈ u → differentiable_at 𝕜 (A i) x) :
    differentiable_at 𝕜 (fun (y : E) => finset.sum u fun (i : ι) => A i y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.sum fun (i : ι) (hi : i ∈ u) => differentiable_at.has_fderiv_at (h i hi))

theorem differentiable_on.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {s : set E} {ι : Type u_6} {u : finset ι} {A : ι → E → F}
    (h : ∀ (i : ι), i ∈ u → differentiable_on 𝕜 (A i) s) :
    differentiable_on 𝕜 (fun (y : E) => finset.sum u fun (i : ι) => A i y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.sum fun (i : ι) (hi : i ∈ u) => h i hi x hx

@[simp] theorem differentiable.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {ι : Type u_6} {u : finset ι} {A : ι → E → F} (h : ∀ (i : ι), i ∈ u → differentiable 𝕜 (A i)) :
    differentiable 𝕜 fun (y : E) => finset.sum u fun (i : ι) => A i y :=
  fun (x : E) => differentiable_at.sum fun (i : ι) (hi : i ∈ u) => h i hi x

theorem fderiv_within_sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} {ι : Type u_6} {u : finset ι} {A : ι → E → F} (hxs : unique_diff_within_at 𝕜 s x)
    (h : ∀ (i : ι), i ∈ u → differentiable_within_at 𝕜 (A i) s x) :
    fderiv_within 𝕜 (fun (y : E) => finset.sum u fun (i : ι) => A i y) s x =
        finset.sum u fun (i : ι) => fderiv_within 𝕜 (A i) s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.sum
      fun (i : ι) (hi : i ∈ u) => differentiable_within_at.has_fderiv_within_at (h i hi))
    hxs

theorem fderiv_sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {ι : Type u_6}
    {u : finset ι} {A : ι → E → F} (h : ∀ (i : ι), i ∈ u → differentiable_at 𝕜 (A i) x) :
    fderiv 𝕜 (fun (y : E) => finset.sum u fun (i : ι) => A i y) x =
        finset.sum u fun (i : ι) => fderiv 𝕜 (A i) x :=
  has_fderiv_at.fderiv
    (has_fderiv_at.sum fun (i : ι) (hi : i ∈ u) => differentiable_at.has_fderiv_at (h i hi))

/-! ### Derivative of the negative of a function -/

theorem has_strict_fderiv_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_strict_fderiv_at f f' x) :
    has_strict_fderiv_at (fun (x : E) => -f x) (-f') x :=
  has_strict_fderiv_at.comp x (continuous_linear_map.has_strict_fderiv_at (-1)) h

theorem has_fderiv_at_filter.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (h : has_fderiv_at_filter f f' x L) : has_fderiv_at_filter (fun (x : E) => -f x) (-f') x L :=
  has_fderiv_at_filter.comp x (continuous_linear_map.has_fderiv_at_filter (-1)) h

theorem has_fderiv_within_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x) : has_fderiv_within_at (fun (x : E) => -f x) (-f') s x :=
  has_fderiv_at_filter.neg h

theorem has_fderiv_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_fderiv_at f f' x) :
    has_fderiv_at (fun (x : E) => -f x) (-f') x :=
  has_fderiv_at_filter.neg h

theorem differentiable_within_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (h : differentiable_within_at 𝕜 f s x) :
    differentiable_within_at 𝕜 (fun (y : E) => -f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.neg (differentiable_within_at.has_fderiv_within_at h))

@[simp] theorem differentiable_within_at_neg_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} :
    differentiable_within_at 𝕜 (fun (y : E) => -f y) s x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (h : differentiable_at 𝕜 f x) :
    differentiable_at 𝕜 (fun (y : E) => -f y) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.neg (differentiable_at.has_fderiv_at h))

@[simp] theorem differentiable_at_neg_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} : differentiable_at 𝕜 (fun (y : E) => -f y) x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_on.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (h : differentiable_on 𝕜 f s) :
    differentiable_on 𝕜 (fun (y : E) => -f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.neg (h x hx)

@[simp] theorem differentiable_on_neg_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} :
    differentiable_on 𝕜 (fun (y : E) => -f y) s ↔ differentiable_on 𝕜 f s :=
  sorry

theorem differentiable.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (h : differentiable 𝕜 f) : differentiable 𝕜 fun (y : E) => -f y :=
  fun (x : E) => differentiable_at.neg (h x)

@[simp] theorem differentiable_neg_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} : (differentiable 𝕜 fun (y : E) => -f y) ↔ differentiable 𝕜 f :=
  sorry

theorem fderiv_within_neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (fun (y : E) => -f y) s x = -fderiv_within 𝕜 f s x :=
  sorry

@[simp] theorem fderiv_neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} : fderiv 𝕜 (fun (y : E) => -f y) x = -fderiv 𝕜 f x :=
  sorry

/-! ### Derivative of the difference of two functions -/

theorem has_strict_fderiv_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} (hf : has_strict_fderiv_at f f' x) (hg : has_strict_fderiv_at g g' x) :
    has_strict_fderiv_at (fun (x : E) => f x - g x) (f' - g') x :=
  sorry

theorem has_fderiv_at_filter.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} {L : filter E} (hf : has_fderiv_at_filter f f' x L)
    (hg : has_fderiv_at_filter g g' x L) :
    has_fderiv_at_filter (fun (x : E) => f x - g x) (f' - g') x L :=
  sorry

theorem has_fderiv_within_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} {s : set E} (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
    has_fderiv_within_at (fun (x : E) => f x - g x) (f' - g') s x :=
  has_fderiv_at_filter.sub hf hg

theorem has_fderiv_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {f' : continuous_linear_map 𝕜 E F} {g' : continuous_linear_map 𝕜 E F}
    {x : E} (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
    has_fderiv_at (fun (x : E) => f x - g x) (f' - g') x :=
  has_fderiv_at_filter.sub hf hg

theorem differentiable_within_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {x : E} {s : set E} (hf : differentiable_within_at 𝕜 f s x)
    (hg : differentiable_within_at 𝕜 g s x) :
    differentiable_within_at 𝕜 (fun (y : E) => f y - g y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.sub (differentiable_within_at.has_fderiv_within_at hf)
      (differentiable_within_at.has_fderiv_within_at hg))

@[simp] theorem differentiable_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {x : E} (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
    differentiable_at 𝕜 (fun (y : E) => f y - g y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.sub (differentiable_at.has_fderiv_at hf) (differentiable_at.has_fderiv_at hg))

theorem differentiable_on.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {s : set E} (hf : differentiable_on 𝕜 f s)
    (hg : differentiable_on 𝕜 g s) : differentiable_on 𝕜 (fun (y : E) => f y - g y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.sub (hf x hx) (hg x hx)

@[simp] theorem differentiable.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
    differentiable 𝕜 fun (y : E) => f y - g y :=
  fun (x : E) => differentiable_at.sub (hf x) (hg x)

theorem fderiv_within_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {g : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x)
    (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
    fderiv_within 𝕜 (fun (y : E) => f y - g y) s x =
        fderiv_within 𝕜 f s x - fderiv_within 𝕜 g s x :=
  sorry

theorem fderiv_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {g : E → F}
    {x : E} (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
    fderiv 𝕜 (fun (y : E) => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  has_fderiv_at.fderiv
    (has_fderiv_at.sub (differentiable_at.has_fderiv_at hf) (differentiable_at.has_fderiv_at hg))

theorem has_strict_fderiv_at.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_strict_fderiv_at f f' x)
    (c : F) : has_strict_fderiv_at (fun (x : E) => f x - c) f' x :=
  sorry

theorem has_fderiv_at_filter.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (hf : has_fderiv_at_filter f f' x L) (c : F) :
    has_fderiv_at_filter (fun (x : E) => f x - c) f' x L :=
  sorry

theorem has_fderiv_within_at.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (hf : has_fderiv_within_at f f' s x) (c : F) :
    has_fderiv_within_at (fun (x : E) => f x - c) f' s x :=
  has_fderiv_at_filter.sub_const hf c

theorem has_fderiv_at.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_fderiv_at f f' x) (c : F) :
    has_fderiv_at (fun (x : E) => f x - c) f' x :=
  has_fderiv_at_filter.sub_const hf c

theorem differentiable_within_at.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (hf : differentiable_within_at 𝕜 f s x)
    (c : F) : differentiable_within_at 𝕜 (fun (y : E) => f y - c) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.sub_const (differentiable_within_at.has_fderiv_within_at hf) c)

@[simp] theorem differentiable_within_at_sub_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (c : F) :
    differentiable_within_at 𝕜 (fun (y : E) => f y - c) s x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_at.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (hf : differentiable_at 𝕜 f x) (c : F) :
    differentiable_at 𝕜 (fun (y : E) => f y - c) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.sub_const (differentiable_at.has_fderiv_at hf) c)

@[simp] theorem differentiable_at_sub_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (c : F) :
    differentiable_at 𝕜 (fun (y : E) => f y - c) x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_on.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (hf : differentiable_on 𝕜 f s) (c : F) :
    differentiable_on 𝕜 (fun (y : E) => f y - c) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.sub_const (hf x hx) c

@[simp] theorem differentiable_on_sub_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} (c : F) :
    differentiable_on 𝕜 (fun (y : E) => f y - c) s ↔ differentiable_on 𝕜 f s :=
  sorry

theorem differentiable.sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (hf : differentiable 𝕜 f) (c : F) : differentiable 𝕜 fun (y : E) => f y - c :=
  fun (x : E) => differentiable_at.sub_const (hf x) c

@[simp] theorem differentiable_sub_const_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} (c : F) :
    (differentiable 𝕜 fun (y : E) => f y - c) ↔ differentiable 𝕜 f :=
  sorry

theorem fderiv_within_sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
    fderiv_within 𝕜 (fun (y : E) => f y - c) s x = fderiv_within 𝕜 f s x :=
  sorry

theorem fderiv_sub_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E}
    (c : F) : fderiv 𝕜 (fun (y : E) => f y - c) x = fderiv 𝕜 f x :=
  sorry

theorem has_strict_fderiv_at.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_strict_fderiv_at f f' x)
    (c : F) : has_strict_fderiv_at (fun (x : E) => c - f x) (-f') x :=
  sorry

theorem has_fderiv_at_filter.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {L : filter E}
    (hf : has_fderiv_at_filter f f' x L) (c : F) :
    has_fderiv_at_filter (fun (x : E) => c - f x) (-f') x L :=
  sorry

theorem has_fderiv_within_at.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (hf : has_fderiv_within_at f f' s x) (c : F) :
    has_fderiv_within_at (fun (x : E) => c - f x) (-f') s x :=
  has_fderiv_at_filter.const_sub hf c

theorem has_fderiv_at.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (hf : has_fderiv_at f f' x) (c : F) :
    has_fderiv_at (fun (x : E) => c - f x) (-f') x :=
  has_fderiv_at_filter.const_sub hf c

theorem differentiable_within_at.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (hf : differentiable_within_at 𝕜 f s x)
    (c : F) : differentiable_within_at 𝕜 (fun (y : E) => c - f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.const_sub (differentiable_within_at.has_fderiv_within_at hf) c)

@[simp] theorem differentiable_within_at_const_sub_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} {s : set E} (c : F) :
    differentiable_within_at 𝕜 (fun (y : E) => c - f y) s x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem differentiable_at.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} (hf : differentiable_at 𝕜 f x) (c : F) :
    differentiable_at 𝕜 (fun (y : E) => c - f y) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.const_sub (differentiable_at.has_fderiv_at hf) c)

@[simp] theorem differentiable_at_const_sub_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {x : E} (c : F) :
    differentiable_at 𝕜 (fun (y : E) => c - f y) x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem differentiable_on.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} (hf : differentiable_on 𝕜 f s) (c : F) :
    differentiable_on 𝕜 (fun (y : E) => c - f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.const_sub (hf x hx) c

@[simp] theorem differentiable_on_const_sub_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} (c : F) :
    differentiable_on 𝕜 (fun (y : E) => c - f y) s ↔ differentiable_on 𝕜 f s :=
  sorry

theorem differentiable.const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} (hf : differentiable 𝕜 f) (c : F) : differentiable 𝕜 fun (y : E) => c - f y :=
  fun (x : E) => differentiable_at.const_sub (hf x) c

@[simp] theorem differentiable_const_sub_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} (c : F) :
    (differentiable 𝕜 fun (y : E) => c - f y) ↔ differentiable 𝕜 f :=
  sorry

theorem fderiv_within_const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
    fderiv_within 𝕜 (fun (y : E) => c - f y) s x = -fderiv_within 𝕜 f s x :=
  sorry

theorem fderiv_const_sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E}
    (c : F) : fderiv 𝕜 (fun (y : E) => c - f y) x = -fderiv 𝕜 f x :=
  sorry

/-! ### Derivative of a bounded bilinear map -/

theorem is_bounded_bilinear_map.has_strict_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
    has_strict_fderiv_at b (is_bounded_bilinear_map.deriv h p) p :=
  sorry

theorem is_bounded_bilinear_map.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
    has_fderiv_at b (is_bounded_bilinear_map.deriv h p) p :=
  has_strict_fderiv_at.has_fderiv_at (is_bounded_bilinear_map.has_strict_fderiv_at h p)

theorem is_bounded_bilinear_map.has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    {u : set (E × F)} (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
    has_fderiv_within_at b (is_bounded_bilinear_map.deriv h p) u p :=
  has_fderiv_at.has_fderiv_within_at (is_bounded_bilinear_map.has_fderiv_at h p)

theorem is_bounded_bilinear_map.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) : differentiable_at 𝕜 b p :=
  has_fderiv_at.differentiable_at (is_bounded_bilinear_map.has_fderiv_at h p)

theorem is_bounded_bilinear_map.differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    {u : set (E × F)} (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
    differentiable_within_at 𝕜 b u p :=
  differentiable_at.differentiable_within_at (is_bounded_bilinear_map.differentiable_at h p)

theorem is_bounded_bilinear_map.fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
    fderiv 𝕜 b p = is_bounded_bilinear_map.deriv h p :=
  has_fderiv_at.fderiv (is_bounded_bilinear_map.has_fderiv_at h p)

theorem is_bounded_bilinear_map.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    {u : set (E × F)} (h : is_bounded_bilinear_map 𝕜 b) (p : E × F)
    (hxs : unique_diff_within_at 𝕜 u p) :
    fderiv_within 𝕜 b u p = is_bounded_bilinear_map.deriv h p :=
  sorry

theorem is_bounded_bilinear_map.differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) : differentiable 𝕜 b :=
  fun (x : E × F) => is_bounded_bilinear_map.differentiable_at h x

theorem is_bounded_bilinear_map.differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    {u : set (E × F)} (h : is_bounded_bilinear_map 𝕜 b) : differentiable_on 𝕜 b u :=
  differentiable.differentiable_on (is_bounded_bilinear_map.differentiable h)

theorem is_bounded_bilinear_map.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) : continuous b :=
  differentiable.continuous (is_bounded_bilinear_map.differentiable h)

theorem is_bounded_bilinear_map.continuous_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) {f : F} : continuous fun (e : E) => b (e, f) :=
  continuous.comp (is_bounded_bilinear_map.continuous h)
    (continuous.prod_mk continuous_id continuous_const)

theorem is_bounded_bilinear_map.continuous_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G}
    (h : is_bounded_bilinear_map 𝕜 b) {e : E} : continuous fun (f : F) => b (e, f) :=
  continuous.comp (is_bounded_bilinear_map.continuous h)
    (continuous.prod_mk continuous_const continuous_id)

namespace continuous_linear_equiv


/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.  These facts are placed here
because the proof uses `is_bounded_bilinear_map.continuous_left`, proved just above as a consequence
of its differentiability.
-/

protected theorem is_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    [complete_space E] : is_open (set.range coe) :=
  sorry

protected theorem nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space E]
    (e : continuous_linear_equiv 𝕜 E F) : set.range coe ∈ nhds ↑e :=
  sorry

end continuous_linear_equiv


/-! ### Derivative of the product of a scalar-valued function and a vector-valued function -/

theorem has_strict_fderiv_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {c : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_strict_fderiv_at c c' x)
    (hf : has_strict_fderiv_at f f' x) :
    has_strict_fderiv_at (fun (y : E) => c y • f y)
        (c x • f' + continuous_linear_map.smul_right c' (f x)) x :=
  has_strict_fderiv_at.comp x
    (is_bounded_bilinear_map.has_strict_fderiv_at is_bounded_bilinear_map_smul (c x, f x))
    (has_strict_fderiv_at.prod hc hf)

theorem has_fderiv_within_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E} {c : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_fderiv_within_at c c' s x)
    (hf : has_fderiv_within_at f f' s x) :
    has_fderiv_within_at (fun (y : E) => c y • f y)
        (c x • f' + continuous_linear_map.smul_right c' (f x)) s x :=
  has_fderiv_at.comp_has_fderiv_within_at x
    (is_bounded_bilinear_map.has_fderiv_at is_bounded_bilinear_map_smul (c x, f x))
    (has_fderiv_within_at.prod hc hf)

theorem has_fderiv_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {c : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_fderiv_at c c' x) (hf : has_fderiv_at f f' x) :
    has_fderiv_at (fun (y : E) => c y • f y) (c x • f' + continuous_linear_map.smul_right c' (f x))
        x :=
  has_fderiv_at.comp x
    (is_bounded_bilinear_map.has_fderiv_at is_bounded_bilinear_map_smul (c x, f x))
    (has_fderiv_at.prod hc hf)

theorem differentiable_within_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {c : E → 𝕜} (hc : differentiable_within_at 𝕜 c s x)
    (hf : differentiable_within_at 𝕜 f s x) :
    differentiable_within_at 𝕜 (fun (y : E) => c y • f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.smul (differentiable_within_at.has_fderiv_within_at hc)
      (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
    differentiable_at 𝕜 (fun (y : E) => c y • f y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.smul (differentiable_at.has_fderiv_at hc) (differentiable_at.has_fderiv_at hf))

theorem differentiable_on.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {s : set E} {c : E → 𝕜} (hc : differentiable_on 𝕜 c s)
    (hf : differentiable_on 𝕜 f s) : differentiable_on 𝕜 (fun (y : E) => c y • f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.smul (hc x hx) (hf x hx)

@[simp] theorem differentiable.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {c : E → 𝕜} (hc : differentiable 𝕜 c) (hf : differentiable 𝕜 f) :
    differentiable 𝕜 fun (y : E) => c y • f y :=
  fun (x : E) => differentiable_at.smul (hc x) (hf x)

theorem fderiv_within_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {x : E} {s : set E} {c : E → 𝕜} (hxs : unique_diff_within_at 𝕜 s x)
    (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
    fderiv_within 𝕜 (fun (y : E) => c y • f y) s x =
        c x • fderiv_within 𝕜 f s x +
          continuous_linear_map.smul_right (fderiv_within 𝕜 c s x) (f x) :=
  sorry

theorem fderiv_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E}
    {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
    fderiv 𝕜 (fun (y : E) => c y • f y) x =
        c x • fderiv 𝕜 f x + continuous_linear_map.smul_right (fderiv 𝕜 c x) (f x) :=
  has_fderiv_at.fderiv
    (has_fderiv_at.smul (differentiable_at.has_fderiv_at hc) (differentiable_at.has_fderiv_at hf))

theorem has_strict_fderiv_at.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_strict_fderiv_at c c' x) (f : F) :
    has_strict_fderiv_at (fun (y : E) => c y • f) (continuous_linear_map.smul_right c' f) x :=
  sorry

theorem has_fderiv_within_at.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_fderiv_within_at c c' s x)
    (f : F) :
    has_fderiv_within_at (fun (y : E) => c y • f) (continuous_linear_map.smul_right c' f) s x :=
  sorry

theorem has_fderiv_at.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_fderiv_at c c' x) (f : F) :
    has_fderiv_at (fun (y : E) => c y • f) (continuous_linear_map.smul_right c' f) x :=
  sorry

theorem differentiable_within_at.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {x : E} {s : set E} {c : E → 𝕜} (hc : differentiable_within_at 𝕜 c s x)
    (f : F) : differentiable_within_at 𝕜 (fun (y : E) => c y • f) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.smul_const (differentiable_within_at.has_fderiv_within_at hc) f)

theorem differentiable_at.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (f : F) :
    differentiable_at 𝕜 (fun (y : E) => c y • f) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.smul_const (differentiable_at.has_fderiv_at hc) f)

theorem differentiable_on.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {s : set E} {c : E → 𝕜} (hc : differentiable_on 𝕜 c s) (f : F) :
    differentiable_on 𝕜 (fun (y : E) => c y • f) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.smul_const (hc x hx) f

theorem differentiable.smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {c : E → 𝕜} (hc : differentiable 𝕜 c) (f : F) : differentiable 𝕜 fun (y : E) => c y • f :=
  fun (x : E) => differentiable_at.smul_const (hc x) f

theorem fderiv_within_smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {s : set E} {c : E → 𝕜} (hxs : unique_diff_within_at 𝕜 s x)
    (hc : differentiable_within_at 𝕜 c s x) (f : F) :
    fderiv_within 𝕜 (fun (y : E) => c y • f) s x =
        continuous_linear_map.smul_right (fderiv_within 𝕜 c s x) f :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.smul_const (differentiable_within_at.has_fderiv_within_at hc) f) hxs

theorem fderiv_smul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E}
    {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun (y : E) => c y • f) x = continuous_linear_map.smul_right (fderiv 𝕜 c x) f :=
  has_fderiv_at.fderiv (has_fderiv_at.smul_const (differentiable_at.has_fderiv_at hc) f)

/-! ### Derivative of the product of two scalar-valued functions -/

theorem has_strict_fderiv_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {d : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} {d' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_strict_fderiv_at c c' x) (hd : has_strict_fderiv_at d d' x) :
    has_strict_fderiv_at (fun (y : E) => c y * d y) (c x • d' + d x • c') x :=
  sorry

theorem has_fderiv_within_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜} {d : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} {d' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_fderiv_within_at c c' s x) (hd : has_fderiv_within_at d d' s x) :
    has_fderiv_within_at (fun (y : E) => c y * d y) (c x • d' + d x • c') s x :=
  sorry

theorem has_fderiv_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {d : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} {d' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_fderiv_at c c' x) (hd : has_fderiv_at d d' x) :
    has_fderiv_at (fun (y : E) => c y * d y) (c x • d' + d x • c') x :=
  sorry

theorem differentiable_within_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜} {d : E → 𝕜}
    (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
    differentiable_within_at 𝕜 (fun (y : E) => c y * d y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.mul (differentiable_within_at.has_fderiv_within_at hc)
      (differentiable_within_at.has_fderiv_within_at hd))

@[simp] theorem differentiable_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {d : E → 𝕜}
    (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
    differentiable_at 𝕜 (fun (y : E) => c y * d y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.mul (differentiable_at.has_fderiv_at hc) (differentiable_at.has_fderiv_at hd))

theorem differentiable_on.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {s : set E} {c : E → 𝕜} {d : E → 𝕜}
    (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) :
    differentiable_on 𝕜 (fun (y : E) => c y * d y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.mul (hc x hx) (hd x hx)

@[simp] theorem differentiable.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {c : E → 𝕜} {d : E → 𝕜} (hc : differentiable 𝕜 c)
    (hd : differentiable 𝕜 d) : differentiable 𝕜 fun (y : E) => c y * d y :=
  fun (x : E) => differentiable_at.mul (hc x) (hd x)

theorem fderiv_within_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜} {d : E → 𝕜}
    (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x)
    (hd : differentiable_within_at 𝕜 d s x) :
    fderiv_within 𝕜 (fun (y : E) => c y * d y) s x =
        c x • fderiv_within 𝕜 d s x + d x • fderiv_within 𝕜 c s x :=
  sorry

theorem fderiv_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {d : E → 𝕜} (hc : differentiable_at 𝕜 c x)
    (hd : differentiable_at 𝕜 d x) :
    fderiv 𝕜 (fun (y : E) => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  has_fderiv_at.fderiv
    (has_fderiv_at.mul (differentiable_at.has_fderiv_at hc) (differentiable_at.has_fderiv_at hd))

theorem has_strict_fderiv_at.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_strict_fderiv_at c c' x) (d : 𝕜) :
    has_strict_fderiv_at (fun (y : E) => c y * d) (d • c') x :=
  sorry

theorem has_fderiv_within_at.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_fderiv_within_at c c' s x) (d : 𝕜) :
    has_fderiv_within_at (fun (y : E) => c y * d) (d • c') s x :=
  sorry

theorem has_fderiv_at.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_fderiv_at c c' x) (d : 𝕜) : has_fderiv_at (fun (y : E) => c y * d) (d • c') x :=
  sorry

theorem differentiable_within_at.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜}
    (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜) :
    differentiable_within_at 𝕜 (fun (y : E) => c y * d) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.mul_const (differentiable_within_at.has_fderiv_within_at hc) d)

theorem differentiable_at.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (d : 𝕜) :
    differentiable_at 𝕜 (fun (y : E) => c y * d) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.mul_const (differentiable_at.has_fderiv_at hc) d)

theorem differentiable_on.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {s : set E} {c : E → 𝕜} (hc : differentiable_on 𝕜 c s)
    (d : 𝕜) : differentiable_on 𝕜 (fun (y : E) => c y * d) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.mul_const (hc x hx) d

theorem differentiable.mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {c : E → 𝕜} (hc : differentiable 𝕜 c) (d : 𝕜) :
    differentiable 𝕜 fun (y : E) => c y * d :=
  fun (x : E) => differentiable_at.mul_const (hc x) d

theorem fderiv_within_mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜}
    (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜) :
    fderiv_within 𝕜 (fun (y : E) => c y * d) s x = d • fderiv_within 𝕜 c s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.mul_const (differentiable_within_at.has_fderiv_within_at hc) d) hxs

theorem fderiv_mul_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {x : E} {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (d : 𝕜) :
    fderiv 𝕜 (fun (y : E) => c y * d) x = d • fderiv 𝕜 c x :=
  has_fderiv_at.fderiv (has_fderiv_at.mul_const (differentiable_at.has_fderiv_at hc) d)

theorem has_strict_fderiv_at.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_strict_fderiv_at c c' x) (d : 𝕜) :
    has_strict_fderiv_at (fun (y : E) => d * c y) (d • c') x :=
  sorry

theorem has_fderiv_within_at.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜}
    {c' : continuous_linear_map 𝕜 E 𝕜} (hc : has_fderiv_within_at c c' s x) (d : 𝕜) :
    has_fderiv_within_at (fun (y : E) => d * c y) (d • c') s x :=
  sorry

theorem has_fderiv_at.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} {c' : continuous_linear_map 𝕜 E 𝕜}
    (hc : has_fderiv_at c c' x) (d : 𝕜) : has_fderiv_at (fun (y : E) => d * c y) (d • c') x :=
  sorry

theorem differentiable_within_at.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜}
    (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜) :
    differentiable_within_at 𝕜 (fun (y : E) => d * c y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.const_mul (differentiable_within_at.has_fderiv_within_at hc) d)

theorem differentiable_at.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (d : 𝕜) :
    differentiable_at 𝕜 (fun (y : E) => d * c y) x :=
  has_fderiv_at.differentiable_at (has_fderiv_at.const_mul (differentiable_at.has_fderiv_at hc) d)

theorem differentiable_on.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {s : set E} {c : E → 𝕜} (hc : differentiable_on 𝕜 c s)
    (d : 𝕜) : differentiable_on 𝕜 (fun (y : E) => d * c y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.const_mul (hc x hx) d

theorem differentiable.const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {c : E → 𝕜} (hc : differentiable 𝕜 c) (d : 𝕜) :
    differentiable 𝕜 fun (y : E) => d * c y :=
  fun (x : E) => differentiable_at.const_mul (hc x) d

theorem fderiv_within_const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {x : E} {s : set E} {c : E → 𝕜}
    (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x) (d : 𝕜) :
    fderiv_within 𝕜 (fun (y : E) => d * c y) s x = d • fderiv_within 𝕜 c s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.const_mul (differentiable_within_at.has_fderiv_within_at hc) d) hxs

theorem fderiv_const_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E]
    [normed_space 𝕜 E] {x : E} {c : E → 𝕜} (hc : differentiable_at 𝕜 c x) (d : 𝕜) :
    fderiv 𝕜 (fun (y : E) => d * c y) x = d • fderiv 𝕜 c x :=
  has_fderiv_at.fderiv (has_fderiv_at.const_mul (differentiable_at.has_fderiv_at hc) d)

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
theorem has_fderiv_at_ring_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {R : Type u_6}
    [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] (x : units R) :
    has_fderiv_at ring.inverse
        (-continuous_linear_map.comp (continuous_linear_map.lmul_right 𝕜 R ↑(x⁻¹))
            (continuous_linear_map.lmul_left 𝕜 R ↑(x⁻¹)))
        ↑x :=
  sorry

theorem differentiable_at_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {R : Type u_6}
    [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] (x : units R) :
    differentiable_at 𝕜 ring.inverse ↑x :=
  has_fderiv_at.differentiable_at (has_fderiv_at_ring_inverse x)

theorem fderiv_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {R : Type u_6} [normed_ring R]
    [normed_algebra 𝕜 R] [complete_space R] (x : units R) :
    fderiv 𝕜 ring.inverse ↑x =
        -continuous_linear_map.comp (continuous_linear_map.lmul_right 𝕜 R ↑(x⁻¹))
            (continuous_linear_map.lmul_left 𝕜 R ↑(x⁻¹)) :=
  has_fderiv_at.fderiv (has_fderiv_at_ring_inverse x)

/-! ### Differentiability of linear equivs, and invariance of differentiability -/

protected theorem continuous_linear_equiv.has_strict_fderiv_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {x : E} (iso : continuous_linear_equiv 𝕜 E F) :
    has_strict_fderiv_at (⇑iso) (↑iso) x :=
  continuous_linear_map.has_strict_fderiv_at (continuous_linear_equiv.to_continuous_linear_map iso)

protected theorem continuous_linear_equiv.has_fderiv_within_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {x : E} {s : set E} (iso : continuous_linear_equiv 𝕜 E F) :
    has_fderiv_within_at (⇑iso) (↑iso) s x :=
  continuous_linear_map.has_fderiv_within_at (continuous_linear_equiv.to_continuous_linear_map iso)

protected theorem continuous_linear_equiv.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {x : E} (iso : continuous_linear_equiv 𝕜 E F) :
    has_fderiv_at (⇑iso) (↑iso) x :=
  continuous_linear_map.has_fderiv_at_filter (continuous_linear_equiv.to_continuous_linear_map iso)

protected theorem continuous_linear_equiv.differentiable_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {x : E} (iso : continuous_linear_equiv 𝕜 E F) :
    differentiable_at 𝕜 (⇑iso) x :=
  has_fderiv_at.differentiable_at (continuous_linear_equiv.has_fderiv_at iso)

protected theorem continuous_linear_equiv.differentiable_within_at {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {x : E} {s : set E} (iso : continuous_linear_equiv 𝕜 E F) :
    differentiable_within_at 𝕜 (⇑iso) s x :=
  differentiable_at.differentiable_within_at (continuous_linear_equiv.differentiable_at iso)

protected theorem continuous_linear_equiv.fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {x : E} (iso : continuous_linear_equiv 𝕜 E F) : fderiv 𝕜 (⇑iso) x = ↑iso :=
  has_fderiv_at.fderiv (continuous_linear_equiv.has_fderiv_at iso)

protected theorem continuous_linear_equiv.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {x : E} {s : set E} (iso : continuous_linear_equiv 𝕜 E F)
    (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 (⇑iso) s x = ↑iso :=
  continuous_linear_map.fderiv_within (continuous_linear_equiv.to_continuous_linear_map iso) hxs

protected theorem continuous_linear_equiv.differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (iso : continuous_linear_equiv 𝕜 E F) : differentiable 𝕜 ⇑iso :=
  fun (x : E) => continuous_linear_equiv.differentiable_at iso

protected theorem continuous_linear_equiv.differentiable_on {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {s : set E} (iso : continuous_linear_equiv 𝕜 E F) :
    differentiable_on 𝕜 (⇑iso) s :=
  differentiable.differentiable_on (continuous_linear_equiv.differentiable iso)

theorem continuous_linear_equiv.comp_differentiable_within_at_iff {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {s : set G} {x : G} :
    differentiable_within_at 𝕜 (⇑iso ∘ f) s x ↔ differentiable_within_at 𝕜 f s x :=
  sorry

theorem continuous_linear_equiv.comp_differentiable_at_iff {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {x : G} :
    differentiable_at 𝕜 (⇑iso ∘ f) x ↔ differentiable_at 𝕜 f x :=
  sorry

theorem continuous_linear_equiv.comp_differentiable_on_iff {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {s : set G} :
    differentiable_on 𝕜 (⇑iso ∘ f) s ↔ differentiable_on 𝕜 f s :=
  sorry

theorem continuous_linear_equiv.comp_differentiable_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} :
    differentiable 𝕜 (⇑iso ∘ f) ↔ differentiable 𝕜 f :=
  sorry

theorem continuous_linear_equiv.comp_has_fderiv_within_at_iff {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {s : set G} {x : G}
    {f' : continuous_linear_map 𝕜 G E} :
    has_fderiv_within_at (⇑iso ∘ f) (continuous_linear_map.comp (↑iso) f') s x ↔
        has_fderiv_within_at f f' s x :=
  sorry

theorem continuous_linear_equiv.comp_has_strict_fderiv_at_iff {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {x : G} {f' : continuous_linear_map 𝕜 G E} :
    has_strict_fderiv_at (⇑iso ∘ f) (continuous_linear_map.comp (↑iso) f') x ↔
        has_strict_fderiv_at f f' x :=
  sorry

theorem continuous_linear_equiv.comp_has_fderiv_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {x : G} {f' : continuous_linear_map 𝕜 G E} :
    has_fderiv_at (⇑iso ∘ f) (continuous_linear_map.comp (↑iso) f') x ↔ has_fderiv_at f f' x :=
  sorry

theorem continuous_linear_equiv.comp_has_fderiv_within_at_iff' {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {s : set G} {x : G}
    {f' : continuous_linear_map 𝕜 G F} :
    has_fderiv_within_at (⇑iso ∘ f) f' s x ↔
        has_fderiv_within_at f (continuous_linear_map.comp (↑(continuous_linear_equiv.symm iso)) f')
          s x :=
  sorry

theorem continuous_linear_equiv.comp_has_fderiv_at_iff' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {x : G} {f' : continuous_linear_map 𝕜 G F} :
    has_fderiv_at (⇑iso ∘ f) f' x ↔
        has_fderiv_at f (continuous_linear_map.comp (↑(continuous_linear_equiv.symm iso)) f') x :=
  sorry

theorem continuous_linear_equiv.comp_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {s : set G} {x : G}
    (hxs : unique_diff_within_at 𝕜 s x) :
    fderiv_within 𝕜 (⇑iso ∘ f) s x = continuous_linear_map.comp (↑iso) (fderiv_within 𝕜 f s x) :=
  sorry

theorem continuous_linear_equiv.comp_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G]
    (iso : continuous_linear_equiv 𝕜 E F) {f : G → E} {x : G} :
    fderiv 𝕜 (⇑iso ∘ f) x = continuous_linear_map.comp (↑iso) (fderiv 𝕜 f x) :=
  sorry

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_fderiv_at.of_local_left_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {g : F → E} {a : F}
    (hg : continuous_at g a) (hf : has_strict_fderiv_at f (↑f') (g a))
    (hfg : filter.eventually (fun (y : F) => f (g y) = y) (nhds a)) :
    has_strict_fderiv_at g (↑(continuous_linear_equiv.symm f')) a :=
  sorry

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_fderiv_at.of_local_left_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_equiv 𝕜 E F} {g : F → E} {a : F}
    (hg : continuous_at g a) (hf : has_fderiv_at f (↑f') (g a))
    (hfg : filter.eventually (fun (y : F) => f (g y) = y) (nhds a)) :
    has_fderiv_at g (↑(continuous_linear_equiv.symm f')) a :=
  sorry

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.has_strict_fderiv_at_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (f : local_homeomorph E F) {f' : continuous_linear_equiv 𝕜 E F} {a : F}
    (ha : a ∈ local_equiv.target (local_homeomorph.to_local_equiv f))
    (htff' : has_strict_fderiv_at (⇑f) (↑f') (coe_fn (local_homeomorph.symm f) a)) :
    has_strict_fderiv_at (⇑(local_homeomorph.symm f)) (↑(continuous_linear_equiv.symm f')) a :=
  has_strict_fderiv_at.of_local_left_inverse
    (local_homeomorph.continuous_at (local_homeomorph.symm f) ha) htff'
    (local_homeomorph.eventually_right_inverse f ha)

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.has_fderiv_at_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] (f : local_homeomorph E F) {f' : continuous_linear_equiv 𝕜 E F} {a : F}
    (ha : a ∈ local_equiv.target (local_homeomorph.to_local_equiv f))
    (htff' : has_fderiv_at (⇑f) (↑f') (coe_fn (local_homeomorph.symm f) a)) :
    has_fderiv_at (⇑(local_homeomorph.symm f)) (↑(continuous_linear_equiv.symm f')) a :=
  has_fderiv_at.of_local_left_inverse (local_homeomorph.continuous_at (local_homeomorph.symm f) ha)
    htff' (local_homeomorph.eventually_right_inverse f ha)

theorem has_fderiv_within_at.eventually_ne {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {s : set E}
    (h : has_fderiv_within_at f f' s x)
    (hf' : ∃ (C : ℝ), ∀ (z : E), norm z ≤ C * norm (coe_fn f' z)) :
    filter.eventually (fun (z : E) => f z ≠ f x) (nhds_within x (s \ singleton x)) :=
  sorry

theorem has_fderiv_at.eventually_ne {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F]
    {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} (h : has_fderiv_at f f' x)
    (hf' : ∃ (C : ℝ), ∀ (z : E), norm z ≤ C * norm (coe_fn f' z)) :
    filter.eventually (fun (z : E) => f z ≠ f x) (nhds_within x (singleton xᶜ)) :=
  sorry

/-
  In the special case of a normed space over the reals,
  we can use  scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/

theorem has_fderiv_at_filter_real_equiv {E : Type u_1} [normed_group E] [normed_space ℝ E]
    {F : Type u_2} [normed_group F] [normed_space ℝ F] {f : E → F}
    {f' : continuous_linear_map ℝ E F} {x : E} {L : filter E} :
    filter.tendsto (fun (x' : E) => norm (x' - x)⁻¹ * norm (f x' - f x - coe_fn f' (x' - x))) L
          (nhds 0) ↔
        filter.tendsto (fun (x' : E) => norm (x' - x)⁻¹ • (f x' - f x - coe_fn f' (x' - x))) L
          (nhds 0) :=
  sorry

theorem has_fderiv_at.lim_real {E : Type u_1} [normed_group E] [normed_space ℝ E] {F : Type u_2}
    [normed_group F] [normed_space ℝ F] {f : E → F} {f' : continuous_linear_map ℝ E F} {x : E}
    (hf : has_fderiv_at f f' x) (v : E) :
    filter.tendsto (fun (c : ℝ) => c • (f (x + c⁻¹ • v) - f x)) filter.at_top
        (nhds (coe_fn f' v)) :=
  sorry

/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
theorem has_fderiv_within_at.maps_to_tangent_cone {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (h : has_fderiv_within_at f f' s x) :
    set.maps_to (⇑f') (tangent_cone_at 𝕜 s x) (tangent_cone_at 𝕜 (f '' s) (f x)) :=
  sorry

/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
theorem has_fderiv_within_at.unique_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F]
    [normed_space 𝕜 F] {f : E → F} {s : set E} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (h : has_fderiv_within_at f f' s x) (hs : unique_diff_within_at 𝕜 s x) (h' : dense_range ⇑f') :
    unique_diff_within_at 𝕜 (f '' s) (f x) :=
  sorry

theorem has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {f : E → F} {s : set E} {x : E}
    (e' : continuous_linear_equiv 𝕜 E F) (h : has_fderiv_within_at f (↑e') s x)
    (hs : unique_diff_within_at 𝕜 s x) : unique_diff_within_at 𝕜 (f '' s) (f x) :=
  has_fderiv_within_at.unique_diff_within_at h hs
    (function.surjective.dense_range (continuous_linear_equiv.surjective e'))

theorem continuous_linear_equiv.unique_diff_on_preimage_iff {𝕜 : Type u_1}
    [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3}
    [normed_group F] [normed_space 𝕜 F] {s : set E} (e : continuous_linear_equiv 𝕜 F E) :
    unique_diff_on 𝕜 (⇑e ⁻¹' s) ↔ unique_diff_on 𝕜 s :=
  sorry

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/

theorem has_strict_fderiv_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4}
    [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    {f' : continuous_linear_map 𝕜' E F} {x : E} (h : has_strict_fderiv_at f f' x) :
    has_strict_fderiv_at f (continuous_linear_map.restrict_scalars 𝕜 f') x :=
  h

theorem has_fderiv_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4} [normed_group F]
    [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    {f' : continuous_linear_map 𝕜' E F} {x : E} (h : has_fderiv_at f f' x) :
    has_fderiv_at f (continuous_linear_map.restrict_scalars 𝕜 f') x :=
  h

theorem has_fderiv_within_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4}
    [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    {f' : continuous_linear_map 𝕜' E F} {s : set E} {x : E} (h : has_fderiv_within_at f f' s x) :
    has_fderiv_within_at f (continuous_linear_map.restrict_scalars 𝕜 f') s x :=
  h

theorem differentiable_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4}
    [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    {x : E} (h : differentiable_at 𝕜' f x) : differentiable_at 𝕜 f x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.restrict_scalars 𝕜 (differentiable_at.has_fderiv_at h))

theorem differentiable_within_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4}
    [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    {s : set E} {x : E} (h : differentiable_within_at 𝕜' f s x) :
    differentiable_within_at 𝕜 f s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.restrict_scalars 𝕜 (differentiable_within_at.has_fderiv_within_at h))

theorem differentiable_on.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4}
    [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    {s : set E} (h : differentiable_on 𝕜' f s) : differentiable_on 𝕜 f s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.restrict_scalars 𝕜 (h x hx)

theorem differentiable.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] {F : Type u_4} [normed_group F]
    [normed_space 𝕜 F] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F}
    (h : differentiable 𝕜' f) : differentiable 𝕜 f :=
  fun (x : E) => differentiable_at.restrict_scalars 𝕜 (h x)

/-!
### Multiplying by a complex function respects real differentiability

Consider two functions `c : E → ℂ` and `f : E → F` where `F` is a complex vector space. If both
`c` and `f` are differentiable over `ℝ`, then so is their product. This paragraph proves this
statement, in the general version where `ℝ` is replaced by a field `𝕜`, and `ℂ` is replaced
by a normed algebra `𝕜'` over `𝕜`.
 -/

theorem has_strict_fderiv_at.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F}
    {x : E} {c : E → 𝕜'} {c' : continuous_linear_map 𝕜 E 𝕜'} (hc : has_strict_fderiv_at c c' x)
    (hf : has_strict_fderiv_at f f' x) :
    has_strict_fderiv_at (fun (y : E) => c y • f y)
        (c x • f' + continuous_linear_map.smul_algebra_right c' (f x)) x :=
  has_strict_fderiv_at.comp x
    (is_bounded_bilinear_map.has_strict_fderiv_at is_bounded_bilinear_map_smul_algebra (c x, f x))
    (has_strict_fderiv_at.prod hc hf)

theorem has_fderiv_within_at.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F}
    {s : set E} {x : E} {c : E → 𝕜'} {c' : continuous_linear_map 𝕜 E 𝕜'}
    (hc : has_fderiv_within_at c c' s x) (hf : has_fderiv_within_at f f' s x) :
    has_fderiv_within_at (fun (y : E) => c y • f y)
        (c x • f' + continuous_linear_map.smul_algebra_right c' (f x)) s x :=
  has_fderiv_at.comp_has_fderiv_within_at x
    (is_bounded_bilinear_map.has_fderiv_at is_bounded_bilinear_map_smul_algebra (c x, f x))
    (has_fderiv_within_at.prod hc hf)

theorem has_fderiv_at.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E} {c : E → 𝕜'}
    {c' : continuous_linear_map 𝕜 E 𝕜'} (hc : has_fderiv_at c c' x) (hf : has_fderiv_at f f' x) :
    has_fderiv_at (fun (y : E) => c y • f y)
        (c x • f' + continuous_linear_map.smul_algebra_right c' (f x)) x :=
  has_fderiv_at.comp x
    (is_bounded_bilinear_map.has_fderiv_at is_bounded_bilinear_map_smul_algebra (c x, f x))
    (has_fderiv_at.prod hc hf)

theorem differentiable_within_at.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {s : set E} {x : E} {c : E → 𝕜'}
    (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
    differentiable_within_at 𝕜 (fun (y : E) => c y • f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.smul_algebra (differentiable_within_at.has_fderiv_within_at hc)
      (differentiable_within_at.has_fderiv_within_at hf))

@[simp] theorem differentiable_at.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {x : E} {c : E → 𝕜'}
    (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
    differentiable_at 𝕜 (fun (y : E) => c y • f y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.smul_algebra (differentiable_at.has_fderiv_at hc)
      (differentiable_at.has_fderiv_at hf))

theorem differentiable_on.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {s : set E} {c : E → 𝕜'} (hc : differentiable_on 𝕜 c s)
    (hf : differentiable_on 𝕜 f s) : differentiable_on 𝕜 (fun (y : E) => c y • f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.smul_algebra (hc x hx) (hf x hx)

@[simp] theorem differentiable.smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {c : E → 𝕜'} (hc : differentiable 𝕜 c)
    (hf : differentiable 𝕜 f) : differentiable 𝕜 fun (y : E) => c y • f y :=
  fun (x : E) => differentiable_at.smul_algebra (hc x) (hf x)

theorem fderiv_within_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {s : set E} {x : E} {c : E → 𝕜'}
    (hxs : unique_diff_within_at 𝕜 s x) (hc : differentiable_within_at 𝕜 c s x)
    (hf : differentiable_within_at 𝕜 f s x) :
    fderiv_within 𝕜 (fun (y : E) => c y • f y) s x =
        c x • fderiv_within 𝕜 f s x +
          continuous_linear_map.smul_algebra_right (fderiv_within 𝕜 c s x) (f x) :=
  sorry

theorem fderiv_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {x : E} {c : E → 𝕜'} (hc : differentiable_at 𝕜 c x)
    (hf : differentiable_at 𝕜 f x) :
    fderiv 𝕜 (fun (y : E) => c y • f y) x =
        c x • fderiv 𝕜 f x + continuous_linear_map.smul_algebra_right (fderiv 𝕜 c x) (f x) :=
  has_fderiv_at.fderiv
    (has_fderiv_at.smul_algebra (differentiable_at.has_fderiv_at hc)
      (differentiable_at.has_fderiv_at hf))

theorem has_strict_fderiv_at.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {x : E} {c : E → 𝕜'}
    {c' : continuous_linear_map 𝕜 E 𝕜'} (hc : has_strict_fderiv_at c c' x) (f : F) :
    has_strict_fderiv_at (fun (y : E) => c y • f) (continuous_linear_map.smul_algebra_right c' f)
        x :=
  sorry

theorem has_fderiv_within_at.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {s : set E} {x : E} {c : E → 𝕜'}
    {c' : continuous_linear_map 𝕜 E 𝕜'} (hc : has_fderiv_within_at c c' s x) (f : F) :
    has_fderiv_within_at (fun (y : E) => c y • f) (continuous_linear_map.smul_algebra_right c' f) s
        x :=
  sorry

theorem has_fderiv_at.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {x : E} {c : E → 𝕜'} {c' : continuous_linear_map 𝕜 E 𝕜'}
    (hc : has_fderiv_at c c' x) (f : F) :
    has_fderiv_at (fun (y : E) => c y • f) (continuous_linear_map.smul_algebra_right c' f) x :=
  sorry

theorem differentiable_within_at.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {s : set E} {x : E} {c : E → 𝕜'}
    (hc : differentiable_within_at 𝕜 c s x) (f : F) :
    differentiable_within_at 𝕜 (fun (y : E) => c y • f) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.smul_algebra_const (differentiable_within_at.has_fderiv_within_at hc) f)

theorem differentiable_at.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {x : E} {c : E → 𝕜'} (hc : differentiable_at 𝕜 c x)
    (f : F) : differentiable_at 𝕜 (fun (y : E) => c y • f) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.smul_algebra_const (differentiable_at.has_fderiv_at hc) f)

theorem differentiable_on.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {s : set E} {c : E → 𝕜'}
    (hc : differentiable_on 𝕜 c s) (f : F) : differentiable_on 𝕜 (fun (y : E) => c y • f) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.smul_algebra_const (hc x hx) f

theorem differentiable.smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {c : E → 𝕜'} (hc : differentiable 𝕜 c) (f : F) :
    differentiable 𝕜 fun (y : E) => c y • f :=
  fun (x : E) => differentiable_at.smul_algebra_const (hc x) f

theorem fderiv_within_smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {s : set E} {x : E} {c : E → 𝕜'} (hxs : unique_diff_within_at 𝕜 s x)
    (hc : differentiable_within_at 𝕜 c s x) (f : F) :
    fderiv_within 𝕜 (fun (y : E) => c y • f) s x =
        continuous_linear_map.smul_algebra_right (fderiv_within 𝕜 c s x) f :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.smul_algebra_const (differentiable_within_at.has_fderiv_within_at hc) f)
    hxs

theorem fderiv_smul_algebra_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {x : E} {c : E → 𝕜'} (hc : differentiable_at 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun (y : E) => c y • f) x =
        continuous_linear_map.smul_algebra_right (fderiv 𝕜 c x) f :=
  has_fderiv_at.fderiv (has_fderiv_at.smul_algebra_const (differentiable_at.has_fderiv_at hc) f)

theorem has_strict_fderiv_at.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F}
    {x : E} (h : has_strict_fderiv_at f f' x) (c : 𝕜') :
    has_strict_fderiv_at (fun (x : E) => c • f x) (c • f') x :=
  has_strict_fderiv_at.comp x (continuous_linear_map.has_strict_fderiv_at (c • 1)) h

theorem has_fderiv_at_filter.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F}
    {x : E} {L : filter E} (h : has_fderiv_at_filter f f' x L) (c : 𝕜') :
    has_fderiv_at_filter (fun (x : E) => c • f x) (c • f') x L :=
  has_fderiv_at_filter.comp x (continuous_linear_map.has_fderiv_at_filter (c • 1)) h

theorem has_fderiv_within_at.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F}
    {s : set E} {x : E} (h : has_fderiv_within_at f f' s x) (c : 𝕜') :
    has_fderiv_within_at (fun (x : E) => c • f x) (c • f') s x :=
  has_fderiv_at_filter.const_smul_algebra h c

theorem has_fderiv_at.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {f' : continuous_linear_map 𝕜 E F} {x : E}
    (h : has_fderiv_at f f' x) (c : 𝕜') : has_fderiv_at (fun (x : E) => c • f x) (c • f') x :=
  has_fderiv_at_filter.const_smul_algebra h c

theorem differentiable_within_at.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {s : set E} {x : E}
    (h : differentiable_within_at 𝕜 f s x) (c : 𝕜') :
    differentiable_within_at 𝕜 (fun (y : E) => c • f y) s x :=
  has_fderiv_within_at.differentiable_within_at
    (has_fderiv_within_at.const_smul_algebra (differentiable_within_at.has_fderiv_within_at h) c)

theorem differentiable_at.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {x : E} (h : differentiable_at 𝕜 f x)
    (c : 𝕜') : differentiable_at 𝕜 (fun (y : E) => c • f y) x :=
  has_fderiv_at.differentiable_at
    (has_fderiv_at.const_smul_algebra (differentiable_at.has_fderiv_at h) c)

theorem differentiable_on.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {s : set E}
    (h : differentiable_on 𝕜 f s) (c : 𝕜') : differentiable_on 𝕜 (fun (y : E) => c • f y) s :=
  fun (x : E) (hx : x ∈ s) => differentiable_within_at.const_smul_algebra (h x hx) c

theorem differentiable.const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜]
    {𝕜' : Type u_2} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3}
    [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F]
    [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {f : E → F} (h : differentiable 𝕜 f) (c : 𝕜') :
    differentiable 𝕜 fun (y : E) => c • f y :=
  fun (x : E) => differentiable_at.const_smul_algebra (h x) c

theorem fderiv_within_const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {s : set E} {x : E} (hxs : unique_diff_within_at 𝕜 s x)
    (h : differentiable_within_at 𝕜 f s x) (c : 𝕜') :
    fderiv_within 𝕜 (fun (y : E) => c • f y) s x = c • fderiv_within 𝕜 f s x :=
  has_fderiv_within_at.fderiv_within
    (has_fderiv_within_at.const_smul_algebra (differentiable_within_at.has_fderiv_within_at h) c)
    hxs

theorem fderiv_const_smul_algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {𝕜' : Type u_2}
    [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] {E : Type u_3} [normed_group E]
    [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
    [is_scalar_tower 𝕜 𝕜' F] {f : E → F} {x : E} (h : differentiable_at 𝕜 f x) (c : 𝕜') :
    fderiv 𝕜 (fun (y : E) => c • f y) x = c • fderiv 𝕜 f x :=
  has_fderiv_at.fderiv (has_fderiv_at.const_smul_algebra (differentiable_at.has_fderiv_at h) c)

end Mathlib