/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.mean_value
import Mathlib.analysis.calculus.formal_multilinear_series
import Mathlib.PostPort

universes u_1 u_2 u_3 l u_4 u u_5 u_6 u_7 

namespace Mathlib

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iterated_fderiv_within` relative to a domain,
as well as predicates `times_cont_diff_within_at`, `times_cont_diff_at`, `times_cont_diff_on` and
`times_cont_diff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `times_cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nondiscrete normed field `𝕜`.

* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `times_cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `times_cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `times_cont_diff_at 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `times_cont_diff_within_at 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `times_cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`times_cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

We also prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be  glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `times_cont_diff_within_at` and `times_cont_diff_on`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `times_cont_diff_within_at 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iterated_fderiv 𝕜 (n + 1) f x = iterated_fderiv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : with_top ℕ` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

/-! ### Functions with a Taylor series on a domain -/

/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : with_top ℕ) (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) (s : set E) 
where
  zero_eq : ∀ (x : E), x ∈ s → continuous_multilinear_map.uncurry0 (p x 0) = f x
  fderiv_within : ∀ (m : ℕ),
  ↑m < n →
    ∀ (x : E),
      x ∈ s → has_fderiv_within_at (fun (y : E) => p y m) (continuous_multilinear_map.curry_left (p x (Nat.succ m))) s x
  cont : ∀ (m : ℕ), ↑m ≤ n → continuous_on (fun (x : E) => p x m) s

theorem has_ftaylor_series_up_to_on.zero_eq' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) {x : E} (hx : x ∈ s) : p x 0 = coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_fin0 𝕜 E F)) (f x) := sorry

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
theorem has_ftaylor_series_up_to_on.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) (h₁ : ∀ (x : E), x ∈ s → f₁ x = f x) : has_ftaylor_series_up_to_on n f₁ p s := sorry

theorem has_ftaylor_series_up_to_on.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) {t : set E} (hst : t ⊆ s) : has_ftaylor_series_up_to_on n f p t := sorry

theorem has_ftaylor_series_up_to_on.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {m : with_top ℕ} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) (hmn : m ≤ n) : has_ftaylor_series_up_to_on m f p s := sorry

theorem has_ftaylor_series_up_to_on.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) : continuous_on f s := sorry

theorem has_ftaylor_series_up_to_on_zero_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} : has_ftaylor_series_up_to_on 0 f p s ↔
  continuous_on f s ∧ ∀ (x : E), x ∈ s → continuous_multilinear_map.uncurry0 (p x 0) = f x := sorry

theorem has_ftaylor_series_up_to_on_top_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} : has_ftaylor_series_up_to_on ⊤ f p s ↔ ∀ (n : ℕ), has_ftaylor_series_up_to_on (↑n) f p s := sorry

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on.has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : x ∈ s) : has_fderiv_within_at f (coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p x 1)) s x := sorry

theorem has_ftaylor_series_up_to_on.differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
  fun (x : E) (hx : x ∈ s) =>
    has_fderiv_within_at.differentiable_within_at (has_ftaylor_series_up_to_on.has_fderiv_within_at h hn hx)

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : ℕ} : has_ftaylor_series_up_to_on (↑n + 1) f p s ↔
  has_ftaylor_series_up_to_on (↑n) f p s ∧
    (∀ (x : E),
        x ∈ s →
          has_fderiv_within_at (fun (y : E) => p y n) (continuous_multilinear_map.curry_left (p x (Nat.succ n))) s x) ∧
      continuous_on (fun (x : E) => p x (n + 1)) s := sorry

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : ℕ} : has_ftaylor_series_up_to_on (↑(n + 1)) f p s ↔
  (∀ (x : E), x ∈ s → continuous_multilinear_map.uncurry0 (p x 0) = f x) ∧
    (∀ (x : E),
        x ∈ s → has_fderiv_within_at (fun (y : E) => p y 0) (continuous_multilinear_map.curry_left (p x 1)) s x) ∧
      has_ftaylor_series_up_to_on (↑n) (fun (x : E) => coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p x 1))
        (fun (x : E) => formal_multilinear_series.shift (p x)) s := sorry

/-! ### Smooth functions within a set around a point -/

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def times_cont_diff_within_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : with_top ℕ) (f : E → F) (s : set E) (x : E) :=
  ∀ (m : ℕ),
    ↑m ≤ n →
      ∃ (u : set E),
        ∃ (H : u ∈ nhds_within x (insert x s)),
          ∃ (p : E → formal_multilinear_series 𝕜 E F), has_ftaylor_series_up_to_on (↑m) f p u

theorem times_cont_diff_within_at_nat {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : ℕ} : times_cont_diff_within_at 𝕜 (↑n) f s x ↔
  ∃ (u : set E),
    ∃ (H : u ∈ nhds_within x (insert x s)),
      ∃ (p : E → formal_multilinear_series 𝕜 E F), has_ftaylor_series_up_to_on (↑n) f p u := sorry

theorem times_cont_diff_within_at.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {m : with_top ℕ} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (hmn : m ≤ n) : times_cont_diff_within_at 𝕜 m f s x :=
  fun (k : ℕ) (hk : ↑k ≤ m) => h k (le_trans hk hmn)

theorem times_cont_diff_within_at_iff_forall_nat_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} : times_cont_diff_within_at 𝕜 n f s x ↔ ∀ (m : ℕ), ↑m ≤ n → times_cont_diff_within_at 𝕜 (↑m) f s x :=
  { mp := fun (H : times_cont_diff_within_at 𝕜 n f s x) (m : ℕ) (hm : ↑m ≤ n) => times_cont_diff_within_at.of_le H hm,
    mpr := fun (H : ∀ (m : ℕ), ↑m ≤ n → times_cont_diff_within_at 𝕜 (↑m) f s x) (m : ℕ) (hm : ↑m ≤ n) => H m hm m le_rfl }

theorem times_cont_diff_within_at_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} : times_cont_diff_within_at 𝕜 ⊤ f s x ↔ ∀ (n : ℕ), times_cont_diff_within_at 𝕜 (↑n) f s x := sorry

theorem times_cont_diff_within_at.continuous_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) : continuous_within_at f s x := sorry

theorem times_cont_diff_within_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : times_cont_diff_within_at 𝕜 n f₁ s x := sorry

theorem times_cont_diff_within_at.congr_of_eventually_eq' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : x ∈ s) : times_cont_diff_within_at 𝕜 n f₁ s x :=
  times_cont_diff_within_at.congr_of_eventually_eq h h₁ (filter.eventually.self_of_nhds_within h₁ hx)

theorem filter.eventually_eq.times_cont_diff_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {x : E} {n : with_top ℕ} (h₁ : filter.eventually_eq (nhds_within x s) f₁ f) (hx : f₁ x = f x) : times_cont_diff_within_at 𝕜 n f₁ s x ↔ times_cont_diff_within_at 𝕜 n f s x := sorry

theorem times_cont_diff_within_at.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (h₁ : ∀ (y : E), y ∈ s → f₁ y = f y) (hx : f₁ x = f x) : times_cont_diff_within_at 𝕜 n f₁ s x :=
  times_cont_diff_within_at.congr_of_eventually_eq h (filter.eventually_eq_of_mem self_mem_nhds_within h₁) hx

theorem times_cont_diff_within_at.mono_of_mem {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : s ∈ nhds_within x t) : times_cont_diff_within_at 𝕜 n f t x := sorry

theorem times_cont_diff_within_at.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : t ⊆ s) : times_cont_diff_within_at 𝕜 n f t x :=
  times_cont_diff_within_at.mono_of_mem h (filter.mem_sets_of_superset self_mem_nhds_within hst)

theorem times_cont_diff_within_at.congr_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : nhds_within x s = nhds_within x t) : times_cont_diff_within_at 𝕜 n f t x :=
  times_cont_diff_within_at.mono_of_mem h (hst ▸ self_mem_nhds_within)

theorem times_cont_diff_within_at_congr_nhds {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} {t : set E} (hst : nhds_within x s = nhds_within x t) : times_cont_diff_within_at 𝕜 n f s x ↔ times_cont_diff_within_at 𝕜 n f t x :=
  { mp := fun (h : times_cont_diff_within_at 𝕜 n f s x) => times_cont_diff_within_at.congr_nhds h hst,
    mpr := fun (h : times_cont_diff_within_at 𝕜 n f t x) => times_cont_diff_within_at.congr_nhds h (Eq.symm hst) }

theorem times_cont_diff_within_at_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {t : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : t ∈ nhds_within x s) : times_cont_diff_within_at 𝕜 n f (s ∩ t) x ↔ times_cont_diff_within_at 𝕜 n f s x :=
  times_cont_diff_within_at_congr_nhds (Eq.symm (nhds_within_restrict'' s h))

theorem times_cont_diff_within_at_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {t : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : t ∈ nhds x) : times_cont_diff_within_at 𝕜 n f (s ∩ t) x ↔ times_cont_diff_within_at 𝕜 n f s x :=
  times_cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds h)

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
theorem times_cont_diff_within_at.differentiable_within_at' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (hn : 1 ≤ n) : differentiable_within_at 𝕜 f (insert x s) x := sorry

theorem times_cont_diff_within_at.differentiable_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (hn : 1 ≤ n) : differentiable_within_at 𝕜 f s x :=
  differentiable_within_at.mono (times_cont_diff_within_at.differentiable_within_at' h hn) (set.subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_within_at_succ_iff_has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : ℕ} : times_cont_diff_within_at 𝕜 (↑(n + 1)) f s x ↔
  ∃ (u : set E),
    ∃ (H : u ∈ nhds_within x (insert x s)),
      ∃ (f' : E → continuous_linear_map 𝕜 E F),
        (∀ (x : E), x ∈ u → has_fderiv_within_at f (f' x) u x) ∧ times_cont_diff_within_at 𝕜 (↑n) f' u x := sorry

/-! ### Smooth functions within a set -/

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def times_cont_diff_on (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : with_top ℕ) (f : E → F) (s : set E) :=
  ∀ (x : E), x ∈ s → times_cont_diff_within_at 𝕜 n f s x

theorem times_cont_diff_on.times_cont_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hx : x ∈ s) : times_cont_diff_within_at 𝕜 n f s x :=
  h x hx

theorem times_cont_diff_within_at.times_cont_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} {m : ℕ} (hm : ↑m ≤ n) (h : times_cont_diff_within_at 𝕜 n f s x) : ∃ (u : set E), ∃ (H : u ∈ nhds_within x (insert x s)), u ⊆ insert x s ∧ times_cont_diff_on 𝕜 (↑m) f u := sorry

theorem times_cont_diff_on.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {m : with_top ℕ} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hmn : m ≤ n) : times_cont_diff_on 𝕜 m f s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.of_le (h x hx) hmn

theorem times_cont_diff_on_iff_forall_nat_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} : times_cont_diff_on 𝕜 n f s ↔ ∀ (m : ℕ), ↑m ≤ n → times_cont_diff_on 𝕜 (↑m) f s := sorry

theorem times_cont_diff_on_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} : times_cont_diff_on 𝕜 ⊤ f s ↔ ∀ (n : ℕ), times_cont_diff_on 𝕜 (↑n) f s := sorry

theorem times_cont_diff_on_all_iff_nat {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} : (∀ (n : with_top ℕ), times_cont_diff_on 𝕜 n f s) ↔ ∀ (n : ℕ), times_cont_diff_on 𝕜 (↑n) f s := sorry

theorem times_cont_diff_on.continuous_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) : continuous_on f s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.continuous_within_at (h x hx)

theorem times_cont_diff_on.congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (h₁ : ∀ (x : E), x ∈ s → f₁ x = f x) : times_cont_diff_on 𝕜 n f₁ s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.congr (h x hx) h₁ (h₁ x hx)

theorem times_cont_diff_on_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {n : with_top ℕ} (h₁ : ∀ (x : E), x ∈ s → f₁ x = f x) : times_cont_diff_on 𝕜 n f₁ s ↔ times_cont_diff_on 𝕜 n f s :=
  { mp :=
      fun (H : times_cont_diff_on 𝕜 n f₁ s) => times_cont_diff_on.congr H fun (x : E) (hx : x ∈ s) => Eq.symm (h₁ x hx),
    mpr := fun (H : times_cont_diff_on 𝕜 n f s) => times_cont_diff_on.congr H h₁ }

theorem times_cont_diff_on.mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) {t : set E} (hst : t ⊆ s) : times_cont_diff_on 𝕜 n f t :=
  fun (x : E) (hx : x ∈ t) => times_cont_diff_within_at.mono (h x (hst hx)) hst

theorem times_cont_diff_on.congr_mono {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {s₁ : set E} {f : E → F} {f₁ : E → F} {n : with_top ℕ} (hf : times_cont_diff_on 𝕜 n f s) (h₁ : ∀ (x : E), x ∈ s₁ → f₁ x = f x) (hs : s₁ ⊆ s) : times_cont_diff_on 𝕜 n f₁ s₁ :=
  times_cont_diff_on.congr (times_cont_diff_on.mono hf hs) h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
theorem times_cont_diff_on.differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.differentiable_within_at (h x hx) hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
theorem times_cont_diff_on_of_locally_times_cont_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : ∀ (x : E), x ∈ s → ∃ (u : set E), is_open u ∧ x ∈ u ∧ times_cont_diff_on 𝕜 n f (s ∩ u)) : times_cont_diff_on 𝕜 n f s := sorry

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_on_succ_iff_has_fderiv_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : ℕ} : times_cont_diff_on 𝕜 (↑(n + 1)) f s ↔
  ∀ (x : E) (H : x ∈ s),
    ∃ (u : set E),
      ∃ (H : u ∈ nhds_within x (insert x s)),
        ∃ (f' : E → continuous_linear_map 𝕜 E F),
          (∀ (x : E), x ∈ u → has_fderiv_within_at f (f' x) u x) ∧ times_cont_diff_on 𝕜 (↑n) f' u := sorry

/-! ### Iterated derivative within a set -/

/--
The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
def iterated_fderiv_within (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : ℕ) (f : E → F) (s : set E) : E → continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F :=
  nat.rec_on n (fun (x : E) => continuous_multilinear_map.curry0 𝕜 E (f x))
    fun (n : ℕ) (rec : E → continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F) (x : E) =>
      continuous_linear_map.uncurry_left (fderiv_within 𝕜 rec s x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylor_series_within (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (s : set E) (x : E) : formal_multilinear_series 𝕜 E F :=
  fun (n : ℕ) => iterated_fderiv_within 𝕜 n f s x

@[simp] theorem iterated_fderiv_within_zero_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} (m : fin 0 → E) : coe_fn (iterated_fderiv_within 𝕜 0 f s x) m = f x :=
  rfl

theorem iterated_fderiv_within_zero_eq_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} : iterated_fderiv_within 𝕜 0 f s = ⇑(continuous_linear_equiv.symm (continuous_multilinear_curry_fin0 𝕜 E F)) ∘ f :=
  rfl

theorem iterated_fderiv_within_succ_apply_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : ℕ} (m : fin (n + 1) → E) : coe_fn (iterated_fderiv_within 𝕜 (n + 1) f s x) m =
  coe_fn (coe_fn (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s x) (m 0)) (fin.tail m) :=
  rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iterated_fderiv_within_succ_eq_comp_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : ℕ} : iterated_fderiv_within 𝕜 (n + 1) f s =
  ⇑(continuous_multilinear_curry_left_equiv 𝕜 (fun (i : fin (n + 1)) => E) F) ∘
    fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s :=
  rfl

theorem iterated_fderiv_within_succ_apply_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : ℕ} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : fin (n + 1) → E) : coe_fn (iterated_fderiv_within 𝕜 (n + 1) f s x) m =
  coe_fn (coe_fn (iterated_fderiv_within 𝕜 n (fun (y : E) => fderiv_within 𝕜 f s y) s x) (fin.init m)) (m (fin.last n)) := sorry

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iterated_fderiv_within_succ_eq_comp_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : ℕ} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) : iterated_fderiv_within 𝕜 (n + 1) f s x =
  function.comp (⇑(continuous_multilinear_curry_right_equiv' 𝕜 n E F))
    (iterated_fderiv_within 𝕜 n (fun (y : E) => fderiv_within 𝕜 f s y) s) x := sorry

@[simp] theorem iterated_fderiv_within_one_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : fin 1 → E) : coe_fn (iterated_fderiv_within 𝕜 1 f s x) m = coe_fn (fderiv_within 𝕜 f s x) (m 0) := sorry

/-- If two functions coincide on a set `s` of unique differentiability, then their iterated
differentials within this set coincide. -/
theorem iterated_fderiv_within_congr {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {f₁ : E → F} {x : E} {n : ℕ} (hs : unique_diff_on 𝕜 s) (hL : ∀ (y : E), y ∈ s → f₁ y = f y) (hx : x ∈ s) : iterated_fderiv_within 𝕜 n f₁ s x = iterated_fderiv_within 𝕜 n f s x := sorry

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
theorem iterated_fderiv_within_inter_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {u : set E} {f : E → F} {x : E} {n : ℕ} (hu : is_open u) (hs : unique_diff_on 𝕜 (s ∩ u)) (hx : x ∈ s ∩ u) : iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x := sorry

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
theorem iterated_fderiv_within_inter' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {u : set E} {f : E → F} {x : E} {n : ℕ} (hu : u ∈ nhds_within x s) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) : iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x := sorry

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
theorem iterated_fderiv_within_inter {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {u : set E} {f : E → F} {x : E} {n : ℕ} (hu : u ∈ nhds x) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) : iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
  iterated_fderiv_within_inter' (mem_nhds_within_of_mem_nhds hu) hs xs

@[simp] theorem times_cont_diff_on_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} : times_cont_diff_on 𝕜 0 f s ↔ continuous_on f s := sorry

theorem times_cont_diff_within_at_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} (hx : x ∈ s) : times_cont_diff_within_at 𝕜 0 f s x ↔ ∃ (u : set E), ∃ (H : u ∈ nhds_within x s), continuous_on f (s ∩ u) := sorry

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p s) {m : ℕ} (hmn : ↑m ≤ n) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) : p x m = iterated_fderiv_within 𝕜 m f s x := sorry

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on.ftaylor_series_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) : has_ftaylor_series_up_to_on n f (ftaylor_series_within 𝕜 f s) s := sorry

theorem times_cont_diff_on_of_continuous_on_differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (Hcont : ∀ (m : ℕ), ↑m ≤ n → continuous_on (fun (x : E) => iterated_fderiv_within 𝕜 m f s x) s) (Hdiff : ∀ (m : ℕ), ↑m < n → differentiable_on 𝕜 (fun (x : E) => iterated_fderiv_within 𝕜 m f s x) s) : times_cont_diff_on 𝕜 n f s := sorry

theorem times_cont_diff_on_of_differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : ∀ (m : ℕ), ↑m ≤ n → differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s) : times_cont_diff_on 𝕜 n f s :=
  times_cont_diff_on_of_continuous_on_differentiable_on
    (fun (m : ℕ) (hm : ↑m ≤ n) => differentiable_on.continuous_on (h m hm)) fun (m : ℕ) (hm : ↑m < n) => h m (le_of_lt hm)

theorem times_cont_diff_on.continuous_on_iterated_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} {m : ℕ} (h : times_cont_diff_on 𝕜 n f s) (hmn : ↑m ≤ n) (hs : unique_diff_on 𝕜 s) : continuous_on (iterated_fderiv_within 𝕜 m f s) s :=
  has_ftaylor_series_up_to_on.cont (times_cont_diff_on.ftaylor_series_within h hs) m hmn

theorem times_cont_diff_on.differentiable_on_iterated_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} {m : ℕ} (h : times_cont_diff_on 𝕜 n f s) (hmn : ↑m < n) (hs : unique_diff_on 𝕜 s) : differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s :=
  fun (x : E) (hx : x ∈ s) =>
    has_fderiv_within_at.differentiable_within_at
      (has_ftaylor_series_up_to_on.fderiv_within (times_cont_diff_on.ftaylor_series_within h hs) m hmn x hx)

theorem times_cont_diff_on_iff_continuous_on_differentiable_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (hs : unique_diff_on 𝕜 s) : times_cont_diff_on 𝕜 n f s ↔
  (∀ (m : ℕ), ↑m ≤ n → continuous_on (fun (x : E) => iterated_fderiv_within 𝕜 m f s x) s) ∧
    ∀ (m : ℕ), ↑m < n → differentiable_on 𝕜 (fun (x : E) => iterated_fderiv_within 𝕜 m f s x) s := sorry

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderiv_within`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : ℕ} (hs : unique_diff_on 𝕜 s) : times_cont_diff_on 𝕜 (↑(n + 1)) f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 (↑n) (fun (y : E) => fderiv_within 𝕜 f s y) s := sorry

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : ℕ} (hs : is_open s) : times_cont_diff_on 𝕜 (↑(n + 1)) f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 (↑n) (fun (y : E) => fderiv 𝕜 f y) s := sorry

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderiv_within`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} (hs : unique_diff_on 𝕜 s) : times_cont_diff_on 𝕜 ⊤ f s ↔ differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 ⊤ (fun (y : E) => fderiv_within 𝕜 f s y) s := sorry

/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} (hs : is_open s) : times_cont_diff_on 𝕜 ⊤ f s ↔ differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 ⊤ (fun (y : E) => fderiv 𝕜 f y) s := sorry

theorem times_cont_diff_on.fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) : times_cont_diff_on 𝕜 m (fun (y : E) => fderiv_within 𝕜 f s y) s := sorry

theorem times_cont_diff_on.fderiv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_diff_on 𝕜 n f s) (hs : is_open s) (hmn : m + 1 ≤ n) : times_cont_diff_on 𝕜 m (fun (y : E) => fderiv 𝕜 f y) s :=
  times_cont_diff_on.congr (times_cont_diff_on.fderiv_within hf (is_open.unique_diff_on hs) hmn)
    fun (x : E) (hx : x ∈ s) => Eq.symm (fderiv_within_of_open hs hx)

theorem times_cont_diff_on.continuous_on_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) : continuous_on (fun (x : E) => fderiv_within 𝕜 f s x) s :=
  times_cont_diff_on.continuous_on
    (and.right (iff.mp (times_cont_diff_on_succ_iff_fderiv_within hs) (times_cont_diff_on.of_le h hn)))

theorem times_cont_diff_on.continuous_on_fderiv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hs : is_open s) (hn : 1 ≤ n) : continuous_on (fun (x : E) => fderiv 𝕜 f x) s :=
  times_cont_diff_on.continuous_on
    (and.right (iff.mp (times_cont_diff_on_succ_iff_fderiv_of_open hs) (times_cont_diff_on.of_le h hn)))

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem times_cont_diff_on.continuous_on_fderiv_within_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) : continuous_on (fun (p : E × E) => coe_fn (fderiv_within 𝕜 f s (prod.fst p)) (prod.snd p)) (set.prod s set.univ) := sorry

/-! ### Functions with a Taylor series on the whole space -/

/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : with_top ℕ) (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) 
where
  zero_eq : ∀ (x : E), continuous_multilinear_map.uncurry0 (p x 0) = f x
  fderiv : ∀ (m : ℕ),
  ↑m < n → ∀ (x : E), has_fderiv_at (fun (y : E) => p y m) (continuous_multilinear_map.curry_left (p x (Nat.succ m))) x
  cont : ∀ (m : ℕ), ↑m ≤ n → continuous fun (x : E) => p x m

theorem has_ftaylor_series_up_to.zero_eq' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to n f p) (x : E) : p x 0 = coe_fn (continuous_linear_equiv.symm (continuous_multilinear_curry_fin0 𝕜 E F)) (f x) := sorry

theorem has_ftaylor_series_up_to_on_univ_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} : has_ftaylor_series_up_to_on n f p set.univ ↔ has_ftaylor_series_up_to n f p := sorry

theorem has_ftaylor_series_up_to.has_ftaylor_series_up_to_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to n f p) (s : set E) : has_ftaylor_series_up_to_on n f p s :=
  has_ftaylor_series_up_to_on.mono (iff.mpr has_ftaylor_series_up_to_on_univ_iff h) (set.subset_univ s)

theorem has_ftaylor_series_up_to.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {m : with_top ℕ} {n : with_top ℕ} (h : has_ftaylor_series_up_to n f p) (hmn : m ≤ n) : has_ftaylor_series_up_to m f p := sorry

theorem has_ftaylor_series_up_to.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to n f p) : continuous f := sorry

theorem has_ftaylor_series_up_to_zero_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} : has_ftaylor_series_up_to 0 f p ↔ continuous f ∧ ∀ (x : E), continuous_multilinear_map.uncurry0 (p x 0) = f x := sorry

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem has_ftaylor_series_up_to.has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) (x : E) : has_fderiv_at f (coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p x 1)) x := sorry

theorem has_ftaylor_series_up_to.differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) : differentiable 𝕜 f :=
  fun (x : E) => has_fderiv_at.differentiable_at (has_ftaylor_series_up_to.has_fderiv_at h hn x)

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_succ_iff_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : ℕ} : has_ftaylor_series_up_to (↑(n + 1)) f p ↔
  (∀ (x : E), continuous_multilinear_map.uncurry0 (p x 0) = f x) ∧
    (∀ (x : E), has_fderiv_at (fun (y : E) => p y 0) (continuous_multilinear_map.curry_left (p x 1)) x) ∧
      has_ftaylor_series_up_to (↑n) (fun (x : E) => coe_fn (continuous_multilinear_curry_fin1 𝕜 E F) (p x 1))
        fun (x : E) => formal_multilinear_series.shift (p x) := sorry

/-! ### Smooth functions at a point -/

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def times_cont_diff_at (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : with_top ℕ) (f : E → F) (x : E) :=
  times_cont_diff_within_at 𝕜 n f set.univ x

theorem times_cont_diff_within_at_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : with_top ℕ} : times_cont_diff_within_at 𝕜 n f set.univ x ↔ times_cont_diff_at 𝕜 n f x :=
  iff.rfl

theorem times_cont_diff_at_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} : times_cont_diff_at 𝕜 ⊤ f x ↔ ∀ (n : ℕ), times_cont_diff_at 𝕜 (↑n) f x := sorry

theorem times_cont_diff_at.times_cont_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_at 𝕜 n f x) : times_cont_diff_within_at 𝕜 n f s x :=
  times_cont_diff_within_at.mono h (set.subset_univ s)

theorem times_cont_diff_within_at.times_cont_diff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜 n f s x) (hx : s ∈ nhds x) : times_cont_diff_at 𝕜 n f x := sorry

theorem times_cont_diff_at.congr_of_eventually_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {f₁ : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_at 𝕜 n f x) (hg : filter.eventually_eq (nhds x) f₁ f) : times_cont_diff_at 𝕜 n f₁ x :=
  times_cont_diff_within_at.congr_of_eventually_eq' h
    (eq.mpr (id (Eq._oldrec (Eq.refl (filter.eventually_eq (nhds_within x set.univ) f₁ f)) (nhds_within_univ x))) hg)
    (set.mem_univ x)

theorem times_cont_diff_at.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {m : with_top ℕ} {n : with_top ℕ} (h : times_cont_diff_at 𝕜 n f x) (hmn : m ≤ n) : times_cont_diff_at 𝕜 m f x :=
  times_cont_diff_within_at.of_le h hmn

theorem times_cont_diff_at.continuous_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_at 𝕜 n f x) : continuous_at f x :=
  eq.mpr (id (Eq.refl (continuous_at f x)))
    (eq.mp (propext (continuous_within_at_univ f x)) (times_cont_diff_within_at.continuous_within_at h))

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
theorem times_cont_diff_at.differentiable_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff_at 𝕜 n f x) (hn : 1 ≤ n) : differentiable_at 𝕜 f x := sorry

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_at_succ_iff_has_fderiv_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : ℕ} : times_cont_diff_at 𝕜 (↑(n + 1)) f x ↔
  ∃ (f' : E → continuous_linear_map 𝕜 E F),
    (∃ (u : set E), ∃ (H : u ∈ nhds x), ∀ (x : E), x ∈ u → has_fderiv_at f (f' x) x) ∧ times_cont_diff_at 𝕜 (↑n) f' x := sorry

/-! ### Smooth functions -/

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def times_cont_diff (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : with_top ℕ) (f : E → F) :=
  ∃ (p : E → formal_multilinear_series 𝕜 E F), has_ftaylor_series_up_to n f p

theorem times_cont_diff_on_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} : times_cont_diff_on 𝕜 n f set.univ ↔ times_cont_diff 𝕜 n f := sorry

theorem times_cont_diff_iff_times_cont_diff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} : times_cont_diff 𝕜 n f ↔ ∀ (x : E), times_cont_diff_at 𝕜 n f x := sorry

theorem times_cont_diff.times_cont_diff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) : times_cont_diff_at 𝕜 n f x :=
  iff.mp times_cont_diff_iff_times_cont_diff_at h x

theorem times_cont_diff.times_cont_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) : times_cont_diff_within_at 𝕜 n f s x :=
  times_cont_diff_at.times_cont_diff_within_at (times_cont_diff.times_cont_diff_at h)

theorem times_cont_diff_top {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} : times_cont_diff 𝕜 ⊤ f ↔ ∀ (n : ℕ), times_cont_diff 𝕜 (↑n) f := sorry

theorem times_cont_diff_all_iff_nat {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} : (∀ (n : with_top ℕ), times_cont_diff 𝕜 n f) ↔ ∀ (n : ℕ), times_cont_diff 𝕜 (↑n) f := sorry

theorem times_cont_diff.times_cont_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) : times_cont_diff_on 𝕜 n f s :=
  times_cont_diff_on.mono (iff.mpr times_cont_diff_on_univ h) (set.subset_univ s)

@[simp] theorem times_cont_diff_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} : times_cont_diff 𝕜 0 f ↔ continuous f := sorry

theorem times_cont_diff_at_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} : times_cont_diff_at 𝕜 0 f x ↔ ∃ (u : set E), ∃ (H : u ∈ nhds x), continuous_on f u := sorry

theorem times_cont_diff.of_le {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {m : with_top ℕ} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (hmn : m ≤ n) : times_cont_diff 𝕜 m f :=
  iff.mp times_cont_diff_on_univ (times_cont_diff_on.of_le (iff.mpr times_cont_diff_on_univ h) hmn)

theorem times_cont_diff.continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) : continuous f :=
  iff.mp times_cont_diff_zero (times_cont_diff.of_le h bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
theorem times_cont_diff.differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) : differentiable 𝕜 f :=
  iff.mp differentiable_on_univ (times_cont_diff_on.differentiable_on (iff.mpr times_cont_diff_on_univ h) hn)

/-! ### Iterated derivative -/

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
def iterated_fderiv (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (n : ℕ) (f : E → F) : E → continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F :=
  nat.rec_on n (fun (x : E) => continuous_multilinear_map.curry0 𝕜 E (f x))
    fun (n : ℕ) (rec : E → continuous_multilinear_map 𝕜 (fun (i : fin n) => E) F) (x : E) =>
      continuous_linear_map.uncurry_left (fderiv 𝕜 rec x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylor_series (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] (f : E → F) (x : E) : formal_multilinear_series 𝕜 E F :=
  fun (n : ℕ) => iterated_fderiv 𝕜 n f x

@[simp] theorem iterated_fderiv_zero_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} (m : fin 0 → E) : coe_fn (iterated_fderiv 𝕜 0 f x) m = f x :=
  rfl

theorem iterated_fderiv_zero_eq_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} : iterated_fderiv 𝕜 0 f = ⇑(continuous_linear_equiv.symm (continuous_multilinear_curry_fin0 𝕜 E F)) ∘ f :=
  rfl

theorem iterated_fderiv_succ_apply_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : ℕ} (m : fin (n + 1) → E) : coe_fn (iterated_fderiv 𝕜 (n + 1) f x) m = coe_fn (coe_fn (fderiv 𝕜 (iterated_fderiv 𝕜 n f) x) (m 0)) (fin.tail m) :=
  rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iterated_fderiv_succ_eq_comp_left {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : ℕ} : iterated_fderiv 𝕜 (n + 1) f =
  ⇑(continuous_multilinear_curry_left_equiv 𝕜 (fun (i : fin (n + 1)) => E) F) ∘ fderiv 𝕜 (iterated_fderiv 𝕜 n f) :=
  rfl

theorem iterated_fderiv_within_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : ℕ} : iterated_fderiv_within 𝕜 n f set.univ = iterated_fderiv 𝕜 n f := sorry

theorem ftaylor_series_within_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} : ftaylor_series_within 𝕜 f set.univ = ftaylor_series 𝕜 f := sorry

theorem iterated_fderiv_succ_apply_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : ℕ} (m : fin (n + 1) → E) : coe_fn (iterated_fderiv 𝕜 (n + 1) f x) m =
  coe_fn (coe_fn (iterated_fderiv 𝕜 n (fun (y : E) => fderiv 𝕜 f y) x) (fin.init m)) (m (fin.last n)) := sorry

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iterated_fderiv_succ_eq_comp_right {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {n : ℕ} : iterated_fderiv 𝕜 (n + 1) f x =
  function.comp (⇑(continuous_multilinear_curry_right_equiv' 𝕜 n E F)) (iterated_fderiv 𝕜 n fun (y : E) => fderiv 𝕜 f y)
    x := sorry

@[simp] theorem iterated_fderiv_one_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} (m : fin 1 → E) : coe_fn (iterated_fderiv 𝕜 1 f x) m = coe_fn (fderiv 𝕜 f x) (m 0) := sorry

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on_iff_ftaylor_series {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} : times_cont_diff 𝕜 n f ↔ has_ftaylor_series_up_to n f (ftaylor_series 𝕜 f) := sorry

theorem times_cont_diff_iff_continuous_differentiable {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} : times_cont_diff 𝕜 n f ↔
  (∀ (m : ℕ), ↑m ≤ n → continuous fun (x : E) => iterated_fderiv 𝕜 m f x) ∧
    ∀ (m : ℕ), ↑m < n → differentiable 𝕜 fun (x : E) => iterated_fderiv 𝕜 m f x := sorry

theorem times_cont_diff_of_differentiable_iterated_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} (h : ∀ (m : ℕ), ↑m ≤ n → differentiable 𝕜 (iterated_fderiv 𝕜 m f)) : times_cont_diff 𝕜 n f :=
  iff.mpr times_cont_diff_iff_continuous_differentiable
    { left := fun (m : ℕ) (hm : ↑m ≤ n) => differentiable.continuous (h m hm),
      right := fun (m : ℕ) (hm : ↑m < n) => h m (le_of_lt hm) }

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : ℕ} : times_cont_diff 𝕜 (↑(n + 1)) f ↔ differentiable 𝕜 f ∧ times_cont_diff 𝕜 ↑n fun (y : E) => fderiv 𝕜 f y := sorry

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^∞`. -/
theorem times_cont_diff_top_iff_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} : times_cont_diff 𝕜 ⊤ f ↔ differentiable 𝕜 f ∧ times_cont_diff 𝕜 ⊤ fun (y : E) => fderiv 𝕜 f y := sorry

theorem times_cont_diff.continuous_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) : continuous fun (x : E) => fderiv 𝕜 f x :=
  times_cont_diff.continuous (and.right (iff.mp times_cont_diff_succ_iff_fderiv (times_cont_diff.of_le h hn)))

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem times_cont_diff.continuous_fderiv_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) : continuous fun (p : E × E) => coe_fn (fderiv 𝕜 f (prod.fst p)) (prod.snd p) :=
  continuous.comp (is_bounded_bilinear_map.continuous is_bounded_bilinear_map_apply)
    (continuous.prod_mk (continuous.comp (times_cont_diff.continuous_fderiv h hn) continuous_fst) continuous_snd)

/-! ### Constants -/

theorem iterated_fderiv_within_zero_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : ℕ} : (iterated_fderiv 𝕜 n fun (x : E) => 0) = 0 := sorry

theorem times_cont_diff_zero_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} : times_cont_diff 𝕜 n fun (x : E) => 0 := sorry

/--
Constants are `C^∞`.
-/
theorem times_cont_diff_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {c : F} : times_cont_diff 𝕜 n fun (x : E) => c := sorry

theorem times_cont_diff_on_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {c : F} {s : set E} : times_cont_diff_on 𝕜 n (fun (x : E) => c) s :=
  times_cont_diff.times_cont_diff_on times_cont_diff_const

theorem times_cont_diff_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {c : F} : times_cont_diff_at 𝕜 n (fun (x : E) => c) x :=
  times_cont_diff.times_cont_diff_at times_cont_diff_const

theorem times_cont_diff_within_at_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {x : E} {n : with_top ℕ} {c : F} : times_cont_diff_within_at 𝕜 n (fun (x : E) => c) s x :=
  times_cont_diff_at.times_cont_diff_within_at times_cont_diff_at_const

theorem times_cont_diff_of_subsingleton {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} [subsingleton F] {n : with_top ℕ} : times_cont_diff 𝕜 n f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (times_cont_diff 𝕜 n f)) (subsingleton.elim f fun (_x : E) => 0))) times_cont_diff_const

theorem times_cont_diff_at_of_subsingleton {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} [subsingleton F] {n : with_top ℕ} : times_cont_diff_at 𝕜 n f x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (times_cont_diff_at 𝕜 n f x)) (subsingleton.elim f fun (_x : E) => 0)))
    times_cont_diff_at_const

theorem times_cont_diff_within_at_of_subsingleton {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} [subsingleton F] {n : with_top ℕ} : times_cont_diff_within_at 𝕜 n f s x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (times_cont_diff_within_at 𝕜 n f s x)) (subsingleton.elim f fun (_x : E) => 0)))
    times_cont_diff_within_at_const

theorem times_cont_diff_on_of_subsingleton {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} [subsingleton F] {n : with_top ℕ} : times_cont_diff_on 𝕜 n f s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (times_cont_diff_on 𝕜 n f s)) (subsingleton.elim f fun (_x : E) => 0)))
    times_cont_diff_on_const

/-! ### Linear functions -/

/--
Unbundled bounded linear functions are `C^∞`.
-/
theorem is_bounded_linear_map.times_cont_diff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {n : with_top ℕ} (hf : is_bounded_linear_map 𝕜 f) : times_cont_diff 𝕜 n f := sorry

theorem continuous_linear_map.times_cont_diff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} (f : continuous_linear_map 𝕜 E F) : times_cont_diff 𝕜 n ⇑f :=
  is_bounded_linear_map.times_cont_diff (continuous_linear_map.is_bounded_linear_map f)

/--
The first projection in a product is `C^∞`.
-/
theorem times_cont_diff_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} : times_cont_diff 𝕜 n prod.fst :=
  is_bounded_linear_map.times_cont_diff is_bounded_linear_map.fst

/--
The first projection on a domain in a product is `C^∞`.
-/
theorem times_cont_diff_on_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set (E × F)} {n : with_top ℕ} : times_cont_diff_on 𝕜 n prod.fst s :=
  times_cont_diff.times_cont_diff_on times_cont_diff_fst

/--
The first projection at a point in a product is `C^∞`.
-/
theorem times_cont_diff_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {p : E × F} {n : with_top ℕ} : times_cont_diff_at 𝕜 n prod.fst p :=
  times_cont_diff.times_cont_diff_at times_cont_diff_fst

/--
The first projection within a domain at a point in a product is `C^∞`.
-/
theorem times_cont_diff_within_at_fst {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set (E × F)} {p : E × F} {n : with_top ℕ} : times_cont_diff_within_at 𝕜 n prod.fst s p :=
  times_cont_diff.times_cont_diff_within_at times_cont_diff_fst

/--
The second projection in a product is `C^∞`.
-/
theorem times_cont_diff_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} : times_cont_diff 𝕜 n prod.snd :=
  is_bounded_linear_map.times_cont_diff is_bounded_linear_map.snd

/--
The second projection on a domain in a product is `C^∞`.
-/
theorem times_cont_diff_on_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set (E × F)} {n : with_top ℕ} : times_cont_diff_on 𝕜 n prod.snd s :=
  times_cont_diff.times_cont_diff_on times_cont_diff_snd

/--
The second projection at a point in a product is `C^∞`.
-/
theorem times_cont_diff_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {p : E × F} {n : with_top ℕ} : times_cont_diff_at 𝕜 n prod.snd p :=
  times_cont_diff.times_cont_diff_at times_cont_diff_snd

/--
The second projection within a domain at a point in a product is `C^∞`.
-/
theorem times_cont_diff_within_at_snd {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set (E × F)} {p : E × F} {n : with_top ℕ} : times_cont_diff_within_at 𝕜 n prod.snd s p :=
  times_cont_diff.times_cont_diff_within_at times_cont_diff_snd

/--
The identity is `C^∞`.
-/
theorem times_cont_diff_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} : times_cont_diff 𝕜 n id :=
  is_bounded_linear_map.times_cont_diff is_bounded_linear_map.id

theorem times_cont_diff_within_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} {s : set E} {x : E} : times_cont_diff_within_at 𝕜 n id s x :=
  times_cont_diff.times_cont_diff_within_at times_cont_diff_id

theorem times_cont_diff_at_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} {x : E} : times_cont_diff_at 𝕜 n id x :=
  times_cont_diff.times_cont_diff_at times_cont_diff_id

theorem times_cont_diff_on_id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} {s : set E} : times_cont_diff_on 𝕜 n id s :=
  times_cont_diff.times_cont_diff_on times_cont_diff_id

/--
Bilinear functions are `C^∞`.
-/
theorem is_bounded_bilinear_map.times_cont_diff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {b : E × F → G} {n : with_top ℕ} (hb : is_bounded_bilinear_map 𝕜 b) : times_cont_diff 𝕜 n b := sorry

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
theorem has_ftaylor_series_up_to_on.continuous_linear_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (g : continuous_linear_map 𝕜 F G) (hf : has_ftaylor_series_up_to_on n f p s) : has_ftaylor_series_up_to_on n (⇑g ∘ f)
  (fun (x : E) (k : ℕ) => continuous_linear_map.comp_continuous_multilinear_map g (p x k)) s := sorry

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem times_cont_diff_within_at.continuous_linear_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (g : continuous_linear_map 𝕜 F G) (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_diff_within_at 𝕜 n (⇑g ∘ f) s x := sorry

/-- Composition by continuous linear maps on the left preserves `C^n` functions in a domain
at a point. -/
theorem times_cont_diff_at.continuous_linear_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} {x : E} {n : with_top ℕ} (g : continuous_linear_map 𝕜 F G) (hf : times_cont_diff_at 𝕜 n f x) : times_cont_diff_at 𝕜 n (⇑g ∘ f) x :=
  times_cont_diff_within_at.continuous_linear_map_comp g hf

/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
theorem times_cont_diff_on.continuous_linear_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {n : with_top ℕ} (g : continuous_linear_map 𝕜 F G) (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (⇑g ∘ f) s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.continuous_linear_map_comp g (hf x hx)

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
theorem times_cont_diff.continuous_linear_map_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {f : E → F} (g : continuous_linear_map 𝕜 F G) (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n fun (x : E) => coe_fn g (f x) :=
  iff.mp times_cont_diff_on_univ (times_cont_diff_on.continuous_linear_map_comp g (iff.mpr times_cont_diff_on_univ hf))

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem continuous_linear_equiv.comp_times_cont_diff_within_at_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (e : continuous_linear_equiv 𝕜 F G) : times_cont_diff_within_at 𝕜 n (⇑e ∘ f) s x ↔ times_cont_diff_within_at 𝕜 n f s x := sorry

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
theorem continuous_linear_equiv.comp_times_cont_diff_on_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {n : with_top ℕ} (e : continuous_linear_equiv 𝕜 F G) : times_cont_diff_on 𝕜 n (⇑e ∘ f) s ↔ times_cont_diff_on 𝕜 n f s := sorry

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
theorem has_ftaylor_series_up_to_on.comp_continuous_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (hf : has_ftaylor_series_up_to_on n f p s) (g : continuous_linear_map 𝕜 G E) : has_ftaylor_series_up_to_on n (f ∘ ⇑g)
  (fun (x : G) (k : ℕ) =>
    continuous_multilinear_map.comp_continuous_linear_map (p (coe_fn g x) k) fun (_x : fin k) => g)
  (⇑g ⁻¹' s) := sorry

/-- Composition by continuous linear maps on the right preserves `C^n` functions at a point on
a domain. -/
theorem times_cont_diff_within_at.comp_continuous_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {n : with_top ℕ} {x : G} (g : continuous_linear_map 𝕜 G E) (hf : times_cont_diff_within_at 𝕜 n f s (coe_fn g x)) : times_cont_diff_within_at 𝕜 n (f ∘ ⇑g) (⇑g ⁻¹' s) x := sorry

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
theorem times_cont_diff_on.comp_continuous_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {n : with_top ℕ} (hf : times_cont_diff_on 𝕜 n f s) (g : continuous_linear_map 𝕜 G E) : times_cont_diff_on 𝕜 n (f ∘ ⇑g) (⇑g ⁻¹' s) :=
  fun (x : G) (hx : x ∈ ⇑g ⁻¹' s) => times_cont_diff_within_at.comp_continuous_linear_map g (hf (coe_fn g x) hx)

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
theorem times_cont_diff.comp_continuous_linear_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {f : E → F} {g : continuous_linear_map 𝕜 G E} (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n (f ∘ ⇑g) :=
  iff.mp times_cont_diff_on_univ (times_cont_diff_on.comp_continuous_linear_map (iff.mpr times_cont_diff_on_univ hf) g)

/-- Composition by continuous linear equivs on the right respects higher differentiability at a
point in a domain. -/
theorem continuous_linear_equiv.times_cont_diff_within_at_comp_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {x : E} {n : with_top ℕ} (e : continuous_linear_equiv 𝕜 G E) : times_cont_diff_within_at 𝕜 n (f ∘ ⇑e) (⇑e ⁻¹' s) (coe_fn (continuous_linear_equiv.symm e) x) ↔
  times_cont_diff_within_at 𝕜 n f s x := sorry

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
theorem continuous_linear_equiv.times_cont_diff_on_comp_iff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {n : with_top ℕ} (e : continuous_linear_equiv 𝕜 G E) : times_cont_diff_on 𝕜 n (f ∘ ⇑e) (⇑e ⁻¹' s) ↔ times_cont_diff_on 𝕜 n f s := sorry

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
theorem has_ftaylor_series_up_to_on.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ} (hf : has_ftaylor_series_up_to_on n f p s) {g : E → G} {q : E → formal_multilinear_series 𝕜 E G} (hg : has_ftaylor_series_up_to_on n g q s) : has_ftaylor_series_up_to_on n (fun (y : E) => (f y, g y))
  (fun (y : E) (k : ℕ) => continuous_multilinear_map.prod (p y k) (q y k)) s := sorry

/-- The cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
theorem times_cont_diff_within_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {n : with_top ℕ} {s : set E} {f : E → F} {g : E → G} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => (f x, g x)) s x := sorry

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
theorem times_cont_diff_on.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {s : set E} {f : E → F} {g : E → G} (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) : times_cont_diff_on 𝕜 n (fun (x : E) => (f x, g x)) s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.prod (hf x hx) (hg x hx)

/-- The cartesian product of `C^n` functions at a point is `C^n`. -/
theorem times_cont_diff_at.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {x : E} {n : with_top ℕ} {f : E → F} {g : E → G} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) : times_cont_diff_at 𝕜 n (fun (x : E) => (f x, g x)) x :=
  iff.mp times_cont_diff_within_at_univ
    (times_cont_diff_within_at.prod (iff.mpr times_cont_diff_within_at_univ hf)
      (iff.mpr times_cont_diff_within_at_univ hg))

/--
The cartesian product of `C^n` functions is `C^n`.
-/
theorem times_cont_diff.prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {f : E → F} {g : E → G} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n fun (x : E) => (f x, g x) :=
  iff.mp times_cont_diff_on_univ
    (times_cont_diff_on.prod (iff.mpr times_cont_diff_on_univ hf) (iff.mpr times_cont_diff_on_univ hg))

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe. We use the trick that any space `H` is isomorphic through a continuous linear
equiv to `continuous_multilinear_map (λ (i : fin 0), E × F × G) H` to change the universe level,
and then argue that composing with such a linear equiv does not change the fact of being `C^n`,
which we have already proved previously.
-/

/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `times_cont_diff_on.comp` which removes the universe
assumption (but is deduced from this one). -/
/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem times_cont_diff_on.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F} (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) : times_cont_diff_on 𝕜 n (g ∘ f) s := sorry

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem times_cont_diff_on.comp' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F} (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) :=
  times_cont_diff_on.comp hg (times_cont_diff_on.mono hf (set.inter_subset_left s (f ⁻¹' t)))
    (set.inter_subset_right s (f ⁻¹' t))

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
theorem times_cont_diff.comp_times_cont_diff_on {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {s : set E} {g : F → G} {f : E → F} (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (g ∘ f) s :=
  times_cont_diff_on.comp (iff.mpr times_cont_diff_on_univ hg) hf set.subset_preimage_univ

/-- The composition of `C^n` functions is `C^n`. -/
theorem times_cont_diff.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {g : F → G} {f : E → F} (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n (g ∘ f) :=
  iff.mp times_cont_diff_on_univ
    (times_cont_diff_on.comp (iff.mpr times_cont_diff_on_univ hg) (iff.mpr times_cont_diff_on_univ hf)
      (set.subset_univ set.univ))

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem times_cont_diff_within_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E) (hg : times_cont_diff_within_at 𝕜 n g t (f x)) (hf : times_cont_diff_within_at 𝕜 n f s x) (st : s ⊆ f ⁻¹' t) : times_cont_diff_within_at 𝕜 n (g ∘ f) s x := sorry

/-- The composition of `C^n` functions at points in domains is `C^n`. -/
theorem times_cont_diff_within_at.comp' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F} (x : E) (hg : times_cont_diff_within_at 𝕜 n g t (f x)) (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_diff_within_at 𝕜 n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  times_cont_diff_within_at.comp x hg (times_cont_diff_within_at.mono hf (set.inter_subset_left s (f ⁻¹' t)))
    (set.inter_subset_right s (f ⁻¹' t))

theorem times_cont_diff_at.comp_times_cont_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {s : set E} {f : E → F} {g : F → G} {n : with_top ℕ} (x : E) (hg : times_cont_diff_at 𝕜 n g (f x)) (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_diff_within_at 𝕜 n (g ∘ f) s x :=
  times_cont_diff_within_at.comp x hg hf (set.maps_to_univ (fun (a : E) => a) s)

/-- The composition of `C^n` functions at points is `C^n`. -/
theorem times_cont_diff_at.comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {f : E → F} {g : F → G} {n : with_top ℕ} (x : E) (hg : times_cont_diff_at 𝕜 n g (f x)) (hf : times_cont_diff_at 𝕜 n f x) : times_cont_diff_at 𝕜 n (g ∘ f) x :=
  times_cont_diff_within_at.comp x hg hf set.subset_preimage_univ

theorem times_cont_diff.comp_times_cont_diff_within_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {t : set E} {x : E} {n : with_top ℕ} {g : F → G} {f : E → F} (h : times_cont_diff 𝕜 n g) (hf : times_cont_diff_within_at 𝕜 n f t x) : times_cont_diff_within_at 𝕜 n (g ∘ f) t x :=
  times_cont_diff_within_at.comp x (times_cont_diff_at.times_cont_diff_within_at (times_cont_diff.times_cont_diff_at h))
    hf (set.subset_univ t)

theorem times_cont_diff.comp_times_cont_diff_at {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {G : Type u_4} [normed_group G] [normed_space 𝕜 G] {n : with_top ℕ} {g : F → G} {f : E → F} (x : E) (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff_at 𝕜 n f x) : times_cont_diff_at 𝕜 n (g ∘ f) x :=
  times_cont_diff.comp_times_cont_diff_within_at hg hf

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem times_cont_diff_on_fderiv_within_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {m : with_top ℕ} {n : with_top ℕ} {s : set E} {f : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) : times_cont_diff_on 𝕜 m (fun (p : E × E) => coe_fn (fderiv_within 𝕜 f s (prod.fst p)) (prod.snd p)) (set.prod s set.univ) := sorry

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
theorem times_cont_diff.times_cont_diff_fderiv_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {m : with_top ℕ} {f : E → F} (hf : times_cont_diff 𝕜 n f) (hmn : m + 1 ≤ n) : times_cont_diff 𝕜 m fun (p : E × E) => coe_fn (fderiv 𝕜 f (prod.fst p)) (prod.snd p) := sorry

/-! ### Sum of two functions -/

/- The sum is smooth. -/

theorem times_cont_diff_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} : times_cont_diff 𝕜 n fun (p : F × F) => prod.fst p + prod.snd p :=
  is_bounded_linear_map.times_cont_diff (is_bounded_linear_map.add is_bounded_linear_map.fst is_bounded_linear_map.snd)

/-- The sum of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem times_cont_diff_within_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {s : set E} {f : E → F} {g : E → F} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x + g x) s x :=
  times_cont_diff_within_at.comp x (times_cont_diff.times_cont_diff_within_at times_cont_diff_add)
    (times_cont_diff_within_at.prod hf hg) set.subset_preimage_univ

/-- The sum of two `C^n` functions at a point is `C^n` at this point. -/
theorem times_cont_diff_at.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {f : E → F} {g : E → F} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) : times_cont_diff_at 𝕜 n (fun (x : E) => f x + g x) x := sorry

/-- The sum of two `C^n`functions is `C^n`. -/
theorem times_cont_diff.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {f : E → F} {g : E → F} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n fun (x : E) => f x + g x :=
  times_cont_diff.comp times_cont_diff_add (times_cont_diff.prod hf hg)

/-- The sum of two `C^n` functions on a domain is `C^n`. -/
theorem times_cont_diff_on.add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {s : set E} {f : E → F} {g : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) : times_cont_diff_on 𝕜 n (fun (x : E) => f x + g x) s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.add (hf x hx) (hg x hx)

/-! ### Negative -/

/- The negative is smooth. -/

theorem times_cont_diff_neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} : times_cont_diff 𝕜 n fun (p : F) => -p :=
  is_bounded_linear_map.times_cont_diff (is_bounded_linear_map.neg is_bounded_linear_map.id)

/-- The negative of a `C^n` function within a domain at a point is `C^n` within this domain at
this point. -/
theorem times_cont_diff_within_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {s : set E} {f : E → F} (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => -f x) s x :=
  times_cont_diff_within_at.comp x (times_cont_diff.times_cont_diff_within_at times_cont_diff_neg) hf
    set.subset_preimage_univ

/-- The negative of a `C^n` function at a point is `C^n` at this point. -/
theorem times_cont_diff_at.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {f : E → F} (hf : times_cont_diff_at 𝕜 n f x) : times_cont_diff_at 𝕜 n (fun (x : E) => -f x) x := sorry

/-- The negative of a `C^n`function is `C^n`. -/
theorem times_cont_diff.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {f : E → F} (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n fun (x : E) => -f x :=
  times_cont_diff.comp times_cont_diff_neg hf

/-- The negative of a `C^n` function on a domain is `C^n`. -/
theorem times_cont_diff_on.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {s : set E} {f : E → F} (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (fun (x : E) => -f x) s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.neg (hf x hx)

/-! ### Subtraction -/

/-- The difference of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem times_cont_diff_within_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {s : set E} {f : E → F} {g : E → F} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x - g x) s x := sorry

/-- The difference of two `C^n` functions at a point is `C^n` at this point. -/
theorem times_cont_diff_at.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {f : E → F} {g : E → F} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) : times_cont_diff_at 𝕜 n (fun (x : E) => f x - g x) x := sorry

/-- The difference of two `C^n` functions on a domain is `C^n`. -/
theorem times_cont_diff_on.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {s : set E} {f : E → F} {g : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) : times_cont_diff_on 𝕜 n (fun (x : E) => f x - g x) s := sorry

/-- The difference of two `C^n` functions is `C^n`. -/
theorem times_cont_diff.sub {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {f : E → F} {g : E → F} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n fun (x : E) => f x - g x := sorry

/-! ### Sum of finitely many functions -/

theorem times_cont_diff_within_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {ι : Type u_4} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {t : set E} {x : E} (h : ∀ (i : ι), i ∈ s → times_cont_diff_within_at 𝕜 n (fun (x : E) => f i x) t x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => finset.sum s fun (i : ι) => f i x) t x := sorry

theorem times_cont_diff_at.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {ι : Type u_4} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {x : E} (h : ∀ (i : ι), i ∈ s → times_cont_diff_at 𝕜 n (fun (x : E) => f i x) x) : times_cont_diff_at 𝕜 n (fun (x : E) => finset.sum s fun (i : ι) => f i x) x := sorry

theorem times_cont_diff_on.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {ι : Type u_4} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} {t : set E} (h : ∀ (i : ι), i ∈ s → times_cont_diff_on 𝕜 n (fun (x : E) => f i x) t) : times_cont_diff_on 𝕜 n (fun (x : E) => finset.sum s fun (i : ι) => f i x) t :=
  fun (x : E) (hx : x ∈ t) => times_cont_diff_within_at.sum fun (i : ι) (hi : i ∈ s) => h i hi x hx

theorem times_cont_diff.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {ι : Type u_4} {f : ι → E → F} {s : finset ι} {n : with_top ℕ} (h : ∀ (i : ι), i ∈ s → times_cont_diff 𝕜 n fun (x : E) => f i x) : times_cont_diff 𝕜 n fun (x : E) => finset.sum s fun (i : ι) => f i x := sorry

/-! ### Product of two functions -/

/- The product is smooth. -/

theorem times_cont_diff_mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {n : with_top ℕ} : times_cont_diff 𝕜 n fun (p : 𝕜 × 𝕜) => prod.fst p * prod.snd p :=
  is_bounded_bilinear_map.times_cont_diff is_bounded_bilinear_map_mul

/-- The product of two `C^n` functions within a set at a point is `C^n` within this set
at this point. -/
theorem times_cont_diff_within_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {n : with_top ℕ} {s : set E} {f : E → 𝕜} {g : E → 𝕜} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x * g x) s x :=
  times_cont_diff_within_at.comp x (times_cont_diff.times_cont_diff_within_at times_cont_diff_mul)
    (times_cont_diff_within_at.prod hf hg) set.subset_preimage_univ

/-- The product of two `C^n` functions at a point is `C^n` at this point. -/
theorem times_cont_diff_at.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {n : with_top ℕ} {f : E → 𝕜} {g : E → 𝕜} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) : times_cont_diff_at 𝕜 n (fun (x : E) => f x * g x) x := sorry

/-- The product of two `C^n` functions on a domain is `C^n`. -/
theorem times_cont_diff_on.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} {s : set E} {f : E → 𝕜} {g : E → 𝕜} (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) : times_cont_diff_on 𝕜 n (fun (x : E) => f x * g x) s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.mul (hf x hx) (hg x hx)

/-- The product of two `C^n`functions is `C^n`. -/
theorem times_cont_diff.mul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} {f : E → 𝕜} {g : E → 𝕜} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n fun (x : E) => f x * g x :=
  times_cont_diff.comp times_cont_diff_mul (times_cont_diff.prod hf hg)

theorem times_cont_diff_within_at.div_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {x : E} {f : E → 𝕜} {n : with_top ℕ} {c : 𝕜} (hf : times_cont_diff_within_at 𝕜 n f s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x / c) s x :=
  times_cont_diff_within_at.mul hf times_cont_diff_within_at_const

theorem times_cont_diff_at.div_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {f : E → 𝕜} {n : with_top ℕ} {c : 𝕜} (hf : times_cont_diff_at 𝕜 n f x) : times_cont_diff_at 𝕜 n (fun (x : E) => f x / c) x :=
  times_cont_diff_at.mul hf times_cont_diff_at_const

theorem times_cont_diff_on.div_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {f : E → 𝕜} {n : with_top ℕ} {c : 𝕜} (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (fun (x : E) => f x / c) s :=
  times_cont_diff_on.mul hf times_cont_diff_on_const

theorem times_cont_diff.div_const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {f : E → 𝕜} {n : with_top ℕ} {c : 𝕜} (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n fun (x : E) => f x / c :=
  times_cont_diff.mul hf times_cont_diff_const

theorem times_cont_diff.pow {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {n : with_top ℕ} {f : E → 𝕜} (hf : times_cont_diff 𝕜 n f) (m : ℕ) : times_cont_diff 𝕜 n fun (x : E) => f x ^ m := sorry

/-! ### Scalar multiplication -/

/- The scalar multiplication is smooth. -/

theorem times_cont_diff_smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} : times_cont_diff 𝕜 n fun (p : 𝕜 × F) => prod.fst p • prod.snd p :=
  is_bounded_bilinear_map.times_cont_diff is_bounded_bilinear_map_smul

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
theorem times_cont_diff_within_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {s : set E} {f : E → 𝕜} {g : E → F} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x • g x) s x :=
  times_cont_diff_within_at.comp x (times_cont_diff.times_cont_diff_within_at times_cont_diff_smul)
    (times_cont_diff_within_at.prod hf hg) set.subset_preimage_univ

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
theorem times_cont_diff_at.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {x : E} {n : with_top ℕ} {f : E → 𝕜} {g : E → F} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) : times_cont_diff_at 𝕜 n (fun (x : E) => f x • g x) x := sorry

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
theorem times_cont_diff.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {f : E → 𝕜} {g : E → F} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n fun (x : E) => f x • g x :=
  times_cont_diff.comp times_cont_diff_smul (times_cont_diff.prod hf hg)

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n`. -/
theorem times_cont_diff_on.smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {n : with_top ℕ} {s : set E} {f : E → 𝕜} {g : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) : times_cont_diff_on 𝕜 n (fun (x : E) => f x • g x) s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.smul (hf x hx) (hg x hx)

/-! ### Cartesian product of two functions-/

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem times_cont_diff_within_at.prod_map' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] {n : with_top ℕ} {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {p : E × E'} (hf : times_cont_diff_within_at 𝕜 n f s (prod.fst p)) (hg : times_cont_diff_within_at 𝕜 n g t (prod.snd p)) : times_cont_diff_within_at 𝕜 n (prod.map f g) (set.prod s t) p :=
  times_cont_diff_within_at.prod
    (times_cont_diff_within_at.comp p hf times_cont_diff_within_at_fst (set.prod_subset_preimage_fst s t))
    (times_cont_diff_within_at.comp p hg times_cont_diff_within_at_snd (set.prod_subset_preimage_snd s t))

theorem times_cont_diff_within_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] {n : with_top ℕ} {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g t y) : times_cont_diff_within_at 𝕜 n (prod.map f g) (set.prod s t) (x, y) :=
  times_cont_diff_within_at.prod_map' hf hg

/-- The product map of two `C^n` functions on a set is `C^n` on the product set. -/
theorem times_cont_diff_on.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {E' : Type u_4} [normed_group E'] [normed_space 𝕜 E'] {F' : Type u_5} [normed_group F'] [normed_space 𝕜 F'] {s : set E} {t : set E'} {n : with_top ℕ} {f : E → F} {g : E' → F'} (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g t) : times_cont_diff_on 𝕜 n (prod.map f g) (set.prod s t) :=
  times_cont_diff_on.prod (times_cont_diff_on.comp hf times_cont_diff_on_fst (set.prod_subset_preimage_fst s t))
    (times_cont_diff_on.comp hg times_cont_diff_on_snd (set.prod_subset_preimage_snd s t))

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem times_cont_diff_at.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] {n : with_top ℕ} {f : E → F} {g : E' → F'} {x : E} {y : E'} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g y) : times_cont_diff_at 𝕜 n (prod.map f g) (x, y) := sorry

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem times_cont_diff_at.prod_map' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] {n : with_top ℕ} {f : E → F} {g : E' → F'} {p : E × E'} (hf : times_cont_diff_at 𝕜 n f (prod.fst p)) (hg : times_cont_diff_at 𝕜 n g (prod.snd p)) : times_cont_diff_at 𝕜 n (prod.map f g) p := sorry

/-- The product map of two `C^n` functions is `C^n`. -/
theorem times_cont_diff.prod_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {F' : Type u_6} [normed_group F'] [normed_space 𝕜 F'] {n : with_top ℕ} {f : E → F} {g : E' → F'} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n (prod.map f g) := sorry

/-! ### Inversion in a complete normed algebra -/

/-- In a complete normed algebra, the operation of inversion is `C^n`, for all `n`, at each
invertible element.  The proof is by induction, bootstrapping using an identity expressing the
derivative of inversion as a bilinear map of inversion itself. -/
theorem times_cont_diff_at_ring_inverse (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {R : Type u_5} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R] {n : with_top ℕ} (x : units R) : times_cont_diff_at 𝕜 n ring.inverse ↑x := sorry

theorem times_cont_diff_at_inv (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {𝕜' : Type u_6} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [complete_space 𝕜'] {x : 𝕜'} (hx : x ≠ 0) {n : with_top ℕ} : times_cont_diff_at 𝕜 n has_inv.inv x := sorry

theorem times_cont_diff_on_inv (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {𝕜' : Type u_6} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [complete_space 𝕜'] {n : with_top ℕ} : times_cont_diff_on 𝕜 n has_inv.inv (singleton 0ᶜ) :=
  fun (x : 𝕜') (hx : x ∈ (singleton 0ᶜ)) => times_cont_diff_at.times_cont_diff_within_at (times_cont_diff_at_inv 𝕜 hx)

-- TODO: the next few lemmas don't need `𝕜` or `𝕜'` to be complete

-- A good way to show this is to generalize `times_cont_diff_at_ring_inverse` to the setting

-- of a function `f` such that `∀ᶠ x in 𝓝 a, x * f x = 1`.

theorem times_cont_diff_within_at.inv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {x : E} {𝕜' : Type u_6} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [complete_space 𝕜'] {f : E → 𝕜'} {n : with_top ℕ} (hf : times_cont_diff_within_at 𝕜 n f s x) (hx : f x ≠ 0) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x⁻¹) s x :=
  times_cont_diff_at.comp_times_cont_diff_within_at x (times_cont_diff_at_inv 𝕜 hx) hf

theorem times_cont_diff_at.inv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} {𝕜' : Type u_6} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [complete_space 𝕜'] {f : E → 𝕜'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕜 n f x) (hx : f x ≠ 0) : times_cont_diff_at 𝕜 n (fun (x : E) => f x⁻¹) x :=
  times_cont_diff_within_at.inv hf hx

-- TODO: generalize to `f g : E → 𝕜'`

theorem times_cont_diff_within_at.div {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {s : set E} {x : E} [complete_space 𝕜] {f : E → 𝕜} {g : E → 𝕜} {n : with_top ℕ} (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g s x) (hx : g x ≠ 0) : times_cont_diff_within_at 𝕜 n (fun (x : E) => f x / g x) s x :=
  times_cont_diff_within_at.mul hf (times_cont_diff_within_at.inv hg hx)

theorem times_cont_diff_at.div {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {x : E} [complete_space 𝕜] {f : E → 𝕜} {g : E → 𝕜} {n : with_top ℕ} (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g x) (hx : g x ≠ 0) : times_cont_diff_at 𝕜 n (fun (x : E) => f x / g x) x :=
  times_cont_diff_within_at.div hf hg hx

theorem times_cont_diff.div {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] [complete_space 𝕜] {f : E → 𝕜} {g : E → 𝕜} {n : with_top ℕ} (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) (h0 : ∀ (x : E), g x ≠ 0) : times_cont_diff 𝕜 n fun (x : E) => f x / g x := sorry

/-! ### Inversion of continuous linear maps between Banach spaces -/

/-- At a continuous linear equivalence `e : E ≃L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem times_cont_diff_at_map_inverse {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space E] {n : with_top ℕ} (e : continuous_linear_equiv 𝕜 E F) : times_cont_diff_at 𝕜 n continuous_linear_map.inverse ↑e := sorry

/-- If `f` is a local homeomorphism and the point `a` is in its target, and if `f` is `n` times
continuously differentiable at `f.symm a`, and if the derivative at `f.symm a` is a continuous linear
equivalence, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.times_cont_diff_at_symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] [complete_space E] {n : with_top ℕ} (f : local_homeomorph E F) {f₀' : continuous_linear_equiv 𝕜 E F} {a : F} (ha : a ∈ local_equiv.target (local_homeomorph.to_local_equiv f)) (hf₀' : has_fderiv_at (⇑f) (↑f₀') (coe_fn (local_homeomorph.symm f) a)) (hf : times_cont_diff_at 𝕜 n (⇑f) (coe_fn (local_homeomorph.symm f) a)) : times_cont_diff_at 𝕜 n (⇑(local_homeomorph.symm f)) a := sorry

/-- Let `f` be a local homeomorphism of a nondiscrete normed field, let `a` be a point in its
target. if `f` is `n` times continuously differentiable at `f.symm a`, and if the derivative at
`f.symm a` is nonzero, then `f.symm` is `n` times continuously differentiable at the point `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem local_homeomorph.times_cont_diff_at_symm_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] [complete_space 𝕜] {n : with_top ℕ} (f : local_homeomorph 𝕜 𝕜) {f₀' : 𝕜} {a : 𝕜} (h₀ : f₀' ≠ 0) (ha : a ∈ local_equiv.target (local_homeomorph.to_local_equiv f)) (hf₀' : has_deriv_at (⇑f) f₀' (coe_fn (local_homeomorph.symm f) a)) (hf : times_cont_diff_at 𝕜 n (⇑f) (coe_fn (local_homeomorph.symm f) a)) : times_cont_diff_at 𝕜 n (⇑(local_homeomorph.symm f)) a :=
  local_homeomorph.times_cont_diff_at_symm f ha (has_deriv_at.has_fderiv_at_equiv hf₀' h₀) hf

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

/-- If a function has a Taylor series at order at least 1, then at points in the interior of the
    domain of definition, the term of order 1 of this series is a strict derivative of `f`. -/
theorem has_ftaylor_series_up_to_on.has_strict_fderiv_at {𝕂 : Type u_5} [is_R_or_C 𝕂] {E' : Type u_6} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_7} [normed_group F'] [normed_space 𝕂 F'] {s : set E'} {f : E' → F'} {x : E'} {p : E' → formal_multilinear_series 𝕂 E' F'} {n : with_top ℕ} (hf : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hs : s ∈ nhds x) : has_strict_fderiv_at f (coe_fn (continuous_multilinear_curry_fin1 𝕂 E' F') (p x 1)) x := sorry

/-- If a function is `C^n` with `1 ≤ n` around a point, then the derivative of `f` at this point
is also a strict derivative. -/
theorem times_cont_diff_at.has_strict_fderiv_at {𝕂 : Type u_5} [is_R_or_C 𝕂] {E' : Type u_6} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_7} [normed_group F'] [normed_space 𝕂 F'] {f : E' → F'} {x : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) : has_strict_fderiv_at f (fderiv 𝕂 f x) x := sorry

/-- If a function is `C^n` with `1 ≤ n` around a point, and its derivative at that point is given to
us as `f'`, then `f'` is also a strict derivative. -/
theorem times_cont_diff_at.has_strict_fderiv_at' {𝕂 : Type u_5} [is_R_or_C 𝕂] {E' : Type u_6} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_7} [normed_group F'] [normed_space 𝕂 F'] {f : E' → F'} {f' : continuous_linear_map 𝕂 E' F'} {x : E'} {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f x) (hf' : has_fderiv_at f f' x) (hn : 1 ≤ n) : has_strict_fderiv_at f f' x := sorry

/-- If a function is `C^n` with `1 ≤ n`, then the derivative of `f` is also a strict derivative. -/
theorem times_cont_diff.has_strict_fderiv_at {𝕂 : Type u_5} [is_R_or_C 𝕂] {E' : Type u_6} [normed_group E'] [normed_space 𝕂 E'] {F' : Type u_7} [normed_group F'] [normed_space 𝕂 F'] {f : E' → F'} {x : E'} {n : with_top ℕ} (hf : times_cont_diff 𝕂 n f) (hn : 1 ≤ n) : has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
  times_cont_diff_at.has_strict_fderiv_at (times_cont_diff.times_cont_diff_at hf) hn

/-!
### One dimension

All results up to now have been expressed in terms of the general Fréchet derivative `fderiv`. For
maps defined on the field, the one-dimensional derivative `deriv` is often easier to use. In this
paragraph, we reformulate some higher smoothness results in terms of `deriv`.
-/

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (formulated with `deriv_within`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} {n : ℕ} (hs : unique_diff_on 𝕜 s₂) : times_cont_diff_on 𝕜 (↑(n + 1)) f₂ s₂ ↔ differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 (↑n) (deriv_within f₂ s₂) s₂ := sorry

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (formulated with `deriv`) is `C^n`. -/
theorem times_cont_diff_on_succ_iff_deriv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} {n : ℕ} (hs : is_open s₂) : times_cont_diff_on 𝕜 (↑(n + 1)) f₂ s₂ ↔ differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 (↑n) (deriv f₂) s₂ := sorry

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (formulated with `deriv_within`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} (hs : unique_diff_on 𝕜 s₂) : times_cont_diff_on 𝕜 ⊤ f₂ s₂ ↔ differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 ⊤ (deriv_within f₂ s₂) s₂ := sorry

/-- A function is `C^∞` on an open domain if and only if it is differentiable
there, and its derivative (formulated with `deriv`) is `C^∞`. -/
theorem times_cont_diff_on_top_iff_deriv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} (hs : is_open s₂) : times_cont_diff_on 𝕜 ⊤ f₂ s₂ ↔ differentiable_on 𝕜 f₂ s₂ ∧ times_cont_diff_on 𝕜 ⊤ (deriv f₂) s₂ := sorry

theorem times_cont_diff_on.deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_diff_on 𝕜 n f₂ s₂) (hs : unique_diff_on 𝕜 s₂) (hmn : m + 1 ≤ n) : times_cont_diff_on 𝕜 m (deriv_within f₂ s₂) s₂ := sorry

theorem times_cont_diff_on.deriv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} {m : with_top ℕ} {n : with_top ℕ} (hf : times_cont_diff_on 𝕜 n f₂ s₂) (hs : is_open s₂) (hmn : m + 1 ≤ n) : times_cont_diff_on 𝕜 m (deriv f₂) s₂ :=
  times_cont_diff_on.congr (times_cont_diff_on.deriv_within hf (is_open.unique_diff_on hs) hmn)
    fun (x : 𝕜) (hx : x ∈ s₂) => Eq.symm (deriv_within_of_open hs hx)

theorem times_cont_diff_on.continuous_on_deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f₂ s₂) (hs : unique_diff_on 𝕜 s₂) (hn : 1 ≤ n) : continuous_on (deriv_within f₂ s₂) s₂ :=
  times_cont_diff_on.continuous_on
    (and.right (iff.mp (times_cont_diff_on_succ_iff_deriv_within hs) (times_cont_diff_on.of_le h hn)))

theorem times_cont_diff_on.continuous_on_deriv_of_open {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {s₂ : set 𝕜} {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f₂ s₂) (hs : is_open s₂) (hn : 1 ≤ n) : continuous_on (deriv f₂) s₂ :=
  times_cont_diff_on.continuous_on
    (and.right (iff.mp (times_cont_diff_on_succ_iff_deriv_of_open hs) (times_cont_diff_on.of_le h hn)))

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f₂ : 𝕜 → F} {n : ℕ} : times_cont_diff 𝕜 (↑(n + 1)) f₂ ↔ differentiable 𝕜 f₂ ∧ times_cont_diff 𝕜 (↑n) (deriv f₂) := sorry

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is `n` times continuously differentiable over `ℂ`, then it is `n` times continuously
differentiable over `ℝ`. In this paragraph, we give variants of this statement, in the general
situation where `ℂ` and `ℝ` are replaced respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra
over `𝕜`.
-/

theorem has_ftaylor_series_up_to_on.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {𝕜' : Type u_5} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {p' : E → formal_multilinear_series 𝕜' E F} {n : with_top ℕ} (h : has_ftaylor_series_up_to_on n f p' s) : has_ftaylor_series_up_to_on n f (fun (x : E) => formal_multilinear_series.restrict_scalars 𝕜 (p' x)) s := sorry

theorem times_cont_diff_within_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {x : E} {𝕜' : Type u_5} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {n : with_top ℕ} (h : times_cont_diff_within_at 𝕜' n f s x) : times_cont_diff_within_at 𝕜 n f s x := sorry

theorem times_cont_diff_on.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {s : set E} {f : E → F} {𝕜' : Type u_5} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {n : with_top ℕ} (h : times_cont_diff_on 𝕜' n f s) : times_cont_diff_on 𝕜 n f s :=
  fun (x : E) (hx : x ∈ s) => times_cont_diff_within_at.restrict_scalars 𝕜 (h x hx)

theorem times_cont_diff_at.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {x : E} {𝕜' : Type u_5} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {n : with_top ℕ} (h : times_cont_diff_at 𝕜' n f x) : times_cont_diff_at 𝕜 n f x :=
  iff.mp times_cont_diff_within_at_univ
    (times_cont_diff_within_at.restrict_scalars 𝕜 (times_cont_diff_at.times_cont_diff_within_at h))

theorem times_cont_diff.restrict_scalars (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_3} [normed_group F] [normed_space 𝕜 F] {f : E → F} {𝕜' : Type u_5} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] [normed_space 𝕜' E] [is_scalar_tower 𝕜 𝕜' E] [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {n : with_top ℕ} (h : times_cont_diff 𝕜' n f) : times_cont_diff 𝕜 n f :=
  iff.mpr times_cont_diff_iff_times_cont_diff_at
    fun (x : E) => times_cont_diff_at.restrict_scalars 𝕜 (times_cont_diff.times_cont_diff_at h)

