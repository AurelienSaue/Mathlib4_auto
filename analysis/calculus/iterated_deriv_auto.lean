/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.calculus.deriv
import Mathlib.analysis.calculus.times_cont_diff
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iterated_deriv n f : 𝕜 → F`, as well as a version on domains `iterated_deriv_within n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nondiscrete normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iterated_deriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iterated_deriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iterated_deriv_within n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iterated_deriv_within_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iterated_deriv n f` as the composition of
`iterated_fderiv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iterated_deriv_within_succ`,
by translating the corresponding result `iterated_fderiv_within_succ_apply_left` for the
iterated Fréchet derivative.
-/

/-- The `n`-th iterated derivative of a function from `𝕜` to `F`, as a function from `𝕜` to `F`. -/
def iterated_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
  coe_fn (iterated_fderiv 𝕜 n f x) fun (i : fin n) => 1

/-- The `n`-th iterated derivative of a function from `𝕜` to `F` within a set `s`, as a function
from `𝕜` to `F`. -/
def iterated_deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] (n : ℕ) (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) : F :=
  coe_fn (iterated_fderiv_within 𝕜 n f s x) fun (i : fin n) => 1

theorem iterated_deriv_within_univ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} : iterated_deriv_within n f set.univ = iterated_deriv n f := sorry

/-! ### Properties of the iterated derivative within a set -/

theorem iterated_deriv_within_eq_iterated_fderiv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} {x : 𝕜} : iterated_deriv_within n f s x = coe_fn (iterated_fderiv_within 𝕜 n f s x) fun (i : fin n) => 1 :=
  rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
theorem iterated_deriv_within_eq_equiv_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} : iterated_deriv_within n f s =
  ⇑(continuous_linear_equiv.symm (continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F)) ∘
    iterated_fderiv_within 𝕜 n f s :=
  funext fun (x : 𝕜) => Eq.refl (iterated_deriv_within n f s x)

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
theorem iterated_fderiv_within_eq_equiv_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} : iterated_fderiv_within 𝕜 n f s = ⇑(continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F) ∘ iterated_deriv_within n f s := sorry

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
theorem iterated_fderiv_within_apply_eq_iterated_deriv_within_mul_prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} {x : 𝕜} {m : fin n → 𝕜} : coe_fn (iterated_fderiv_within 𝕜 n f s x) m =
  (finset.prod finset.univ fun (i : fin n) => m i) • iterated_deriv_within n f s x := sorry

@[simp] theorem iterated_deriv_within_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} : iterated_deriv_within 0 f s = f := sorry

@[simp] theorem iterated_deriv_within_one {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} (hs : unique_diff_on 𝕜 s) {x : 𝕜} (hx : x ∈ s) : iterated_deriv_within 1 f s x = deriv_within f s x := sorry

/-- If the first `n` derivatives within a set of a function are continuous, and its first `n-1`
derivatives are differentiable, then the function is `C^n`. This is not an equivalence in general,
but this is an equivalence when the set has unique derivatives, see
`times_cont_diff_on_iff_continuous_on_differentiable_on_deriv`. -/
theorem times_cont_diff_on_of_continuous_on_differentiable_on_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} {n : with_top ℕ} (Hcont : ∀ (m : ℕ), ↑m ≤ n → continuous_on (fun (x : 𝕜) => iterated_deriv_within m f s x) s) (Hdiff : ∀ (m : ℕ), ↑m < n → differentiable_on 𝕜 (fun (x : 𝕜) => iterated_deriv_within m f s x) s) : times_cont_diff_on 𝕜 n f s := sorry

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
theorem times_cont_diff_on_of_differentiable_on_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} {n : with_top ℕ} (h : ∀ (m : ℕ), ↑m ≤ n → differentiable_on 𝕜 (iterated_deriv_within m f s) s) : times_cont_diff_on 𝕜 n f s := sorry

/-- On a set with unique derivatives, a `C^n` function has derivatives up to `n` which are
continuous. -/
theorem times_cont_diff_on.continuous_on_iterated_deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} {n : with_top ℕ} {m : ℕ} (h : times_cont_diff_on 𝕜 n f s) (hmn : ↑m ≤ n) (hs : unique_diff_on 𝕜 s) : continuous_on (iterated_deriv_within m f s) s := sorry

/-- On a set with unique derivatives, a `C^n` function has derivatives less than `n` which are
differentiable. -/
theorem times_cont_diff_on.differentiable_on_iterated_deriv_within {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} {n : with_top ℕ} {m : ℕ} (h : times_cont_diff_on 𝕜 n f s) (hmn : ↑m < n) (hs : unique_diff_on 𝕜 s) : differentiable_on 𝕜 (iterated_deriv_within m f s) s := sorry

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
theorem times_cont_diff_on_iff_continuous_on_differentiable_on_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {s : set 𝕜} {n : with_top ℕ} (hs : unique_diff_on 𝕜 s) : times_cont_diff_on 𝕜 n f s ↔
  (∀ (m : ℕ), ↑m ≤ n → continuous_on (iterated_deriv_within m f s) s) ∧
    ∀ (m : ℕ), ↑m < n → differentiable_on 𝕜 (iterated_deriv_within m f s) s := sorry

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
differentiating the `n`-th iterated derivative. -/
theorem iterated_deriv_within_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} {x : 𝕜} (hxs : unique_diff_within_at 𝕜 s x) : iterated_deriv_within (n + 1) f s x = deriv_within (iterated_deriv_within n f s) s x := sorry

/-- The `n`-th iterated derivative within a set with unique derivatives can be obtained by
iterating `n` times the differentiation operation. -/
theorem iterated_deriv_within_eq_iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} {x : 𝕜} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) : iterated_deriv_within n f s x = nat.iterate (fun (g : 𝕜 → F) => deriv_within g s) n f x := sorry

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
taking the `n`-th derivative of the derivative. -/
theorem iterated_deriv_within_succ' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {s : set 𝕜} {x : 𝕜} (hxs : unique_diff_on 𝕜 s) (hx : x ∈ s) : iterated_deriv_within (n + 1) f s x = iterated_deriv_within n (deriv_within f s) s x := sorry

/-! ### Properties of the iterated derivative on the whole space -/

theorem iterated_deriv_eq_iterated_fderiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {x : 𝕜} : iterated_deriv n f x = coe_fn (iterated_fderiv 𝕜 n f x) fun (i : fin n) => 1 :=
  rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
theorem iterated_deriv_eq_equiv_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} : iterated_deriv n f =
  ⇑(continuous_linear_equiv.symm (continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F)) ∘ iterated_fderiv 𝕜 n f :=
  funext fun (x : 𝕜) => Eq.refl (iterated_deriv n f x)

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
theorem iterated_fderiv_eq_equiv_comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} : iterated_fderiv 𝕜 n f = ⇑(continuous_multilinear_map.pi_field_equiv 𝕜 (fin n) F) ∘ iterated_deriv n f := sorry

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
theorem iterated_fderiv_apply_eq_iterated_deriv_mul_prod {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} {x : 𝕜} {m : fin n → 𝕜} : coe_fn (iterated_fderiv 𝕜 n f x) m = (finset.prod finset.univ fun (i : fin n) => m i) • iterated_deriv n f x := sorry

@[simp] theorem iterated_deriv_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} : iterated_deriv 0 f = f := sorry

@[simp] theorem iterated_deriv_one {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} : iterated_deriv 1 f = deriv f := sorry

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
theorem times_cont_diff_iff_iterated_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {n : with_top ℕ} : times_cont_diff 𝕜 n f ↔
  (∀ (m : ℕ), ↑m ≤ n → continuous (iterated_deriv m f)) ∧ ∀ (m : ℕ), ↑m < n → differentiable 𝕜 (iterated_deriv m f) := sorry

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
theorem times_cont_diff_of_differentiable_iterated_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {n : with_top ℕ} (h : ∀ (m : ℕ), ↑m ≤ n → differentiable 𝕜 (iterated_deriv m f)) : times_cont_diff 𝕜 n f :=
  iff.mpr times_cont_diff_iff_iterated_deriv
    { left := fun (m : ℕ) (hm : ↑m ≤ n) => differentiable.continuous (h m hm),
      right := fun (m : ℕ) (hm : ↑m < n) => h m (le_of_lt hm) }

theorem times_cont_diff.continuous_iterated_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {n : with_top ℕ} (m : ℕ) (h : times_cont_diff 𝕜 n f) (hmn : ↑m ≤ n) : continuous (iterated_deriv m f) :=
  and.left (iff.mp times_cont_diff_iff_iterated_deriv h) m hmn

theorem times_cont_diff.differentiable_iterated_deriv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {f : 𝕜 → F} {n : with_top ℕ} (m : ℕ) (h : times_cont_diff 𝕜 n f) (hmn : ↑m < n) : differentiable 𝕜 (iterated_deriv m f) :=
  and.right (iff.mp times_cont_diff_iff_iterated_deriv h) m hmn

/-- The `n+1`-th iterated derivative can be obtained by differentiating the `n`-th
iterated derivative. -/
theorem iterated_deriv_succ {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} : iterated_deriv (n + 1) f = deriv (iterated_deriv n f) := sorry

/-- The `n`-th iterated derivative can be obtained by iterating `n` times the
differentiation operation. -/
theorem iterated_deriv_eq_iterate {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} : iterated_deriv n f = nat.iterate deriv n f := sorry

/-- The `n+1`-th iterated derivative can be obtained by taking the `n`-th derivative of the
derivative. -/
theorem iterated_deriv_succ' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {F : Type u_2} [normed_group F] [normed_space 𝕜 F] {n : ℕ} {f : 𝕜 → F} : iterated_deriv (n + 1) f = iterated_deriv n (deriv f) := sorry

