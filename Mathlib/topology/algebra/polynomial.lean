/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.algebra_map
import Mathlib.data.polynomial.div
import Mathlib.topology.metric_space.cau_seq_filter
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `polynomial.continuous_eval₂: `polynomial.eval₂` defines a continuous function.
* `polynomial.continuous_aeval: `polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `polynomial.continuous_at_aeval`,
  `polynomial.continuous_within_at_aeval`, `polynomial.continuous_on_aeval`.
* `polynomial.continuous`:  `polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `polynomial.continuous_at`, `polynomial.continuous_within_at`,
  `polynomial.continuous_on`.
* `polynomial.tendsto_norm_at_top`: `λ x, ∥polynomial.eval (z x) p∥` tends to infinity provided that
  `λ x, ∥z x∥` tends to infinity and `0 < degree p`;
* `polynomial.tendsto_abv_eval₂_at_top`, `polynomial.tendsto_abv_at_top`,
  `polynomial.tendsto_abv_aeval_at_top`: a few versions of the previous statement for
  `is_absolute_value abv` instead of norm.

## Tags

polynomial, continuity
-/

namespace polynomial


protected theorem continuous_eval₂ {R : Type u_1} {S : Type u_2} [semiring R] [topological_space R] [topological_semiring R] [semiring S] (p : polynomial S) (f : S →+* R) : continuous fun (x : R) => eval₂ f x p :=
  id
    (continuous_finset_sum (finsupp.support p)
      fun (c : ℕ) (hc : c ∈ finsupp.support p) => continuous.mul continuous_const (continuous_pow c))

protected theorem continuous {R : Type u_1} [semiring R] [topological_space R] [topological_semiring R] (p : polynomial R) : continuous fun (x : R) => eval x p :=
  polynomial.continuous_eval₂ p (ring_hom.id R)

protected theorem continuous_at {R : Type u_1} [semiring R] [topological_space R] [topological_semiring R] (p : polynomial R) {a : R} : continuous_at (fun (x : R) => eval x p) a :=
  continuous.continuous_at (polynomial.continuous p)

protected theorem continuous_within_at {R : Type u_1} [semiring R] [topological_space R] [topological_semiring R] (p : polynomial R) {s : set R} {a : R} : continuous_within_at (fun (x : R) => eval x p) s a :=
  continuous.continuous_within_at (polynomial.continuous p)

protected theorem continuous_on {R : Type u_1} [semiring R] [topological_space R] [topological_semiring R] (p : polynomial R) {s : set R} : continuous_on (fun (x : R) => eval x p) s :=
  continuous.continuous_on (polynomial.continuous p)

protected theorem continuous_aeval {R : Type u_1} {A : Type u_2} [comm_semiring R] [semiring A] [algebra R A] [topological_space A] [topological_semiring A] (p : polynomial R) : continuous fun (x : A) => coe_fn (aeval x) p :=
  polynomial.continuous_eval₂ p (algebra_map R A)

protected theorem continuous_at_aeval {R : Type u_1} {A : Type u_2} [comm_semiring R] [semiring A] [algebra R A] [topological_space A] [topological_semiring A] (p : polynomial R) {a : A} : continuous_at (fun (x : A) => coe_fn (aeval x) p) a :=
  continuous.continuous_at (polynomial.continuous_aeval p)

protected theorem continuous_within_at_aeval {R : Type u_1} {A : Type u_2} [comm_semiring R] [semiring A] [algebra R A] [topological_space A] [topological_semiring A] (p : polynomial R) {s : set A} {a : A} : continuous_within_at (fun (x : A) => coe_fn (aeval x) p) s a :=
  continuous.continuous_within_at (polynomial.continuous_aeval p)

protected theorem continuous_on_aeval {R : Type u_1} {A : Type u_2} [comm_semiring R] [semiring A] [algebra R A] [topological_space A] [topological_semiring A] (p : polynomial R) {s : set A} : continuous_on (fun (x : A) => coe_fn (aeval x) p) s :=
  continuous.continuous_on (polynomial.continuous_aeval p)

theorem tendsto_abv_eval₂_at_top {R : Type u_1} {S : Type u_2} {k : Type u_3} {α : Type u_4} [semiring R] [ring S] [linear_ordered_field k] (f : R →+* S) (abv : S → k) [is_absolute_value abv] (p : polynomial R) (hd : 0 < degree p) (hf : coe_fn f (leading_coeff p) ≠ 0) {l : filter α} {z : α → S} (hz : filter.tendsto (abv ∘ z) l filter.at_top) : filter.tendsto (fun (x : α) => abv (eval₂ f (z x) p)) l filter.at_top := sorry

theorem tendsto_abv_at_top {R : Type u_1} {k : Type u_2} {α : Type u_3} [ring R] [linear_ordered_field k] (abv : R → k) [is_absolute_value abv] (p : polynomial R) (h : 0 < degree p) {l : filter α} {z : α → R} (hz : filter.tendsto (abv ∘ z) l filter.at_top) : filter.tendsto (fun (x : α) => abv (eval (z x) p)) l filter.at_top :=
  tendsto_abv_eval₂_at_top (ring_hom.id R) abv p h (mt (iff.mp leading_coeff_eq_zero) (ne_zero_of_degree_gt h)) hz

theorem tendsto_abv_aeval_at_top {R : Type u_1} {A : Type u_2} {k : Type u_3} {α : Type u_4} [comm_semiring R] [ring A] [algebra R A] [linear_ordered_field k] (abv : A → k) [is_absolute_value abv] (p : polynomial R) (hd : 0 < degree p) (h₀ : coe_fn (algebra_map R A) (leading_coeff p) ≠ 0) {l : filter α} {z : α → A} (hz : filter.tendsto (abv ∘ z) l filter.at_top) : filter.tendsto (fun (x : α) => abv (coe_fn (aeval (z x)) p)) l filter.at_top :=
  tendsto_abv_eval₂_at_top (algebra_map R A) abv p hd h₀ hz

theorem tendsto_norm_at_top {α : Type u_1} {R : Type u_2} [normed_ring R] [is_absolute_value norm] (p : polynomial R) (h : 0 < degree p) {l : filter α} {z : α → R} (hz : filter.tendsto (fun (x : α) => norm (z x)) l filter.at_top) : filter.tendsto (fun (x : α) => norm (eval (z x) p)) l filter.at_top :=
  tendsto_abv_at_top norm p h hz

theorem exists_forall_norm_le {R : Type u_2} [normed_ring R] [is_absolute_value norm] [proper_space R] (p : polynomial R) : ∃ (x : R), ∀ (y : R), norm (eval x p) ≤ norm (eval y p) := sorry

