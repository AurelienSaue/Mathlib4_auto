/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.eval
import Mathlib.tactic.interval_cases
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Theory of degrees of polynomials

Some of the main results include
- `nat_degree_comp_le` : The degree of the composition is at most the product of degrees

-/

namespace polynomial


theorem nat_degree_comp_le {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} :
    nat_degree (comp p q) ≤ nat_degree p * nat_degree q :=
  sorry

theorem degree_map_le {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S]
    (f : R →+* S) : degree (map f p) ≤ degree p :=
  sorry

theorem nat_degree_map_le {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S]
    (f : R →+* S) : nat_degree (map f p) ≤ nat_degree p :=
  sorry

theorem degree_map_eq_of_leading_coeff_ne_zero {R : Type u} {S : Type v} [semiring R]
    {p : polynomial R} [semiring S] (f : R →+* S) (hf : coe_fn f (leading_coeff p) ≠ 0) :
    degree (map f p) = degree p :=
  sorry

theorem nat_degree_map_of_leading_coeff_ne_zero {R : Type u} {S : Type v} [semiring R]
    {p : polynomial R} [semiring S] (f : R →+* S) (hf : coe_fn f (leading_coeff p) ≠ 0) :
    nat_degree (map f p) = nat_degree p :=
  nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f hf)

theorem leading_coeff_map_of_leading_coeff_ne_zero {R : Type u} {S : Type v} [semiring R]
    {p : polynomial R} [semiring S] (f : R →+* S) (hf : coe_fn f (leading_coeff p) ≠ 0) :
    leading_coeff (map f p) = coe_fn f (leading_coeff p) :=
  sorry

theorem degree_pos_of_root {R : Type u} {a : R} [semiring R] {p : polynomial R} (hp : p ≠ 0)
    (h : is_root p a) : 0 < degree p :=
  sorry

theorem nat_degree_pos_of_eval₂_root {R : Type u} {S : Type v} [semiring R] [semiring S]
    {p : polynomial R} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ (x : R), coe_fn f x = 0 → x = 0) : 0 < nat_degree p :=
  sorry

theorem degree_pos_of_eval₂_root {R : Type u} {S : Type v} [semiring R] [semiring S]
    {p : polynomial R} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ (x : R), coe_fn f x = 0 → x = 0) : 0 < degree p :=
  iff.mp nat_degree_pos_iff_degree_pos (nat_degree_pos_of_eval₂_root hp f hz inj)

theorem degree_map_eq_of_injective {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S}
    (hf : function.injective ⇑f) (p : polynomial R) : degree (map f p) = degree p :=
  sorry

theorem degree_map' {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S}
    (hf : function.injective ⇑f) (p : polynomial R) : degree (map f p) = degree p :=
  degree_map_eq_of_injective hf p

theorem nat_degree_map' {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S}
    (hf : function.injective ⇑f) (p : polynomial R) : nat_degree (map f p) = nat_degree p :=
  nat_degree_eq_of_degree_eq (degree_map' hf p)

theorem leading_coeff_map' {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S}
    (hf : function.injective ⇑f) (p : polynomial R) :
    leading_coeff (map f p) = coe_fn f (leading_coeff p) :=
  sorry

theorem monomial_nat_degree_leading_coeff_eq_self {R : Type u} [semiring R] {f : polynomial R}
    (h : finset.card (finsupp.support f) ≤ 1) :
    coe_fn (monomial (nat_degree f)) (leading_coeff f) = f :=
  sorry

theorem C_mul_X_pow_eq_self {R : Type u} [semiring R] {f : polynomial R}
    (h : finset.card (finsupp.support f) ≤ 1) : coe_fn C (leading_coeff f) * X ^ nat_degree f = f :=
  sorry

end Mathlib