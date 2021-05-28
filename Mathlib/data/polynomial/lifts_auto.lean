/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Riccardo Brasca
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.algebra_map
import Mathlib.algebra.algebra.subalgebra
import Mathlib.algebra.polynomial.big_operators
import Mathlib.data.polynomial.erase_lead
import PostPort

universes u v 

namespace Mathlib

/-!
# Polynomials that lift

Given semirings `R` and `S` with a morphism `f : R →+* S`, we define a subsemiring `lifts` of
`polynomial S` by the image of `ring_hom.of (map f)`.
Then, we prove that a polynomial that lifts can always be lifted to a polynomial of the same degree
and that a monic polynomial that lifts can be lifted to a monic polynomial (of the same degree).

## Main definition

* `lifts (f : R →+* S)` : the subsemiring of polynomials that lift.

## Main results

* `lifts_and_degree_eq` : A polynomial lifts if and only if it can be lifted to a polynomial
of the same degree.
* `lifts_and_degree_eq_and_monic` : A monic polynomial lifts if and only if it can be lifted to a
monic polynomial of the same degree.
* `lifts_iff_alg` : if `R` is commutative, a polynomial lifts if and only if it is in the image of
`map_alg`, where `map_alg : polynomial R →ₐ[R] polynomial S` is the only `R`-algebra map
that sends `X` to `X`.

## Implementation details

In general `R` and `S` are semiring, so `lifts` is a semiring. In the case of rings, see
`lifts_iff_lifts_ring`.

Since we do not assume `R` to be commutative, we cannot say in general that the set of polynomials
that lift is a subalgebra. (By `lift_iff` this is true if `R` is commutative.)

-/

namespace polynomial


/-- We define the subsemiring of polynomials that lifts as the image of `ring_hom.of (map f)`. -/
def lifts {R : Type u} [semiring R] {S : Type v} [semiring S] (f : R →+* S) : subsemiring (polynomial S) :=
  ring_hom.srange (ring_hom.of (map f))

theorem mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} (p : polynomial S) : p ∈ lifts f ↔ ∃ (q : polynomial R), map f q = p := sorry

theorem lifts_iff_set_range {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} (p : polynomial S) : p ∈ lifts f ↔ p ∈ set.range (map f) := sorry

theorem lifts_iff_coeff_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} (p : polynomial S) : p ∈ lifts f ↔ ∀ (n : ℕ), coeff p n ∈ set.range ⇑f := sorry

/--If `(r : R)`, then `C (f r)` lifts. -/
theorem C_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] (f : R →+* S) (r : R) : coe_fn C (coe_fn f r) ∈ lifts f := sorry

/-- If `(s : S)` is in the image of `f`, then `C s` lifts. -/
theorem C'_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} {s : S} (h : s ∈ set.range ⇑f) : coe_fn C s ∈ lifts f := sorry

/-- The polynomial `X` lifts. -/
theorem X_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] (f : R →+* S) : X ∈ lifts f := sorry

/-- The polynomial `X ^ n` lifts. -/
theorem X_pow_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] (f : R →+* S) (n : ℕ) : X ^ n ∈ lifts f := sorry

/-- If `p` lifts and `(r : R)` then `r * p` lifts. -/
theorem base_mul_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} {p : polynomial S} (r : R) (hp : p ∈ lifts f) : coe_fn C (coe_fn f r) * p ∈ lifts f := sorry

/-- If `(s : S)` is in the image of `f`, then `monomial n s` lifts. -/
theorem monomial_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} {s : S} (n : ℕ) (h : s ∈ set.range ⇑f) : coe_fn (monomial n) s ∈ lifts f := sorry

/-- If `p` lifts then `p.erase n` lifts. -/
theorem erase_mem_lifts {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} {p : polynomial S} (n : ℕ) (h : p ∈ lifts f) : finsupp.erase n p ∈ lifts f := sorry

theorem monomial_mem_lifts_and_degree_eq {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} {s : S} {n : ℕ} (hl : coe_fn (monomial n) s ∈ lifts f) : ∃ (q : polynomial R), map f q = coe_fn (monomial n) s ∧ degree q = degree (coe_fn (monomial n) s) := sorry

/-- A polynomial lifts if and only if it can be lifted to a polynomial of the same degree. -/
theorem mem_lifts_and_degree_eq {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} {p : polynomial S} (hlifts : p ∈ lifts f) : ∃ (q : polynomial R), map f q = p ∧ degree q = degree p := sorry

/-- A monic polynomial lifts if and only if it can be lifted to a monic polynomial
of the same degree. -/
theorem lifts_and_degree_eq_and_monic {R : Type u} [semiring R] {S : Type v} [semiring S] {f : R →+* S} [nontrivial S] {p : polynomial S} (hlifts : p ∈ lifts f) (hmonic : monic p) : ∃ (q : polynomial R), map f q = p ∧ degree q = degree p ∧ monic q := sorry

/-- The subring of polynomials that lift. -/
def lifts_ring {R : Type u} [ring R] {S : Type v} [ring S] (f : R →+* S) : subring (polynomial S) :=
  ring_hom.range (ring_hom.of (map f))

/-- If `R` and `S` are rings, `p` is in the subring of polynomials that lift if and only if it is in
the subsemiring of polynomials that lift. -/
theorem lifts_iff_lifts_ring {R : Type u} [ring R] {S : Type v} [ring S] (f : R →+* S) (p : polynomial S) : p ∈ lifts f ↔ p ∈ lifts_ring f := sorry

/-- The map `polynomial R → polynomial S` as an algebra homomorphism. -/
def map_alg (R : Type u) [comm_semiring R] (S : Type v) [semiring S] [algebra R S] : alg_hom R (polynomial R) (polynomial S) :=
  aeval X

/-- `map_alg` is the morphism induced by `R → S`. -/
theorem map_alg_eq_map {R : Type u} [comm_semiring R] {S : Type v} [semiring S] [algebra R S] (p : polynomial R) : coe_fn (map_alg R S) p = map (algebra_map R S) p := sorry

/-- A polynomial `p` lifts if and only if it is in the image of `map_alg`. -/
theorem mem_lifts_iff_mem_alg (R : Type u) [comm_semiring R] {S : Type v} [semiring S] [algebra R S] (p : polynomial S) : p ∈ lifts (algebra_map R S) ↔ p ∈ alg_hom.range (map_alg R S) := sorry

/-- If `p` lifts and `(r : R)` then `r • p` lifts. -/
theorem smul_mem_lifts {R : Type u} [comm_semiring R] {S : Type v} [semiring S] [algebra R S] {p : polynomial S} (r : R) (hp : p ∈ lifts (algebra_map R S)) : r • p ∈ lifts (algebra_map R S) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (r • p ∈ lifts (algebra_map R S))) (propext (mem_lifts_iff_mem_alg R (r • p)))))
    (subalgebra.smul_mem (alg_hom.range (map_alg R S))
      (eq.mp (Eq._oldrec (Eq.refl (p ∈ lifts (algebra_map R S))) (propext (mem_lifts_iff_mem_alg R p))) hp) r)

