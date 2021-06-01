/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alexander Bentkamp.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.field_theory.algebraic_closure
import Mathlib.linear_algebra.finsupp
import Mathlib.linear_algebra.matrix
import Mathlib.PostPort

universes v w u_1 u_2 

namespace Mathlib

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`has_eigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

namespace module


namespace End


/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M] [module R M] (f : End R M)
    (μ : R) : submodule R M :=
  linear_map.ker (f - coe_fn (algebra_map R (End R M)) μ)

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def has_eigenvector {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M] [module R M]
    (f : End R M) (μ : R) (x : M) :=
  x ≠ 0 ∧ x ∈ eigenspace f μ

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def has_eigenvalue {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M] [module R M]
    (f : End R M) (a : R) :=
  eigenspace f a ≠ ⊥

theorem mem_eigenspace_iff {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M] [module R M]
    {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ coe_fn f x = μ • x :=
  sorry

theorem eigenspace_div {K : Type v} {V : Type w} [field K] [add_comm_group V] [vector_space K V]
    (f : End K V) (a : K) (b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = linear_map.ker (b • f - coe_fn (algebra_map K (End K V)) a) :=
  sorry

theorem eigenspace_aeval_polynomial_degree_1 {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] (f : End K V) (q : polynomial K) (hq : polynomial.degree q = 1) :
    eigenspace f (-polynomial.coeff q 0 / polynomial.leading_coeff q) =
        linear_map.ker (coe_fn (polynomial.aeval f) q) :=
  sorry

theorem ker_aeval_ring_hom'_unit_polynomial {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] (f : End K V) (c : units (polynomial K)) :
    linear_map.ker (coe_fn (polynomial.aeval f) ↑c) = ⊥ :=
  sorry

theorem aeval_apply_of_has_eigenvector {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] {f : End K V} {p : polynomial K} {μ : K} {x : V}
    (h : has_eigenvector f μ x) :
    coe_fn (coe_fn (polynomial.aeval f) p) x = polynomial.eval μ p • x :=
  sorry

theorem is_root_of_has_eigenvalue {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] {f : End K V} {μ : K} (h : has_eigenvalue f μ) :
    polynomial.is_root (minpoly K f) μ :=
  sorry

protected theorem is_integral {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] [finite_dimensional K V] (f : End K V) : is_integral K f :=
  is_integral_of_noetherian (finite_dimensional.linear_map K V V) f

theorem has_eigenvalue_of_is_root {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] [finite_dimensional K V] {f : End K V} {μ : K}
    (h : polynomial.is_root (minpoly K f) μ) : has_eigenvalue f μ :=
  sorry

theorem has_eigenvalue_iff_is_root {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] [finite_dimensional K V] {f : End K V} {μ : K} :
    has_eigenvalue f μ ↔ polynomial.is_root (minpoly K f) μ :=
  { mp := is_root_of_has_eigenvalue, mpr := has_eigenvalue_of_is_root }

/-- Every linear operator on a vector space over an algebraically closed field has
    an eigenvalue. (Lemma 5.21 of [axler2015]) -/
theorem exists_eigenvalue {K : Type v} {V : Type w} [field K] [add_comm_group V] [vector_space K V]
    [is_alg_closed K] [finite_dimensional K V] [nontrivial V] (f : End K V) :
    ∃ (c : K), has_eigenvalue f c :=
  sorry

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
theorem eigenvectors_linear_independent {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] (f : End K V) (μs : set K) (xs : ↥μs → V)
    (h_eigenvec : ∀ (μ : ↥μs), has_eigenvector f (↑μ) (xs μ)) : linear_independent K xs :=
  sorry

/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015])-/
def generalized_eigenspace {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M] [module R M]
    (f : End R M) (μ : R) (k : ℕ) : submodule R M :=
  linear_map.ker ((f - coe_fn (algebra_map R (End R M)) μ) ^ k)

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def has_generalized_eigenvector {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M]
    [module R M] (f : End R M) (μ : R) (k : ℕ) (x : M) :=
  x ≠ 0 ∧ x ∈ generalized_eigenspace f μ k

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def has_generalized_eigenvalue {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M]
    [module R M] (f : End R M) (μ : R) (k : ℕ) :=
  generalized_eigenspace f μ k ≠ ⊥

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def generalized_eigenrange {R : Type v} {M : Type w} [comm_ring R] [add_comm_group M] [module R M]
    (f : End R M) (μ : R) (k : ℕ) : submodule R M :=
  linear_map.range ((f - coe_fn (algebra_map R (End R M)) μ) ^ k)

/-- The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_has_generalized_eigenvalue {R : Type v} {M : Type w} [comm_ring R]
    [add_comm_group M] [module R M] {f : End R M} {μ : R} {k : ℕ}
    (h : has_generalized_eigenvalue f μ k) : k ≠ 0 :=
  id
    fun (ᾰ : k = 0) =>
      Eq._oldrec (fun (h : has_generalized_eigenvalue f μ 0) => h linear_map.ker_id) (Eq.symm ᾰ) h

/-- A generalized eigenspace for some exponent `k` is contained in
    the generalized eigenspace for exponents larger than `k`. -/
theorem generalized_eigenspace_mono {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] {f : End K V} {μ : K} {k : ℕ} {m : ℕ} (hm : k ≤ m) :
    generalized_eigenspace f μ k ≤ generalized_eigenspace f μ m :=
  sorry

/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le {K : Type v} {V : Type w}
    [field K] [add_comm_group V] [vector_space K V] {f : End K V} {μ : K} {k : ℕ} {m : ℕ}
    (hm : k ≤ m) (hk : has_generalized_eigenvalue f μ k) : has_generalized_eigenvalue f μ m :=
  sorry

/-- The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_generalized_eigenspace {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] {f : End K V} {μ : K} {k : ℕ} (hk : 0 < k) :
    eigenspace f μ ≤ generalized_eigenspace f μ k :=
  generalized_eigenspace_mono (nat.succ_le_of_lt hk)

/-- All eigenvalues are generalized eigenvalues. -/
theorem has_generalized_eigenvalue_of_has_eigenvalue {K : Type v} {V : Type w} [field K]
    [add_comm_group V] [vector_space K V] {f : End K V} {μ : K} {k : ℕ} (hk : 0 < k)
    (hμ : has_eigenvalue f μ) : has_generalized_eigenvalue f μ k :=
  sorry

/-- Every generalized eigenvector is a generalized eigenvector for exponent `findim K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem generalized_eigenspace_le_generalized_eigenspace_findim {K : Type v} {V : Type w} [field K]
    [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : End K V) (μ : K) (k : ℕ) :
    generalized_eigenspace f μ k ≤ generalized_eigenspace f μ (finite_dimensional.findim K V) :=
  ker_pow_le_ker_pow_findim (f - coe_fn (algebra_map K (End K V)) μ) k

/-- Generalized eigenspaces for exponents at least `findim K V` are equal to each other. -/
theorem generalized_eigenspace_eq_generalized_eigenspace_findim_of_le {K : Type v} {V : Type w}
    [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : End K V) (μ : K)
    {k : ℕ} (hk : finite_dimensional.findim K V ≤ k) :
    generalized_eigenspace f μ k = generalized_eigenspace f μ (finite_dimensional.findim K V) :=
  ker_pow_eq_ker_pow_findim_of_le hk

/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem generalized_eigenspace_restrict {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] (f : End K V) (p : submodule K V) (k : ℕ) (μ : K)
    (hfp : ∀ (x : V), x ∈ p → coe_fn f x ∈ p) :
    generalized_eigenspace (linear_map.restrict f hfp) μ k =
        submodule.comap (submodule.subtype p) (generalized_eigenspace f μ k) :=
  sorry

/-- Generalized eigenrange and generalized eigenspace for exponent `findim K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker {K : Type v} {V : Type w} [field K]
    [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : End K V) (μ : K) :
    disjoint (generalized_eigenrange f μ (finite_dimensional.findim K V))
        (generalized_eigenspace f μ (finite_dimensional.findim K V)) :=
  sorry

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_findim_generalized_eigenspace_of_has_eigenvalue {K : Type v} {V : Type w} [field K]
    [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : End K V} {k : ℕ} {μ : K}
    (hx : has_eigenvalue f μ) (hk : 0 < k) :
    0 < finite_dimensional.findim K ↥(generalized_eigenspace f μ k) :=
  sorry

/-- A linear map maps a generalized eigenrange into itself. -/
theorem map_generalized_eigenrange_le {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] {f : End K V} {μ : K} {n : ℕ} :
    submodule.map f (generalized_eigenrange f μ n) ≤ generalized_eigenrange f μ n :=
  sorry

/-- The generalized eigenvectors span the entire vector space (Lemma 8.21 of [axler2015]). -/
theorem supr_generalized_eigenspace_eq_top {K : Type v} {V : Type w} [field K] [add_comm_group V]
    [vector_space K V] [is_alg_closed K] [finite_dimensional K V] (f : End K V) :
    (supr fun (μ : K) => supr fun (k : ℕ) => generalized_eigenspace f μ k) = ⊤ :=
  sorry

end End


end module


protected theorem linear_map.is_integral {K : Type u_1} {V : Type u_2} [field K] [add_comm_group V]
    [vector_space K V] [finite_dimensional K V] (f : linear_map K V V) : is_integral K f :=
  module.End.is_integral f

end Mathlib