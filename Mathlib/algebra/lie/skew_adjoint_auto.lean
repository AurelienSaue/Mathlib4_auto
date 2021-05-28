/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.lie.basic
import Mathlib.linear_algebra.bilinear_form
import PostPort

universes u v w 

namespace Mathlib

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

## Tags

lie algebra, skew-adjoint, bilinear form
-/

theorem bilin_form.is_skew_adjoint_bracket {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M] (B : bilin_form R M) (f : module.End R M) (g : module.End R M) (hf : f ∈ bilin_form.skew_adjoint_submodule B) (hg : g ∈ bilin_form.skew_adjoint_submodule B) : has_bracket.bracket f g ∈ bilin_form.skew_adjoint_submodule B := sorry

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
def skew_adjoint_lie_subalgebra {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M] (B : bilin_form R M) : lie_subalgebra R (module.End R M) :=
  lie_subalgebra.mk (submodule.carrier (bilin_form.skew_adjoint_submodule B)) sorry sorry sorry
    (bilin_form.is_skew_adjoint_bracket B)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
def skew_adjoint_lie_subalgebra_equiv {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M] (B : bilin_form R M) {N : Type w} [add_comm_group N] [module R N] (e : linear_equiv R N M) : lie_algebra.equiv R ↥(skew_adjoint_lie_subalgebra (bilin_form.comp B ↑e ↑e)) ↥(skew_adjoint_lie_subalgebra B) :=
  lie_algebra.equiv.of_subalgebras (skew_adjoint_lie_subalgebra (bilin_form.comp B ↑e ↑e)) (skew_adjoint_lie_subalgebra B)
    (linear_equiv.lie_conj e) sorry

@[simp] theorem skew_adjoint_lie_subalgebra_equiv_apply {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M] (B : bilin_form R M) {N : Type w} [add_comm_group N] [module R N] (e : linear_equiv R N M) (f : ↥(skew_adjoint_lie_subalgebra (bilin_form.comp B ↑e ↑e))) : ↑(coe_fn (skew_adjoint_lie_subalgebra_equiv B e) f) = coe_fn (linear_equiv.lie_conj e) ↑f := sorry

@[simp] theorem skew_adjoint_lie_subalgebra_equiv_symm_apply {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M] (B : bilin_form R M) {N : Type w} [add_comm_group N] [module R N] (e : linear_equiv R N M) (f : ↥(skew_adjoint_lie_subalgebra B)) : ↑(coe_fn (lie_algebra.equiv.symm (skew_adjoint_lie_subalgebra_equiv B e)) f) =
  coe_fn (linear_equiv.lie_conj (linear_equiv.symm e)) ↑f := sorry

theorem matrix.lie_transpose {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (A : matrix n n R) (B : matrix n n R) : matrix.transpose (has_bracket.bracket A B) = has_bracket.bracket (matrix.transpose B) (matrix.transpose A) := sorry

theorem matrix.is_skew_adjoint_bracket {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) (A : matrix n n R) (B : matrix n n R) (hA : A ∈ skew_adjoint_matrices_submodule J) (hB : B ∈ skew_adjoint_matrices_submodule J) : has_bracket.bracket A B ∈ skew_adjoint_matrices_submodule J := sorry

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
def skew_adjoint_matrices_lie_subalgebra {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) : lie_subalgebra R (matrix n n R) :=
  lie_subalgebra.mk (submodule.carrier (skew_adjoint_matrices_submodule J)) sorry sorry sorry sorry

@[simp] theorem mem_skew_adjoint_matrices_lie_subalgebra {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) (A : matrix n n R) : A ∈ skew_adjoint_matrices_lie_subalgebra J ↔ A ∈ skew_adjoint_matrices_submodule J :=
  iff.rfl

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
def skew_adjoint_matrices_lie_subalgebra_equiv {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) (P : matrix n n R) (h : is_unit P) : lie_algebra.equiv R ↥(skew_adjoint_matrices_lie_subalgebra J)
  ↥(skew_adjoint_matrices_lie_subalgebra (matrix.mul (matrix.mul (matrix.transpose P) J) P)) :=
  lie_algebra.equiv.of_subalgebras (skew_adjoint_matrices_lie_subalgebra J)
    (skew_adjoint_matrices_lie_subalgebra (matrix.mul (matrix.mul (matrix.transpose P) J) P))
    (lie_algebra.equiv.symm (matrix.lie_conj P h)) sorry

theorem skew_adjoint_matrices_lie_subalgebra_equiv_apply {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) (P : matrix n n R) (h : is_unit P) (A : ↥(skew_adjoint_matrices_lie_subalgebra J)) : ↑(coe_fn (skew_adjoint_matrices_lie_subalgebra_equiv J P h) A) = matrix.mul (matrix.mul (P⁻¹) ↑A) P := sorry

/-- An equivalence of matrix algebras commuting with the transpose endomorphisms restricts to an
equivalence of Lie algebras of skew-adjoint matrices. -/
def skew_adjoint_matrices_lie_subalgebra_equiv_transpose {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) {m : Type w} [DecidableEq m] [fintype m] (e : alg_equiv R (matrix n n R) (matrix m m R)) (h : ∀ (A : matrix n n R), matrix.transpose (coe_fn e A) = coe_fn e (matrix.transpose A)) : lie_algebra.equiv R ↥(skew_adjoint_matrices_lie_subalgebra J) ↥(skew_adjoint_matrices_lie_subalgebra (coe_fn e J)) :=
  lie_algebra.equiv.of_subalgebras (skew_adjoint_matrices_lie_subalgebra J)
    (skew_adjoint_matrices_lie_subalgebra (coe_fn e J)) (alg_equiv.to_lie_equiv e) sorry

@[simp] theorem skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (J : matrix n n R) {m : Type w} [DecidableEq m] [fintype m] (e : alg_equiv R (matrix n n R) (matrix m m R)) (h : ∀ (A : matrix n n R), matrix.transpose (coe_fn e A) = coe_fn e (matrix.transpose A)) (A : ↥(skew_adjoint_matrices_lie_subalgebra J)) : ↑(coe_fn (skew_adjoint_matrices_lie_subalgebra_equiv_transpose J e h) A) = coe_fn e ↑A :=
  rfl

theorem mem_skew_adjoint_matrices_lie_subalgebra_unit_smul {R : Type u} {n : Type w} [comm_ring R] [DecidableEq n] [fintype n] (u : units R) (J : matrix n n R) (A : matrix n n R) : A ∈ skew_adjoint_matrices_lie_subalgebra (↑u • J) ↔ A ∈ skew_adjoint_matrices_lie_subalgebra J := sorry

