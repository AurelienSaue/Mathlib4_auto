/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.matrix.pequiv
import Mathlib.data.fintype.card
import Mathlib.group_theory.perm.sign
import Mathlib.algebra.algebra.basic
import Mathlib.tactic.ring
import Mathlib.linear_algebra.alternating
import Mathlib.PostPort

universes u v w z u_1 

namespace Mathlib

namespace matrix


/-- The determinant of a matrix given by the Leibniz formula. -/
def det {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] (M : matrix n n R) :
    R :=
  finset.sum finset.univ
    fun (σ : equiv.perm n) =>
      ↑↑(coe_fn equiv.perm.sign σ) * finset.prod finset.univ fun (i : n) => M (coe_fn σ i) i

@[simp] theorem det_diagonal {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    {d : n → R} : det (diagonal d) = finset.prod finset.univ fun (i : n) => d i :=
  sorry

@[simp] theorem det_zero {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (h : Nonempty n) : det 0 = 0 :=
  sorry

@[simp] theorem det_one {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] :
    det 1 = 1 :=
  sorry

theorem det_eq_one_of_card_eq_zero {n : Type u} [DecidableEq n] [fintype n] {R : Type v}
    [comm_ring R] {A : matrix n n R} (h : fintype.card n = 0) : det A = 1 :=
  sorry

theorem det_mul_aux {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    {M : matrix n n R} {N : matrix n n R} {p : n → n} (H : ¬function.bijective p) :
    (finset.sum finset.univ
          fun (σ : equiv.perm n) =>
            ↑↑(coe_fn equiv.perm.sign σ) *
              finset.prod finset.univ fun (x : n) => M (coe_fn σ x) (p x) * N (p x) x) =
        0 :=
  sorry

@[simp] theorem det_mul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (M : matrix n n R) (N : matrix n n R) : det (matrix.mul M N) = det M * det N :=
  sorry

protected instance det.is_monoid_hom {n : Type u} [DecidableEq n] [fintype n] {R : Type v}
    [comm_ring R] : is_monoid_hom det :=
  is_monoid_hom.mk det_one

/-- Transposing a matrix preserves the determinant. -/
@[simp] theorem det_transpose {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (M : matrix n n R) : det (transpose M) = det M :=
  sorry

/-- The determinant of a permutation matrix equals its sign. -/
@[simp] theorem det_permutation {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (σ : equiv.perm n) : det (pequiv.to_matrix (equiv.to_pequiv σ)) = ↑(coe_fn equiv.perm.sign σ) :=
  sorry

/-- Permuting the columns changes the sign of the determinant. -/
theorem det_permute {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (σ : equiv.perm n) (M : matrix n n R) :
    (det fun (i : n) => M (coe_fn σ i)) = ↑(coe_fn equiv.perm.sign σ) * det M :=
  sorry

@[simp] theorem det_smul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    {A : matrix n n R} {c : R} : det (c • A) = c ^ fintype.card n * det A :=
  sorry

theorem ring_hom.map_det {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    {S : Type w} [comm_ring S] {M : matrix n n R} {f : R →+* S} :
    coe_fn f (det M) = det (coe_fn (ring_hom.map_matrix f) M) :=
  sorry

theorem alg_hom.map_det {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    {S : Type w} [comm_ring S] [algebra R S] {T : Type z} [comm_ring T] [algebra R T]
    {M : matrix n n S} {f : alg_hom R S T} :
    coe_fn f (det M) = det (coe_fn (ring_hom.map_matrix ↑f) M) :=
  sorry

/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/

theorem det_eq_zero_of_row_eq_zero {n : Type u} [DecidableEq n] [fintype n] {R : Type v}
    [comm_ring R] {A : matrix n n R} (i : n) (h : ∀ (j : n), A i j = 0) : det A = 0 :=
  sorry

theorem det_eq_zero_of_column_eq_zero {n : Type u} [DecidableEq n] [fintype n] {R : Type v}
    [comm_ring R] {A : matrix n n R} (j : n) (h : ∀ (i : n), A i j = 0) : det A = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (det A = 0)) (Eq.symm (det_transpose A))))
    (det_eq_zero_of_row_eq_zero j h)

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    {M : matrix n n R} {i : n} {j : n} (i_ne_j : i ≠ j) (hij : M i = M j) : det M = 0 :=
  sorry

theorem det_update_column_add {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (M : matrix n n R) (j : n) (u : n → R) (v : n → R) :
    det (update_column M j (u + v)) = det (update_column M j u) + det (update_column M j v) :=
  sorry

theorem det_update_row_add {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (M : matrix n n R) (j : n) (u : n → R) (v : n → R) :
    det (update_row M j (u + v)) = det (update_row M j u) + det (update_row M j v) :=
  sorry

theorem det_update_column_smul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (M : matrix n n R) (j : n) (s : R) (u : n → R) :
    det (update_column M j (s • u)) = s * det (update_column M j u) :=
  sorry

theorem det_update_row_smul {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R]
    (M : matrix n n R) (j : n) (s : R) (u : n → R) :
    det (update_row M j (s • u)) = s * det (update_row M j u) :=
  sorry

/-- `det` is an alternating multilinear map over the rows of the matrix.

See also `is_basis.det`. -/
def det_row_multilinear {n : Type u} [DecidableEq n] [fintype n] {R : Type v} [comm_ring R] :
    alternating_map R (n → R) R n :=
  alternating_map.mk det sorry sorry sorry

@[simp] theorem det_block_diagonal {n : Type u} [DecidableEq n] [fintype n] {R : Type v}
    [comm_ring R] {o : Type u_1} [fintype o] [DecidableEq o] (M : o → matrix n n R) :
    det (block_diagonal M) = finset.prod finset.univ fun (k : o) => det (M k) :=
  sorry

end Mathlib