/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.invertible
import Mathlib.algebra.lie.skew_adjoint
import Mathlib.linear_algebra.matrix
import Mathlib.PostPort

universes u₂ u_1 u_4 u_2 u_3 

namespace Mathlib

/-!
# Classical Lie algebras

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `lie_algebra.special_linear.sl`
  * `lie_algebra.symplectic.sp`
  * `lie_algebra.orthogonal.so`
  * `lie_algebra.orthogonal.so'`
  * `lie_algebra.orthogonal.so_indefinite_equiv`
  * `lie_algebra.orthogonal.type_D`
  * `lie_algebra.orthogonal.type_B`
  * `lie_algebra.orthogonal.type_D_equiv_so'`
  * `lie_algebra.orthogonal.type_B_equiv_so'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lie_equiv_matrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
the `2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `type_D_equiv_so'`, `so_indefinite_equiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/

namespace lie_algebra


@[simp] theorem matrix_trace_commutator_zero (n : Type u_1) (R : Type u₂) [fintype n]
    [DecidableEq n] [comm_ring R] (X : matrix n n R) (Y : matrix n n R) :
    coe_fn (matrix.trace n R R) (has_bracket.bracket X Y) = 0 :=
  sorry

namespace special_linear


/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl (n : Type u_1) (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R] :
    lie_subalgebra R (matrix n n R) :=
  lie_subalgebra.mk (submodule.carrier (linear_map.ker (matrix.trace n R R))) sorry sorry sorry
    sorry

theorem sl_bracket (n : Type u_1) (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    (A : ↥(sl n R)) (B : ↥(sl n R)) :
    subtype.val (has_bracket.bracket A B) =
        matrix.mul (subtype.val A) (subtype.val B) - matrix.mul (subtype.val B) (subtype.val A) :=
  rfl

/-- It is useful to define these matrices for explicit calculations in sl n R. -/
def E {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R] (i : n) (j : n) :
    matrix n n R :=
  fun (i' j' : n) => ite (i = i' ∧ j = j') 1 0

@[simp] theorem E_apply_one {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    (i : n) (j : n) : E R i j i j = 1 :=
  if_pos { left := rfl, right := rfl }

@[simp] theorem E_apply_zero {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    (i : n) (j : n) (i' : n) (j' : n) (h : ¬(i = i' ∧ j = j')) : E R i j i' j' = 0 :=
  if_neg h

@[simp] theorem E_diag_zero {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    (i : n) (j : n) (h : j ≠ i) : coe_fn (matrix.diag n R R) (E R i j) = 0 :=
  sorry

theorem E_trace_zero {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R] (i : n)
    (j : n) (h : j ≠ i) : coe_fn (matrix.trace n R R) (E R i j) = 0 :=
  sorry

/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def Eb {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R] (i : n) (j : n)
    (h : j ≠ i) : ↥(sl n R) :=
  { val := E R i j, property := sorry }

@[simp] theorem Eb_val {n : Type u_1} (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    (i : n) (j : n) (h : j ≠ i) : subtype.val (Eb R i j h) = E R i j :=
  rfl

theorem sl_non_abelian (n : Type u_1) (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    [nontrivial R] (h : 1 < fintype.card n) : ¬is_lie_abelian ↥(sl n R) :=
  sorry

end special_linear


namespace symplectic


/-- The matrix defining the canonical skew-symmetric bilinear form. -/
def J (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix (l ⊕ l) (l ⊕ l) R :=
  matrix.from_blocks 0 (-1) 1 0

/-- The symplectic Lie algebra: skew-adjoint matrices with respect to the canonical skew-symmetric
bilinear form. -/
def sp (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    lie_subalgebra R (matrix (l ⊕ l) (l ⊕ l) R) :=
  skew_adjoint_matrices_lie_subalgebra (J l R)

end symplectic


namespace orthogonal


/-- The definite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the identity matrix. -/
def so (n : Type u_1) (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R] :
    lie_subalgebra R (matrix n n R) :=
  skew_adjoint_matrices_lie_subalgebra 1

@[simp] theorem mem_so (n : Type u_1) (R : Type u₂) [fintype n] [DecidableEq n] [comm_ring R]
    (A : matrix n n R) : A ∈ so n R ↔ matrix.transpose A = -A :=
  sorry

/-- The indefinite diagonal matrix with `p` 1s and `q` -1s. -/
def indefinite_diagonal (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p] [fintype q]
    [DecidableEq p] [DecidableEq q] [comm_ring R] : matrix (p ⊕ q) (p ⊕ q) R :=
  matrix.diagonal (sum.elim (fun (_x : p) => 1) fun (_x : q) => -1)

/-- The indefinite orthogonal Lie subalgebra: skew-adjoint matrices with respect to the symmetric
bilinear form defined by the indefinite diagonal matrix. -/
def so' (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p] [fintype q] [DecidableEq p]
    [DecidableEq q] [comm_ring R] : lie_subalgebra R (matrix (p ⊕ q) (p ⊕ q) R) :=
  skew_adjoint_matrices_lie_subalgebra (indefinite_diagonal p q R)

/-- A matrix for transforming the indefinite diagonal bilinear form into the definite one, provided
the parameter `i` is a square root of -1. -/
def Pso (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p] [fintype q] [DecidableEq p]
    [DecidableEq q] [comm_ring R] (i : R) : matrix (p ⊕ q) (p ⊕ q) R :=
  matrix.diagonal (sum.elim (fun (_x : p) => 1) fun (_x : q) => i)

theorem Pso_inv (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p] [fintype q] [DecidableEq p]
    [DecidableEq q] [comm_ring R] {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 :=
  sorry

theorem is_unit_Pso (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p] [fintype q]
    [DecidableEq p] [DecidableEq q] [comm_ring R] {i : R} (hi : i * i = -1) :
    is_unit (Pso p q R i) :=
  sorry

theorem indefinite_diagonal_transform (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p]
    [fintype q] [DecidableEq p] [DecidableEq q] [comm_ring R] {i : R} (hi : i * i = -1) :
    matrix.mul (matrix.mul (matrix.transpose (Pso p q R i)) (indefinite_diagonal p q R))
          (Pso p q R i) =
        1 :=
  sorry

/-- An equivalence between the indefinite and definite orthogonal Lie algebras, over a ring
containing a square root of -1. -/
def so_indefinite_equiv (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p] [fintype q]
    [DecidableEq p] [DecidableEq q] [comm_ring R] {i : R} (hi : i * i = -1) :
    equiv R ↥(so' p q R) ↥(so (p ⊕ q) R) :=
  equiv.trans
    (skew_adjoint_matrices_lie_subalgebra_equiv (indefinite_diagonal p q R) (Pso p q R i) sorry)
    (equiv.of_eq
      (skew_adjoint_matrices_lie_subalgebra
        (matrix.mul (matrix.mul (matrix.transpose (Pso p q R i)) (indefinite_diagonal p q R))
          (Pso p q R i)))
      (so (p ⊕ q) R) sorry)

theorem so_indefinite_equiv_apply (p : Type u_2) (q : Type u_3) (R : Type u₂) [fintype p]
    [fintype q] [DecidableEq p] [DecidableEq q] [comm_ring R] {i : R} (hi : i * i = -1)
    (A : ↥(so' p q R)) :
    ↑(coe_fn (so_indefinite_equiv p q R hi) A) =
        matrix.mul (matrix.mul (Pso p q R i⁻¹) ↑A) (Pso p q R i) :=
  sorry

/-- A matrix defining a canonical even-rank symmetric bilinear form.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 0 1 ]  
   [ 1 0 ]
-/
def JD (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix (l ⊕ l) (l ⊕ l) R :=
  matrix.from_blocks 0 1 1 0

/-- The classical Lie algebra of type D as a Lie subalgebra of matrices associated to the matrix
`JD`. -/
def type_D (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    lie_subalgebra R (matrix (l ⊕ l) (l ⊕ l) R) :=
  skew_adjoint_matrices_lie_subalgebra (JD l R)

/-- A matrix transforming the bilinear form defined by the matrix `JD` into a split-signature
diagonal matrix.

It looks like this as a `2l x 2l` matrix of `l x l` blocks:

   [ 1 -1 ]  
   [ 1  1 ]
-/
def PD (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix (l ⊕ l) (l ⊕ l) R :=
  matrix.from_blocks 1 (-1) 1 1

/-- The split-signature diagonal matrix. -/
def S (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix (l ⊕ l) (l ⊕ l) R :=
  indefinite_diagonal l l R

theorem S_as_blocks (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    S l R = matrix.from_blocks 1 0 0 (-1) :=
  sorry

theorem JD_transform (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix.mul (matrix.mul (matrix.transpose (PD l R)) (JD l R)) (PD l R) = bit0 1 • S l R :=
  sorry

theorem PD_inv (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R]
    [invertible (bit0 1)] : PD l R * ⅟ • matrix.transpose (PD l R) = 1 :=
  sorry

theorem is_unit_PD (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R]
    [invertible (bit0 1)] : is_unit (PD l R) :=
  sorry

/-- An equivalence between two possible definitions of the classical Lie algebra of type D. -/
def type_D_equiv_so' (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R]
    [invertible (bit0 1)] : equiv R ↥(type_D l R) ↥(so' l l R) :=
  equiv.trans (skew_adjoint_matrices_lie_subalgebra_equiv (JD l R) (PD l R) sorry)
    (equiv.of_eq
      (skew_adjoint_matrices_lie_subalgebra
        (matrix.mul (matrix.mul (matrix.transpose (PD l R)) (JD l R)) (PD l R)))
      (so' l l R) sorry)

/-- A matrix defining a canonical odd-rank symmetric bilinear form.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 2 0 0 ]  
   [ 0 0 1 ]  
   [ 0 1 0 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]  
   [`l x 1` `l x l` `l x l`]  
   [`l x 1` `l x l` `l x l`]
-/
def JB (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix (Unit ⊕ l ⊕ l) (Unit ⊕ l ⊕ l) R :=
  matrix.from_blocks (bit0 1 • 1) 0 0 (JD l R)

/-- The classical Lie algebra of type B as a Lie subalgebra of matrices associated to the matrix
`JB`. -/
def type_B (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    lie_subalgebra R (matrix (Unit ⊕ l ⊕ l) (Unit ⊕ l ⊕ l) R) :=
  skew_adjoint_matrices_lie_subalgebra (JB l R)

/-- A matrix transforming the bilinear form defined by the matrix `JB` into an
almost-split-signature diagonal matrix.

It looks like this as a `(2l+1) x (2l+1)` matrix of blocks:

   [ 1 0  0 ]  
   [ 0 1 -1 ]  
   [ 0 1  1 ]

where sizes of the blocks are:

   [`1 x 1` `1 x l` `1 x l`]  
   [`l x 1` `l x l` `l x l`]  
   [`l x 1` `l x l` `l x l`]
-/
def PB (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix (Unit ⊕ l ⊕ l) (Unit ⊕ l ⊕ l) R :=
  matrix.from_blocks 1 0 0 (PD l R)

theorem PB_inv (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R]
    [invertible (bit0 1)] : PB l R * matrix.from_blocks 1 0 0 (PD l R⁻¹) = 1 :=
  sorry

theorem is_unit_PB (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R]
    [invertible (bit0 1)] : is_unit (PB l R) :=
  sorry

theorem JB_transform (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R] :
    matrix.mul (matrix.mul (matrix.transpose (PB l R)) (JB l R)) (PB l R) =
        bit0 1 • matrix.from_blocks 1 0 0 (S l R) :=
  sorry

theorem indefinite_diagonal_assoc (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l]
    [comm_ring R] :
    indefinite_diagonal (Unit ⊕ l) l R =
        coe_fn (matrix.reindex_lie_equiv (equiv.symm (equiv.sum_assoc Unit l l)))
          (matrix.from_blocks 1 0 0 (indefinite_diagonal l l R)) :=
  sorry

/-- An equivalence between two possible definitions of the classical Lie algebra of type B. -/
def type_B_equiv_so' (l : Type u_4) (R : Type u₂) [fintype l] [DecidableEq l] [comm_ring R]
    [invertible (bit0 1)] : equiv R ↥(type_B l R) ↥(so' (Unit ⊕ l) l R) :=
  equiv.trans (skew_adjoint_matrices_lie_subalgebra_equiv (JB l R) (PB l R) sorry)
    (equiv.symm
      (equiv.trans
        (skew_adjoint_matrices_lie_subalgebra_equiv_transpose (indefinite_diagonal (Unit ⊕ l) l R)
          (matrix.reindex_alg_equiv (equiv.sum_assoc PUnit l l)) sorry)
        (equiv.of_eq
          (skew_adjoint_matrices_lie_subalgebra
            (coe_fn (matrix.reindex_alg_equiv (equiv.sum_assoc PUnit l l))
              (indefinite_diagonal (Unit ⊕ l) l R)))
          (skew_adjoint_matrices_lie_subalgebra
            (matrix.mul (matrix.mul (matrix.transpose (PB l R)) (JB l R)) (PB l R)))
          sorry)))

end Mathlib