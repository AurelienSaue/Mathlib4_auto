/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Tim Baanen.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.associated
import Mathlib.linear_algebra.determinant
import Mathlib.tactic.linarith.default
import Mathlib.tactic.ring_exp
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible
determinant. For matrices that are not square or not of full rank, there is a
more general notion of pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
The adjugate is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the determinants of each minor of `A`.
Instead of defining a minor to be `A` with row `i` and column `j` deleted, we
replace the `i`th row of `A` with the `j`th basis vector; this has the same
determinant as the minor but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`. Finally, we show that dividing
the adjugate by `det A` (if possible), giving a matrix `nonsing_inv A`, will
result in a multiplicative inverse to `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

namespace matrix


/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/

/--
  `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer_map A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramer_map {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (b : n → α) (i : n) : α :=
  det (update_column A i b)

theorem cramer_map_is_linear {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (i : n) : is_linear_map α fun (b : n → α) => cramer_map A b i := sorry

theorem cramer_is_linear {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : is_linear_map α (cramer_map A) :=
  is_linear_map.mk (fun (x y : n → α) => funext fun (i : n) => is_linear_map.map_add (cramer_map_is_linear A i) x y)
    fun (c : α) (x : n → α) => funext fun (i : n) => is_linear_map.map_smul (cramer_map_is_linear A i) c x

/--
  `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : linear_map α (n → α) (n → α) :=
  is_linear_map.mk' (cramer_map A) sorry

theorem cramer_apply {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (b : n → α) (i : n) : coe_fn (cramer A) b i = det (update_column A i b) :=
  rfl

theorem cramer_transpose_row_self {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (i : n) : coe_fn (cramer (transpose A)) (A i) = fun (j : n) => ite (i = j) (det A) 0 := sorry

/-- Use linearity of `cramer` to take it out of a summation. -/
theorem sum_cramer {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) {β : Type u_1} (s : finset β) (f : β → n → α) : (finset.sum s fun (x : β) => coe_fn (cramer A) (f x)) = coe_fn (cramer A) (finset.sum s fun (x : β) => f x) :=
  Eq.symm (linear_map.map_sum (cramer A))

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
theorem sum_cramer_apply {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) {β : Type u_1} (s : finset β) (f : n → β → α) (i : n) : (finset.sum s fun (x : β) => coe_fn (cramer A) (fun (j : n) => f j x) i) =
  coe_fn (cramer A) (fun (j : n) => finset.sum s fun (x : β) => f j x) i := sorry

/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring,
while the `inv` section is specifically for invertible matrices.
-/

/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we define the
  minor as replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : matrix n n α :=
  fun (i : n) => coe_fn (cramer (transpose A)) fun (j : n) => ite (i = j) 1 0

theorem adjugate_def {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : adjugate A = fun (i : n) => coe_fn (cramer (transpose A)) fun (j : n) => ite (i = j) 1 0 :=
  rfl

theorem adjugate_apply {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (i : n) (j : n) : adjugate A i j = det (update_row A j fun (j : n) => ite (i = j) 1 0) := sorry

theorem adjugate_transpose {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : transpose (adjugate A) = adjugate (transpose A) := sorry

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
theorem cramer_eq_adjugate_mul_vec {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (b : n → α) : coe_fn (cramer A) b = mul_vec (adjugate A) b := sorry

theorem mul_adjugate_apply {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (i : n) (j : n) (k : n) : A i k * adjugate A k j = coe_fn (cramer (transpose A)) (fun (j : n) => ite (k = j) (A i k) 0) j := sorry

theorem mul_adjugate {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : matrix.mul A (adjugate A) = det A • 1 := sorry

theorem adjugate_mul {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : matrix.mul (adjugate A) A = det A • 1 := sorry

/-- `det_adjugate_of_cancel` is an auxiliary lemma for computing `(adjugate A).det`,
  used in `det_adjugate_eq_one` and `det_adjugate_of_is_unit`.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_cancel` covers the case that `det A` cancels
  on the left of the equation `A.det * b = A.det ^ n`.
-/
theorem det_adjugate_of_cancel {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] {A : matrix n n α} (h : ∀ (b : α), det A * b = det A ^ fintype.card n → b = det A ^ (fintype.card n - 1)) : det (adjugate A) = det A ^ (fintype.card n - 1) := sorry

theorem adjugate_eq_one_of_card_eq_one {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] {A : matrix n n α} (h : fintype.card n = 1) : adjugate A = 1 := sorry

@[simp] theorem adjugate_zero {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (h : 1 < fintype.card n) : adjugate 0 = 0 := sorry

theorem det_adjugate_eq_one {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] {A : matrix n n α} (h : det A = 1) : det (adjugate A) = 1 := sorry

/-- `det_adjugate_of_is_unit` gives the formula for `(adjugate A).det` if `A.det` has an inverse.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_is_unit` covers the case that `det A` has an inverse.
-/
theorem det_adjugate_of_is_unit {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] {A : matrix n n α} (h : is_unit (det A)) : det (adjugate A) = det A ^ (fintype.card n - 1) := sorry

/-!
### `inv` section

Defines the matrix `nonsing_inv A` and proves it is the inverse matrix
of a square matrix `A` as long as `det A` has a multiplicative inverse.
-/

theorem is_unit_det_transpose {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : is_unit (det (transpose A)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_unit (det (transpose A)))) (det_transpose A))) h

/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
def nonsing_inv {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : matrix n n α :=
  dite (is_unit (det A)) (fun (h : is_unit (det A)) => ↑(is_unit.unit h⁻¹) • adjugate A) fun (h : ¬is_unit (det A)) => 0

protected instance has_inv {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] : has_inv (matrix n n α) :=
  has_inv.mk nonsing_inv

theorem nonsing_inv_apply {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : A⁻¹ = ↑(is_unit.unit h⁻¹) • adjugate A := sorry

theorem transpose_nonsing_inv {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : transpose (A⁻¹) = (transpose A⁻¹) := sorry

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp] theorem mul_nonsing_inv {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : matrix.mul A (A⁻¹) = 1 := sorry

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp] theorem nonsing_inv_mul {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : matrix.mul (A⁻¹) A = 1 := sorry

@[simp] theorem nonsing_inv_det {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : det (A⁻¹) * det A = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (det (A⁻¹) * det A = 1)) (Eq.symm (det_mul (A⁻¹) A))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (det (matrix.mul (A⁻¹) A) = 1)) (nonsing_inv_mul A h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (det 1 = 1)) det_one)) (Eq.refl 1)))

theorem is_unit_nonsing_inv_det {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : is_unit (det (A⁻¹)) :=
  is_unit_of_mul_eq_one (det (A⁻¹)) (det A) (nonsing_inv_det A h)

@[simp] theorem nonsing_inv_nonsing_inv {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : A⁻¹⁻¹ = A := sorry

/-- A matrix whose determinant is a unit is itself a unit. -/
def nonsing_inv_unit {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (h : is_unit (det A)) : units (matrix n n α) :=
  units.mk A (A⁻¹) sorry sorry

theorem is_unit_iff_is_unit_det {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) : is_unit A ↔ is_unit (det A) := sorry

theorem is_unit_det_of_left_inverse {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (B : matrix n n α) (h : matrix.mul B A = 1) : is_unit (det A) := sorry

theorem is_unit_det_of_right_inverse {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (B : matrix n n α) (h : matrix.mul A B = 1) : is_unit (det A) := sorry

theorem nonsing_inv_left_right {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (B : matrix n n α) (h : matrix.mul A B = 1) : matrix.mul B A = 1 := sorry

theorem nonsing_inv_right_left {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (B : matrix n n α) (h : matrix.mul B A = 1) : matrix.mul A B = 1 :=
  nonsing_inv_left_right B A h

/- One form of Cramer's rule. -/

@[simp] theorem det_smul_inv_mul_vec_eq_cramer {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (b : n → α) (h : is_unit (det A)) : det A • mul_vec (A⁻¹) b = coe_fn (cramer A) b := sorry

/- A stronger form of Cramer's rule that allows us to solve some instances of `A ⬝ x = b` even if
the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/

@[simp] theorem mul_vec_cramer {n : Type u} [DecidableEq n] [fintype n] {α : Type v} [comm_ring α] (A : matrix n n α) (b : n → α) : mul_vec A (coe_fn (cramer A) b) = det A • b := sorry

