/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.matrix.basic
import Mathlib.data.pequiv
import Mathlib.PostPort

universes u_3 u_4 v u_2 u_1 

namespace Mathlib

/-
# partial equivalences for matrices

Using partial equivalences to represent matrices.
This file introduces the function `pequiv.to_matrix`, which returns a matrix containing ones and
zeros. For any partial equivalence `f`, `f.to_matrix i j = 1 ↔ f i = some j`.

The following important properties of this function are proved
`to_matrix_trans : (f.trans g).to_matrix = f.to_matrix ⬝ g.to_matrix`
`to_matrix_symm  : f.symm.to_matrix = f.to_matrixᵀ`
`to_matrix_refl : (pequiv.refl n).to_matrix = 1`
`to_matrix_bot : ⊥.to_matrix = 0`

This theory gives the matrix representation of projection linear maps, and their right inverses.
For example, the matrix `(single (0 : fin 1) (i : fin n)).to_matrix` corresponds to the the ith
projection map from R^n to R.

Any injective function `fin m → fin n` gives rise to a `pequiv`, whose matrix is the projection
map from R^m → R^n represented by the same function. The transpose of this matrix is the right
inverse of this map, sending anything not in the image to zero.

## notations

This file uses the notation ` ⬝ ` for `matrix.mul` and `ᵀ` for `matrix.transpose`.
-/

namespace pequiv


/-- `to_matrix` returns a matrix containing ones and zeros. `f.to_matrix i j` is `1` if
  `f i = some j` and `0` otherwise -/
def to_matrix {m : Type u_3} {n : Type u_4} [fintype m] [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] (f : m ≃. n) : matrix m n α :=
  sorry

theorem mul_matrix_apply {l : Type u_2} {m : Type u_3} {n : Type u_4} [fintype l] [fintype m] [fintype n] {α : Type v} [DecidableEq m] [semiring α] (f : l ≃. m) (M : matrix m n α) (i : l) (j : n) : matrix.mul (to_matrix f) M i j = option.cases_on (coe_fn f i) 0 fun (fi : m) => M fi j := sorry

theorem to_matrix_symm {m : Type u_3} {n : Type u_4} [fintype m] [fintype n] {α : Type v} [DecidableEq m] [DecidableEq n] [HasZero α] [HasOne α] (f : m ≃. n) : to_matrix (pequiv.symm f) = matrix.transpose (to_matrix f) := sorry

@[simp] theorem to_matrix_refl {n : Type u_4} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] : to_matrix (pequiv.refl n) = 1 := sorry

theorem matrix_mul_apply {l : Type u_2} {m : Type u_3} {n : Type u_4} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq n] (M : matrix l m α) (f : m ≃. n) (i : l) (j : n) : matrix.mul M (to_matrix f) i j = option.cases_on (coe_fn (pequiv.symm f) j) 0 fun (fj : m) => M i fj := sorry

theorem to_pequiv_mul_matrix {m : Type u_3} {n : Type u_4} [fintype m] [fintype n] {α : Type v} [DecidableEq m] [semiring α] (f : m ≃ m) (M : matrix m n α) : matrix.mul (to_matrix (equiv.to_pequiv f)) M = fun (i : m) => M (coe_fn f i) := sorry

theorem to_matrix_trans {l : Type u_2} {m : Type u_3} {n : Type u_4} [fintype l] [fintype m] [fintype n] {α : Type v} [DecidableEq m] [DecidableEq n] [semiring α] (f : l ≃. m) (g : m ≃. n) : to_matrix (pequiv.trans f g) = matrix.mul (to_matrix f) (to_matrix g) := sorry

@[simp] theorem to_matrix_bot {m : Type u_3} {n : Type u_4} [fintype m] [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] : to_matrix ⊥ = 0 :=
  rfl

theorem to_matrix_injective {m : Type u_3} {n : Type u_4} [fintype m] [fintype n] {α : Type v} [DecidableEq n] [monoid_with_zero α] [nontrivial α] : function.injective to_matrix := sorry

theorem to_matrix_swap {n : Type u_4} [fintype n] {α : Type v} [DecidableEq n] [ring α] (i : n) (j : n) : to_matrix (equiv.to_pequiv (equiv.swap i j)) =
  1 - to_matrix (single i i) - to_matrix (single j j) + to_matrix (single i j) + to_matrix (single j i) := sorry

@[simp] theorem single_mul_single {k : Type u_1} {m : Type u_3} {n : Type u_4} [fintype k] [fintype m] [fintype n] {α : Type v} [DecidableEq k] [DecidableEq m] [DecidableEq n] [semiring α] (a : m) (b : n) (c : k) : matrix.mul (to_matrix (single a b)) (to_matrix (single b c)) = to_matrix (single a c) := sorry

theorem single_mul_single_of_ne {k : Type u_1} {m : Type u_3} {n : Type u_4} [fintype k] [fintype m] [fintype n] {α : Type v} [DecidableEq k] [DecidableEq m] [DecidableEq n] [semiring α] {b₁ : n} {b₂ : n} (hb : b₁ ≠ b₂) (a : m) (c : k) : matrix.mul (to_matrix (single a b₁)) (to_matrix (single b₂ c)) = 0 := sorry

/-- Restatement of `single_mul_single`, which will simplify expressions in `simp` normal form,
  when associativity may otherwise need to be carefully applied. -/
@[simp] theorem single_mul_single_right {k : Type u_1} {l : Type u_2} {m : Type u_3} {n : Type u_4} [fintype k] [fintype l] [fintype m] [fintype n] {α : Type v} [DecidableEq k] [DecidableEq m] [DecidableEq n] [semiring α] (a : m) (b : n) (c : k) (M : matrix k l α) : matrix.mul (to_matrix (single a b)) (matrix.mul (to_matrix (single b c)) M) = matrix.mul (to_matrix (single a c)) M := sorry

/-- We can also define permutation matrices by permuting the rows of the identity matrix. -/
theorem equiv_to_pequiv_to_matrix {n : Type u_4} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] (σ : n ≃ n) (i : n) (j : n) : to_matrix (equiv.to_pequiv σ) i j = HasOne.one (coe_fn σ i) j :=
  if_congr option.some_inj rfl rfl

