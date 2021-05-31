/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.big_operators.pi
import Mathlib.algebra.module.pi
import Mathlib.algebra.module.linear_map
import Mathlib.algebra.big_operators.ring
import Mathlib.algebra.star.basic
import Mathlib.data.equiv.ring
import Mathlib.data.fintype.card
import Mathlib.PostPort

universes u u' v u_2 u_3 w u_1 u_4 u_5 u_6 

namespace Mathlib

/-!
# Matrices
-/

/-- `matrix m n` is the type of matrices whose rows are indexed by the fintype `m`
    and whose columns are indexed by the fintype `n`. -/
def matrix (m : Type u) (n : Type u') [fintype m] [fintype n] (α : Type v) :=
  m → n → α

namespace matrix


theorem ext_iff {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix m n α} {N : matrix m n α} : (∀ (i : m) (j : n), M i j = N i j) ↔ M = N := sorry

theorem ext {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix m n α} {N : matrix m n α} : (∀ (i : m) (j : n), M i j = N i j) → M = N :=
  iff.mp ext_iff

/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`. -/
def map {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} (M : matrix m n α) {β : Type w} (f : α → β) : matrix m n β :=
  fun (i : m) (j : n) => f (M i j)

@[simp] theorem map_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix m n α} {β : Type w} {f : α → β} {i : m} {j : n} : map M f i j = f (M i j) :=
  rfl

@[simp] theorem map_map {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix m n α} {β : Type u_1} {γ : Type u_4} {f : α → β} {g : β → γ} : map (map M f) g = map M (g ∘ f) := sorry

/-- The transpose of a matrix. -/
def transpose {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} (M : matrix m n α) : matrix n m α :=
  sorry

/-- `matrix.col u` is the column matrix whose entries are given by `u`. -/
def col {m : Type u_2} [fintype m] {α : Type v} (w : m → α) : matrix m Unit α :=
  sorry

/-- `matrix.row u` is the row matrix whose entries are given by `u`. -/
def row {n : Type u_3} [fintype n] {α : Type v} (v : n → α) : matrix Unit n α :=
  sorry

protected instance inhabited {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Inhabited α] : Inhabited (matrix m n α) :=
  pi.inhabited m

protected instance has_add {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Add α] : Add (matrix m n α) :=
  pi.has_add

protected instance add_semigroup {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_semigroup α] : add_semigroup (matrix m n α) :=
  pi.add_semigroup

protected instance add_comm_semigroup {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) :=
  pi.add_comm_semigroup

protected instance has_zero {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [HasZero α] : HasZero (matrix m n α) :=
  pi.has_zero

protected instance add_monoid {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_monoid α] : add_monoid (matrix m n α) :=
  pi.add_monoid

protected instance add_comm_monoid {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_comm_monoid α] : add_comm_monoid (matrix m n α) :=
  pi.add_comm_monoid

protected instance has_neg {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Neg α] : Neg (matrix m n α) :=
  pi.has_neg

protected instance has_sub {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Sub α] : Sub (matrix m n α) :=
  pi.has_sub

protected instance add_group {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_group α] : add_group (matrix m n α) :=
  pi.add_group

protected instance add_comm_group {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_comm_group α] : add_comm_group (matrix m n α) :=
  pi.add_comm_group

@[simp] theorem zero_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [HasZero α] (i : m) (j : n) : HasZero.zero i j = 0 :=
  rfl

@[simp] theorem neg_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Neg α] (M : matrix m n α) (i : m) (j : n) : Neg.neg M i j = -M i j :=
  rfl

@[simp] theorem add_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Add α] (M : matrix m n α) (N : matrix m n α) (i : m) (j : n) : Add.add M N i j = M i j + N i j :=
  rfl

@[simp] theorem sub_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Sub α] (M : matrix m n α) (N : matrix m n α) (i : m) (j : n) : Sub.sub M N i j = M i j - N i j :=
  rfl

@[simp] theorem map_zero {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [HasZero α] {β : Type w} [HasZero β] {f : α → β} (h : f 0 = 0) : map 0 f = 0 := sorry

theorem map_add {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_monoid α] {β : Type w} [add_monoid β] (f : α →+ β) (M : matrix m n α) (N : matrix m n α) : map (M + N) ⇑f = map M ⇑f + map N ⇑f := sorry

theorem map_sub {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_group α] {β : Type w} [add_group β] (f : α →+ β) (M : matrix m n α) (N : matrix m n α) : map (M - N) ⇑f = map M ⇑f - map N ⇑f := sorry

theorem subsingleton_of_empty_left {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} (hm : ¬Nonempty m) : subsingleton (matrix m n α) := sorry

theorem subsingleton_of_empty_right {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} (hn : ¬Nonempty n) : subsingleton (matrix m n α) := sorry

end matrix


/-- The `add_monoid_hom` between spaces of matrices induced by an `add_monoid_hom` between their
coefficients. -/
def add_monoid_hom.map_matrix {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_monoid α] {β : Type w} [add_monoid β] (f : α →+ β) : matrix m n α →+ matrix m n β :=
  add_monoid_hom.mk (fun (M : matrix m n α) => matrix.map M ⇑f) sorry (matrix.map_add f)

@[simp] theorem add_monoid_hom.map_matrix_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_monoid α] {β : Type w} [add_monoid β] (f : α →+ β) (M : matrix m n α) : coe_fn (add_monoid_hom.map_matrix f) M = matrix.map M ⇑f :=
  rfl

namespace matrix


/-- `diagonal d` is the square matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
if `i ≠ j`. -/
def diagonal {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] (d : n → α) : matrix n n α :=
  fun (i j : n) => ite (i = j) (d i) 0

@[simp] theorem diagonal_apply_eq {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] {d : n → α} (i : n) : diagonal d i i = d i := sorry

@[simp] theorem diagonal_apply_ne {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] {d : n → α} {i : n} {j : n} (h : i ≠ j) : diagonal d i j = 0 := sorry

theorem diagonal_apply_ne' {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] {d : n → α} {i : n} {j : n} (h : j ≠ i) : diagonal d i j = 0 :=
  diagonal_apply_ne (ne.symm h)

@[simp] theorem diagonal_zero {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] : (diagonal fun (_x : n) => 0) = 0 := sorry

@[simp] theorem diagonal_transpose {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] (v : n → α) : transpose (diagonal v) = diagonal v := sorry

@[simp] theorem diagonal_add {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [add_monoid α] (d₁ : n → α) (d₂ : n → α) : diagonal d₁ + diagonal d₂ = diagonal fun (i : n) => d₁ i + d₂ i := sorry

@[simp] theorem diagonal_map {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] {β : Type w} [HasZero α] [HasZero β] {f : α → β} (h : f 0 = 0) {d : n → α} : map (diagonal d) f = diagonal fun (m : n) => f (d m) := sorry

protected instance has_one {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] : HasOne (matrix n n α) :=
  { one := diagonal fun (_x : n) => 1 }

@[simp] theorem diagonal_one {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] : (diagonal fun (_x : n) => 1) = 1 :=
  rfl

theorem one_apply {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] {i : n} {j : n} : HasOne.one i j = ite (i = j) 1 0 :=
  rfl

@[simp] theorem one_apply_eq {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] (i : n) : HasOne.one i i = 1 :=
  diagonal_apply_eq i

@[simp] theorem one_apply_ne {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] {i : n} {j : n} : i ≠ j → HasOne.one i j = 0 :=
  diagonal_apply_ne

theorem one_apply_ne' {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] {i : n} {j : n} : j ≠ i → HasOne.one i j = 0 :=
  diagonal_apply_ne'

@[simp] theorem one_map {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] {β : Type w} [HasZero β] [HasOne β] {f : α → β} (h₀ : f 0 = 0) (h₁ : f 1 = 1) : map 1 f = 1 := sorry

@[simp] theorem bit0_apply {m : Type u_2} [fintype m] {α : Type v} [Add α] (M : matrix m m α) (i : m) (j : m) : bit0 M i j = bit0 (M i j) :=
  rfl

theorem bit1_apply {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [add_monoid α] [HasOne α] (M : matrix n n α) (i : n) (j : n) : bit1 M i j = ite (i = j) (bit1 (M i j)) (bit0 (M i j)) := sorry

@[simp] theorem bit1_apply_eq {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [add_monoid α] [HasOne α] (M : matrix n n α) (i : n) : bit1 M i i = bit1 (M i i) := sorry

@[simp] theorem bit1_apply_ne {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [add_monoid α] [HasOne α] (M : matrix n n α) {i : n} {j : n} (h : i ≠ j) : bit1 M i j = bit0 (M i j) := sorry

/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dot_product {m : Type u_2} [fintype m] {α : Type v} [Mul α] [add_comm_monoid α] (v : m → α) (w : m → α) : α :=
  finset.sum finset.univ fun (i : m) => v i * w i

theorem dot_product_assoc {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (u : m → α) (v : m → n → α) (w : n → α) : dot_product (fun (j : n) => dot_product u fun (i : m) => v i j) w = dot_product u fun (i : m) => dot_product (v i) w := sorry

theorem dot_product_comm {m : Type u_2} [fintype m] {α : Type v} [comm_semiring α] (v : m → α) (w : m → α) : dot_product v w = dot_product w v := sorry

@[simp] theorem dot_product_punit {α : Type v} [add_comm_monoid α] [Mul α] (v : PUnit → α) (w : PUnit → α) : dot_product v w = v PUnit.unit * w PUnit.unit := sorry

@[simp] theorem dot_product_zero {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) : dot_product v 0 = 0 := sorry

@[simp] theorem dot_product_zero' {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) : (dot_product v fun (_x : m) => 0) = 0 :=
  dot_product_zero v

@[simp] theorem zero_dot_product {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) : dot_product 0 v = 0 := sorry

@[simp] theorem zero_dot_product' {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) : dot_product (fun (_x : m) => 0) v = 0 :=
  zero_dot_product v

@[simp] theorem add_dot_product {m : Type u_2} [fintype m] {α : Type v} [semiring α] (u : m → α) (v : m → α) (w : m → α) : dot_product (u + v) w = dot_product u w + dot_product v w := sorry

@[simp] theorem dot_product_add {m : Type u_2} [fintype m] {α : Type v} [semiring α] (u : m → α) (v : m → α) (w : m → α) : dot_product u (v + w) = dot_product u v + dot_product u w := sorry

@[simp] theorem diagonal_dot_product {m : Type u_2} [fintype m] {α : Type v} [DecidableEq m] [semiring α] (v : m → α) (w : m → α) (i : m) : dot_product (diagonal v i) w = v i * w i := sorry

@[simp] theorem dot_product_diagonal {m : Type u_2} [fintype m] {α : Type v} [DecidableEq m] [semiring α] (v : m → α) (w : m → α) (i : m) : dot_product v (diagonal w i) = v i * w i := sorry

@[simp] theorem dot_product_diagonal' {m : Type u_2} [fintype m] {α : Type v} [DecidableEq m] [semiring α] (v : m → α) (w : m → α) (i : m) : (dot_product v fun (j : m) => diagonal w j i) = v i * w i := sorry

@[simp] theorem neg_dot_product {m : Type u_2} [fintype m] {α : Type v} [ring α] (v : m → α) (w : m → α) : dot_product (-v) w = -dot_product v w := sorry

@[simp] theorem dot_product_neg {m : Type u_2} [fintype m] {α : Type v} [ring α] (v : m → α) (w : m → α) : dot_product v (-w) = -dot_product v w := sorry

@[simp] theorem smul_dot_product {m : Type u_2} [fintype m] {α : Type v} [semiring α] (x : α) (v : m → α) (w : m → α) : dot_product (x • v) w = x * dot_product v w := sorry

@[simp] theorem dot_product_smul {m : Type u_2} [fintype m] {α : Type v} [comm_semiring α] (x : α) (v : m → α) (w : m → α) : dot_product v (x • w) = x * dot_product v w := sorry

/-- `M ⬝ N` is the usual product of matrices `M` and `N`, i.e. we have that
    `(M ⬝ N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `Ǹ`. -/
protected def mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [Mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) : matrix l n α :=
  fun (i : l) (k : n) => dot_product (fun (j : m) => M i j) fun (j : m) => N j k

theorem mul_apply {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [Mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i : l} {k : n} : matrix.mul M N i k = finset.sum finset.univ fun (j : m) => M i j * N j k :=
  rfl

protected instance has_mul {n : Type u_3} [fintype n] {α : Type v} [Mul α] [add_comm_monoid α] : Mul (matrix n n α) :=
  { mul := matrix.mul }

@[simp] theorem mul_eq_mul {n : Type u_3} [fintype n] {α : Type v} [Mul α] [add_comm_monoid α] (M : matrix n n α) (N : matrix n n α) : M * N = matrix.mul M N :=
  rfl

theorem mul_apply' {n : Type u_3} [fintype n] {α : Type v} [Mul α] [add_comm_monoid α] {M : matrix n n α} {N : matrix n n α} {i : n} {k : n} : matrix.mul M N i k = dot_product (fun (j : n) => M i j) fun (j : n) => N j k :=
  rfl

protected theorem mul_assoc {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) : matrix.mul (matrix.mul L M) N = matrix.mul L (matrix.mul M N) :=
  ext
    fun (i : l) (j : o) =>
      dot_product_assoc (fun (j : m) => L i j) (fun (i : m) (j : n) => M i j) fun (j_1 : n) => N j_1 j

protected instance semigroup {n : Type u_3} [fintype n] {α : Type v} [semiring α] : semigroup (matrix n n α) :=
  semigroup.mk Mul.mul matrix.mul_assoc

@[simp] theorem diagonal_neg {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [add_group α] (d : n → α) : -diagonal d = diagonal fun (i : n) => -d i := sorry

@[simp] protected theorem mul_zero {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (M : matrix m n α) : matrix.mul M 0 = 0 :=
  ext fun (i : m) (j : o) => dot_product_zero fun (j : n) => M i j

@[simp] protected theorem zero_mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) : matrix.mul 0 M = 0 :=
  ext fun (i : l) (j : n) => zero_dot_product fun (j_1 : m) => M j_1 j

protected theorem mul_add {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (L : matrix m n α) (M : matrix n o α) (N : matrix n o α) : matrix.mul L (M + N) = matrix.mul L M + matrix.mul L N :=
  ext fun (i : m) (j : o) => dot_product_add (fun (j : n) => L i j) (fun (i : n) => M i j) fun (i : n) => N i j

protected theorem add_mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] (L : matrix l m α) (M : matrix l m α) (N : matrix m n α) : matrix.mul (L + M) N = matrix.mul L N + matrix.mul M N :=
  ext
    fun (i : l) (j : n) => add_dot_product (fun (i_1 : m) => L i i_1) (fun (i_1 : m) => M i i_1) fun (j_1 : m) => N j_1 j

@[simp] theorem diagonal_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] (d : m → α) (M : matrix m n α) (i : m) (j : n) : matrix.mul (diagonal d) M i j = d i * M i j :=
  diagonal_dot_product (fun (i : m) => d i) (fun (j_1 : m) => M j_1 j) i

@[simp] theorem mul_diagonal {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq n] (d : n → α) (M : matrix m n α) (i : m) (j : n) : matrix.mul M (diagonal d) i j = M i j * d j :=
  eq.mpr (id (Eq._oldrec (Eq.refl (matrix.mul M (diagonal d) i j = M i j * d j)) (Eq.symm (diagonal_transpose d))))
    (dot_product_diagonal (fun (j : n) => M i j) (fun (j : n) => d j) j)

@[simp] protected theorem one_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] (M : matrix m n α) : matrix.mul 1 M = M := sorry

@[simp] protected theorem mul_one {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq n] (M : matrix m n α) : matrix.mul M 1 = M := sorry

protected instance monoid {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] : monoid (matrix n n α) :=
  monoid.mk semigroup.mul sorry 1 sorry sorry

protected instance semiring {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] : semiring (matrix n n α) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry monoid.one sorry sorry
    matrix.zero_mul matrix.mul_zero matrix.mul_add matrix.add_mul

@[simp] theorem diagonal_mul_diagonal {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] (d₁ : n → α) (d₂ : n → α) : matrix.mul (diagonal d₁) (diagonal d₂) = diagonal fun (i : n) => d₁ i * d₂ i := sorry

theorem diagonal_mul_diagonal' {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] (d₁ : n → α) (d₂ : n → α) : diagonal d₁ * diagonal d₂ = diagonal fun (i : n) => d₁ i * d₂ i :=
  diagonal_mul_diagonal d₁ d₂

@[simp] theorem map_mul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] {L : matrix m n α} {M : matrix n o α} {β : Type w} [semiring β] {f : α →+* β} : map (matrix.mul L M) ⇑f = matrix.mul (map L ⇑f) (map M ⇑f) := sorry

-- TODO: there should be a way to avoid restating these for each `foo_hom`. 

/-- A version of `one_map` where `f` is a ring hom. -/
@[simp] theorem ring_hom_map_one {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] {β : Type w} [semiring β] (f : α →+* β) : map 1 ⇑f = 1 :=
  one_map (ring_hom.map_zero f) (ring_hom.map_one f)

/-- A version of `one_map` where `f` is a `ring_equiv`. -/
@[simp] theorem ring_equiv_map_one {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] {β : Type w} [semiring β] (f : α ≃+* β) : map 1 ⇑f = 1 :=
  one_map (ring_equiv.map_zero f) (ring_equiv.map_one f)

/-- A version of `map_zero` where `f` is a `zero_hom`. -/
@[simp] theorem zero_hom_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {β : Type w} [HasZero β] (f : zero_hom α β) : map 0 ⇑f = 0 :=
  map_zero (zero_hom.map_zero f)

/-- A version of `map_zero` where `f` is a `add_monoid_hom`. -/
@[simp] theorem add_monoid_hom_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {β : Type w} [add_monoid β] (f : α →+ β) : map 0 ⇑f = 0 :=
  map_zero (add_monoid_hom.map_zero f)

/-- A version of `map_zero` where `f` is a `add_equiv`. -/
@[simp] theorem add_equiv_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {β : Type w} [add_monoid β] (f : α ≃+ β) : map 0 ⇑f = 0 :=
  map_zero (add_equiv.map_zero f)

/-- A version of `map_zero` where `f` is a `linear_map`. -/
@[simp] theorem linear_map_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {R : Type u_1} [semiring R] {β : Type w} [add_comm_monoid β] [semimodule R α] [semimodule R β] (f : linear_map R α β) : map 0 ⇑f = 0 :=
  map_zero (linear_map.map_zero f)

/-- A version of `map_zero` where `f` is a `linear_equiv`. -/
@[simp] theorem linear_equiv_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {R : Type u_1} [semiring R] {β : Type w} [add_comm_monoid β] [semimodule R α] [semimodule R β] (f : linear_equiv R α β) : map 0 ⇑f = 0 :=
  map_zero (linear_equiv.map_zero f)

/-- A version of `map_zero` where `f` is a `ring_hom`. -/
@[simp] theorem ring_hom_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {β : Type w} [semiring β] (f : α →+* β) : map 0 ⇑f = 0 :=
  map_zero (ring_hom.map_zero f)

/-- A version of `map_zero` where `f` is a `ring_equiv`. -/
@[simp] theorem ring_equiv_map_zero {n : Type u_3} [fintype n] {α : Type v} [semiring α] {β : Type w} [semiring β] (f : α ≃+* β) : map 0 ⇑f = 0 :=
  map_zero (ring_equiv.map_zero f)

theorem is_add_monoid_hom_mul_left {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix l m α) : is_add_monoid_hom fun (x : matrix m n α) => matrix.mul M x :=
  is_add_monoid_hom.mk (matrix.mul_zero M)

theorem is_add_monoid_hom_mul_right {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) : is_add_monoid_hom fun (x : matrix l m α) => matrix.mul x M :=
  is_add_monoid_hom.mk (matrix.zero_mul M)

protected theorem sum_mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] {β : Type u_4} (s : finset β) (f : β → matrix l m α) (M : matrix m n α) : matrix.mul (finset.sum s fun (a : β) => f a) M = finset.sum s fun (a : β) => matrix.mul (f a) M :=
  Eq.symm (finset.sum_hom s fun (x : matrix l m α) => matrix.mul x M)

/- This line does not type-check without `id` and `: _`. Lean did not recognize that two different
  `add_monoid` instances were def-eq -/

protected theorem mul_sum {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] {β : Type u_4} (s : finset β) (f : β → matrix m n α) (M : matrix l m α) : matrix.mul M (finset.sum s fun (a : β) => f a) = finset.sum s fun (a : β) => matrix.mul M (f a) :=
  Eq.symm (finset.sum_hom s fun (x : matrix m n α) => matrix.mul M x)

/- This line does not type-check without `id` and `: _`. Lean did not recognize that two different
  `add_monoid` instances were def-eq -/

@[simp] theorem row_mul_col_apply {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) (w : m → α) (i : Unit) (j : Unit) : matrix.mul (row v) (col w) i j = dot_product v w :=
  rfl

end matrix


/-- The `ring_hom` between spaces of square matrices induced by a `ring_hom` between their
coefficients. -/
def ring_hom.map_matrix {m : Type u_2} [fintype m] {α : Type v} [DecidableEq m] [semiring α] {β : Type w} [semiring β] (f : α →+* β) : matrix m m α →+* matrix m m β :=
  ring_hom.mk (fun (M : matrix m m α) => matrix.map M ⇑f) sorry sorry sorry sorry

@[simp] theorem ring_hom.map_matrix_apply {m : Type u_2} [fintype m] {α : Type v} [DecidableEq m] [semiring α] {β : Type w} [semiring β] (f : α →+* β) (M : matrix m m α) : coe_fn (ring_hom.map_matrix f) M = matrix.map M ⇑f :=
  rfl

namespace matrix


@[simp] theorem neg_mul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [ring α] (M : matrix m n α) (N : matrix n o α) : matrix.mul (-M) N = -matrix.mul M N :=
  ext fun (i : m) (j : o) => neg_dot_product (fun (i_1 : n) => M i i_1) fun (j_1 : n) => N j_1 j

@[simp] theorem mul_neg {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [ring α] (M : matrix m n α) (N : matrix n o α) : matrix.mul M (-N) = -matrix.mul M N :=
  ext fun (i : m) (j : o) => dot_product_neg (fun (j : n) => M i j) fun (i : n) => N i j

protected theorem sub_mul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [ring α] (M : matrix m n α) (M' : matrix m n α) (N : matrix n o α) : matrix.mul (M - M') N = matrix.mul M N - matrix.mul M' N := sorry

protected theorem mul_sub {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [ring α] (M : matrix m n α) (N : matrix n o α) (N' : matrix n o α) : matrix.mul M (N - N') = matrix.mul M N - matrix.mul M N' := sorry

protected instance ring {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [ring α] : ring (matrix n n α) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry

protected instance has_scalar {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] : has_scalar α (matrix m n α) :=
  pi.has_scalar

protected instance semimodule {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {β : Type w} [semiring α] [add_comm_monoid β] [semimodule α β] : semimodule α (matrix m n β) :=
  pi.semimodule m (fun (ᾰ : m) => n → β) α

@[simp] theorem smul_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (a : α) (A : matrix m n α) (i : m) (j : n) : has_scalar.smul a A i j = a * A i j :=
  rfl

theorem smul_eq_diagonal_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] (M : matrix m n α) (a : α) : a • M = matrix.mul (diagonal fun (_x : m) => a) M := sorry

@[simp] theorem smul_mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) (a : α) (N : matrix n l α) : matrix.mul (a • M) N = a • matrix.mul M N :=
  ext fun (i : m) (j : l) => smul_dot_product a (fun (i_1 : n) => M i i_1) fun (j_1 : n) => N j_1 j

@[simp] theorem mul_mul_left {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (M : matrix m n α) (N : matrix n o α) (a : α) : matrix.mul (fun (i : m) (j : n) => a * M i j) N = a • matrix.mul M N := sorry

/--
The ring homomorphism `α →+* matrix n n α`
sending `a` to the diagonal matrix with `a` on the diagonal.
-/
def scalar {α : Type v} [semiring α] (n : Type u) [DecidableEq n] [fintype n] : α →+* matrix n n α :=
  ring_hom.mk (fun (a : α) => a • 1) sorry sorry sorry sorry

@[simp] theorem coe_scalar {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] : ⇑(scalar n) = fun (a : α) => a • 1 :=
  rfl

theorem scalar_apply_eq {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] (a : α) (i : n) : coe_fn (scalar n) a i i = a := sorry

theorem scalar_apply_ne {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] (a : α) (i : n) (j : n) (h : i ≠ j) : coe_fn (scalar n) a i j = 0 := sorry

theorem scalar_inj {n : Type u_3} [fintype n] {α : Type v} [semiring α] [DecidableEq n] [Nonempty n] {r : α} {s : α} : coe_fn (scalar n) r = coe_fn (scalar n) s ↔ r = s := sorry

theorem smul_eq_mul_diagonal {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [comm_semiring α] [DecidableEq n] (M : matrix m n α) (a : α) : a • M = matrix.mul M (diagonal fun (_x : n) => a) := sorry

@[simp] theorem mul_smul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [comm_semiring α] (M : matrix m n α) (a : α) (N : matrix n l α) : matrix.mul M (a • N) = a • matrix.mul M N :=
  ext fun (i : m) (j : l) => dot_product_smul a (fun (j : n) => M i j) fun (i : n) => N i j

@[simp] theorem mul_mul_right {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [comm_semiring α] (M : matrix m n α) (N : matrix n o α) (a : α) : (matrix.mul M fun (i : n) (j : o) => a * N i j) = a • matrix.mul M N := sorry

theorem scalar.commute {n : Type u_3} [fintype n] {α : Type v} [comm_semiring α] [DecidableEq n] (r : α) (M : matrix n n α) : commute (coe_fn (scalar n) r) M := sorry

/-- For two vectors `w` and `v`, `vec_mul_vec w v i j` is defined to be `w i * v j`.
    Put another way, `vec_mul_vec w v` is exactly `col w ⬝ row v`. -/
def vec_mul_vec {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (w : m → α) (v : n → α) : matrix m n α :=
  sorry

/-- `mul_vec M v` is the matrix-vector product of `M` and `v`, where `v` is seen as a column matrix.
    Put another way, `mul_vec M v` is the vector whose entries
    are those of `M ⬝ col v` (see `col_mul_vec`). -/
def mul_vec {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) (v : n → α) : m → α :=
  sorry

/-- `vec_mul v M` is the vector-matrix product of `v` and `M`, where `v` is seen as a row matrix.
    Put another way, `vec_mul v M` is the vector whose entries
    are those of `row v ⬝ M` (see `row_vec_mul`). -/
def vec_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (v : m → α) (M : matrix m n α) : n → α :=
  sorry

protected instance mul_vec.is_add_monoid_hom_left {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (v : n → α) : is_add_monoid_hom fun (M : matrix m n α) => mul_vec M v :=
  is_add_monoid_hom.mk
    (funext
      fun (x : m) =>
        eq.mpr
          (id
            (Eq.trans
              ((fun (a a_1 : α) (e_1 : a = a_1) (ᾰ ᾰ_1 : α) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                (mul_vec 0 v x) 0
                (Eq.trans
                  (Eq.trans (mul_vec.equations._eqn_1 0 v x)
                    ((fun [_inst_2 : fintype n] {α : Type v} (v v_1 : n → α) (e_5 : v = v_1) (w w_1 : n → α)
                        (e_6 : w = w_1) => eq.drec (eq.drec (Eq.refl (dot_product v w)) e_6) e_5)
                      (fun (j : n) => HasZero.zero x j) (fun (j : n) => 0) (funext fun (j : n) => zero_apply x j) v v
                      (Eq.refl v)))
                  (zero_dot_product' v))
                (HasZero.zero x) 0 (pi.zero_apply x))
              (propext (eq_self_iff_true 0))))
          trivial)

theorem mul_vec_diagonal {m : Type u_2} [fintype m] {α : Type v} [semiring α] [DecidableEq m] (v : m → α) (w : m → α) (x : m) : mul_vec (diagonal v) w x = v x * w x :=
  diagonal_dot_product v w x

theorem vec_mul_diagonal {m : Type u_2} [fintype m] {α : Type v} [semiring α] [DecidableEq m] (v : m → α) (w : m → α) (x : m) : vec_mul v (diagonal w) x = v x * w x :=
  dot_product_diagonal' v w x

@[simp] theorem mul_vec_one {m : Type u_2} [fintype m] {α : Type v} [semiring α] [DecidableEq m] (v : m → α) : mul_vec 1 v = v := sorry

@[simp] theorem vec_mul_one {m : Type u_2} [fintype m] {α : Type v} [semiring α] [DecidableEq m] (v : m → α) : vec_mul v 1 = v := sorry

@[simp] theorem mul_vec_zero {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (A : matrix m n α) : mul_vec A 0 = 0 := sorry

@[simp] theorem vec_mul_zero {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (A : matrix m n α) : vec_mul 0 A = 0 := sorry

@[simp] theorem vec_mul_vec_mul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (v : m → α) (M : matrix m n α) (N : matrix n o α) : vec_mul (vec_mul v M) N = vec_mul v (matrix.mul M N) :=
  funext fun (x : o) => dot_product_assoc v (fun (i : m) (j : n) => M i j) fun (i : n) => N i x

@[simp] theorem mul_vec_mul_vec {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (v : o → α) (M : matrix m n α) (N : matrix n o α) : mul_vec M (mul_vec N v) = mul_vec (matrix.mul M N) v :=
  funext fun (x : m) => Eq.symm (dot_product_assoc (fun (j : n) => M x j) (fun (i : n) (j : o) => N i j) v)

theorem vec_mul_vec_eq {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (w : m → α) (v : n → α) : vec_mul_vec w v = matrix.mul (col w) (row v) := sorry

/--
`std_basis_matrix i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def std_basis_matrix {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : α) : matrix m n α :=
  fun (i' : m) (j' : n) => ite (i' = i ∧ j' = j) a 0

@[simp] theorem smul_std_basis_matrix {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : α) (b : α) : b • std_basis_matrix i j a = std_basis_matrix i j (b • a) := sorry

@[simp] theorem std_basis_matrix_zero {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] [DecidableEq n] (i : m) (j : n) : std_basis_matrix i j 0 = 0 := sorry

theorem std_basis_matrix_add {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : α) (b : α) : std_basis_matrix i j (a + b) = std_basis_matrix i j a + std_basis_matrix i j b := sorry

theorem matrix_eq_sum_std_basis {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] [DecidableEq m] [DecidableEq n] (x : matrix n m α) : x = finset.sum finset.univ fun (i : n) => finset.sum finset.univ fun (j : m) => std_basis_matrix i j (x i j) := sorry

-- TODO: tie this up with the `basis` machinery of linear algebra

-- this is not completely trivial because we are indexing by two types, instead of one

-- TODO: add `std_basis_vec`

theorem std_basis_eq_basis_mul_basis {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] [DecidableEq m] [DecidableEq n] (i : m) (j : n) : std_basis_matrix i j 1 = vec_mul_vec (fun (i' : m) => ite (i = i') 1 0) fun (j' : n) => ite (j = j') 1 0 := sorry

protected theorem induction_on' {n : Type u_3} [fintype n] [DecidableEq n] {X : Type u_1} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X) (h_zero : M 0) (h_add : ∀ (p q : matrix n n X), M p → M q → M (p + q)) (h_std_basis : ∀ (i j : n) (x : X), M (std_basis_matrix i j x)) : M m := sorry

protected theorem induction_on {n : Type u_3} [fintype n] [DecidableEq n] [Nonempty n] {X : Type u_1} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X) (h_add : ∀ (p q : matrix n n X), M p → M q → M (p + q)) (h_std_basis : ∀ (i j : n) (x : X), M (std_basis_matrix i j x)) : M m := sorry

theorem neg_vec_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [ring α] (v : m → α) (A : matrix m n α) : vec_mul (-v) A = -vec_mul v A :=
  funext fun (x : n) => neg_dot_product v fun (i : m) => A i x

theorem vec_mul_neg {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [ring α] (v : m → α) (A : matrix m n α) : vec_mul v (-A) = -vec_mul v A :=
  funext fun (x : n) => dot_product_neg v fun (i : m) => A i x

theorem neg_mul_vec {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [ring α] (v : n → α) (A : matrix m n α) : mul_vec (-A) v = -mul_vec A v :=
  funext fun (x : m) => neg_dot_product (fun (i : n) => A x i) v

theorem mul_vec_neg {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [ring α] (v : n → α) (A : matrix m n α) : mul_vec A (-v) = -mul_vec A v :=
  funext fun (x : m) => dot_product_neg (fun (j : n) => A x j) v

theorem smul_mul_vec_assoc {n : Type u_3} [fintype n] {α : Type v} [ring α] (A : matrix n n α) (b : n → α) (a : α) : mul_vec (a • A) b = a • mul_vec A b := sorry

/--
  Tell `simp` what the entries are in a transposed matrix.

  Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-/
@[simp] theorem transpose_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} (M : matrix m n α) (i : m) (j : n) : transpose M j i = M i j :=
  rfl

@[simp] theorem transpose_transpose {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} (M : matrix m n α) : transpose (transpose M) = M :=
  ext fun (i : m) (j : n) => Eq.refl (transpose (transpose M) i j)

@[simp] theorem transpose_zero {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [HasZero α] : transpose 0 = 0 :=
  ext fun (i : n) (j : m) => Eq.refl (transpose 0 i j)

@[simp] theorem transpose_one {n : Type u_3} [fintype n] {α : Type v} [DecidableEq n] [HasZero α] [HasOne α] : transpose 1 = 1 := sorry

@[simp] theorem transpose_add {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Add α] (M : matrix m n α) (N : matrix m n α) : transpose (M + N) = transpose M + transpose N := sorry

@[simp] theorem transpose_sub {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [add_group α] (M : matrix m n α) (N : matrix m n α) : transpose (M - N) = transpose M - transpose N := sorry

@[simp] theorem transpose_mul {l : Type u_1} {m : Type u_2} {n : Type u_3} [fintype l] [fintype m] [fintype n] {α : Type v} [comm_semiring α] (M : matrix m n α) (N : matrix n l α) : transpose (matrix.mul M N) = matrix.mul (transpose N) (transpose M) :=
  ext
    fun (i : l) (j : m) =>
      dot_product_comm (fun (i : n) => (fun (j_1 : n) => M j j_1) i) fun (i_1 : n) => (fun (j : n) => N j i) i_1

@[simp] theorem transpose_smul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (c : α) (M : matrix m n α) : transpose (c • M) = c • transpose M :=
  ext fun (i : n) (j : m) => Eq.refl (transpose (c • M) i j)

@[simp] theorem transpose_neg {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [Neg α] (M : matrix m n α) : transpose (-M) = -transpose M :=
  ext fun (i : n) (j : m) => Eq.refl (transpose (-M) i j)

theorem transpose_map {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {β : Type w} {f : α → β} {M : matrix m n α} : map (transpose M) f = transpose (map M f) :=
  ext fun (i : n) (j : m) => Eq.refl (map (transpose M) f i j)

/--
When `R` is a *-(semi)ring, `matrix n n R` becomes a *-(semi)ring with
the star operation given by taking the conjugate, and the star of each entry.
-/
protected instance star_ring {n : Type u_3} [fintype n] [DecidableEq n] {R : Type u_5} [semiring R] [star_ring R] : star_ring (matrix n n R) :=
  star_ring.mk sorry

@[simp] theorem star_apply {n : Type u_3} [fintype n] [DecidableEq n] {R : Type u_5} [semiring R] [star_ring R] (M : matrix n n R) (i : n) (j : n) : star M i j = star (M j i) :=
  rfl

/-- `M.minor row col` is the matrix obtained by reindexing the rows and the lines of
    `M`, such that `M.minor row col i j = M (row i) (col j)`. Note that the total number
    of row/colums doesn't have to be preserved. -/
def minor {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix m n α) (row : l → m) (col : o → n) : matrix l o α :=
  fun (i : l) (j : o) => A (row i) (col j)

/-- The left `n × l` part of a `n × (l+r)` matrix. -/
def sub_left {α : Type v} {m : ℕ} {l : ℕ} {r : ℕ} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin l) α :=
  minor A id ⇑(fin.cast_add r)

/-- The right `n × r` part of a `n × (l+r)` matrix. -/
def sub_right {α : Type v} {m : ℕ} {l : ℕ} {r : ℕ} (A : matrix (fin m) (fin (l + r)) α) : matrix (fin m) (fin r) α :=
  minor A id ⇑(fin.nat_add l)

/-- The top `u × n` part of a `(u+d) × n` matrix. -/
def sub_up {α : Type v} {d : ℕ} {u : ℕ} {n : ℕ} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin u) (fin n) α :=
  minor A (⇑(fin.cast_add d)) id

/-- The bottom `d × n` part of a `(u+d) × n` matrix. -/
def sub_down {α : Type v} {d : ℕ} {u : ℕ} {n : ℕ} (A : matrix (fin (u + d)) (fin n) α) : matrix (fin d) (fin n) α :=
  minor A (⇑(fin.nat_add u)) id

/-- The top-right `u × r` part of a `(u+d) × (l+r)` matrix. -/
def sub_up_right {α : Type v} {d : ℕ} {u : ℕ} {l : ℕ} {r : ℕ} (A : matrix (fin (u + d)) (fin (l + r)) α) : matrix (fin u) (fin r) α :=
  sub_up (sub_right A)

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
def sub_down_right {α : Type v} {d : ℕ} {u : ℕ} {l : ℕ} {r : ℕ} (A : matrix (fin (u + d)) (fin (l + r)) α) : matrix (fin d) (fin r) α :=
  sub_down (sub_right A)

/-- The top-left `u × l` part of a `(u+d) × (l+r)` matrix. -/
def sub_up_left {α : Type v} {d : ℕ} {u : ℕ} {l : ℕ} {r : ℕ} (A : matrix (fin (u + d)) (fin (l + r)) α) : matrix (fin u) (fin l) α :=
  sub_up (sub_left A)

/-- The bottom-left `d × l` part of a `(u+d) × (l+r)` matrix. -/
def sub_down_left {α : Type v} {d : ℕ} {u : ℕ} {l : ℕ} {r : ℕ} (A : matrix (fin (u + d)) (fin (l + r)) α) : matrix (fin d) (fin l) α :=
  sub_down (sub_left A)

/-!
### `row_col` section

Simplification lemmas for `matrix.row` and `matrix.col`.
-/

@[simp] theorem col_add {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) (w : m → α) : col (v + w) = col v + col w :=
  ext fun (i : m) (j : Unit) => Eq.refl (col (v + w) i j)

@[simp] theorem col_smul {m : Type u_2} [fintype m] {α : Type v} [semiring α] (x : α) (v : m → α) : col (x • v) = x • col v :=
  ext fun (i : m) (j : Unit) => Eq.refl (col (x • v) i j)

@[simp] theorem row_add {m : Type u_2} [fintype m] {α : Type v} [semiring α] (v : m → α) (w : m → α) : row (v + w) = row v + row w :=
  ext fun (i : Unit) (j : m) => Eq.refl (row (v + w) i j)

@[simp] theorem row_smul {m : Type u_2} [fintype m] {α : Type v} [semiring α] (x : α) (v : m → α) : row (x • v) = x • row v :=
  ext fun (i : Unit) (j : m) => Eq.refl (row (x • v) i j)

@[simp] theorem col_apply {m : Type u_2} [fintype m] {α : Type v} (v : m → α) (i : m) (j : Unit) : col v i j = v i :=
  rfl

@[simp] theorem row_apply {m : Type u_2} [fintype m] {α : Type v} (v : m → α) (i : Unit) (j : m) : row v i j = v j :=
  rfl

@[simp] theorem transpose_col {m : Type u_2} [fintype m] {α : Type v} (v : m → α) : transpose (col v) = row v :=
  ext fun (i : Unit) (j : m) => Eq.refl (transpose (col v) i j)

@[simp] theorem transpose_row {m : Type u_2} [fintype m] {α : Type v} (v : m → α) : transpose (row v) = col v :=
  ext fun (i : m) (j : Unit) => Eq.refl (transpose (row v) i j)

theorem row_vec_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) (v : m → α) : row (vec_mul v M) = matrix.mul (row v) M :=
  ext fun (i : Unit) (j : n) => Eq.refl (row (vec_mul v M) i j)

theorem col_vec_mul {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) (v : m → α) : col (vec_mul v M) = transpose (matrix.mul (row v) M) :=
  ext fun (i : n) (j : Unit) => Eq.refl (col (vec_mul v M) i j)

theorem col_mul_vec {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) (v : n → α) : col (mul_vec M v) = matrix.mul M (col v) :=
  ext fun (i : m) (j : Unit) => Eq.refl (col (mul_vec M v) i j)

theorem row_mul_vec {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [semiring α] (M : matrix m n α) (v : n → α) : row (mul_vec M v) = transpose (matrix.mul M (col v)) :=
  ext fun (i : Unit) (j : m) => Eq.refl (row (mul_vec M v) i j)

/-- Update, i.e. replace the `i`th row of matrix `A` with the values in `b`. -/
def update_row {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [DecidableEq n] (M : matrix n m α) (i : n) (b : m → α) : matrix n m α :=
  function.update M i b

/-- Update, i.e. replace the `j`th column of matrix `A` with the values in `b`. -/
def update_column {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} [DecidableEq m] (M : matrix n m α) (j : m) (b : n → α) : matrix n m α :=
  fun (i : n) => function.update (M i) j (b i)

@[simp] theorem update_row_self {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {b : m → α} [DecidableEq n] : update_row M i b i = b :=
  function.update_same i b M

@[simp] theorem update_column_self {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {j : m} {c : n → α} [DecidableEq m] : update_column M j c i j = c i :=
  function.update_same j (c i) (M i)

@[simp] theorem update_row_ne {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {b : m → α} [DecidableEq n] {i' : n} (i_ne : i' ≠ i) : update_row M i b i' = M i' :=
  function.update_noteq i_ne b M

@[simp] theorem update_column_ne {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {j : m} {c : n → α} [DecidableEq m] {j' : m} (j_ne : j' ≠ j) : update_column M j c i j' = M i j' :=
  function.update_noteq j_ne (c i) (M i)

theorem update_row_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {j : m} {b : m → α} [DecidableEq n] {i' : n} : update_row M i b i' j = ite (i' = i) (b j) (M i' j) := sorry

theorem update_column_apply {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {j : m} {c : n → α} [DecidableEq m] {j' : m} : update_column M j c i j' = ite (j' = j) (c i) (M i j') := sorry

theorem update_row_transpose {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {j : m} {c : n → α} [DecidableEq m] : update_row (transpose M) j c = transpose (update_column M j c) := sorry

theorem update_column_transpose {m : Type u_2} {n : Type u_3} [fintype m] [fintype n] {α : Type v} {M : matrix n m α} {i : n} {b : m → α} [DecidableEq n] : update_column (transpose M) i b = transpose (update_row M i b) := sorry

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
def from_blocks {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : matrix (n ⊕ o) (l ⊕ m) α :=
  sum.elim (fun (i : n) => sum.elim (A i) (B i)) fun (i : o) => sum.elim (C i) (D i)

@[simp] theorem from_blocks_apply₁₁ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : n) (j : l) : from_blocks A B C D (sum.inl i) (sum.inl j) = A i j :=
  rfl

@[simp] theorem from_blocks_apply₁₂ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : n) (j : m) : from_blocks A B C D (sum.inl i) (sum.inr j) = B i j :=
  rfl

@[simp] theorem from_blocks_apply₂₁ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : o) (j : l) : from_blocks A B C D (sum.inr i) (sum.inl j) = C i j :=
  rfl

@[simp] theorem from_blocks_apply₂₂ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : o) (j : m) : from_blocks A B C D (sum.inr i) (sum.inr j) = D i j :=
  rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the correspnding
"top left" submatrix. -/
def to_blocks₁₁ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n l α :=
  fun (i : n) (j : l) => M (sum.inl i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the correspnding
"top right" submatrix. -/
def to_blocks₁₂ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n m α :=
  fun (i : n) (j : m) => M (sum.inl i) (sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the correspnding
"bottom left" submatrix. -/
def to_blocks₂₁ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o l α :=
  fun (i : o) (j : l) => M (sum.inr i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the correspnding
"bottom right" submatrix. -/
def to_blocks₂₂ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o m α :=
  fun (i : o) (j : m) => M (sum.inr i) (sum.inr j)

theorem from_blocks_to_blocks {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (M : matrix (n ⊕ o) (l ⊕ m) α) : from_blocks (to_blocks₁₁ M) (to_blocks₁₂ M) (to_blocks₂₁ M) (to_blocks₂₂ M) = M := sorry

@[simp] theorem to_blocks_from_blocks₁₁ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : to_blocks₁₁ (from_blocks A B C D) = A :=
  rfl

@[simp] theorem to_blocks_from_blocks₁₂ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : to_blocks₁₂ (from_blocks A B C D) = B :=
  rfl

@[simp] theorem to_blocks_from_blocks₂₁ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : to_blocks₂₁ (from_blocks A B C D) = C :=
  rfl

@[simp] theorem to_blocks_from_blocks₂₂ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : to_blocks₂₂ (from_blocks A B C D) = D :=
  rfl

theorem from_blocks_transpose {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : transpose (from_blocks A B C D) = from_blocks (transpose A) (transpose C) (transpose B) (transpose D) := sorry

theorem from_blocks_smul {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (x : α) (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) : x • from_blocks A B C D = from_blocks (x • A) (x • B) (x • C) (x • D) := sorry

theorem from_blocks_add {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (A' : matrix n l α) (B' : matrix n m α) (C' : matrix o l α) (D' : matrix o m α) : from_blocks A B C D + from_blocks A' B' C' D' = from_blocks (A + A') (B + B') (C + C') (D + D') := sorry

theorem from_blocks_multiply {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype l] [fintype m] [fintype n] [fintype o] {α : Type v} [semiring α] {p : Type u_5} {q : Type u_6} [fintype p] [fintype q] (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (A' : matrix l p α) (B' : matrix l q α) (C' : matrix m p α) (D' : matrix m q α) : matrix.mul (from_blocks A B C D) (from_blocks A' B' C' D') =
  from_blocks (matrix.mul A A' + matrix.mul B C') (matrix.mul A B' + matrix.mul B D')
    (matrix.mul C A' + matrix.mul D C') (matrix.mul C B' + matrix.mul D D') := sorry

@[simp] theorem from_blocks_diagonal {l : Type u_1} {m : Type u_2} [fintype l] [fintype m] {α : Type v} [semiring α] [DecidableEq l] [DecidableEq m] (d₁ : l → α) (d₂ : m → α) : from_blocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (sum.elim d₁ d₂) := sorry

@[simp] theorem from_blocks_one {l : Type u_1} {m : Type u_2} [fintype l] [fintype m] {α : Type v} [semiring α] [DecidableEq l] [DecidableEq m] : from_blocks 1 0 0 1 = 1 := sorry

/-- `matrix.block_diagonal M` turns `M : o → matrix m n α'` into a
`m × o`-by`n × o` block matrix which has the entries of `M` along the diagonal
and zero elsewhere. -/
def block_diagonal {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] [HasZero α] : matrix (m × o) (n × o) α :=
  sorry

theorem block_diagonal_apply {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] [HasZero α] (ik : m × o) (jk : n × o) : block_diagonal M ik jk = ite (prod.snd ik = prod.snd jk) (M (prod.snd ik) (prod.fst ik) (prod.fst jk)) 0 :=
  prod.cases_on ik
    fun (ik_fst : m) (ik_snd : o) =>
      prod.cases_on jk fun (jk_fst : n) (jk_snd : o) => Eq.refl (block_diagonal M (ik_fst, ik_snd) (jk_fst, jk_snd))

@[simp] theorem block_diagonal_apply_eq {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] [HasZero α] (i : m) (j : n) (k : o) : block_diagonal M (i, k) (j, k) = M k i j :=
  if_pos rfl

theorem block_diagonal_apply_ne {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] [HasZero α] (i : m) (j : n) {k : o} {k' : o} (h : k ≠ k') : block_diagonal M (i, k) (j, k') = 0 :=
  if_neg h

@[simp] theorem block_diagonal_transpose {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] [HasZero α] : transpose (block_diagonal M) = block_diagonal fun (k : o) => transpose (M k) := sorry

@[simp] theorem block_diagonal_zero {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} [DecidableEq o] [HasZero α] : block_diagonal 0 = 0 := sorry

@[simp] theorem block_diagonal_diagonal {m : Type u_2} {o : Type u_4} [fintype m] [fintype o] {α : Type v} [DecidableEq o] [HasZero α] [DecidableEq m] (d : o → m → α) : (block_diagonal fun (k : o) => diagonal (d k)) = diagonal fun (ik : m × o) => d (prod.snd ik) (prod.fst ik) := sorry

@[simp] theorem block_diagonal_one {m : Type u_2} {o : Type u_4} [fintype m] [fintype o] {α : Type v} [DecidableEq o] [HasZero α] [DecidableEq m] [HasOne α] : block_diagonal 1 = 1 := sorry

@[simp] theorem block_diagonal_add {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) (N : o → matrix m n α) [DecidableEq o] [add_monoid α] : block_diagonal (M + N) = block_diagonal M + block_diagonal N := sorry

@[simp] theorem block_diagonal_neg {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] [add_group α] : block_diagonal (-M) = -block_diagonal M := sorry

@[simp] theorem block_diagonal_sub {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) (N : o → matrix m n α) [DecidableEq o] [add_group α] : block_diagonal (M - N) = block_diagonal M - block_diagonal N := sorry

@[simp] theorem block_diagonal_mul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] {p : Type u_1} [fintype p] [semiring α] (N : o → matrix n p α) : (block_diagonal fun (k : o) => matrix.mul (M k) (N k)) = matrix.mul (block_diagonal M) (block_diagonal N) := sorry

@[simp] theorem block_diagonal_smul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} (M : o → matrix m n α) [DecidableEq o] {R : Type u_1} [semiring R] [add_comm_monoid α] [semimodule R α] (x : R) : block_diagonal (x • M) = x • block_diagonal M := sorry

end matrix


namespace ring_hom


theorem map_matrix_mul {m : Type u_2} {n : Type u_3} {o : Type u_4} [fintype m] [fintype n] [fintype o] {α : Type v} {β : Type u_5} [semiring α] [semiring β] (M : matrix m n α) (N : matrix n o α) (i : m) (j : o) (f : α →+* β) : coe_fn f (matrix.mul M N i j) =
  matrix.mul (fun (i : m) (j : n) => coe_fn f (M i j)) (fun (i : n) (j : o) => coe_fn f (N i j)) i j := sorry

