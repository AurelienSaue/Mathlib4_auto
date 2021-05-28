/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

Notation for vectors and matrices
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.card
import Mathlib.data.matrix.basic
import Mathlib.tactic.fin_cases
import Mathlib.PostPort

universes u u_1 u_2 u_3 

namespace Mathlib

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : fin 4 → α`.
Nesting vectors gives a matrix, so `![![a, b], ![c, d]] : matrix (fin 2) (fin 2) α`.
This file includes `simp` lemmas for applying operations in
`data.matrix.basic` to values built out of this notation.

## Main definitions

* `vec_empty` is the empty vector (or `0` by `n` matrix) `![]`
* `vec_cons` prepends an entry to a vector, so `![a, b]` is `vec_cons a (vec_cons b vec_empty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

The main new notation is `![a, b]`, which gets expanded to `vec_cons a (vec_cons b vec_empty)`.
-/

namespace matrix


/-- `![]` is the vector with no entries. -/
def vec_empty {α : Type u} : fin 0 → α :=
  fin_zero_elim

/-- `vec_cons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vec_head` and `vec_tail`.
The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-/
def vec_cons {α : Type u} {n : ℕ} (h : α) (t : fin n → α) : fin (Nat.succ n) → α :=
  fin.cons h t

/-- `vec_head v` gives the first entry of the vector `v` -/
def vec_head {α : Type u} {n : ℕ} (v : fin (Nat.succ n) → α) : α :=
  v 0

/-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
def vec_tail {α : Type u} {n : ℕ} (v : fin (Nat.succ n) → α) : fin n → α :=
  v ∘ fin.succ

theorem empty_eq {α : Type u} (v : fin 0 → α) : v = vec_empty :=
  funext
    fun (i : fin 0) => false.dcases_on (fun (h : i ∈ fintype.elems (fin 0)) => v i = vec_empty i) (fintype.complete i)

@[simp] theorem head_fin_const {α : Type u} {n : ℕ} (a : α) : (vec_head fun (i : fin (n + 1)) => a) = a :=
  rfl

@[simp] theorem cons_val_zero {α : Type u} {m : ℕ} (x : α) (u : fin m → α) : vec_cons x u 0 = x :=
  rfl

theorem cons_val_zero' {α : Type u} {m : ℕ} (h : 0 < Nat.succ m) (x : α) (u : fin m → α) : vec_cons x u { val := 0, property := h } = x :=
  rfl

@[simp] theorem cons_val_succ {α : Type u} {m : ℕ} (x : α) (u : fin m → α) (i : fin m) : vec_cons x u (fin.succ i) = u i := sorry

@[simp] theorem cons_val_succ' {α : Type u} {m : ℕ} {i : ℕ} (h : Nat.succ i < Nat.succ m) (x : α) (u : fin m → α) : vec_cons x u { val := Nat.succ i, property := h } = u { val := i, property := nat.lt_of_succ_lt_succ h } := sorry

@[simp] theorem head_cons {α : Type u} {m : ℕ} (x : α) (u : fin m → α) : vec_head (vec_cons x u) = x :=
  rfl

@[simp] theorem tail_cons {α : Type u} {m : ℕ} (x : α) (u : fin m → α) : vec_tail (vec_cons x u) = u := sorry

@[simp] theorem empty_val' {α : Type u} {n' : Type u_1} (j : n') : (fun (i : fin 0) => vec_empty i j) = vec_empty :=
  empty_eq fun (i : fin 0) => vec_empty i j

@[simp] theorem cons_val' {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] (v : n' → α) (B : matrix (fin m) n' α) (i : fin (Nat.succ m)) (j : n') : vec_cons v B i j = vec_cons (v j) (fun (i : fin m) => B i j) i := sorry

@[simp] theorem head_val' {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] (B : matrix (fin (Nat.succ m)) n' α) (j : n') : (vec_head fun (i : fin (Nat.succ m)) => B i j) = vec_head B j :=
  rfl

@[simp] theorem tail_val' {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] (B : matrix (fin (Nat.succ m)) n' α) (j : n') : (vec_tail fun (i : fin (Nat.succ m)) => B i j) = fun (i : fin m) => vec_tail B i j := sorry

@[simp] theorem cons_head_tail {α : Type u} {m : ℕ} (u : fin (Nat.succ m) → α) : vec_cons (vec_head u) (vec_tail u) = u :=
  fin.cons_self_tail u

@[simp] theorem range_cons {α : Type u} {n : ℕ} (x : α) (u : fin n → α) : set.range (vec_cons x u) = singleton x ∪ set.range u := sorry

@[simp] theorem range_empty {α : Type u} (u : fin 0 → α) : set.range u = ∅ := sorry

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : fin 1 = 0 : fin 1`.
-/
@[simp] theorem cons_val_one {α : Type u} {m : ℕ} (x : α) (u : fin (Nat.succ m) → α) : vec_cons x u 1 = vec_head u :=
  cons_val_succ x u 0

@[simp] theorem cons_val_fin_one {α : Type u} (x : α) (u : fin 0 → α) (i : fin 1) : vec_cons x u i = x := sorry

/-! ### Numeral (`bit0` and `bit1`) indices
The following definitions and `simp` lemmas are to allow any
numeral-indexed element of a vector given with matrix notation to
be extracted by `simp` (even when the numeral is larger than the
number of elements in the vector, which is taken modulo that number
of elements by virtue of the semantics of `bit0` and `bit1` and of
addition on `fin n`).
-/

@[simp] theorem empty_append {α : Type u} {n : ℕ} (v : fin n → α) : fin.append (Eq.symm (zero_add n)) vec_empty v = v := sorry

@[simp] theorem cons_append {α : Type u} {m : ℕ} {n : ℕ} {o : ℕ} (ho : o + 1 = m + 1 + n) (x : α) (u : fin m → α) (v : fin n → α) : fin.append ho (vec_cons x u) v =
  vec_cons x
    (fin.append
      (eq.mp (Eq._oldrec (Eq.refl (o + 1 = m + n + 1)) (propext add_right_cancel_iff))
        (eq.mp (Eq._oldrec (Eq.refl (o + 1 = m + (n + 1))) (Eq.symm (add_assoc m n 1)))
          (eq.mp (Eq._oldrec (Eq.refl (o + 1 = m + (1 + n))) (add_comm 1 n))
            (eq.mp (Eq._oldrec (Eq.refl (o + 1 = m + 1 + n)) (add_assoc m 1 n)) ho))))
      u v) := sorry

/-- `vec_alt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
def vec_alt0 {α : Type u} {m : ℕ} {n : ℕ} (hm : m = n + n) (v : fin m → α) (k : fin n) : α :=
  v { val := ↑k + ↑k, property := sorry }

/-- `vec_alt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered). -/
def vec_alt1 {α : Type u} {m : ℕ} {n : ℕ} (hm : m = n + n) (v : fin m → α) (k : fin n) : α :=
  v { val := ↑k + ↑k + 1, property := sorry }

theorem vec_alt0_append {α : Type u} {n : ℕ} (v : fin n → α) : vec_alt0 rfl (fin.append rfl v v) = v ∘ bit0 := sorry

theorem vec_alt1_append {α : Type u} {n : ℕ} (v : fin (n + 1) → α) : vec_alt1 rfl (fin.append rfl v v) = v ∘ bit1 := sorry

@[simp] theorem vec_head_vec_alt0 {α : Type u} {m : ℕ} {n : ℕ} (hm : m + bit0 1 = n + 1 + (n + 1)) (v : fin (m + bit0 1) → α) : vec_head (vec_alt0 hm v) = v 0 :=
  rfl

@[simp] theorem vec_head_vec_alt1 {α : Type u} {m : ℕ} {n : ℕ} (hm : m + bit0 1 = n + 1 + (n + 1)) (v : fin (m + bit0 1) → α) : vec_head (vec_alt1 hm v) = v 1 :=
  rfl

@[simp] theorem cons_vec_bit0_eq_alt0 {α : Type u} {n : ℕ} (x : α) (u : fin n → α) (i : fin (n + 1)) : vec_cons x u (bit0 i) = vec_alt0 rfl (fin.append rfl (vec_cons x u) (vec_cons x u)) i := sorry

@[simp] theorem cons_vec_bit1_eq_alt1 {α : Type u} {n : ℕ} (x : α) (u : fin n → α) (i : fin (n + 1)) : vec_cons x u (bit1 i) = vec_alt1 rfl (fin.append rfl (vec_cons x u) (vec_cons x u)) i := sorry

@[simp] theorem cons_vec_alt0 {α : Type u} {m : ℕ} {n : ℕ} (h : m + 1 + 1 = n + 1 + (n + 1)) (x : α) (y : α) (u : fin m → α) : vec_alt0 h (vec_cons x (vec_cons y u)) =
  vec_cons x
    (vec_alt0
      (eq.mp (Eq._oldrec (Eq.refl (m + 1 = n + n + 1)) (propext add_right_cancel_iff))
        (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + n + 1 + 1)) (propext add_right_cancel_iff))
          (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + (n + 1) + 1)) (Eq.symm (add_assoc n n 1)))
            (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + (n + 1 + 1))) (Eq.symm (add_assoc n (n + 1) 1)))
              (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + (1 + (n + 1)))) (add_comm 1 (n + 1)))
                (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + 1 + (n + 1))) (add_assoc n 1 (n + 1))) h))))))
      u) := sorry

-- Although proved by simp, extracting element 8 of a five-element

-- vector does not work by simp unless this lemma is present.

@[simp] theorem empty_vec_alt0 (α : Type u_1) {h : 0 = 0 + 0} : vec_alt0 h vec_empty = vec_empty :=
  eq.mpr (id (propext (eq_iff_true_of_subsingleton (vec_alt0 h vec_empty) vec_empty))) trivial

@[simp] theorem cons_vec_alt1 {α : Type u} {m : ℕ} {n : ℕ} (h : m + 1 + 1 = n + 1 + (n + 1)) (x : α) (y : α) (u : fin m → α) : vec_alt1 h (vec_cons x (vec_cons y u)) =
  vec_cons y
    (vec_alt1
      (eq.mp (Eq._oldrec (Eq.refl (m + 1 = n + n + 1)) (propext add_right_cancel_iff))
        (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + n + 1 + 1)) (propext add_right_cancel_iff))
          (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + (n + 1) + 1)) (Eq.symm (add_assoc n n 1)))
            (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + (n + 1 + 1))) (Eq.symm (add_assoc n (n + 1) 1)))
              (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + (1 + (n + 1)))) (add_comm 1 (n + 1)))
                (eq.mp (Eq._oldrec (Eq.refl (m + 1 + 1 = n + 1 + (n + 1))) (add_assoc n 1 (n + 1))) h))))))
      u) := sorry

-- Although proved by simp, extracting element 9 of a five-element

-- vector does not work by simp unless this lemma is present.

@[simp] theorem empty_vec_alt1 (α : Type u_1) {h : 0 = 0 + 0} : vec_alt1 h vec_empty = vec_empty :=
  eq.mpr (id (propext (eq_iff_true_of_subsingleton (vec_alt1 h vec_empty) vec_empty))) trivial

@[simp] theorem dot_product_empty {α : Type u} [add_comm_monoid α] [Mul α] (v : fin 0 → α) (w : fin 0 → α) : dot_product v w = 0 :=
  finset.sum_empty

@[simp] theorem cons_dot_product {α : Type u} {n : ℕ} [add_comm_monoid α] [Mul α] (x : α) (v : fin n → α) (w : fin (Nat.succ n) → α) : dot_product (vec_cons x v) w = x * vec_head w + dot_product v (vec_tail w) := sorry

@[simp] theorem dot_product_cons {α : Type u} {n : ℕ} [add_comm_monoid α] [Mul α] (v : fin (Nat.succ n) → α) (x : α) (w : fin n → α) : dot_product v (vec_cons x w) = vec_head v * x + dot_product (vec_tail v) w := sorry

@[simp] theorem col_empty {α : Type u} (v : fin 0 → α) : col v = vec_empty :=
  empty_eq (col v)

@[simp] theorem col_cons {α : Type u} {m : ℕ} (x : α) (u : fin m → α) : col (vec_cons x u) = vec_cons (fun (_x : Unit) => x) (col u) := sorry

@[simp] theorem row_empty {α : Type u} : row vec_empty = fun (_x : Unit) => vec_empty :=
  funext fun (x : Unit) => funext fun (x_1 : fin 0) => Eq.refl (row vec_empty x x_1)

@[simp] theorem row_cons {α : Type u} {m : ℕ} (x : α) (u : fin m → α) : row (vec_cons x u) = fun (_x : Unit) => vec_cons x u :=
  funext fun (x_1 : Unit) => funext fun (x_2 : fin (Nat.succ m)) => Eq.refl (row (vec_cons x u) x_1 x_2)

@[simp] theorem transpose_empty_rows {α : Type u} {m' : Type u_1} [fintype m'] (A : matrix m' (fin 0) α) : transpose A = vec_empty :=
  empty_eq (transpose A)

@[simp] theorem transpose_empty_cols {α : Type u} {m' : Type u_1} [fintype m'] : transpose vec_empty = fun (i : m') => vec_empty :=
  funext fun (i : m') => empty_eq (transpose vec_empty i)

@[simp] theorem cons_transpose {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] (v : n' → α) (A : matrix (fin m) n' α) : transpose (vec_cons v A) = fun (i : n') => vec_cons (v i) (transpose A i) := sorry

@[simp] theorem head_transpose {α : Type u} {n : ℕ} {m' : Type u_1} [fintype m'] (A : matrix m' (fin (Nat.succ n)) α) : vec_head (transpose A) = vec_head ∘ A :=
  rfl

@[simp] theorem tail_transpose {α : Type u} {n : ℕ} {m' : Type u_1} [fintype m'] (A : matrix m' (fin (Nat.succ n)) α) : vec_tail (transpose A) = transpose (vec_tail ∘ A) :=
  ext fun (i : fin n) (j : m') => Eq.refl (vec_tail (transpose A) i j)

@[simp] theorem empty_mul {α : Type u} {n' : Type u_2} {o' : Type u_3} [fintype n'] [fintype o'] [semiring α] (A : matrix (fin 0) n' α) (B : matrix n' o' α) : matrix.mul A B = vec_empty :=
  empty_eq (matrix.mul A B)

@[simp] theorem empty_mul_empty {α : Type u} {m' : Type u_1} {o' : Type u_3} [fintype m'] [fintype o'] [semiring α] (A : matrix m' (fin 0) α) (B : matrix (fin 0) o' α) : matrix.mul A B = 0 :=
  rfl

@[simp] theorem mul_empty {α : Type u} {m' : Type u_1} {n' : Type u_2} [fintype m'] [fintype n'] [semiring α] (A : matrix m' n' α) (B : matrix n' (fin 0) α) : matrix.mul A B = fun (_x : m') => vec_empty :=
  funext fun (_x : m') => empty_eq (matrix.mul A B _x)

theorem mul_val_succ {α : Type u} {m : ℕ} {n' : Type u_2} {o' : Type u_3} [fintype n'] [fintype o'] [semiring α] (A : matrix (fin (Nat.succ m)) n' α) (B : matrix n' o' α) (i : fin m) (j : o') : matrix.mul A B (fin.succ i) j = matrix.mul (vec_tail A) B i j :=
  rfl

@[simp] theorem cons_mul {α : Type u} {m : ℕ} {n' : Type u_2} {o' : Type u_3} [fintype n'] [fintype o'] [semiring α] (v : n' → α) (A : matrix (fin m) n' α) (B : matrix n' o' α) : matrix.mul (vec_cons v A) B = vec_cons (vec_mul v B) (matrix.mul A B) := sorry

@[simp] theorem empty_vec_mul {α : Type u} {o' : Type u_3} [fintype o'] [semiring α] (v : fin 0 → α) (B : matrix (fin 0) o' α) : vec_mul v B = 0 :=
  rfl

@[simp] theorem vec_mul_empty {α : Type u} {n' : Type u_2} [fintype n'] [semiring α] (v : n' → α) (B : matrix n' (fin 0) α) : vec_mul v B = vec_empty :=
  empty_eq (vec_mul v B)

@[simp] theorem cons_vec_mul {α : Type u} {n : ℕ} {o' : Type u_3} [fintype o'] [semiring α] (x : α) (v : fin n → α) (B : matrix (fin (Nat.succ n)) o' α) : vec_mul (vec_cons x v) B = x • vec_head B + vec_mul v (vec_tail B) := sorry

@[simp] theorem vec_mul_cons {α : Type u} {n : ℕ} {o' : Type u_3} [fintype o'] [semiring α] (v : fin (Nat.succ n) → α) (w : o' → α) (B : matrix (fin n) o' α) : vec_mul v (vec_cons w B) = vec_head v • w + vec_mul (vec_tail v) B := sorry

@[simp] theorem empty_mul_vec {α : Type u} {n' : Type u_2} [fintype n'] [semiring α] (A : matrix (fin 0) n' α) (v : n' → α) : mul_vec A v = vec_empty :=
  empty_eq (mul_vec A v)

@[simp] theorem mul_vec_empty {α : Type u} {m' : Type u_1} [fintype m'] [semiring α] (A : matrix m' (fin 0) α) (v : fin 0 → α) : mul_vec A v = 0 :=
  rfl

@[simp] theorem cons_mul_vec {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] [semiring α] (v : n' → α) (A : fin m → n' → α) (w : n' → α) : mul_vec (vec_cons v A) w = vec_cons (dot_product v w) (mul_vec A w) := sorry

@[simp] theorem mul_vec_cons {n : ℕ} {m' : Type u_1} [fintype m'] {α : Type u_2} [comm_semiring α] (A : m' → fin (Nat.succ n) → α) (x : α) (v : fin n → α) : mul_vec A (vec_cons x v) = x • vec_head ∘ A + mul_vec (vec_tail ∘ A) v := sorry

@[simp] theorem empty_vec_mul_vec {α : Type u} {n' : Type u_2} [fintype n'] [semiring α] (v : fin 0 → α) (w : n' → α) : vec_mul_vec v w = vec_empty :=
  empty_eq (vec_mul_vec v w)

@[simp] theorem vec_mul_vec_empty {α : Type u} {m' : Type u_1} [fintype m'] [semiring α] (v : m' → α) (w : fin 0 → α) : vec_mul_vec v w = fun (_x : m') => vec_empty :=
  funext fun (i : m') => empty_eq (vec_mul_vec v w i)

@[simp] theorem cons_vec_mul_vec {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] [semiring α] (x : α) (v : fin m → α) (w : n' → α) : vec_mul_vec (vec_cons x v) w = vec_cons (x • w) (vec_mul_vec v w) := sorry

@[simp] theorem vec_mul_vec_cons {α : Type u} {n : ℕ} {m' : Type u_1} [fintype m'] [semiring α] (v : m' → α) (x : α) (w : fin n → α) : vec_mul_vec v (vec_cons x w) = fun (i : m') => v i • vec_cons x w := sorry

@[simp] theorem smul_empty {α : Type u} [semiring α] (x : α) (v : fin 0 → α) : x • v = vec_empty :=
  empty_eq (x • v)

@[simp] theorem smul_mat_empty {α : Type u} [semiring α] {m' : Type u_1} (x : α) (A : fin 0 → m' → α) : x • A = vec_empty :=
  empty_eq (x • A)

@[simp] theorem smul_cons {α : Type u} {n : ℕ} [semiring α] (x : α) (y : α) (v : fin n → α) : x • vec_cons y v = vec_cons (x * y) (x • v) := sorry

@[simp] theorem smul_mat_cons {α : Type u} {m : ℕ} {n' : Type u_2} [fintype n'] [semiring α] (x : α) (v : n' → α) (A : matrix (fin m) n' α) : x • vec_cons v A = vec_cons (x • v) (x • A) := sorry

@[simp] theorem empty_add_empty {α : Type u} [Add α] (v : fin 0 → α) (w : fin 0 → α) : v + w = vec_empty :=
  empty_eq (v + w)

@[simp] theorem cons_add {α : Type u} {n : ℕ} [Add α] (x : α) (v : fin n → α) (w : fin (Nat.succ n) → α) : vec_cons x v + w = vec_cons (x + vec_head w) (v + vec_tail w) := sorry

@[simp] theorem add_cons {α : Type u} {n : ℕ} [Add α] (v : fin (Nat.succ n) → α) (y : α) (w : fin n → α) : v + vec_cons y w = vec_cons (vec_head v + y) (vec_tail v + w) := sorry

@[simp] theorem head_add {α : Type u} {n : ℕ} [Add α] (a : fin (Nat.succ n) → α) (b : fin (Nat.succ n) → α) : vec_head (a + b) = vec_head a + vec_head b :=
  rfl

@[simp] theorem tail_add {α : Type u} {n : ℕ} [Add α] (a : fin (Nat.succ n) → α) (b : fin (Nat.succ n) → α) : vec_tail (a + b) = vec_tail a + vec_tail b :=
  rfl

@[simp] theorem empty_sub_empty {α : Type u} [Sub α] (v : fin 0 → α) (w : fin 0 → α) : v - w = vec_empty :=
  empty_eq (v - w)

@[simp] theorem cons_sub {α : Type u} {n : ℕ} [Sub α] (x : α) (v : fin n → α) (w : fin (Nat.succ n) → α) : vec_cons x v - w = vec_cons (x - vec_head w) (v - vec_tail w) := sorry

@[simp] theorem sub_cons {α : Type u} {n : ℕ} [Sub α] (v : fin (Nat.succ n) → α) (y : α) (w : fin n → α) : v - vec_cons y w = vec_cons (vec_head v - y) (vec_tail v - w) := sorry

@[simp] theorem head_sub {α : Type u} {n : ℕ} [Sub α] (a : fin (Nat.succ n) → α) (b : fin (Nat.succ n) → α) : vec_head (a - b) = vec_head a - vec_head b :=
  rfl

@[simp] theorem tail_sub {α : Type u} {n : ℕ} [Sub α] (a : fin (Nat.succ n) → α) (b : fin (Nat.succ n) → α) : vec_tail (a - b) = vec_tail a - vec_tail b :=
  rfl

@[simp] theorem zero_empty {α : Type u} [HasZero α] : 0 = vec_empty :=
  empty_eq 0

@[simp] theorem cons_zero_zero {α : Type u} {n : ℕ} [HasZero α] : vec_cons 0 0 = 0 := sorry

@[simp] theorem head_zero {α : Type u} {n : ℕ} [HasZero α] : vec_head 0 = 0 :=
  rfl

@[simp] theorem tail_zero {α : Type u} {n : ℕ} [HasZero α] : vec_tail 0 = 0 :=
  rfl

@[simp] theorem cons_eq_zero_iff {α : Type u} {n : ℕ} [HasZero α] {v : fin n → α} {x : α} : vec_cons x v = 0 ↔ x = 0 ∧ v = 0 := sorry

theorem cons_nonzero_iff {α : Type u} {n : ℕ} [HasZero α] {v : fin n → α} {x : α} : vec_cons x v ≠ 0 ↔ x ≠ 0 ∨ v ≠ 0 :=
  { mp := fun (h : vec_cons x v ≠ 0) => iff.mp not_and_distrib (h ∘ iff.mpr cons_eq_zero_iff),
    mpr := fun (h : x ≠ 0 ∨ v ≠ 0) => mt (iff.mp cons_eq_zero_iff) (iff.mpr not_and_distrib h) }

@[simp] theorem neg_empty {α : Type u} [Neg α] (v : fin 0 → α) : -v = vec_empty :=
  empty_eq (-v)

@[simp] theorem neg_cons {α : Type u} {n : ℕ} [Neg α] (x : α) (v : fin n → α) : -vec_cons x v = vec_cons (-x) (-v) := sorry

@[simp] theorem head_neg {α : Type u} {n : ℕ} [Neg α] (a : fin (Nat.succ n) → α) : vec_head (-a) = -vec_head a :=
  rfl

@[simp] theorem tail_neg {α : Type u} {n : ℕ} [Neg α] (a : fin (Nat.succ n) → α) : vec_tail (-a) = -vec_tail a :=
  rfl

@[simp] theorem minor_empty {α : Type u} {m' : Type u_1} {n' : Type u_2} {o' : Type u_3} [fintype m'] [fintype n'] [fintype o'] (A : matrix m' n' α) (row : fin 0 → m') (col : o' → n') : minor A row col = vec_empty :=
  empty_eq (minor A row col)

@[simp] theorem minor_cons_row {α : Type u} {m : ℕ} {m' : Type u_1} {n' : Type u_2} {o' : Type u_3} [fintype m'] [fintype n'] [fintype o'] (A : matrix m' n' α) (i : m') (row : fin m → m') (col : o' → n') : minor A (vec_cons i row) col = vec_cons (fun (j : o') => A i (col j)) (minor A row col) := sorry

