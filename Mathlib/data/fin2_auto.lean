/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes l u 

namespace Mathlib

/-- An alternate definition of `fin n` defined as an inductive type
  instead of a subtype of `nat`. This is useful for its induction
  principle and different definitional equalities. -/
inductive fin2 : ℕ → Type where
| fz : {n : ℕ} → fin2 (Nat.succ n)
| fs : {n : ℕ} → fin2 n → fin2 (Nat.succ n)

namespace fin2


/-- Define a dependent function on `fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
protected def cases' {n : ℕ} {C : fin2 (Nat.succ n) → Sort u} (H1 : C fz)
    (H2 : (n_1 : fin2 n) → C (fs n_1)) (i : fin2 (Nat.succ n)) : C i :=
  sorry

/-- Ex falso. The dependent eliminator for the empty `fin2 0` type. -/
def elim0 {C : fin2 0 → Sort u} (i : fin2 0) : C i := sorry

/-- convert a `fin2` into a `nat` -/
def to_nat {n : ℕ} : fin2 n → ℕ := sorry

/-- convert a `nat` into a `fin2` if it is in range -/
def opt_of_nat {n : ℕ} (k : ℕ) : Option (fin2 n) := sorry

/-- `i + k : fin2 (n + k)` when `i : fin2 n` and `k : ℕ` -/
def add {n : ℕ} (i : fin2 n) (k : ℕ) : fin2 (n + k) := sorry

/-- `left k` is the embedding `fin2 n → fin2 (k + n)` -/
def left (k : ℕ) {n : ℕ} : fin2 n → fin2 (k + n) := sorry

/-- `insert_perm a` is a permutation of `fin2 n` with the following properties:
  * `insert_perm a i = i+1` if `i < a`
  * `insert_perm a a = 0`
  * `insert_perm a i = i` if `i > a` -/
def insert_perm {n : ℕ} : fin2 n → fin2 n → fin2 n := sorry

/-- `remap_left f k : fin2 (m + k) → fin2 (n + k)` applies the function
  `f : fin2 m → fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remap_left f k (m + i) = n + i`). -/
def remap_left {m : ℕ} {n : ℕ} (f : fin2 m → fin2 n) (k : ℕ) : fin2 (m + k) → fin2 (n + k) := sorry

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`. -/
class is_lt (m : ℕ) (n : ℕ) where
  h : m < n

protected instance is_lt.zero (n : ℕ) : is_lt 0 (Nat.succ n) := is_lt.mk (nat.succ_pos n)

protected instance is_lt.succ (m : ℕ) (n : ℕ) [l : is_lt m n] : is_lt (Nat.succ m) (Nat.succ n) :=
  is_lt.mk sorry

/-- Use type class inference to infer the boundedness proof, so that we
  can directly convert a `nat` into a `fin2 n`. This supports
  notation like `&1 : fin 3`. -/
def of_nat' {n : ℕ} (m : ℕ) [is_lt m n] : fin2 n := sorry

protected instance inhabited : Inhabited (fin2 1) := { default := fz }

end Mathlib