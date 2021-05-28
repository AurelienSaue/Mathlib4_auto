/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.finset.basic
import Mathlib.data.multiset.nat_antidiagonal
import PostPort

namespace Mathlib

/-!
# The "antidiagonal" {(0,n), (1,n-1), ..., (n,0)} as a finset.
-/

namespace finset


namespace nat


/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
  mk (multiset.nat.antidiagonal n) (multiset.nat.nodup_antidiagonal n)

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ prod.fst x + prod.snd x = n := sorry

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] theorem card_antidiagonal (n : ℕ) : card (antidiagonal n) = n + 1 := sorry

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] theorem antidiagonal_zero : antidiagonal 0 = singleton (0, 0) :=
  rfl

theorem antidiagonal_succ {n : ℕ} : antidiagonal (n + 1) =
  insert (0, n + 1)
    (map (function.embedding.prod_map (function.embedding.mk Nat.succ nat.succ_injective) (function.embedding.refl ℕ))
      (antidiagonal n)) := sorry

theorem map_swap_antidiagonal {n : ℕ} : map (function.embedding.mk prod.swap (function.right_inverse.injective prod.swap_right_inverse)) (antidiagonal n) =
  antidiagonal n := sorry

