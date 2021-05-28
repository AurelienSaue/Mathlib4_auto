/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.nodup
import Mathlib.data.list.nat_antidiagonal
import Mathlib.PostPort

namespace Mathlib

/-!
# The "antidiagonal" {(0,n), (1,n-1), ..., (n,0)} as a multiset.
-/

namespace multiset


namespace nat


/-- The antidiagonal of a natural number `n` is
    the multiset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : multiset (ℕ × ℕ) :=
  ↑(list.nat.antidiagonal n)

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} : x ∈ antidiagonal n ↔ prod.fst x + prod.snd x = n := sorry

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] theorem card_antidiagonal (n : ℕ) : coe_fn card (antidiagonal n) = n + 1 := sorry

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] theorem antidiagonal_zero : antidiagonal 0 = singleton (0, 0) :=
  rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
@[simp] theorem nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
  iff.mpr coe_nodup (list.nat.nodup_antidiagonal n)

@[simp] theorem antidiagonal_succ {n : ℕ} : antidiagonal (n + 1) = (0, n + 1) ::ₘ map (prod.map Nat.succ id) (antidiagonal n) := sorry

