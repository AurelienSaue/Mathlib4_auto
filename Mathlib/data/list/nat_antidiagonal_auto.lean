/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.range
import Mathlib.PostPort

namespace Mathlib

namespace list


namespace nat


/-- The antidiagonal of a natural number `n` is the list of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : List (ℕ × ℕ) := map (fun (i : ℕ) => (i, n - i)) (range (n + 1))

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] theorem mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
    x ∈ antidiagonal n ↔ prod.fst x + prod.snd x = n :=
  sorry

/-- The length of the antidiagonal of `n` is `n+1`. -/
@[simp] theorem length_antidiagonal (n : ℕ) : length (antidiagonal n) = n + 1 := sorry

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] theorem antidiagonal_zero : antidiagonal 0 = [(0, 0)] := rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
theorem nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
  nodup_map (function.left_inverse.injective fun (i : ℕ) => rfl) (nodup_range (n + 1))

@[simp] theorem antidiagonal_succ {n : ℕ} :
    antidiagonal (n + 1) = (0, n + 1) :: map (prod.map Nat.succ id) (antidiagonal n) :=
  sorry

end Mathlib