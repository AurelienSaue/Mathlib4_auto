/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pnat.basic
import Mathlib.data.finset.intervals
import Mathlib.PostPort

namespace Mathlib

namespace pnat


/-- `Ico l u` is the set of positive natural numbers `l ≤ k < u`. -/
def Ico (l : ℕ+) (u : ℕ+) : finset ℕ+ :=
  finset.map
    (function.embedding.mk (fun (n : Subtype fun (x : ℕ) => x ∈ finset.Ico ↑l ↑u) => { val := ↑n, property := sorry })
      sorry)
    (finset.attach (finset.Ico ↑l ↑u))

@[simp] theorem Ico.mem {n : ℕ+} {m : ℕ+} {l : ℕ+} : l ∈ Ico n m ↔ n ≤ l ∧ l < m := sorry

@[simp] theorem Ico.card (l : ℕ+) (u : ℕ+) : finset.card (Ico l u) = ↑u - ↑l := sorry

