/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro and Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.basic
import Mathlib.data.list.range
import Mathlib.PostPort

namespace Mathlib

namespace int


/-- List enumerating `[m, n)`. -/
def range (m : ℤ) (n : ℤ) : List ℤ := list.map (fun (r : ℕ) => m + ↑r) (list.range (to_nat (n - m)))

theorem mem_range_iff {m : ℤ} {n : ℤ} {r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n := sorry

protected instance decidable_le_lt (P : ℤ → Prop) [decidable_pred P] (m : ℤ) (n : ℤ) :
    Decidable (∀ (r : ℤ), m ≤ r → r < n → P r) :=
  decidable_of_iff (∀ (r : ℤ), r ∈ range m n → P r) sorry

protected instance decidable_le_le (P : ℤ → Prop) [decidable_pred P] (m : ℤ) (n : ℤ) :
    Decidable (∀ (r : ℤ), m ≤ r → r ≤ n → P r) :=
  decidable_of_iff (∀ (r : ℤ), r ∈ range m (n + 1) → P r) sorry

protected instance decidable_lt_lt (P : ℤ → Prop) [decidable_pred P] (m : ℤ) (n : ℤ) :
    Decidable (∀ (r : ℤ), m < r → r < n → P r) :=
  int.decidable_le_lt P (m + 1) n

protected instance decidable_lt_le (P : ℤ → Prop) [decidable_pred P] (m : ℤ) (n : ℤ) :
    Decidable (∀ (r : ℤ), m < r → r ≤ n → P r) :=
  int.decidable_le_le P (m + 1) n

end Mathlib