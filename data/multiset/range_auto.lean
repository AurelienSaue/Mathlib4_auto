/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.multiset.basic
import Mathlib.data.list.range
import PostPort

namespace Mathlib

namespace multiset


/- range -/

/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : multiset ℕ :=
  ↑(list.range n)

@[simp] theorem range_zero : range 0 = 0 :=
  rfl

@[simp] theorem range_succ (n : ℕ) : range (Nat.succ n) = n ::ₘ range n := sorry

@[simp] theorem card_range (n : ℕ) : coe_fn card (range n) = n :=
  list.length_range n

theorem range_subset {m : ℕ} {n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
  list.range_subset

@[simp] theorem mem_range {m : ℕ} {n : ℕ} : m ∈ range n ↔ m < n :=
  list.mem_range

@[simp] theorem not_mem_range_self {n : ℕ} : ¬n ∈ range n :=
  list.not_mem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  list.self_mem_range_succ n

