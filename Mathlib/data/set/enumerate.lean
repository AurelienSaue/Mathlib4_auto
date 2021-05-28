/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Enumerate elements of a set with a select function.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.lattice
import Mathlib.tactic.wlog
import Mathlib.PostPort

universes u_1 

namespace Mathlib

namespace set


def enumerate {α : Type u_1} (sel : set α → Option α) : set α → ℕ → Option α :=
  sorry

theorem enumerate_eq_none_of_sel {α : Type u_1} (sel : set α → Option α) {s : set α} (h : sel s = none) {n : ℕ} : enumerate sel s n = none := sorry

theorem enumerate_eq_none {α : Type u_1} (sel : set α → Option α) {s : set α} {n₁ : ℕ} {n₂ : ℕ} : enumerate sel s n₁ = none → n₁ ≤ n₂ → enumerate sel s n₂ = none := sorry

theorem enumerate_mem {α : Type u_1} (sel : set α → Option α) (h_sel : ∀ (s : set α) (a : α), sel s = some a → a ∈ s) {s : set α} {n : ℕ} {a : α} : enumerate sel s n = some a → a ∈ s := sorry

theorem enumerate_inj {α : Type u_1} (sel : set α → Option α) {n₁ : ℕ} {n₂ : ℕ} {a : α} {s : set α} (h_sel : ∀ (s : set α) (a : α), sel s = some a → a ∈ s) (h₁ : enumerate sel s n₁ = some a) (h₂ : enumerate sel s n₂ = some a) : n₁ = n₂ := sorry

