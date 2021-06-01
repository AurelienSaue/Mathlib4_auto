/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.basic
import Mathlib.logic.function.iterate
import Mathlib.data.nat.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Inequalities on iterates

In this file we prove some inequalities comparing `f^[n] x` and `g^[n] x` where `f` and `g` are
two self-maps that commute with each other.

Current selection of inequalities is motivated by formalization of the rotation number of
a circle homeomorphism.
-/

namespace monotone


theorem seq_le_seq {α : Type u_1} [preorder α] {f : α → α} {x : ℕ → α} {y : ℕ → α} (hf : monotone f)
    (n : ℕ) (h₀ : x 0 ≤ y 0) (hx : ∀ (k : ℕ), k < n → x (k + 1) ≤ f (x k))
    (hy : ∀ (k : ℕ), k < n → f (y k) ≤ y (k + 1)) : x n ≤ y n :=
  sorry

theorem seq_pos_lt_seq_of_lt_of_le {α : Type u_1} [preorder α] {f : α → α} {x : ℕ → α} {y : ℕ → α}
    (hf : monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ (k : ℕ), k < n → x (k + 1) < f (x k)) (hy : ∀ (k : ℕ), k < n → f (y k) ≤ y (k + 1)) :
    x n < y n :=
  sorry

theorem seq_pos_lt_seq_of_le_of_lt {α : Type u_1} [preorder α] {f : α → α} {x : ℕ → α} {y : ℕ → α}
    (hf : monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ (k : ℕ), k < n → x (k + 1) ≤ f (x k)) (hy : ∀ (k : ℕ), k < n → f (y k) < y (k + 1)) :
    x n < y n :=
  seq_pos_lt_seq_of_lt_of_le (monotone.order_dual hf) hn h₀ hy hx

theorem seq_lt_seq_of_lt_of_le {α : Type u_1} [preorder α] {f : α → α} {x : ℕ → α} {y : ℕ → α}
    (hf : monotone f) (n : ℕ) (h₀ : x 0 < y 0) (hx : ∀ (k : ℕ), k < n → x (k + 1) < f (x k))
    (hy : ∀ (k : ℕ), k < n → f (y k) ≤ y (k + 1)) : x n < y n :=
  sorry

theorem seq_lt_seq_of_le_of_lt {α : Type u_1} [preorder α] {f : α → α} {x : ℕ → α} {y : ℕ → α}
    (hf : monotone f) (n : ℕ) (h₀ : x 0 < y 0) (hx : ∀ (k : ℕ), k < n → x (k + 1) ≤ f (x k))
    (hy : ∀ (k : ℕ), k < n → f (y k) < y (k + 1)) : x n < y n :=
  seq_lt_seq_of_lt_of_le (monotone.order_dual hf) n h₀ hy hx

end monotone


namespace function


namespace commute


theorem iterate_le_of_map_le {α : Type u_1} [preorder α] {f : α → α} {g : α → α} (h : commute f g)
    (hf : monotone f) (hg : monotone g) {x : α} (hx : f x ≤ g x) (n : ℕ) :
    nat.iterate f n x ≤ nat.iterate g n x :=
  sorry

theorem iterate_pos_lt_of_map_lt {α : Type u_1} [preorder α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : monotone f) (hg : strict_mono g) {x : α} (hx : f x < g x) {n : ℕ}
    (hn : 0 < n) : nat.iterate f n x < nat.iterate g n x :=
  sorry

theorem iterate_pos_lt_of_map_lt' {α : Type u_1} [preorder α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : strict_mono f) (hg : monotone g) {x : α} (hx : f x < g x) {n : ℕ}
    (hn : 0 < n) : nat.iterate f n x < nat.iterate g n x :=
  iterate_pos_lt_of_map_lt (symm h) (monotone.order_dual hg) (strict_mono.order_dual hf) hx hn

theorem iterate_pos_lt_iff_map_lt {α : Type u_1} [linear_order α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : monotone f) (hg : strict_mono g) {x : α} {n : ℕ} (hn : 0 < n) :
    nat.iterate f n x < nat.iterate g n x ↔ f x < g x :=
  sorry

theorem iterate_pos_lt_iff_map_lt' {α : Type u_1} [linear_order α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : strict_mono f) (hg : monotone g) {x : α} {n : ℕ} (hn : 0 < n) :
    nat.iterate f n x < nat.iterate g n x ↔ f x < g x :=
  iterate_pos_lt_iff_map_lt (symm h) (monotone.order_dual hg) (strict_mono.order_dual hf) hn

theorem iterate_pos_le_iff_map_le {α : Type u_1} [linear_order α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : monotone f) (hg : strict_mono g) {x : α} {n : ℕ} (hn : 0 < n) :
    nat.iterate f n x ≤ nat.iterate g n x ↔ f x ≤ g x :=
  sorry

theorem iterate_pos_le_iff_map_le' {α : Type u_1} [linear_order α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : strict_mono f) (hg : monotone g) {x : α} {n : ℕ} (hn : 0 < n) :
    nat.iterate f n x ≤ nat.iterate g n x ↔ f x ≤ g x :=
  sorry

theorem iterate_pos_eq_iff_map_eq {α : Type u_1} [linear_order α] {f : α → α} {g : α → α}
    (h : commute f g) (hf : monotone f) (hg : strict_mono g) {x : α} {n : ℕ} (hn : 0 < n) :
    nat.iterate f n x = nat.iterate g n x ↔ f x = g x :=
  sorry

end commute


end function


namespace monotone


/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
theorem iterate_le_of_le {α : Type u_1} [preorder α] {f : α → α} {g : α → α} (hf : monotone f)
    (h : f ≤ g) (n : ℕ) : nat.iterate f n ≤ nat.iterate g n :=
  sorry

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
theorem iterate_ge_of_ge {α : Type u_1} [preorder α] {f : α → α} {g : α → α} (hg : monotone g)
    (h : f ≤ g) (n : ℕ) : nat.iterate f n ≤ nat.iterate g n :=
  iterate_le_of_le (monotone.order_dual hg) h n

end Mathlib