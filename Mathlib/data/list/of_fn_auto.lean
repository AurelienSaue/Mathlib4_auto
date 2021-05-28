/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.data.fin
import PostPort

universes u u_1 

namespace Mathlib

namespace list


/- of_fn -/

theorem length_of_fn_aux {α : Type u} {n : ℕ} (f : fin n → α) (m : ℕ) (h : m ≤ n) (l : List α) : length (of_fn_aux f m h l) = length l + m := sorry

@[simp] theorem length_of_fn {α : Type u} {n : ℕ} (f : fin n → α) : length (of_fn f) = n :=
  Eq.trans (length_of_fn_aux f n of_fn._proof_1 []) (zero_add n)

theorem nth_of_fn_aux {α : Type u} {n : ℕ} (f : fin n → α) (i : ℕ) (m : ℕ) (h : m ≤ n) (l : List α) : (∀ (i : ℕ), nth l i = of_fn_nth_val f (i + m)) → nth (of_fn_aux f m h l) i = of_fn_nth_val f i := sorry

@[simp] theorem nth_of_fn {α : Type u} {n : ℕ} (f : fin n → α) (i : ℕ) : nth (of_fn f) i = of_fn_nth_val f i := sorry

theorem nth_le_of_fn {α : Type u} {n : ℕ} (f : fin n → α) (i : fin n) : nth_le (of_fn f) (↑i) (Eq.symm (length_of_fn f) ▸ subtype.property i) = f i := sorry

@[simp] theorem nth_le_of_fn' {α : Type u} {n : ℕ} (f : fin n → α) {i : ℕ} (h : i < length (of_fn f)) : nth_le (of_fn f) i h = f { val := i, property := length_of_fn f ▸ h } :=
  nth_le_of_fn f { val := i, property := length_of_fn f ▸ h }

@[simp] theorem map_of_fn {α : Type u} {β : Type u_1} {n : ℕ} (f : fin n → α) (g : α → β) : map g (of_fn f) = of_fn (g ∘ f) := sorry

theorem array_eq_of_fn {α : Type u} {n : ℕ} (a : array n α) : array.to_list a = of_fn (array.read a) := sorry

@[simp] theorem of_fn_zero {α : Type u} (f : fin 0 → α) : of_fn f = [] :=
  rfl

@[simp] theorem of_fn_succ {α : Type u} {n : ℕ} (f : fin (Nat.succ n) → α) : of_fn f = f 0 :: of_fn fun (i : fin n) => f (fin.succ i) := sorry

theorem of_fn_nth_le {α : Type u} (l : List α) : (of_fn fun (i : fin (length l)) => nth_le l (↑i) (subtype.property i)) = l := sorry

-- not registered as a simp lemma, as otherwise it fires before `forall_mem_of_fn_iff` which

-- is much more useful

theorem mem_of_fn {α : Type u} {n : ℕ} (f : fin n → α) (a : α) : a ∈ of_fn f ↔ a ∈ set.range f := sorry

@[simp] theorem forall_mem_of_fn_iff {α : Type u} {n : ℕ} {f : fin n → α} {P : α → Prop} : (∀ (i : α), i ∈ of_fn f → P i) ↔ ∀ (j : fin n), P (f j) := sorry

@[simp] theorem of_fn_const {α : Type u} (n : ℕ) (c : α) : (of_fn fun (i : fin n) => c) = repeat c n := sorry

