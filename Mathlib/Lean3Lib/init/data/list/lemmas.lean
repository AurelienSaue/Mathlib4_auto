/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.list.basic
import Mathlib.Lean3Lib.init.function
import Mathlib.Lean3Lib.init.meta.default
import Mathlib.Lean3Lib.init.data.nat.lemmas
import Mathlib.Lean3Lib.init.meta.interactive
import Mathlib.Lean3Lib.init.meta.smt.rsimp
 

universes u v w w₂ w₁ 

namespace Mathlib

namespace list


/- append -/

@[simp] theorem nil_append {α : Type u} (s : List α) : [] ++ s = s :=
  rfl

@[simp] theorem cons_append {α : Type u} (x : α) (s : List α) (t : List α) : x :: s ++ t = x :: (s ++ t) :=
  rfl

@[simp] theorem append_nil {α : Type u} (t : List α) : t ++ [] = t := sorry

@[simp] theorem append_assoc {α : Type u} (s : List α) (t : List α) (u : List α) : s ++ t ++ u = s ++ (t ++ u) := sorry

/- length -/

theorem length_cons {α : Type u} (a : α) (l : List α) : length (a :: l) = length l + 1 :=
  rfl

@[simp] theorem length_append {α : Type u} (s : List α) (t : List α) : length (s ++ t) = length s + length t := sorry

@[simp] theorem length_repeat {α : Type u} (a : α) (n : ℕ) : length (repeat a n) = n := sorry

@[simp] theorem length_tail {α : Type u} (l : List α) : length (tail l) = length l - 1 :=
  list.cases_on l (Eq.refl (length (tail []))) fun (l_hd : α) (l_tl : List α) => Eq.refl (length (tail (l_hd :: l_tl)))

-- TODO(Leo): cleanup proof after arith dec proc

@[simp] theorem length_drop {α : Type u} (i : ℕ) (l : List α) : length (drop i l) = length l - i := sorry

/- map -/

theorem map_cons {α : Type u} {β : Type v} (f : α → β) (a : α) (l : List α) : map f (a :: l) = f a :: map f l :=
  rfl

@[simp] theorem map_append {α : Type u} {β : Type v} (f : α → β) (l₁ : List α) (l₂ : List α) : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂ := sorry

theorem map_singleton {α : Type u} {β : Type v} (f : α → β) (a : α) : map f [a] = [f a] :=
  rfl

@[simp] theorem map_id {α : Type u} (l : List α) : map id l = l := sorry

@[simp] theorem map_map {α : Type u} {β : Type v} {γ : Type w} (g : β → γ) (f : α → β) (l : List α) : map g (map f l) = map (g ∘ f) l := sorry

@[simp] theorem length_map {α : Type u} {β : Type v} (f : α → β) (l : List α) : length (map f l) = length l := sorry

/- bind -/

@[simp] theorem nil_bind {α : Type u} {β : Type v} (f : α → List β) : list.bind [] f = [] := sorry

@[simp] theorem cons_bind {α : Type u} {β : Type v} (x : α) (xs : List α) (f : α → List β) : list.bind (x :: xs) f = f x ++ list.bind xs f := sorry

@[simp] theorem append_bind {α : Type u} {β : Type v} (xs : List α) (ys : List α) (f : α → List β) : list.bind (xs ++ ys) f = list.bind xs f ++ list.bind ys f := sorry

/- mem -/

@[simp] theorem mem_nil_iff {α : Type u} (a : α) : a ∈ [] ↔ False :=
  iff.rfl

@[simp] theorem not_mem_nil {α : Type u} (a : α) : ¬a ∈ [] :=
  iff.mp (mem_nil_iff a)

@[simp] theorem mem_cons_self {α : Type u} (a : α) (l : List α) : a ∈ a :: l :=
  Or.inl rfl

@[simp] theorem mem_cons_iff {α : Type u} (a : α) (y : α) (l : List α) : a ∈ y :: l ↔ a = y ∨ a ∈ l :=
  iff.rfl

theorem mem_cons_eq {α : Type u} (a : α) (y : α) (l : List α) : a ∈ y :: l = (a = y ∨ a ∈ l) :=
  rfl

theorem mem_cons_of_mem {α : Type u} (y : α) {a : α} {l : List α} : a ∈ l → a ∈ y :: l :=
  fun (H : a ∈ l) => Or.inr H

theorem eq_or_mem_of_mem_cons {α : Type u} {a : α} {y : α} {l : List α} : a ∈ y :: l → a = y ∨ a ∈ l :=
  fun (h : a ∈ y :: l) => h

@[simp] theorem mem_append {α : Type u} {a : α} {s : List α} {t : List α} : a ∈ s ++ t ↔ a ∈ s ∨ a ∈ t := sorry

theorem mem_append_eq {α : Type u} (a : α) (s : List α) (t : List α) : a ∈ s ++ t = (a ∈ s ∨ a ∈ t) :=
  propext mem_append

theorem mem_append_left {α : Type u} {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : a ∈ l₁ ++ l₂ :=
  iff.mpr mem_append (Or.inl h)

theorem mem_append_right {α : Type u} {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ++ l₂ :=
  iff.mpr mem_append (Or.inr h)

@[simp] theorem not_bex_nil {α : Type u} (p : α → Prop) : ¬∃ (x : α), ∃ (H : x ∈ []), p x := sorry

@[simp] theorem ball_nil {α : Type u} (p : α → Prop) (x : α) (H : x ∈ []) : p x :=
  false.elim

@[simp] theorem bex_cons {α : Type u} (p : α → Prop) (a : α) (l : List α) : (∃ (x : α), ∃ (H : x ∈ a :: l), p x) ↔ p a ∨ ∃ (x : α), ∃ (H : x ∈ l), p x := sorry

@[simp] theorem ball_cons {α : Type u} (p : α → Prop) (a : α) (l : List α) : (∀ (x : α), x ∈ a :: l → p x) ↔ p a ∧ ∀ (x : α), x ∈ l → p x := sorry

/- list subset -/

protected def subset {α : Type u} (l₁ : List α) (l₂ : List α) :=
  ∀ {a : α}, a ∈ l₁ → a ∈ l₂

protected instance has_subset {α : Type u} : has_subset (List α) :=
  has_subset.mk list.subset

@[simp] theorem nil_subset {α : Type u} (l : List α) : [] ⊆ l :=
  fun (b : α) (i : b ∈ []) => false.elim (iff.mp (mem_nil_iff b) i)

@[simp] theorem subset.refl {α : Type u} (l : List α) : l ⊆ l :=
  fun (b : α) (i : b ∈ l) => i

theorem subset.trans {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  fun (b : α) (i : b ∈ l₁) => h₂ (h₁ i)

@[simp] theorem subset_cons {α : Type u} (a : α) (l : List α) : l ⊆ a :: l :=
  fun (b : α) (i : b ∈ l) => Or.inr i

theorem subset_of_cons_subset {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : a :: l₁ ⊆ l₂ → l₁ ⊆ l₂ :=
  fun (s : a :: l₁ ⊆ l₂) (b : α) (i : b ∈ l₁) => s (mem_cons_of_mem a i)

theorem cons_subset_cons {α : Type u} {l₁ : List α} {l₂ : List α} (a : α) (s : l₁ ⊆ l₂) : a :: l₁ ⊆ a :: l₂ :=
  fun (b : α) (hin : b ∈ a :: l₁) =>
    or.elim (eq_or_mem_of_mem_cons hin) (fun (e : b = a) => Or.inl e) fun (i : b ∈ l₁) => Or.inr (s i)

@[simp] theorem subset_append_left {α : Type u} (l₁ : List α) (l₂ : List α) : l₁ ⊆ l₁ ++ l₂ :=
  fun (b : α) => mem_append_left l₂

@[simp] theorem subset_append_right {α : Type u} (l₁ : List α) (l₂ : List α) : l₂ ⊆ l₁ ++ l₂ :=
  fun (b : α) => mem_append_right l₁

theorem subset_cons_of_subset {α : Type u} (a : α) {l₁ : List α} {l₂ : List α} : l₁ ⊆ l₂ → l₁ ⊆ a :: l₂ :=
  fun (s : l₁ ⊆ l₂) (a_1 : α) (i : a_1 ∈ l₁) => Or.inr (s i)

theorem eq_nil_of_length_eq_zero {α : Type u} {l : List α} : length l = 0 → l = [] := sorry

theorem ne_nil_of_length_eq_succ {α : Type u} {l : List α} {n : ℕ} : length l = Nat.succ n → l ≠ [] := sorry

@[simp] theorem length_map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l₁ : List α) (l₂ : List β) : length (map₂ f l₁ l₂) = min (length l₁) (length l₂) := sorry

@[simp] theorem length_take {α : Type u} (i : ℕ) (l : List α) : length (take i l) = min i (length l) := sorry

theorem length_take_le {α : Type u} (n : ℕ) (l : List α) : length (take n l) ≤ n := sorry

theorem length_remove_nth {α : Type u} (l : List α) (i : ℕ) : i < length l → length (remove_nth l i) = length l - 1 := sorry

@[simp] theorem partition_eq_filter_filter {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : partition p l = (filter p l, filter (Not ∘ p) l) := sorry

/- sublists -/

inductive sublist {α : Type u} : List α → List α → Prop
where
| slnil : sublist [] []
| cons : ∀ (l₁ l₂ : List α) (a : α), sublist l₁ l₂ → sublist l₁ (a :: l₂)
| cons2 : ∀ (l₁ l₂ : List α) (a : α), sublist l₁ l₂ → sublist (a :: l₁) (a :: l₂)

infixl:50 " <+ " => Mathlib.list.sublist

theorem length_le_of_sublist {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → length l₁ ≤ length l₂ := sorry

/- filter -/

@[simp] theorem filter_nil {α : Type u} (p : α → Prop) [h : decidable_pred p] : filter p [] = [] :=
  rfl

@[simp] theorem filter_cons_of_pos {α : Type u} {p : α → Prop} [h : decidable_pred p] {a : α} (l : List α) : p a → filter p (a :: l) = a :: filter p l :=
  fun (pa : p a) => if_pos pa

@[simp] theorem filter_cons_of_neg {α : Type u} {p : α → Prop} [h : decidable_pred p] {a : α} (l : List α) : ¬p a → filter p (a :: l) = filter p l :=
  fun (pa : ¬p a) => if_neg pa

@[simp] theorem filter_append {α : Type u} {p : α → Prop} [h : decidable_pred p] (l₁ : List α) (l₂ : List α) : filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂ := sorry

@[simp] theorem filter_sublist {α : Type u} {p : α → Prop} [h : decidable_pred p] (l : List α) : filter p l <+ l := sorry

/- map_accumr -/

-- This runs a function over a list returning the intermediate results and a

-- a final result.

def map_accumr {α : Type u} {β : Type v} {σ : Type w₂} (f : α → σ → σ × β) : List α → σ → σ × List β :=
  sorry

@[simp] theorem length_map_accumr {α : Type u} {β : Type v} {σ : Type w₂} (f : α → σ → σ × β) (x : List α) (s : σ) : length (prod.snd (map_accumr f x s)) = length x := sorry

-- This runs a function over two lists returning the intermediate results and a

-- a final result.

def map_accumr₂ {α : Type u} {β : Type v} {φ : Type w₁} {σ : Type w₂} (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ :=
  sorry

@[simp] theorem length_map_accumr₂ {α : Type u} {β : Type v} {φ : Type w₁} {σ : Type w₂} (f : α → β → σ → σ × φ) (x : List α) (y : List β) (c : σ) : length (prod.snd (map_accumr₂ f x y c)) = min (length x) (length y) := sorry

