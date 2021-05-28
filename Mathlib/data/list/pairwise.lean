/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace list


/- pairwise relation (generalized no duplicate) -/

theorem pairwise_iff {α : Type u} (R : α → α → Prop) : ∀ (ᾰ : List α),
  pairwise R ᾰ ↔
    ᾰ = [] ∨ Exists fun {a : α} => Exists fun {l : List α} => (∀ (a' : α), a' ∈ l → R a a') ∧ pairwise R l ∧ ᾰ = a :: l := sorry

theorem rel_of_pairwise_cons {α : Type u} {R : α → α → Prop} {a : α} {l : List α} (p : pairwise R (a :: l)) {a' : α} : a' ∈ l → R a a' :=
  and.left (iff.mp pairwise_cons p)

theorem pairwise_of_pairwise_cons {α : Type u} {R : α → α → Prop} {a : α} {l : List α} (p : pairwise R (a :: l)) : pairwise R l :=
  and.right (iff.mp pairwise_cons p)

theorem pairwise.tail {α : Type u} {R : α → α → Prop} {l : List α} (p : pairwise R l) : pairwise R (tail l) := sorry

theorem pairwise.imp_of_mem {α : Type u} {R : α → α → Prop} {S : α → α → Prop} {l : List α} (H : ∀ {a b : α}, a ∈ l → b ∈ l → R a b → S a b) (p : pairwise R l) : pairwise S l := sorry

theorem pairwise.imp {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (H : ∀ (a b : α), R a b → S a b) {l : List α} : pairwise R l → pairwise S l :=
  pairwise.imp_of_mem fun (a b : α) (_x : a ∈ l) (_x : b ∈ l) => H a b

theorem pairwise.and {α : Type u} {R : α → α → Prop} {S : α → α → Prop} {l : List α} : pairwise (fun (a b : α) => R a b ∧ S a b) l ↔ pairwise R l ∧ pairwise S l := sorry

theorem pairwise.imp₂ {α : Type u} {R : α → α → Prop} {S : α → α → Prop} {T : α → α → Prop} (H : ∀ (a b : α), R a b → S a b → T a b) {l : List α} (hR : pairwise R l) (hS : pairwise S l) : pairwise T l :=
  pairwise.imp (fun (a b : α) => And._oldrec (H a b)) (iff.mpr pairwise.and { left := hR, right := hS })

theorem pairwise.iff_of_mem {α : Type u} {R : α → α → Prop} {S : α → α → Prop} {l : List α} (H : ∀ {a b : α}, a ∈ l → b ∈ l → (R a b ↔ S a b)) : pairwise R l ↔ pairwise S l :=
  { mp := pairwise.imp_of_mem fun (a b : α) (m : a ∈ l) (m' : b ∈ l) => iff.mp (H m m'),
    mpr := pairwise.imp_of_mem fun (a b : α) (m : a ∈ l) (m' : b ∈ l) => iff.mpr (H m m') }

theorem pairwise.iff {α : Type u} {R : α → α → Prop} {S : α → α → Prop} (H : ∀ (a b : α), R a b ↔ S a b) {l : List α} : pairwise R l ↔ pairwise S l :=
  pairwise.iff_of_mem fun (a b : α) (_x : a ∈ l) (_x : b ∈ l) => H a b

theorem pairwise_of_forall {α : Type u} {R : α → α → Prop} {l : List α} (H : ∀ (x y : α), R x y) : pairwise R l := sorry

theorem pairwise.and_mem {α : Type u} {R : α → α → Prop} {l : List α} : pairwise R l ↔ pairwise (fun (x y : α) => x ∈ l ∧ y ∈ l ∧ R x y) l := sorry

theorem pairwise.imp_mem {α : Type u} {R : α → α → Prop} {l : List α} : pairwise R l ↔ pairwise (fun (x y : α) => x ∈ l → y ∈ l → R x y) l := sorry

theorem pairwise_of_sublist {α : Type u} {R : α → α → Prop} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → pairwise R l₂ → pairwise R l₁ := sorry

theorem forall_of_forall_of_pairwise {α : Type u} {R : α → α → Prop} (H : symmetric R) {l : List α} (H₁ : ∀ (x : α), x ∈ l → R x x) (H₂ : pairwise R l) (x : α) : x ∈ l → ∀ (y : α), y ∈ l → R x y := sorry

theorem forall_of_pairwise {α : Type u} {R : α → α → Prop} (H : symmetric R) {l : List α} (hl : pairwise R l) (a : α) : a ∈ l → ∀ (b : α), b ∈ l → a ≠ b → R a b :=
  forall_of_forall_of_pairwise (fun (a b : α) (h : a ≠ b → R a b) (hne : b ≠ a) => H (h (ne.symm hne)))
    (fun (_x : α) (_x_1 : _x ∈ l) (h : _x ≠ _x) => false.elim (h rfl))
    (pairwise.imp (fun (_x _x_1 : α) (h : R _x _x_1) (_x : _x ≠ _x_1) => h) hl)

theorem pairwise_singleton {α : Type u} (R : α → α → Prop) (a : α) : pairwise R [a] := sorry

theorem pairwise_pair {α : Type u} {R : α → α → Prop} {a : α} {b : α} : pairwise R [a, b] ↔ R a b := sorry

theorem pairwise_append {α : Type u} {R : α → α → Prop} {l₁ : List α} {l₂ : List α} : pairwise R (l₁ ++ l₂) ↔ pairwise R l₁ ∧ pairwise R l₂ ∧ ∀ (x : α), x ∈ l₁ → ∀ (y : α), y ∈ l₂ → R x y := sorry

theorem pairwise_append_comm {α : Type u} {R : α → α → Prop} (s : symmetric R) {l₁ : List α} {l₂ : List α} : pairwise R (l₁ ++ l₂) ↔ pairwise R (l₂ ++ l₁) := sorry

theorem pairwise_middle {α : Type u} {R : α → α → Prop} (s : symmetric R) {a : α} {l₁ : List α} {l₂ : List α} : pairwise R (l₁ ++ a :: l₂) ↔ pairwise R (a :: (l₁ ++ l₂)) := sorry

theorem pairwise_map {α : Type u} {β : Type v} {R : α → α → Prop} (f : β → α) {l : List β} : pairwise R (map f l) ↔ pairwise (fun (a b : β) => R (f a) (f b)) l := sorry

theorem pairwise_of_pairwise_map {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), S (f a) (f b) → R a b) {l : List α} (p : pairwise S (map f l)) : pairwise R l :=
  pairwise.imp H (iff.mp (pairwise_map f) p)

theorem pairwise_map_of_pairwise {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), R a b → S (f a) (f b)) {l : List α} (p : pairwise R l) : pairwise S (map f l) :=
  iff.mpr (pairwise_map f) (pairwise.imp H p)

theorem pairwise_filter_map {α : Type u} {β : Type v} {R : α → α → Prop} (f : β → Option α) {l : List β} : pairwise R (filter_map f l) ↔ pairwise (fun (a a' : β) => ∀ (b : α), b ∈ f a → ∀ (b' : α), b' ∈ f a' → R b b') l := sorry

theorem pairwise_filter_map_of_pairwise {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} (f : α → Option β) (H : ∀ (a a' : α), R a a' → ∀ (b : β), b ∈ f a → ∀ (b' : β), b' ∈ f a' → S b b') {l : List α} (p : pairwise R l) : pairwise S (filter_map f l) :=
  iff.mpr (pairwise_filter_map f) (pairwise.imp H p)

theorem pairwise_filter {α : Type u} {R : α → α → Prop} (p : α → Prop) [decidable_pred p] {l : List α} : pairwise R (filter p l) ↔ pairwise (fun (x y : α) => p x → p y → R x y) l := sorry

theorem pairwise_filter_of_pairwise {α : Type u} {R : α → α → Prop} (p : α → Prop) [decidable_pred p] {l : List α} : pairwise R l → pairwise R (filter p l) :=
  pairwise_of_sublist (filter_sublist l)

theorem pairwise_pmap {α : Type u} {β : Type v} {R : α → α → Prop} {p : β → Prop} {f : (b : β) → p b → α} {l : List β} (h : ∀ (x : β), x ∈ l → p x) : pairwise R (pmap f l h) ↔ pairwise (fun (b₁ b₂ : β) => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l := sorry

theorem pairwise.pmap {α : Type u} {β : Type v} {R : α → α → Prop} {l : List α} (hl : pairwise R l) {p : α → Prop} {f : (a : α) → p a → β} (h : ∀ (x : α), x ∈ l → p x) {S : β → β → Prop} (hS : ∀ {x : α} (hx : p x) {y : α} (hy : p y), R x y → S (f x hx) (f y hy)) : pairwise S (pmap f l h) :=
  iff.mpr (pairwise_pmap h)
    (pairwise.imp_of_mem (fun (a b : α) (ᾰ : a ∈ l) (ᾰ_1 : b ∈ l) (ᾰ_2 : R a b) (h₁ : p a) (h₂ : p b) => hS h₁ h₂ ᾰ_2) hl)

theorem pairwise_join {α : Type u} {R : α → α → Prop} {L : List (List α)} : pairwise R (join L) ↔
  (∀ (l : List α), l ∈ L → pairwise R l) ∧
    pairwise (fun (l₁ l₂ : List α) => ∀ (x : α), x ∈ l₁ → ∀ (y : α), y ∈ l₂ → R x y) L := sorry

@[simp] theorem pairwise_reverse {α : Type u} {R : α → α → Prop} {l : List α} : pairwise R (reverse l) ↔ pairwise (fun (x y : α) => R y x) l := sorry

theorem pairwise_iff_nth_le {α : Type u} {R : α → α → Prop} {l : List α} : pairwise R l ↔ ∀ (i j : ℕ) (h₁ : j < length l) (h₂ : i < j), R (nth_le l i (lt_trans h₂ h₁)) (nth_le l j h₁) := sorry

theorem pairwise_sublists' {α : Type u} {R : α → α → Prop} {l : List α} : pairwise R l → pairwise (lex (function.swap R)) (sublists' l) := sorry

theorem pairwise_sublists {α : Type u} {R : α → α → Prop} {l : List α} (H : pairwise R l) : pairwise (fun (l₁ l₂ : List α) => lex R (reverse l₁) (reverse l₂)) (sublists l) := sorry

/- pairwise reduct -/

@[simp] theorem pw_filter_nil {α : Type u} {R : α → α → Prop} [DecidableRel R] : pw_filter R [] = [] :=
  rfl

@[simp] theorem pw_filter_cons_of_pos {α : Type u} {R : α → α → Prop} [DecidableRel R] {a : α} {l : List α} (h : ∀ (b : α), b ∈ pw_filter R l → R a b) : pw_filter R (a :: l) = a :: pw_filter R l :=
  if_pos h

@[simp] theorem pw_filter_cons_of_neg {α : Type u} {R : α → α → Prop} [DecidableRel R] {a : α} {l : List α} (h : ¬∀ (b : α), b ∈ pw_filter R l → R a b) : pw_filter R (a :: l) = pw_filter R l :=
  if_neg h

theorem pw_filter_map {α : Type u} {β : Type v} {R : α → α → Prop} [DecidableRel R] (f : β → α) (l : List β) : pw_filter R (map f l) = map f (pw_filter (fun (x y : β) => R (f x) (f y)) l) := sorry

theorem pw_filter_sublist {α : Type u} {R : α → α → Prop} [DecidableRel R] (l : List α) : pw_filter R l <+ l := sorry

theorem pw_filter_subset {α : Type u} {R : α → α → Prop} [DecidableRel R] (l : List α) : pw_filter R l ⊆ l :=
  sublist.subset (pw_filter_sublist l)

theorem pairwise_pw_filter {α : Type u} {R : α → α → Prop} [DecidableRel R] (l : List α) : pairwise R (pw_filter R l) := sorry

theorem pw_filter_eq_self {α : Type u} {R : α → α → Prop} [DecidableRel R] {l : List α} : pw_filter R l = l ↔ pairwise R l := sorry

@[simp] theorem pw_filter_idempotent {α : Type u} {R : α → α → Prop} [DecidableRel R] {l : List α} : pw_filter R (pw_filter R l) = pw_filter R l :=
  iff.mpr pw_filter_eq_self (pairwise_pw_filter l)

theorem forall_mem_pw_filter {α : Type u} {R : α → α → Prop} [DecidableRel R] (neg_trans : ∀ {x y z : α}, R x z → R x y ∨ R y z) (a : α) (l : List α) : (∀ (b : α), b ∈ pw_filter R l → R a b) ↔ ∀ (b : α), b ∈ l → R a b := sorry

