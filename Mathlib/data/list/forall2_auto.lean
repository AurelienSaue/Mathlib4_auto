/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.basic
import PostPort

universes u v w z 

namespace Mathlib

namespace list


/- forall₂ -/

theorem forall₂_iff {α : Type u} {β : Type v} (R : α → β → Prop) : ∀ (ᾰ : List α) (ᾰ_1 : List β),
  forall₂ R ᾰ ᾰ_1 ↔
    ᾰ = [] ∧ ᾰ_1 = [] ∨
      Exists
        fun {a : α} =>
          Exists
            fun {b : β} =>
              Exists
                fun {l₁ : List α} => Exists fun {l₂ : List β} => R a b ∧ forall₂ R l₁ l₂ ∧ ᾰ = a :: l₁ ∧ ᾰ_1 = b :: l₂ := sorry

@[simp] theorem forall₂_cons {α : Type u} {β : Type v} {R : α → β → Prop} {a : α} {b : β} {l₁ : List α} {l₂ : List β} : forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ forall₂ R l₁ l₂ := sorry

theorem forall₂.imp {α : Type u} {β : Type v} {R : α → β → Prop} {S : α → β → Prop} (H : ∀ (a : α) (b : β), R a b → S a b) {l₁ : List α} {l₂ : List β} (h : forall₂ R l₁ l₂) : forall₂ S l₁ l₂ := sorry

theorem forall₂.mp {α : Type u} {β : Type v} {r : α → β → Prop} {q : α → β → Prop} {s : α → β → Prop} (h : ∀ (a : α) (b : β), r a b → q a b → s a b) {l₁ : List α} {l₂ : List β} : forall₂ r l₁ l₂ → forall₂ q l₁ l₂ → forall₂ s l₁ l₂ := sorry

theorem forall₂.flip {α : Type u} {β : Type v} {r : α → β → Prop} {a : List α} {b : List β} : forall₂ (flip r) b a → forall₂ r a b := sorry

theorem forall₂_same {α : Type u} {r : α → α → Prop} {l : List α} : (∀ (x : α), x ∈ l → r x x) → forall₂ r l l := sorry

theorem forall₂_refl {α : Type u} {r : α → α → Prop} [is_refl α r] (l : List α) : forall₂ r l l :=
  forall₂_same fun (a : α) (h : a ∈ l) => is_refl.refl a

theorem forall₂_eq_eq_eq {α : Type u} : forall₂ Eq = Eq := sorry

@[simp] theorem forall₂_nil_left_iff {α : Type u} {β : Type v} {r : α → β → Prop} {l : List β} : forall₂ r [] l ↔ l = [] := sorry

@[simp] theorem forall₂_nil_right_iff {α : Type u} {β : Type v} {r : α → β → Prop} {l : List α} : forall₂ r l [] ↔ l = [] := sorry

theorem forall₂_cons_left_iff {α : Type u} {β : Type v} {r : α → β → Prop} {a : α} {l : List α} {u : List β} : forall₂ r (a :: l) u ↔ ∃ (b : β), ∃ (u' : List β), r a b ∧ forall₂ r l u' ∧ u = b :: u' := sorry

theorem forall₂_cons_right_iff {α : Type u} {β : Type v} {r : α → β → Prop} {b : β} {l : List β} {u : List α} : forall₂ r u (b :: l) ↔ ∃ (a : α), ∃ (u' : List α), r a b ∧ forall₂ r u' l ∧ u = a :: u' := sorry

theorem forall₂_and_left {α : Type u} {β : Type v} {r : α → β → Prop} {p : α → Prop} (l : List α) (u : List β) : forall₂ (fun (a : α) (b : β) => p a ∧ r a b) l u ↔ (∀ (a : α), a ∈ l → p a) ∧ forall₂ r l u := sorry

@[simp] theorem forall₂_map_left_iff {α : Type u} {β : Type v} {γ : Type w} {r : α → β → Prop} {f : γ → α} {l : List γ} {u : List β} : forall₂ r (map f l) u ↔ forall₂ (fun (c : γ) (b : β) => r (f c) b) l u := sorry

@[simp] theorem forall₂_map_right_iff {α : Type u} {β : Type v} {γ : Type w} {r : α → β → Prop} {f : γ → β} {l : List α} {u : List γ} : forall₂ r l (map f u) ↔ forall₂ (fun (a : α) (c : γ) => r a (f c)) l u := sorry

theorem left_unique_forall₂ {α : Type u} {β : Type v} {r : α → β → Prop} (hr : relator.left_unique r) : relator.left_unique (forall₂ r) := sorry

theorem right_unique_forall₂ {α : Type u} {β : Type v} {r : α → β → Prop} (hr : relator.right_unique r) : relator.right_unique (forall₂ r) := sorry

theorem bi_unique_forall₂ {α : Type u} {β : Type v} {r : α → β → Prop} (hr : relator.bi_unique r) : relator.bi_unique (forall₂ r) :=
  { left := fun (a : List α) (b : List β) (c : List α) => left_unique_forall₂ (and.left hr),
    right := fun (a : List α) (b c : List β) => right_unique_forall₂ (and.right hr) }

theorem forall₂_length_eq {α : Type u} {β : Type v} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} : forall₂ R l₁ l₂ → length l₁ = length l₂ := sorry

theorem forall₂_zip {α : Type u} {β : Type v} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} : forall₂ R l₁ l₂ → ∀ {a : α} {b : β}, (a, b) ∈ zip l₁ l₂ → R a b := sorry

theorem forall₂_iff_zip {α : Type u} {β : Type v} {R : α → β → Prop} {l₁ : List α} {l₂ : List β} : forall₂ R l₁ l₂ ↔ length l₁ = length l₂ ∧ ∀ {a : α} {b : β}, (a, b) ∈ zip l₁ l₂ → R a b := sorry

theorem forall₂_take {α : Type u} {β : Type v} {R : α → β → Prop} (n : ℕ) {l₁ : List α} {l₂ : List β} : forall₂ R l₁ l₂ → forall₂ R (take n l₁) (take n l₂) := sorry

theorem forall₂_drop {α : Type u} {β : Type v} {R : α → β → Prop} (n : ℕ) {l₁ : List α} {l₂ : List β} : forall₂ R l₁ l₂ → forall₂ R (drop n l₁) (drop n l₂) := sorry

theorem forall₂_take_append {α : Type u} {β : Type v} {R : α → β → Prop} (l : List α) (l₁ : List β) (l₂ : List β) (h : forall₂ R l (l₁ ++ l₂)) : forall₂ R (take (length l₁) l) l₁ :=
  (fun (h' : forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂))) =>
      eq.mp (Eq._oldrec (Eq.refl (forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)))) (take_left l₁ l₂)) h')
    (forall₂_take (length l₁) h)

theorem forall₂_drop_append {α : Type u} {β : Type v} {R : α → β → Prop} (l : List α) (l₁ : List β) (l₂ : List β) (h : forall₂ R l (l₁ ++ l₂)) : forall₂ R (drop (length l₁) l) l₂ :=
  (fun (h' : forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂))) =>
      eq.mp (Eq._oldrec (Eq.refl (forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)))) (drop_left l₁ l₂)) h')
    (forall₂_drop (length l₁) h)

theorem rel_mem {α : Type u} {β : Type v} {r : α → β → Prop} (hr : relator.bi_unique r) : relator.lift_fun r (forall₂ r ⇒ Iff) has_mem.mem has_mem.mem := sorry

theorem rel_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} {r : α → β → Prop} {p : γ → δ → Prop} : relator.lift_fun (r ⇒ p) (forall₂ r ⇒ forall₂ p) map map := sorry

theorem rel_append {α : Type u} {β : Type v} {r : α → β → Prop} : relator.lift_fun (forall₂ r) (forall₂ r ⇒ forall₂ r) append append := sorry

theorem rel_join {α : Type u} {β : Type v} {r : α → β → Prop} : relator.lift_fun (forall₂ (forall₂ r)) (forall₂ r) join join := sorry

theorem rel_bind {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} {r : α → β → Prop} {p : γ → δ → Prop} : relator.lift_fun (forall₂ r) ((r ⇒ forall₂ p) ⇒ forall₂ p) list.bind list.bind :=
  fun (a : List α) (b : List β) (h₁ : forall₂ r a b) (f : α → List γ) (g : β → List δ)
    (h₂ : relator.lift_fun r (forall₂ p) f g) => rel_join (rel_map h₂ h₁)

theorem rel_foldl {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} {r : α → β → Prop} {p : γ → δ → Prop} : relator.lift_fun (p ⇒ r ⇒ p) (p ⇒ forall₂ r ⇒ p) foldl foldl := sorry

theorem rel_foldr {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} {r : α → β → Prop} {p : γ → δ → Prop} : relator.lift_fun (r ⇒ p ⇒ p) (p ⇒ forall₂ r ⇒ p) foldr foldr := sorry

theorem rel_filter {α : Type u} {β : Type v} {r : α → β → Prop} {p : α → Prop} {q : β → Prop} [decidable_pred p] [decidable_pred q] (hpq : relator.lift_fun r Iff p q) : relator.lift_fun (forall₂ r) (forall₂ r) (filter p) (filter q) := sorry

theorem filter_map_cons {α : Type u} {β : Type v} (f : α → Option β) (a : α) (l : List α) : filter_map f (a :: l) = option.cases_on (f a) (filter_map f l) fun (b : β) => b :: filter_map f l := sorry

theorem rel_filter_map {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} {r : α → β → Prop} {p : γ → δ → Prop} : relator.lift_fun (r ⇒ option.rel p) (forall₂ r ⇒ forall₂ p) filter_map filter_map := sorry

theorem rel_sum {α : Type u} {β : Type v} {r : α → β → Prop} [add_monoid α] [add_monoid β] (h : r 0 0) (hf : relator.lift_fun r (r ⇒ r) Add.add Add.add) : relator.lift_fun (forall₂ r) r sum sum :=
  rel_foldl hf h

