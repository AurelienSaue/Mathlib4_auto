/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.order_functions
import Mathlib.control.monad.basic
import Mathlib.data.nat.choose.basic
import Mathlib.order.rel_classes
import Mathlib.PostPort

universes u v w u_1 u_2 u_3 

namespace Mathlib

/-!
# Basic properties of lists
-/

namespace list


protected instance nil.is_left_id {α : Type u} : is_left_id (List α) append [] :=
  is_left_id.mk nil_append

protected instance nil.is_right_id {α : Type u} : is_right_id (List α) append [] :=
  is_right_id.mk append_nil

protected instance has_append.append.is_associative {α : Type u} : is_associative (List α) append :=
  is_associative.mk append_assoc

theorem cons_ne_nil {α : Type u} (a : α) (l : List α) : a :: l ≠ [] :=
  fun (ᾰ : a :: l = []) => eq.dcases_on ᾰ (fun (H_1 : [] = a :: l) => list.no_confusion H_1) (Eq.refl []) (HEq.refl ᾰ)

theorem cons_ne_self {α : Type u} (a : α) (l : List α) : a :: l ≠ l :=
  mt (congr_arg length) (nat.succ_ne_self (length l))

theorem head_eq_of_cons_eq {α : Type u} {h₁ : α} {h₂ : α} {t₁ : List α} {t₂ : List α} : h₁ :: t₁ = h₂ :: t₂ → h₁ = h₂ :=
  fun (Peq : h₁ :: t₁ = h₂ :: t₂) => list.no_confusion Peq fun (Pheq : h₁ = h₂) (Pteq : t₁ = t₂) => Pheq

theorem tail_eq_of_cons_eq {α : Type u} {h₁ : α} {h₂ : α} {t₁ : List α} {t₂ : List α} : h₁ :: t₁ = h₂ :: t₂ → t₁ = t₂ :=
  fun (Peq : h₁ :: t₁ = h₂ :: t₂) => list.no_confusion Peq fun (Pheq : h₁ = h₂) (Pteq : t₁ = t₂) => Pteq

@[simp] theorem cons_injective {α : Type u} {a : α} : function.injective (List.cons a) :=
  fun (l₁ l₂ : List α) (Pe : a :: l₁ = a :: l₂) => tail_eq_of_cons_eq Pe

theorem cons_inj {α : Type u} (a : α) {l : List α} {l' : List α} : a :: l = a :: l' ↔ l = l' :=
  function.injective.eq_iff cons_injective

theorem exists_cons_of_ne_nil {α : Type u} {l : List α} (h : l ≠ []) : ∃ (b : α), ∃ (L : List α), l = b :: L := sorry

/-! ### mem -/

theorem mem_singleton_self {α : Type u} (a : α) : a ∈ [a] :=
  mem_cons_self a []

theorem eq_of_mem_singleton {α : Type u} {a : α} {b : α} : a ∈ [b] → a = b :=
  fun (this : a ∈ [b]) =>
    or.elim (eq_or_mem_of_mem_cons this) (fun (this : a = b) => this) fun (this : a ∈ []) => absurd this (not_mem_nil a)

@[simp] theorem mem_singleton {α : Type u} {a : α} {b : α} : a ∈ [b] ↔ a = b :=
  { mp := eq_of_mem_singleton, mpr := Or.inl }

theorem mem_of_mem_cons_of_mem {α : Type u} {a : α} {b : α} {l : List α} : a ∈ b :: l → b ∈ l → a ∈ l := sorry

theorem eq_or_ne_mem_of_mem {α : Type u} {a : α} {b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ a ≠ b ∧ a ∈ l :=
  classical.by_cases Or.inl
    fun (this : a ≠ b) => or.elim h Or.inl fun (h : list.mem a l) => Or.inr { left := this, right := h }

theorem not_mem_append {α : Type u} {a : α} {s : List α} {t : List α} (h₁ : ¬a ∈ s) (h₂ : ¬a ∈ t) : ¬a ∈ s ++ t :=
  mt (iff.mp mem_append) (iff.mpr not_or_distrib { left := h₁, right := h₂ })

theorem ne_nil_of_mem {α : Type u} {a : α} {l : List α} (h : a ∈ l) : l ≠ [] :=
  id fun (e : l = []) => false.dcases_on (fun (h : a ∈ []) => False) (eq.mp (Eq._oldrec (Eq.refl (a ∈ l)) e) h)

theorem mem_split {α : Type u} {a : α} {l : List α} (h : a ∈ l) : ∃ (s : List α), ∃ (t : List α), l = s ++ a :: t := sorry

theorem mem_of_ne_of_mem {α : Type u} {a : α} {y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  or.elim (eq_or_mem_of_mem_cons h₂) (fun (e : a = y) => absurd e h₁) fun (r : a ∈ l) => r

theorem ne_of_not_mem_cons {α : Type u} {a : α} {b : α} {l : List α} : ¬a ∈ b :: l → a ≠ b :=
  fun (nin : ¬a ∈ b :: l) (aeqb : a = b) => absurd (Or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {α : Type u} {a : α} {b : α} {l : List α} : ¬a ∈ b :: l → ¬a ∈ l :=
  fun (nin : ¬a ∈ b :: l) (nainl : a ∈ l) => absurd (Or.inr nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {α : Type u} {a : α} {y : α} {l : List α} : a ≠ y → ¬a ∈ l → ¬a ∈ y :: l :=
  fun (p1 : a ≠ y) (p2 : ¬a ∈ l) =>
    not.intro fun (Pain : a ∈ y :: l) => absurd (eq_or_mem_of_mem_cons Pain) (not_or p1 p2)

theorem ne_and_not_mem_of_not_mem_cons {α : Type u} {a : α} {y : α} {l : List α} : ¬a ∈ y :: l → a ≠ y ∧ ¬a ∈ l :=
  fun (p : ¬a ∈ y :: l) => { left := ne_of_not_mem_cons p, right := not_mem_of_not_mem_cons p }

theorem mem_map_of_mem {α : Type u} {β : Type v} (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ map f l := sorry

theorem exists_of_mem_map {α : Type u} {β : Type v} {f : α → β} {b : β} {l : List α} (h : b ∈ map f l) : ∃ (a : α), a ∈ l ∧ f a = b := sorry

@[simp] theorem mem_map {α : Type u} {β : Type v} {f : α → β} {b : β} {l : List α} : b ∈ map f l ↔ ∃ (a : α), a ∈ l ∧ f a = b := sorry

theorem mem_map_of_injective {α : Type u} {β : Type v} {f : α → β} (H : function.injective f) {a : α} {l : List α} : f a ∈ map f l ↔ a ∈ l := sorry

theorem forall_mem_map_iff {α : Type u} {β : Type v} {f : α → β} {l : List α} {P : β → Prop} : (∀ (i : β), i ∈ map f l → P i) ↔ ∀ (j : α), j ∈ l → P (f j) := sorry

@[simp] theorem map_eq_nil {α : Type u} {β : Type v} {f : α → β} {l : List α} : map f l = [] ↔ l = [] := sorry

@[simp] theorem mem_join {α : Type u} {a : α} {L : List (List α)} : a ∈ join L ↔ ∃ (l : List α), l ∈ L ∧ a ∈ l := sorry

theorem exists_of_mem_join {α : Type u} {a : α} {L : List (List α)} : a ∈ join L → ∃ (l : List α), l ∈ L ∧ a ∈ l :=
  iff.mp mem_join

theorem mem_join_of_mem {α : Type u} {a : α} {L : List (List α)} {l : List α} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
  iff.mpr mem_join (Exists.intro l { left := lL, right := al })

@[simp] theorem mem_bind {α : Type u} {β : Type v} {b : β} {l : List α} {f : α → List β} : b ∈ list.bind l f ↔ ∃ (a : α), ∃ (H : a ∈ l), b ∈ f a := sorry

theorem exists_of_mem_bind {α : Type u} {β : Type v} {b : β} {l : List α} {f : α → List β} : b ∈ list.bind l f → ∃ (a : α), ∃ (H : a ∈ l), b ∈ f a :=
  iff.mp mem_bind

theorem mem_bind_of_mem {α : Type u} {β : Type v} {b : β} {l : List α} {f : α → List β} {a : α} (al : a ∈ l) (h : b ∈ f a) : b ∈ list.bind l f :=
  iff.mpr mem_bind (Exists.intro a (Exists.intro al h))

theorem bind_map {α : Type u} {β : Type v} {γ : Type w} {g : α → List β} {f : β → γ} (l : List α) : map f (list.bind l g) = list.bind l fun (a : α) => map f (g a) := sorry

/-! ### length -/

theorem length_eq_zero {α : Type u} {l : List α} : length l = 0 ↔ l = [] :=
  { mp := eq_nil_of_length_eq_zero, mpr := fun (h : l = []) => Eq.symm h ▸ rfl }

@[simp] theorem length_singleton {α : Type u} (a : α) : length [a] = 1 :=
  rfl

theorem length_pos_of_mem {α : Type u} {a : α} {l : List α} : a ∈ l → 0 < length l := sorry

theorem exists_mem_of_length_pos {α : Type u} {l : List α} : 0 < length l → ∃ (a : α), a ∈ l := sorry

theorem length_pos_iff_exists_mem {α : Type u} {l : List α} : 0 < length l ↔ ∃ (a : α), a ∈ l := sorry

theorem ne_nil_of_length_pos {α : Type u} {l : List α} : 0 < length l → l ≠ [] :=
  fun (h1 : 0 < length l) (h2 : l = []) => lt_irrefl 0 (iff.mpr length_eq_zero h2 ▸ h1)

theorem length_pos_of_ne_nil {α : Type u} {l : List α} : l ≠ [] → 0 < length l :=
  fun (h : l ≠ []) => iff.mpr pos_iff_ne_zero fun (h0 : length l = 0) => h (iff.mp length_eq_zero h0)

theorem length_pos_iff_ne_nil {α : Type u} {l : List α} : 0 < length l ↔ l ≠ [] :=
  { mp := ne_nil_of_length_pos, mpr := length_pos_of_ne_nil }

theorem length_eq_one {α : Type u} {l : List α} : length l = 1 ↔ ∃ (a : α), l = [a] := sorry

theorem exists_of_length_succ {α : Type u} {n : ℕ} (l : List α) : length l = n + 1 → ∃ (h : α), ∃ (t : List α), l = h :: t := sorry

@[simp] theorem length_injective_iff {α : Type u} : function.injective length ↔ subsingleton α := sorry

@[simp] theorem length_injective {α : Type u} [subsingleton α] : function.injective length :=
  iff.mpr length_injective_iff _inst_1

/-! ### set-theoretic notation of lists -/

theorem empty_eq {α : Type u} : ∅ = [] :=
  Eq.refl ∅

theorem singleton_eq {α : Type u} (x : α) : singleton x = [x] :=
  rfl

theorem insert_neg {α : Type u} [DecidableEq α] {x : α} {l : List α} (h : ¬x ∈ l) : insert x l = x :: l :=
  if_neg h

theorem insert_pos {α : Type u} [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : insert x l = l :=
  if_pos h

theorem doubleton_eq {α : Type u} [DecidableEq α] {x : α} {y : α} (h : x ≠ y) : insert x (singleton y) = [x, y] := sorry

/-! ### bounded quantifiers over lists -/

theorem forall_mem_nil {α : Type u} (p : α → Prop) (x : α) (H : x ∈ []) : p x :=
  false.dcases_on (fun (H : x ∈ []) => p x) H

theorem forall_mem_cons {α : Type u} {p : α → Prop} {a : α} {l : List α} : (∀ (x : α), x ∈ a :: l → p x) ↔ p a ∧ ∀ (x : α), x ∈ l → p x :=
  ball_cons

theorem forall_mem_of_forall_mem_cons {α : Type u} {p : α → Prop} {a : α} {l : List α} (h : ∀ (x : α), x ∈ a :: l → p x) (x : α) (H : x ∈ l) : p x :=
  and.right (iff.mp forall_mem_cons h)

theorem forall_mem_singleton {α : Type u} {p : α → Prop} {a : α} : (∀ (x : α), x ∈ [a] → p x) ↔ p a := sorry

theorem forall_mem_append {α : Type u} {p : α → Prop} {l₁ : List α} {l₂ : List α} : (∀ (x : α), x ∈ l₁ ++ l₂ → p x) ↔ (∀ (x : α), x ∈ l₁ → p x) ∧ ∀ (x : α), x ∈ l₂ → p x := sorry

theorem not_exists_mem_nil {α : Type u} (p : α → Prop) : ¬∃ (x : α), ∃ (H : x ∈ []), p x := sorry

theorem exists_mem_cons_of {α : Type u} {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ (x : α), ∃ (H : x ∈ a :: l), p x :=
  bex.intro a (mem_cons_self a l) h

theorem exists_mem_cons_of_exists {α : Type u} {p : α → Prop} {a : α} {l : List α} (h : ∃ (x : α), ∃ (H : x ∈ l), p x) : ∃ (x : α), ∃ (H : x ∈ a :: l), p x :=
  bex.elim h fun (x : α) (xl : x ∈ l) (px : p x) => bex.intro x (mem_cons_of_mem a xl) px

theorem or_exists_of_exists_mem_cons {α : Type u} {p : α → Prop} {a : α} {l : List α} (h : ∃ (x : α), ∃ (H : x ∈ a :: l), p x) : p a ∨ ∃ (x : α), ∃ (H : x ∈ l), p x := sorry

theorem exists_mem_cons_iff {α : Type u} (p : α → Prop) (a : α) (l : List α) : (∃ (x : α), ∃ (H : x ∈ a :: l), p x) ↔ p a ∨ ∃ (x : α), ∃ (H : x ∈ l), p x :=
  { mp := or_exists_of_exists_mem_cons,
    mpr := fun (h : p a ∨ ∃ (x : α), ∃ (H : x ∈ l), p x) => or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists }

/-! ### list subset -/

theorem subset_def {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ {a : α}, a ∈ l₁ → a ∈ l₂ :=
  iff.rfl

theorem subset_append_of_subset_left {α : Type u} (l : List α) (l₁ : List α) (l₂ : List α) : l ⊆ l₁ → l ⊆ l₁ ++ l₂ :=
  fun (s : l ⊆ l₁) => subset.trans s (subset_append_left l₁ l₂)

theorem subset_append_of_subset_right {α : Type u} (l : List α) (l₁ : List α) (l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
  fun (s : l ⊆ l₂) => subset.trans s (subset_append_right l₁ l₂)

@[simp] theorem cons_subset {α : Type u} {a : α} {l : List α} {m : List α} : a :: l ⊆ m ↔ a ∈ m ∧ l ⊆ m := sorry

theorem cons_subset_of_subset_of_mem {α : Type u} {a : α} {l : List α} {m : List α} (ainm : a ∈ m) (lsubm : l ⊆ m) : a :: l ⊆ m :=
  iff.mpr cons_subset { left := ainm, right := lsubm }

theorem append_subset_of_subset_of_subset {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) : l₁ ++ l₂ ⊆ l :=
  fun (a : α) (h : a ∈ l₁ ++ l₂) => or.elim (iff.mp mem_append h) l₁subl l₂subl

@[simp] theorem append_subset_iff {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} : l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l := sorry

theorem eq_nil_of_subset_nil {α : Type u} {l : List α} : l ⊆ [] → l = [] := sorry

theorem eq_nil_iff_forall_not_mem {α : Type u} {l : List α} : l = [] ↔ ∀ (a : α), ¬a ∈ l :=
  (fun (this : l = [] ↔ l ⊆ []) => this) { mp := fun (e : l = []) => e ▸ subset.refl l, mpr := eq_nil_of_subset_nil }

theorem map_subset {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ := sorry

theorem map_subset_iff {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List α} (f : α → β) (h : function.injective f) : map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := sorry

/-! ### append -/

theorem append_eq_has_append {α : Type u} {L₁ : List α} {L₂ : List α} : list.append L₁ L₂ = L₁ ++ L₂ :=
  rfl

@[simp] theorem singleton_append {α : Type u} {x : α} {l : List α} : [x] ++ l = x :: l :=
  rfl

theorem append_ne_nil_of_ne_nil_left {α : Type u} (s : List α) (t : List α) : s ≠ [] → s ++ t ≠ [] := sorry

theorem append_ne_nil_of_ne_nil_right {α : Type u} (s : List α) (t : List α) : t ≠ [] → s ++ t ≠ [] := sorry

@[simp] theorem append_eq_nil {α : Type u} {p : List α} {q : List α} : p ++ q = [] ↔ p = [] ∧ q = [] := sorry

@[simp] theorem nil_eq_append_iff {α : Type u} {a : List α} {b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] :=
  eq.mpr (id (Eq._oldrec (Eq.refl ([] = a ++ b ↔ a = [] ∧ b = [])) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ++ b = [] ↔ a = [] ∧ b = [])) (propext append_eq_nil)))
      (iff.refl (a = [] ∧ b = [])))

theorem append_eq_cons_iff {α : Type u} {a : List α} {b : List α} {c : List α} {x : α} : a ++ b = x :: c ↔ a = [] ∧ b = x :: c ∨ ∃ (a' : List α), a = x :: a' ∧ c = a' ++ b := sorry

theorem cons_eq_append_iff {α : Type u} {a : List α} {b : List α} {c : List α} {x : α} : x :: c = a ++ b ↔ a = [] ∧ b = x :: c ∨ ∃ (a' : List α), a = x :: a' ∧ c = a' ++ b := sorry

theorem append_eq_append_iff {α : Type u} {a : List α} {b : List α} {c : List α} {d : List α} : a ++ b = c ++ d ↔ (∃ (a' : List α), c = a ++ a' ∧ b = a' ++ d) ∨ ∃ (c' : List α), a = c ++ c' ∧ d = c' ++ b := sorry

@[simp] theorem split_at_eq_take_drop {α : Type u} (n : ℕ) (l : List α) : split_at n l = (take n l, drop n l) := sorry

@[simp] theorem take_append_drop {α : Type u} (n : ℕ) (l : List α) : take n l ++ drop n l = l := sorry

-- TODO(Leo): cleanup proof after arith dec proc

theorem append_inj {α : Type u} {s₁ : List α} {s₂ : List α} {t₁ : List α} {t₂ : List α} : s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂ := sorry

theorem append_inj_right {α : Type u} {s₁ : List α} {s₂ : List α} {t₁ : List α} {t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  and.right (append_inj h hl)

theorem append_inj_left {α : Type u} {s₁ : List α} {s₂ : List α} {t₁ : List α} {t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  and.left (append_inj h hl)

theorem append_inj' {α : Type u} {s₁ : List α} {s₂ : List α} {t₁ : List α} {t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ := sorry

theorem append_inj_right' {α : Type u} {s₁ : List α} {s₂ : List α} {t₁ : List α} {t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  and.right (append_inj' h hl)

theorem append_inj_left' {α : Type u} {s₁ : List α} {s₂ : List α} {t₁ : List α} {t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  and.left (append_inj' h hl)

theorem append_left_cancel {α : Type u} {s : List α} {t₁ : List α} {t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  append_inj_right h rfl

theorem append_right_cancel {α : Type u} {s₁ : List α} {s₂ : List α} {t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  append_inj_left' h rfl

theorem append_right_injective {α : Type u} (s : List α) : function.injective fun (t : List α) => s ++ t :=
  fun (t₁ t₂ : List α) => append_left_cancel

theorem append_right_inj {α : Type u} {t₁ : List α} {t₂ : List α} (s : List α) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  function.injective.eq_iff (append_right_injective s)

theorem append_left_injective {α : Type u} (t : List α) : function.injective fun (s : List α) => s ++ t :=
  fun (s₁ s₂ : List α) => append_right_cancel

theorem append_left_inj {α : Type u} {s₁ : List α} {s₂ : List α} (t : List α) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  function.injective.eq_iff (append_left_injective t)

theorem map_eq_append_split {α : Type u} {β : Type v} {f : α → β} {l : List α} {s₁ : List β} {s₂ : List β} (h : map f l = s₁ ++ s₂) : ∃ (l₁ : List α), ∃ (l₂ : List α), l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ := sorry

/-! ### repeat -/

@[simp] theorem repeat_succ {α : Type u} (a : α) (n : ℕ) : repeat a (n + 1) = a :: repeat a n :=
  rfl

theorem eq_of_mem_repeat {α : Type u} {a : α} {b : α} {n : ℕ} : b ∈ repeat a n → b = a := sorry

theorem eq_repeat_of_mem {α : Type u} {a : α} {l : List α} : (∀ (b : α), b ∈ l → b = a) → l = repeat a (length l) := sorry

theorem eq_repeat' {α : Type u} {a : α} {l : List α} : l = repeat a (length l) ↔ ∀ (b : α), b ∈ l → b = a :=
  { mp := fun (h : l = repeat a (length l)) => Eq.symm h ▸ fun (b : α) => eq_of_mem_repeat, mpr := eq_repeat_of_mem }

theorem eq_repeat {α : Type u} {a : α} {n : ℕ} {l : List α} : l = repeat a n ↔ length l = n ∧ ∀ (b : α), b ∈ l → b = a := sorry

theorem repeat_add {α : Type u} (a : α) (m : ℕ) (n : ℕ) : repeat a (m + n) = repeat a m ++ repeat a n := sorry

theorem repeat_subset_singleton {α : Type u} (a : α) (n : ℕ) : repeat a n ⊆ [a] :=
  fun (b : α) (h : b ∈ repeat a n) => iff.mpr mem_singleton (eq_of_mem_repeat h)

@[simp] theorem map_const {α : Type u} {β : Type v} (l : List α) (b : β) : map (function.const α b) l = repeat b (length l) := sorry

theorem eq_of_mem_map_const {α : Type u} {β : Type v} {b₁ : β} {b₂ : β} {l : List α} (h : b₁ ∈ map (function.const α b₂) l) : b₁ = b₂ :=
  eq_of_mem_repeat (eq.mp (Eq._oldrec (Eq.refl (b₁ ∈ map (function.const α b₂) l)) (map_const l b₂)) h)

@[simp] theorem map_repeat {α : Type u} {β : Type v} (f : α → β) (a : α) (n : ℕ) : map f (repeat a n) = repeat (f a) n := sorry

@[simp] theorem tail_repeat {α : Type u} (a : α) (n : ℕ) : tail (repeat a n) = repeat a (Nat.pred n) :=
  nat.cases_on n (Eq.refl (tail (repeat a 0))) fun (n : ℕ) => Eq.refl (tail (repeat a (Nat.succ n)))

@[simp] theorem join_repeat_nil {α : Type u} (n : ℕ) : join (repeat [] n) = [] := sorry

/-! ### pure -/

@[simp] theorem mem_pure {α : Type u_1} (x : α) (y : α) : x ∈ pure y ↔ x = y := sorry

/-! ### bind -/

@[simp] theorem bind_eq_bind {α : Type u_1} {β : Type u_1} (f : α → List β) (l : List α) : l >>= f = list.bind l f :=
  rfl

@[simp] theorem bind_append {α : Type u} {β : Type v} (f : α → List β) (l₁ : List α) (l₂ : List α) : list.bind (l₁ ++ l₂) f = list.bind l₁ f ++ list.bind l₂ f :=
  append_bind l₁ l₂ f

@[simp] theorem bind_singleton {α : Type u} {β : Type v} (f : α → List β) (x : α) : list.bind [x] f = f x :=
  append_nil (f x)

/-! ### concat -/

theorem concat_nil {α : Type u} (a : α) : concat [] a = [a] :=
  rfl

theorem concat_cons {α : Type u} (a : α) (b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl

@[simp] theorem concat_eq_append {α : Type u} (a : α) (l : List α) : concat l a = l ++ [a] := sorry

theorem init_eq_of_concat_eq {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ := sorry

theorem last_eq_of_concat_eq {α : Type u} {a : α} {b : α} {l : List α} : concat l a = concat l b → a = b := sorry

theorem concat_ne_nil {α : Type u} (a : α) (l : List α) : concat l a ≠ [] := sorry

theorem concat_append {α : Type u} (a : α) (l₁ : List α) (l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ := sorry

theorem length_concat {α : Type u} (a : α) (l : List α) : length (concat l a) = Nat.succ (length l) := sorry

theorem append_concat {α : Type u} (a : α) (l₁ : List α) (l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a := sorry

/-! ### reverse -/

@[simp] theorem reverse_nil {α : Type u} : reverse [] = [] :=
  rfl

@[simp] theorem reverse_cons {α : Type u} (a : α) (l : List α) : reverse (a :: l) = reverse l ++ [a] := sorry

theorem reverse_core_eq {α : Type u} (l₁ : List α) (l₂ : List α) : reverse_core l₁ l₂ = reverse l₁ ++ l₂ := sorry

theorem reverse_cons' {α : Type u} (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := sorry

@[simp] theorem reverse_singleton {α : Type u} (a : α) : reverse [a] = [a] :=
  rfl

@[simp] theorem reverse_append {α : Type u} (s : List α) (t : List α) : reverse (s ++ t) = reverse t ++ reverse s := sorry

theorem reverse_concat {α : Type u} (l : List α) (a : α) : reverse (concat l a) = a :: reverse l := sorry

@[simp] theorem reverse_reverse {α : Type u} (l : List α) : reverse (reverse l) = l := sorry

@[simp] theorem reverse_involutive {α : Type u} : function.involutive reverse :=
  fun (l : List α) => reverse_reverse l

@[simp] theorem reverse_injective {α : Type u} : function.injective reverse :=
  function.involutive.injective reverse_involutive

@[simp] theorem reverse_inj {α : Type u} {l₁ : List α} {l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
  function.injective.eq_iff reverse_injective

@[simp] theorem reverse_eq_nil {α : Type u} {l : List α} : reverse l = [] ↔ l = [] :=
  reverse_inj

theorem concat_eq_reverse_cons {α : Type u} (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := sorry

@[simp] theorem length_reverse {α : Type u} (l : List α) : length (reverse l) = length l := sorry

@[simp] theorem map_reverse {α : Type u} {β : Type v} (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) := sorry

theorem map_reverse_core {α : Type u} {β : Type v} (f : α → β) (l₁ : List α) (l₂ : List α) : map f (reverse_core l₁ l₂) = reverse_core (map f l₁) (map f l₂) := sorry

@[simp] theorem mem_reverse {α : Type u} {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l := sorry

@[simp] theorem reverse_repeat {α : Type u} (a : α) (n : ℕ) : reverse (repeat a n) = repeat a n := sorry

/-! ### is_nil -/

theorem is_nil_iff_eq_nil {α : Type u} {l : List α} : ↥(is_nil l) ↔ l = [] := sorry

/-! ### init -/

@[simp] theorem length_init {α : Type u} (l : List α) : length (init l) = length l - 1 := sorry

/-! ### last -/

@[simp] theorem last_cons {α : Type u} {a : α} {l : List α} (h₁ : a :: l ≠ []) (h₂ : l ≠ []) : last (a :: l) h₁ = last l h₂ := sorry

@[simp] theorem last_append {α : Type u} {a : α} (l : List α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a := sorry

theorem last_concat {α : Type u} {a : α} (l : List α) (h : concat l a ≠ []) : last (concat l a) h = a := sorry

@[simp] theorem last_singleton {α : Type u} (a : α) (h : [a] ≠ []) : last [a] h = a :=
  rfl

@[simp] theorem last_cons_cons {α : Type u} (a₁ : α) (a₂ : α) (l : List α) (h : a₁ :: a₂ :: l ≠ []) : last (a₁ :: a₂ :: l) h = last (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl

theorem init_append_last {α : Type u} {l : List α} (h : l ≠ []) : init l ++ [last l h] = l := sorry

theorem last_congr {α : Type u} {l₁ : List α} {l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) : last l₁ h₁ = last l₂ h₂ :=
  Eq._oldrec (fun (h₁ : l₂ ≠ []) => Eq.refl (last l₂ h₁)) (Eq.symm h₃) h₁

theorem last_mem {α : Type u} {l : List α} (h : l ≠ []) : last l h ∈ l := sorry

theorem last_repeat_succ (a : ℕ) (m : ℕ) : last (repeat a (Nat.succ m))
    (ne_nil_of_length_eq_succ
      ((fun (this : length (repeat a (Nat.succ m)) = Nat.succ m) => this)
        (eq.mpr (id (Eq._oldrec (Eq.refl (length (repeat a (Nat.succ m)) = Nat.succ m)) (length_repeat a (Nat.succ m))))
          (Eq.refl (Nat.succ m))))) =
  a := sorry

/-! ### last' -/

@[simp] theorem last'_is_none {α : Type u} {l : List α} : ↥(option.is_none (last' l)) ↔ l = [] := sorry

@[simp] theorem last'_is_some {α : Type u} {l : List α} : ↥(option.is_some (last' l)) ↔ l ≠ [] := sorry

theorem mem_last'_eq_last {α : Type u} {l : List α} {x : α} : x ∈ last' l → ∃ (h : l ≠ []), x = last l h := sorry

theorem mem_of_mem_last' {α : Type u} {l : List α} {a : α} (ha : a ∈ last' l) : a ∈ l := sorry

theorem init_append_last' {α : Type u} {l : List α} (a : α) (H : a ∈ last' l) : init l ++ [a] = l := sorry

theorem ilast_eq_last' {α : Type u} [Inhabited α] (l : List α) : ilast l = option.iget (last' l) := sorry

@[simp] theorem last'_append_cons {α : Type u} (l₁ : List α) (a : α) (l₂ : List α) : last' (l₁ ++ a :: l₂) = last' (a :: l₂) := sorry

theorem last'_append_of_ne_nil {α : Type u} (l₁ : List α) {l₂ : List α} (hl₂ : l₂ ≠ []) : last' (l₁ ++ l₂) = last' l₂ := sorry

/-! ### head(') and tail -/

theorem head_eq_head' {α : Type u} [Inhabited α] (l : List α) : head l = option.iget (head' l) :=
  list.cases_on l (Eq.refl (head [])) fun (l_hd : α) (l_tl : List α) => Eq.refl (head (l_hd :: l_tl))

theorem mem_of_mem_head' {α : Type u} {x : α} {l : List α} : x ∈ head' l → x ∈ l := sorry

@[simp] theorem head_cons {α : Type u} [Inhabited α] (a : α) (l : List α) : head (a :: l) = a :=
  rfl

@[simp] theorem tail_nil {α : Type u} : tail [] = [] :=
  rfl

@[simp] theorem tail_cons {α : Type u} (a : α) (l : List α) : tail (a :: l) = l :=
  rfl

@[simp] theorem head_append {α : Type u} [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) : head (s ++ t) = head s := sorry

theorem tail_append_singleton_of_ne_nil {α : Type u} {a : α} {l : List α} (h : l ≠ []) : tail (l ++ [a]) = tail l ++ [a] := sorry

theorem cons_head'_tail {α : Type u} {l : List α} {a : α} (h : a ∈ head' l) : a :: tail l = l := sorry

theorem head_mem_head' {α : Type u} [Inhabited α] {l : List α} (h : l ≠ []) : head l ∈ head' l :=
  list.cases_on l (fun (h : [] ≠ []) => idRhs (head [] ∈ head' []) (absurd (Eq.refl []) h))
    (fun (l_hd : α) (l_tl : List α) (h : l_hd :: l_tl ≠ []) => idRhs (head' (l_hd :: l_tl) = head' (l_hd :: l_tl)) rfl) h

theorem cons_head_tail {α : Type u} [Inhabited α] {l : List α} (h : l ≠ []) : head l :: tail l = l :=
  cons_head'_tail (head_mem_head' h)

@[simp] theorem head'_map {α : Type u} {β : Type v} (f : α → β) (l : List α) : head' (map f l) = option.map f (head' l) :=
  list.cases_on l (Eq.refl (head' (map f []))) fun (l_hd : α) (l_tl : List α) => Eq.refl (head' (map f (l_hd :: l_tl)))

/-! ### Induction from the right -/

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def reverse_rec_on {α : Type u} {C : List α → Sort u_1} (l : List α) (H0 : C []) (H1 : (l : List α) → (a : α) → C l → C (l ++ [a])) : C l :=
  eq.mpr sorry
    (List.rec H0 (fun (hd : α) (tl : List α) (ih : C (reverse tl)) => eq.mpr sorry (H1 (reverse tl) hd ih)) (reverse l))

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectional_rec {α : Type u} {C : List α → Sort u_1} (H0 : C []) (H1 : (a : α) → C [a]) (Hn : (a : α) → (l : List α) → (b : α) → C l → C (a :: (l ++ [b]))) (l : List α) : C l :=
  sorry

/-- Like `bidirectional_rec`, but with the list parameter placed first. -/
def bidirectional_rec_on {α : Type u} {C : List α → Sort u_1} (l : List α) (H0 : C []) (H1 : (a : α) → C [a]) (Hn : (a : α) → (l : List α) → (b : α) → C l → C (a :: (l ++ [b]))) : C l :=
  bidirectional_rec H0 H1 Hn l

/-! ### sublists -/

@[simp] theorem nil_sublist {α : Type u} (l : List α) : [] <+ l := sorry

@[simp] theorem sublist.refl {α : Type u} (l : List α) : l <+ l := sorry

theorem sublist.trans {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ := sorry

@[simp] theorem sublist_cons {α : Type u} (a : α) (l : List α) : l <+ a :: l :=
  sublist.cons l l a (sublist.refl l)

theorem sublist_of_cons_sublist {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : a :: l₁ <+ l₂ → l₁ <+ l₂ :=
  sublist.trans (sublist_cons a l₁)

theorem cons_sublist_cons {α : Type u} {l₁ : List α} {l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  sublist.cons2 l₁ l₂ a s

@[simp] theorem sublist_append_left {α : Type u} (l₁ : List α) (l₂ : List α) : l₁ <+ l₁ ++ l₂ := sorry

@[simp] theorem sublist_append_right {α : Type u} (l₁ : List α) (l₂ : List α) : l₂ <+ l₁ ++ l₂ := sorry

theorem sublist_cons_of_sublist {α : Type u} (a : α) {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → l₁ <+ a :: l₂ :=
  sublist.cons l₁ l₂ a

theorem sublist_append_of_sublist_left {α : Type u} {l : List α} {l₁ : List α} {l₂ : List α} (s : l <+ l₁) : l <+ l₁ ++ l₂ :=
  sublist.trans s (sublist_append_left l₁ l₂)

theorem sublist_append_of_sublist_right {α : Type u} {l : List α} {l₁ : List α} {l₂ : List α} (s : l <+ l₂) : l <+ l₁ ++ l₂ :=
  sublist.trans s (sublist_append_right l₁ l₂)

theorem sublist_of_cons_sublist_cons {α : Type u} {l₁ : List α} {l₂ : List α} {a : α} : a :: l₁ <+ a :: l₂ → l₁ <+ l₂ := sorry

theorem cons_sublist_cons_iff {α : Type u} {l₁ : List α} {l₂ : List α} {a : α} : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  { mp := sublist_of_cons_sublist_cons, mpr := cons_sublist_cons a }

@[simp] theorem append_sublist_append_left {α : Type u} {l₁ : List α} {l₂ : List α} (l : List α) : l ++ l₁ <+ l ++ l₂ ↔ l₁ <+ l₂ := sorry

theorem sublist.append_right {α : Type u} {l₁ : List α} {l₂ : List α} (h : l₁ <+ l₂) (l : List α) : l₁ ++ l <+ l₂ ++ l :=
  sublist.drec (sublist.refl ([] ++ l))
    (fun (h_l₁ h_l₂ : List α) (a : α) (h_ᾰ : h_l₁ <+ h_l₂) (ih : h_l₁ ++ l <+ h_l₂ ++ l) => sublist_cons_of_sublist a ih)
    (fun (h_l₁ h_l₂ : List α) (a : α) (h_ᾰ : h_l₁ <+ h_l₂) (ih : h_l₁ ++ l <+ h_l₂ ++ l) => cons_sublist_cons a ih) h

theorem sublist_or_mem_of_sublist {α : Type u} {l : List α} {l₁ : List α} {l₂ : List α} {a : α} (h : l <+ l₁ ++ a :: l₂) : l <+ l₁ ++ l₂ ∨ a ∈ l := sorry

theorem sublist.reverse {α : Type u} {l₁ : List α} {l₂ : List α} (h : l₁ <+ l₂) : reverse l₁ <+ reverse l₂ := sorry

@[simp] theorem reverse_sublist_iff {α : Type u} {l₁ : List α} {l₂ : List α} : reverse l₁ <+ reverse l₂ ↔ l₁ <+ l₂ :=
  { mp := fun (h : reverse l₁ <+ reverse l₂) => reverse_reverse l₁ ▸ reverse_reverse l₂ ▸ sublist.reverse h,
    mpr := sublist.reverse }

@[simp] theorem append_sublist_append_right {α : Type u} {l₁ : List α} {l₂ : List α} (l : List α) : l₁ ++ l <+ l₂ ++ l ↔ l₁ <+ l₂ := sorry

theorem sublist.append {α : Type u} {l₁ : List α} {l₂ : List α} {r₁ : List α} {r₂ : List α} (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
  sublist.trans (sublist.append_right hl r₁) (iff.mpr (append_sublist_append_left l₂) hr)

theorem sublist.subset {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → l₁ ⊆ l₂ := sorry

theorem singleton_sublist {α : Type u} {a : α} {l : List α} : [a] <+ l ↔ a ∈ l := sorry

theorem eq_nil_of_sublist_nil {α : Type u} {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil (sublist.subset s)

theorem repeat_sublist_repeat {α : Type u} (a : α) {m : ℕ} {n : ℕ} : repeat a m <+ repeat a n ↔ m ≤ n := sorry

theorem eq_of_sublist_of_length_eq {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂ := sorry

theorem eq_of_sublist_of_length_le {α : Type u} {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  eq_of_sublist_of_length_eq s (le_antisymm (length_le_of_sublist s) h)

theorem sublist.antisymm {α : Type u} {l₁ : List α} {l₂ : List α} (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  eq_of_sublist_of_length_le s₁ (length_le_of_sublist s₂)

protected instance decidable_sublist {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : Decidable (l₁ <+ l₂) :=
  sorry

/-! ### index_of -/

@[simp] theorem index_of_nil {α : Type u} [DecidableEq α] (a : α) : index_of a [] = 0 :=
  rfl

theorem index_of_cons {α : Type u} [DecidableEq α] (a : α) (b : α) (l : List α) : index_of a (b :: l) = ite (a = b) 0 (Nat.succ (index_of a l)) :=
  rfl

theorem index_of_cons_eq {α : Type u} [DecidableEq α] {a : α} {b : α} (l : List α) : a = b → index_of a (b :: l) = 0 :=
  fun (e : a = b) => if_pos e

@[simp] theorem index_of_cons_self {α : Type u} [DecidableEq α] (a : α) (l : List α) : index_of a (a :: l) = 0 :=
  index_of_cons_eq l rfl

@[simp] theorem index_of_cons_ne {α : Type u} [DecidableEq α] {a : α} {b : α} (l : List α) : a ≠ b → index_of a (b :: l) = Nat.succ (index_of a l) :=
  fun (n : a ≠ b) => if_neg n

theorem index_of_eq_length {α : Type u} [DecidableEq α] {a : α} {l : List α} : index_of a l = length l ↔ ¬a ∈ l := sorry

@[simp] theorem index_of_of_not_mem {α : Type u} [DecidableEq α] {l : List α} {a : α} : ¬a ∈ l → index_of a l = length l :=
  iff.mpr index_of_eq_length

theorem index_of_le_length {α : Type u} [DecidableEq α] {a : α} {l : List α} : index_of a l ≤ length l := sorry

theorem index_of_lt_length {α : Type u} [DecidableEq α] {a : α} {l : List α} : index_of a l < length l ↔ a ∈ l := sorry

/-! ### nth element -/

theorem nth_le_of_mem {α : Type u} {a : α} {l : List α} : a ∈ l → ∃ (n : ℕ), ∃ (h : n < length l), nth_le l n h = a := sorry

theorem nth_le_nth {α : Type u} {l : List α} {n : ℕ} (h : n < length l) : nth l n = some (nth_le l n h) := sorry

theorem nth_len_le {α : Type u} {l : List α} {n : ℕ} : length l ≤ n → nth l n = none := sorry

theorem nth_eq_some {α : Type u} {l : List α} {n : ℕ} {a : α} : nth l n = some a ↔ ∃ (h : n < length l), nth_le l n h = a := sorry

@[simp] theorem nth_eq_none_iff {α : Type u} {l : List α} {n : ℕ} : nth l n = none ↔ length l ≤ n := sorry

theorem nth_of_mem {α : Type u} {a : α} {l : List α} (h : a ∈ l) : ∃ (n : ℕ), nth l n = some a := sorry

theorem nth_le_mem {α : Type u} (l : List α) (n : ℕ) (h : n < length l) : nth_le l n h ∈ l := sorry

theorem nth_mem {α : Type u} {l : List α} {n : ℕ} {a : α} (e : nth l n = some a) : a ∈ l := sorry

theorem mem_iff_nth_le {α : Type u} {a : α} {l : List α} : a ∈ l ↔ ∃ (n : ℕ), ∃ (h : n < length l), nth_le l n h = a := sorry

theorem mem_iff_nth {α : Type u} {a : α} {l : List α} : a ∈ l ↔ ∃ (n : ℕ), nth l n = some a :=
  iff.trans mem_iff_nth_le (exists_congr fun (n : ℕ) => iff.symm nth_eq_some)

theorem nth_zero {α : Type u} (l : List α) : nth l 0 = head' l :=
  list.cases_on l (Eq.refl (nth [] 0)) fun (l_hd : α) (l_tl : List α) => Eq.refl (nth (l_hd :: l_tl) 0)

theorem nth_injective {α : Type u} {xs : List α} {i : ℕ} {j : ℕ} (h₀ : i < length xs) (h₁ : nodup xs) (h₂ : nth xs i = nth xs j) : i = j := sorry

@[simp] theorem nth_map {α : Type u} {β : Type v} (f : α → β) (l : List α) (n : ℕ) : nth (map f l) n = option.map f (nth l n) := sorry

theorem nth_le_map {α : Type u} {β : Type v} (f : α → β) {l : List α} {n : ℕ} (H1 : n < length (map f l)) (H2 : n < length l) : nth_le (map f l) n H1 = f (nth_le l n H2) := sorry

/-- A version of `nth_le_map` that can be used for rewriting. -/
theorem nth_le_map_rev {α : Type u} {β : Type v} (f : α → β) {l : List α} {n : ℕ} (H : n < length l) : f (nth_le l n H) = nth_le (map f l) n (Eq.symm (length_map f l) ▸ H) :=
  Eq.symm (nth_le_map f (Eq.symm (length_map f l) ▸ H) H)

@[simp] theorem nth_le_map' {α : Type u} {β : Type v} (f : α → β) {l : List α} {n : ℕ} (H : n < length (map f l)) : nth_le (map f l) n H = f (nth_le l n (length_map f l ▸ H)) :=
  nth_le_map f H (length_map f l ▸ H)

/-- If one has `nth_le L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
theorem nth_le_of_eq {α : Type u} {L : List α} {L' : List α} (h : L = L') {i : ℕ} (hi : i < length L) : nth_le L i hi = nth_le L' i (h ▸ hi) := sorry

@[simp] theorem nth_le_singleton {α : Type u} (a : α) {n : ℕ} (hn : n < 1) : nth_le [a] n hn = a :=
  (fun (hn0 : n = 0) => Eq._oldrec (fun (hn : 0 < 1) => Eq.refl (nth_le [a] 0 hn)) (Eq.symm hn0) hn)
    (iff.mp nat.le_zero_iff (nat.le_of_lt_succ hn))

theorem nth_le_zero {α : Type u} [Inhabited α] {L : List α} (h : 0 < length L) : nth_le L 0 h = head L := sorry

theorem nth_le_append {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (hn₁ : n < length (l₁ ++ l₂)) (hn₂ : n < length l₁) : nth_le (l₁ ++ l₂) n hn₁ = nth_le l₁ n hn₂ := sorry

theorem nth_le_append_right_aux {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (h₁ : length l₁ ≤ n) (h₂ : n < length (l₁ ++ l₂)) : n - length l₁ < length l₂ := sorry

theorem nth_le_append_right {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (h₁ : length l₁ ≤ n) (h₂ : n < length (l₁ ++ l₂)) : nth_le (l₁ ++ l₂) n h₂ = nth_le l₂ (n - length l₁) (nth_le_append_right_aux h₁ h₂) := sorry

@[simp] theorem nth_le_repeat {α : Type u} (a : α) {n : ℕ} {m : ℕ} (h : m < length (repeat a n)) : nth_le (repeat a n) m h = a :=
  eq_of_mem_repeat (nth_le_mem (repeat a n) m h)

theorem nth_append {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (hn : n < length l₁) : nth (l₁ ++ l₂) n = nth l₁ n := sorry

theorem nth_append_right {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (hn : length l₁ ≤ n) : nth (l₁ ++ l₂) n = nth l₂ (n - length l₁) := sorry

theorem last_eq_nth_le {α : Type u} (l : List α) (h : l ≠ []) : last l h = nth_le l (length l - 1) (nat.sub_lt (length_pos_of_ne_nil h) nat.one_pos) := sorry

@[simp] theorem nth_concat_length {α : Type u} (l : List α) (a : α) : nth (l ++ [a]) (length l) = some a := sorry

theorem ext {α : Type u} {l₁ : List α} {l₂ : List α} : (∀ (n : ℕ), nth l₁ n = nth l₂ n) → l₁ = l₂ := sorry

theorem ext_le {α : Type u} {l₁ : List α} {l₂ : List α} (hl : length l₁ = length l₂) (h : ∀ (n : ℕ) (h₁ : n < length l₁) (h₂ : n < length l₂), nth_le l₁ n h₁ = nth_le l₂ n h₂) : l₁ = l₂ := sorry

@[simp] theorem index_of_nth_le {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : index_of a l < length l) : nth_le l (index_of a l) h = a := sorry

@[simp] theorem index_of_nth {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : nth l (index_of a l) = some a := sorry

theorem nth_le_reverse_aux1 {α : Type u} (l : List α) (r : List α) (i : ℕ) (h1 : i + length l < length (reverse_core l r)) (h2 : i < length r) : nth_le (reverse_core l r) (i + length l) h1 = nth_le r i h2 := sorry

theorem index_of_inj {α : Type u} [DecidableEq α] {l : List α} {x : α} {y : α} (hx : x ∈ l) (hy : y ∈ l) : index_of x l = index_of y l ↔ x = y := sorry

theorem nth_le_reverse_aux2 {α : Type u} (l : List α) (r : List α) (i : ℕ) (h1 : length l - 1 - i < length (reverse_core l r)) (h2 : i < length l) : nth_le (reverse_core l r) (length l - 1 - i) h1 = nth_le l i h2 := sorry

@[simp] theorem nth_le_reverse {α : Type u} (l : List α) (i : ℕ) (h1 : length l - 1 - i < length (reverse l)) (h2 : i < length l) : nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2 :=
  nth_le_reverse_aux2 l [] i h1 h2

theorem eq_cons_of_length_one {α : Type u} {l : List α} (h : length l = 1) : l = [nth_le l 0 (Eq.symm h ▸ zero_lt_one)] := sorry

theorem modify_nth_tail_modify_nth_tail {α : Type u} {f : List α → List α} {g : List α → List α} (m : ℕ) (n : ℕ) (l : List α) : modify_nth_tail g (m + n) (modify_nth_tail f n l) = modify_nth_tail (fun (l : List α) => modify_nth_tail g m (f l)) n l := sorry

theorem modify_nth_tail_modify_nth_tail_le {α : Type u} {f : List α → List α} {g : List α → List α} (m : ℕ) (n : ℕ) (l : List α) (h : n ≤ m) : modify_nth_tail g m (modify_nth_tail f n l) = modify_nth_tail (fun (l : List α) => modify_nth_tail g (m - n) (f l)) n l := sorry

theorem modify_nth_tail_modify_nth_tail_same {α : Type u} {f : List α → List α} {g : List α → List α} (n : ℕ) (l : List α) : modify_nth_tail g n (modify_nth_tail f n l) = modify_nth_tail (g ∘ f) n l := sorry

theorem modify_nth_tail_id {α : Type u} (n : ℕ) (l : List α) : modify_nth_tail id n l = l := sorry

theorem remove_nth_eq_nth_tail {α : Type u} (n : ℕ) (l : List α) : remove_nth l n = modify_nth_tail tail n l := sorry

theorem update_nth_eq_modify_nth {α : Type u} (a : α) (n : ℕ) (l : List α) : update_nth l n a = modify_nth (fun (_x : α) => a) n l := sorry

theorem modify_nth_eq_update_nth {α : Type u} (f : α → α) (n : ℕ) (l : List α) : modify_nth f n l = option.get_or_else ((fun (a : α) => update_nth l n (f a)) <$> nth l n) l := sorry

theorem nth_modify_nth {α : Type u} (f : α → α) (n : ℕ) (l : List α) (m : ℕ) : nth (modify_nth f n l) m = (fun (a : α) => ite (n = m) (f a) a) <$> nth l m := sorry

theorem modify_nth_tail_length {α : Type u} (f : List α → List α) (H : ∀ (l : List α), length (f l) = length l) (n : ℕ) (l : List α) : length (modify_nth_tail f n l) = length l := sorry

@[simp] theorem modify_nth_length {α : Type u} (f : α → α) (n : ℕ) (l : List α) : length (modify_nth f n l) = length l := sorry

@[simp] theorem update_nth_length {α : Type u} (l : List α) (n : ℕ) (a : α) : length (update_nth l n a) = length l := sorry

@[simp] theorem nth_modify_nth_eq {α : Type u} (f : α → α) (n : ℕ) (l : List α) : nth (modify_nth f n l) n = f <$> nth l n := sorry

@[simp] theorem nth_modify_nth_ne {α : Type u} (f : α → α) {m : ℕ} {n : ℕ} (l : List α) (h : m ≠ n) : nth (modify_nth f m l) n = nth l n := sorry

theorem nth_update_nth_eq {α : Type u} (a : α) (n : ℕ) (l : List α) : nth (update_nth l n a) n = (fun (_x : α) => a) <$> nth l n := sorry

theorem nth_update_nth_of_lt {α : Type u} (a : α) {n : ℕ} {l : List α} (h : n < length l) : nth (update_nth l n a) n = some a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nth (update_nth l n a) n = some a)) (nth_update_nth_eq a n l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((fun (_x : α) => a) <$> nth l n = some a)) (nth_le_nth h)))
      (Eq.refl ((fun (_x : α) => a) <$> some (nth_le l n h))))

theorem nth_update_nth_ne {α : Type u} (a : α) {m : ℕ} {n : ℕ} (l : List α) (h : m ≠ n) : nth (update_nth l m a) n = nth l n := sorry

@[simp] theorem nth_le_update_nth_eq {α : Type u} (l : List α) (i : ℕ) (a : α) (h : i < length (update_nth l i a)) : nth_le (update_nth l i a) i h = a := sorry

@[simp] theorem nth_le_update_nth_of_ne {α : Type u} {l : List α} {i : ℕ} {j : ℕ} (h : i ≠ j) (a : α) (hj : j < length (update_nth l i a)) : nth_le (update_nth l i a) j hj =
  nth_le l j
    (eq.mpr (id (Eq.refl (j < length l)))
      (eq.mp
        ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg Less e_2) e_3) j j
          (Eq.refl j) (length (update_nth l i a)) (length l) (update_nth_length l i a))
        hj)) := sorry

theorem mem_or_eq_of_mem_update_nth {α : Type u} {l : List α} {n : ℕ} {a : α} {b : α} (h : a ∈ update_nth l n b) : a ∈ l ∨ a = b := sorry

@[simp] theorem insert_nth_nil {α : Type u} (a : α) : insert_nth 0 a [] = [a] :=
  rfl

@[simp] theorem insert_nth_succ_nil {α : Type u} (n : ℕ) (a : α) : insert_nth (n + 1) a [] = [] :=
  rfl

theorem length_insert_nth {α : Type u} {a : α} (n : ℕ) (as : List α) : n ≤ length as → length (insert_nth n a as) = length as + 1 := sorry

theorem remove_nth_insert_nth {α : Type u} {a : α} (n : ℕ) (l : List α) : remove_nth (insert_nth n a l) n = l := sorry

theorem insert_nth_remove_nth_of_ge {α : Type u} {a : α} (n : ℕ) (m : ℕ) (as : List α) : n < length as → n ≤ m → insert_nth m a (remove_nth as n) = remove_nth (insert_nth (m + 1) a as) n := sorry

theorem insert_nth_remove_nth_of_le {α : Type u} {a : α} (n : ℕ) (m : ℕ) (as : List α) : n < length as → m ≤ n → insert_nth m a (remove_nth as n) = remove_nth (insert_nth m a as) (n + 1) := sorry

theorem insert_nth_comm {α : Type u} (a : α) (b : α) (i : ℕ) (j : ℕ) (l : List α) (h : i ≤ j) (hj : j ≤ length l) : insert_nth (j + 1) b (insert_nth i a l) = insert_nth i a (insert_nth j b l) := sorry

theorem mem_insert_nth {α : Type u} {a : α} {b : α} {n : ℕ} {l : List α} (hi : n ≤ length l) : a ∈ insert_nth n b l ↔ a = b ∨ a ∈ l := sorry

/-! ### map -/

@[simp] theorem map_nil {α : Type u} {β : Type v} (f : α → β) : map f [] = [] :=
  rfl

theorem map_eq_foldr {α : Type u} {β : Type v} (f : α → β) (l : List α) : map f l = foldr (fun (a : α) (bs : List β) => f a :: bs) [] l := sorry

theorem map_congr {α : Type u} {β : Type v} {f : α → β} {g : α → β} {l : List α} : (∀ (x : α), x ∈ l → f x = g x) → map f l = map g l := sorry

theorem map_eq_map_iff {α : Type u} {β : Type v} {f : α → β} {g : α → β} {l : List α} : map f l = map g l ↔ ∀ (x : α), x ∈ l → f x = g x := sorry

theorem map_concat {α : Type u} {β : Type v} (f : α → β) (a : α) (l : List α) : map f (concat l a) = concat (map f l) (f a) := sorry

theorem map_id' {α : Type u} {f : α → α} (h : ∀ (x : α), f x = x) (l : List α) : map f l = l := sorry

theorem eq_nil_of_map_eq_nil {α : Type u} {β : Type v} {f : α → β} {l : List α} (h : map f l = []) : l = [] :=
  eq_nil_of_length_eq_zero
    (eq.mpr (id (Eq._oldrec (Eq.refl (length l = 0)) (Eq.symm (length_map f l))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (length (map f l) = 0)) h)) (Eq.refl (length []))))

@[simp] theorem map_join {α : Type u} {β : Type v} (f : α → β) (L : List (List α)) : map f (join L) = join (map (map f) L) := sorry

theorem bind_ret_eq_map {α : Type u} {β : Type v} (f : α → β) (l : List α) : list.bind l (list.ret ∘ f) = map f l := sorry

@[simp] theorem map_eq_map {α : Type u_1} {β : Type u_1} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl

@[simp] theorem map_tail {α : Type u} {β : Type v} (f : α → β) (l : List α) : map f (tail l) = tail (map f l) :=
  list.cases_on l (Eq.refl (map f (tail []))) fun (l_hd : α) (l_tl : List α) => Eq.refl (map f (tail (l_hd :: l_tl)))

@[simp] theorem map_injective_iff {α : Type u} {β : Type v} {f : α → β} : function.injective (map f) ↔ function.injective f := sorry

/--
A single `list.map` of a composition of functions is equal to
composing a `list.map` with another `list.map`, fully applied.
This is the reverse direction of `list.map_map`.
-/
theorem comp_map {α : Type u} {β : Type v} {γ : Type w} (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  Eq.symm (map_map h g l)

/--
Composing a `list.map` with another `list.map` is equal to
a single `list.map` of composed functions.
-/
@[simp] theorem map_comp_map {α : Type u} {β : Type v} {γ : Type w} (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) := sorry

theorem map_filter_eq_foldr {α : Type u} {β : Type v} (f : α → β) (p : α → Prop) [decidable_pred p] (as : List α) : map f (filter p as) = foldr (fun (a : α) (bs : List β) => ite (p a) (f a :: bs) bs) [] as := sorry

theorem last_map {α : Type u} {β : Type v} (f : α → β) {l : List α} (hl : l ≠ []) : last (map f l) (mt eq_nil_of_map_eq_nil hl) = f (last l hl) := sorry

/-! ### map₂ -/

theorem nil_map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l : List β) : map₂ f [] l = [] :=
  list.cases_on l (Eq.refl (map₂ f [] [])) fun (l_hd : β) (l_tl : List β) => Eq.refl (map₂ f [] (l_hd :: l_tl))

theorem map₂_nil {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l : List α) : map₂ f l [] = [] :=
  list.cases_on l (Eq.refl (map₂ f [] [])) fun (l_hd : α) (l_tl : List α) => Eq.refl (map₂ f (l_hd :: l_tl) [])

@[simp] theorem map₂_flip {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (as : List α) (bs : List β) : map₂ (flip f) bs as = map₂ f as bs := sorry

/-! ### take, drop -/

@[simp] theorem take_zero {α : Type u} (l : List α) : take 0 l = [] :=
  rfl

@[simp] theorem take_nil {α : Type u} (n : ℕ) : take n [] = [] :=
  nat.cases_on n (idRhs (take 0 [] = take 0 []) rfl) fun (n : ℕ) => idRhs (take (n + 1) [] = take (n + 1) []) rfl

theorem take_cons {α : Type u} (n : ℕ) (a : α) (l : List α) : take (Nat.succ n) (a :: l) = a :: take n l :=
  rfl

@[simp] theorem take_length {α : Type u} (l : List α) : take (length l) l = l := sorry

theorem take_all_of_le {α : Type u} {n : ℕ} {l : List α} : length l ≤ n → take n l = l := sorry

@[simp] theorem take_left {α : Type u} (l₁ : List α) (l₂ : List α) : take (length l₁) (l₁ ++ l₂) = l₁ := sorry

theorem take_left' {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (take n (l₁ ++ l₂) = l₁)) (Eq.symm h))) (take_left l₁ l₂)

theorem take_take {α : Type u} (n : ℕ) (m : ℕ) (l : List α) : take n (take m l) = take (min n m) l := sorry

theorem take_repeat {α : Type u} (a : α) (n : ℕ) (m : ℕ) : take n (repeat a m) = repeat a (min n m) := sorry

theorem map_take {α : Type u_1} {β : Type u_2} (f : α → β) (L : List α) (i : ℕ) : map f (take i L) = take i (map f L) := sorry

theorem take_append_of_le_length {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} : n ≤ length l₁ → take n (l₁ ++ l₂) = take n l₁ := sorry

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {α : Type u} {l₁ : List α} {l₂ : List α} (i : ℕ) : take (length l₁ + i) (l₁ ++ l₂) = l₁ ++ take i l₂ := sorry

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem nth_le_take {α : Type u} (L : List α) {i : ℕ} {j : ℕ} (hi : i < length L) (hj : i < j) : nth_le L i hi =
  nth_le (take j L) i (eq.mpr (id (Eq._oldrec (Eq.refl (i < length (take j L))) (length_take j L))) (lt_min hj hi)) := sorry

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem nth_le_take' {α : Type u} (L : List α) {i : ℕ} {j : ℕ} (hi : i < length (take j L)) : nth_le (take j L) i hi =
  nth_le L i
    (lt_of_lt_of_le hi
      (eq.mpr
        (id
          (Eq.trans
            (Eq.trans
              (Eq.trans
                ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg LessEq e_2) e_3)
                  (length (take j L)) (min j (length L)) (length_take j L) (length L) (length L) (Eq.refl (length L)))
                (propext min_le_iff))
              ((fun (a a_1 : Prop) (e_1 : a = a_1) (b b_1 : Prop) (e_2 : b = b_1) => congr (congr_arg Or e_1) e_2)
                (j ≤ length L) (j ≤ length L) (Eq.refl (j ≤ length L)) (length L ≤ length L) True
                (propext ((fun {α : Type} (a : α) => iff_true_intro (le_refl a)) (length L)))))
            (propext (or_true (j ≤ length L)))))
        trivial)) := sorry

theorem nth_take {α : Type u} {l : List α} {n : ℕ} {m : ℕ} (h : m < n) : nth (take n l) m = nth l m := sorry

@[simp] theorem nth_take_of_succ {α : Type u} {l : List α} {n : ℕ} : nth (take (n + 1) l) n = nth l n :=
  nth_take (nat.lt_succ_self n)

theorem take_succ {α : Type u} {l : List α} {n : ℕ} : take (n + 1) l = take n l ++ option.to_list (nth l n) := sorry

@[simp] theorem drop_nil {α : Type u} (n : ℕ) : drop n [] = [] :=
  nat.cases_on n (idRhs (drop 0 [] = drop 0 []) rfl) fun (n : ℕ) => idRhs (drop (n + 1) [] = drop (n + 1) []) rfl

theorem mem_of_mem_drop {α : Type u_1} {n : ℕ} {l : List α} {x : α} (h : x ∈ drop n l) : x ∈ l := sorry

@[simp] theorem drop_one {α : Type u} (l : List α) : drop 1 l = tail l :=
  list.cases_on l (idRhs (drop 1 [] = drop 1 []) rfl)
    fun (l_hd : α) (l_tl : List α) => idRhs (drop 1 (l_hd :: l_tl) = drop 1 (l_hd :: l_tl)) rfl

theorem drop_add {α : Type u} (m : ℕ) (n : ℕ) (l : List α) : drop (m + n) l = drop m (drop n l) := sorry

@[simp] theorem drop_left {α : Type u} (l₁ : List α) (l₂ : List α) : drop (length l₁) (l₁ ++ l₂) = l₂ := sorry

theorem drop_left' {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (drop n (l₁ ++ l₂) = l₂)) (Eq.symm h))) (drop_left l₁ l₂)

theorem drop_eq_nth_le_cons {α : Type u} {n : ℕ} {l : List α} (h : n < length l) : drop n l = nth_le l n h :: drop (n + 1) l := sorry

@[simp] theorem drop_length {α : Type u} (l : List α) : drop (length l) l = [] := sorry

theorem drop_append_of_le_length {α : Type u} {l₁ : List α} {l₂ : List α} {n : ℕ} : n ≤ length l₁ → drop n (l₁ ++ l₂) = drop n l₁ ++ l₂ := sorry

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
theorem drop_append {α : Type u} {l₁ : List α} {l₂ : List α} (i : ℕ) : drop (length l₁ + i) (l₁ ++ l₂) = drop i l₂ := sorry

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem nth_le_drop {α : Type u} (L : List α) {i : ℕ} {j : ℕ} (h : i + j < length L) : nth_le L (i + j) h =
  nth_le (drop i L) j
    (eq.mpr (id (Eq.refl (j < length (drop i L))))
      (eq.mp
        (Eq.trans
          ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg Less e_2) e_3) (i + j)
            (i + j) (Eq.refl (i + j)) (length (take i L ++ drop i L)) (i + length (drop i L))
            (Eq.trans (length_append (take i L) (drop i L))
              ((fun (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3) => congr (congr_arg Add.add e_2) e_3)
                (length (take i L)) i
                (Eq.trans (length_take i L)
                  (min_eq_left (iff.mpr (iff_true_intro (le_of_lt (lt_of_le_of_lt (nat.le.intro rfl) h))) True.intro)))
                (length (drop i L)) (length (drop i L)) (Eq.refl (length (drop i L))))))
          (propext (add_lt_add_iff_left i)))
        (eq.mp (Eq._oldrec (Eq.refl (i + j < length L)) (Eq.symm (take_append_drop i L))) h))) := sorry

/--  The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem nth_le_drop' {α : Type u} (L : List α) {i : ℕ} {j : ℕ} (h : j < length (drop i L)) : nth_le (drop i L) j h = nth_le L (i + j) (nat.add_lt_of_lt_sub_left (length_drop i L ▸ h)) := sorry

@[simp] theorem drop_drop {α : Type u} (n : ℕ) (m : ℕ) (l : List α) : drop n (drop m l) = drop (n + m) l := sorry

theorem drop_take {α : Type u} (m : ℕ) (n : ℕ) (l : List α) : drop m (take (m + n) l) = take n (drop m l) := sorry

theorem map_drop {α : Type u_1} {β : Type u_2} (f : α → β) (L : List α) (i : ℕ) : map f (drop i L) = drop i (map f L) := sorry

theorem modify_nth_tail_eq_take_drop {α : Type u} (f : List α → List α) (H : f [] = []) (n : ℕ) (l : List α) : modify_nth_tail f n l = take n l ++ f (drop n l) := sorry

theorem modify_nth_eq_take_drop {α : Type u} (f : α → α) (n : ℕ) (l : List α) : modify_nth f n l = take n l ++ modify_head f (drop n l) :=
  modify_nth_tail_eq_take_drop (modify_head f) rfl

theorem modify_nth_eq_take_cons_drop {α : Type u} (f : α → α) {n : ℕ} {l : List α} (h : n < length l) : modify_nth f n l = take n l ++ f (nth_le l n h) :: drop (n + 1) l := sorry

theorem update_nth_eq_take_cons_drop {α : Type u} (a : α) {n : ℕ} {l : List α} (h : n < length l) : update_nth l n a = take n l ++ a :: drop (n + 1) l := sorry

theorem reverse_take {α : Type u_1} {xs : List α} (n : ℕ) (h : n ≤ length xs) : take n (reverse xs) = reverse (drop (length xs - n) xs) := sorry

@[simp] theorem update_nth_eq_nil {α : Type u} (l : List α) (n : ℕ) (a : α) : update_nth l n a = [] ↔ l = [] := sorry

@[simp] theorem take'_length {α : Type u} [Inhabited α] (n : ℕ) (l : List α) : length (take' n l) = n := sorry

@[simp] theorem take'_nil {α : Type u} [Inhabited α] (n : ℕ) : take' n [] = repeat Inhabited.default n := sorry

theorem take'_eq_take {α : Type u} [Inhabited α] {n : ℕ} {l : List α} : n ≤ length l → take' n l = take n l := sorry

@[simp] theorem take'_left {α : Type u} [Inhabited α] (l₁ : List α) (l₂ : List α) : take' (length l₁) (l₁ ++ l₂) = l₁ := sorry

theorem take'_left' {α : Type u} [Inhabited α] {l₁ : List α} {l₂ : List α} {n : ℕ} (h : length l₁ = n) : take' n (l₁ ++ l₂) = l₁ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (take' n (l₁ ++ l₂) = l₁)) (Eq.symm h))) (take'_left l₁ l₂)

/-! ### foldl, foldr -/

theorem foldl_ext {α : Type u} {β : Type v} (f : α → β → α) (g : α → β → α) (a : α) {l : List β} (H : ∀ (a : α) (b : β), b ∈ l → f a b = g a b) : foldl f a l = foldl g a l := sorry

theorem foldr_ext {α : Type u} {β : Type v} (f : α → β → β) (g : α → β → β) (b : β) {l : List α} (H : ∀ (a : α), a ∈ l → ∀ (b : β), f a b = g a b) : foldr f b l = foldr g b l := sorry

@[simp] theorem foldl_nil {α : Type u} {β : Type v} (f : α → β → α) (a : α) : foldl f a [] = a :=
  rfl

@[simp] theorem foldl_cons {α : Type u} {β : Type v} (f : α → β → α) (a : α) (b : β) (l : List β) : foldl f a (b :: l) = foldl f (f a b) l :=
  rfl

@[simp] theorem foldr_nil {α : Type u} {β : Type v} (f : α → β → β) (b : β) : foldr f b [] = b :=
  rfl

@[simp] theorem foldr_cons {α : Type u} {β : Type v} (f : α → β → β) (b : β) (a : α) (l : List α) : foldr f b (a :: l) = f a (foldr f b l) :=
  rfl

@[simp] theorem foldl_append {α : Type u} {β : Type v} (f : α → β → α) (a : α) (l₁ : List β) (l₂ : List β) : foldl f a (l₁ ++ l₂) = foldl f (foldl f a l₁) l₂ := sorry

@[simp] theorem foldr_append {α : Type u} {β : Type v} (f : α → β → β) (b : β) (l₁ : List α) (l₂ : List α) : foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁ := sorry

@[simp] theorem foldl_join {α : Type u} {β : Type v} (f : α → β → α) (a : α) (L : List (List β)) : foldl f a (join L) = foldl (foldl f) a L := sorry

@[simp] theorem foldr_join {α : Type u} {β : Type v} (f : α → β → β) (b : β) (L : List (List α)) : foldr f b (join L) = foldr (fun (l : List α) (b : β) => foldr f b l) b L := sorry

theorem foldl_reverse {α : Type u} {β : Type v} (f : α → β → α) (a : α) (l : List β) : foldl f a (reverse l) = foldr (fun (x : β) (y : α) => f y x) a l := sorry

theorem foldr_reverse {α : Type u} {β : Type v} (f : α → β → β) (a : β) (l : List α) : foldr f a (reverse l) = foldl (fun (x : β) (y : α) => f y x) a l := sorry

@[simp] theorem foldr_eta {α : Type u} (l : List α) : foldr List.cons [] l = l := sorry

@[simp] theorem reverse_foldl {α : Type u} {l : List α} : reverse (foldl (fun (t : List α) (h : α) => h :: t) [] l) = l := sorry

@[simp] theorem foldl_map {α : Type u} {β : Type v} {γ : Type w} (g : β → γ) (f : α → γ → α) (a : α) (l : List β) : foldl f a (map g l) = foldl (fun (x : α) (y : β) => f x (g y)) a l := sorry

@[simp] theorem foldr_map {α : Type u} {β : Type v} {γ : Type w} (g : β → γ) (f : γ → α → α) (a : α) (l : List β) : foldr f a (map g l) = foldr (f ∘ g) a l := sorry

theorem foldl_map' {α : Type u} {β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α) (h : ∀ (x y : α), f' (g x) (g y) = g (f x y)) : foldl f' (g a) (map g l) = g (foldl f a l) := sorry

theorem foldr_map' {α : Type u} {β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α) (h : ∀ (x y : α), f' (g x) (g y) = g (f x y)) : foldr f' (g a) (map g l) = g (foldr f a l) := sorry

theorem foldl_hom {α : Type u} {β : Type v} {γ : Type w} (l : List γ) (f : α → β) (op : α → γ → α) (op' : β → γ → β) (a : α) (h : ∀ (a : α) (x : γ), f (op a x) = op' (f a) x) : foldl op' (f a) l = f (foldl op a l) := sorry

theorem foldr_hom {α : Type u} {β : Type v} {γ : Type w} (l : List γ) (f : α → β) (op : γ → α → α) (op' : γ → β → β) (a : α) (h : ∀ (x : γ) (a : α), f (op x a) = op' x (f a)) : foldr op' (f a) l = f (foldr op a l) := sorry

theorem injective_foldl_comp {α : Type u_1} {l : List (α → α)} {f : α → α} (hl : ∀ (f : α → α), f ∈ l → function.injective f) (hf : function.injective f) : function.injective (foldl function.comp f l) := sorry

/- scanl -/

theorem length_scanl {α : Type u} {β : Type v} {f : β → α → β} (a : β) (l : List α) : length (scanl f a l) = length l + 1 := sorry

@[simp] theorem scanl_nil {α : Type u} {β : Type v} {f : β → α → β} (b : β) : scanl f b [] = [b] :=
  rfl

@[simp] theorem scanl_cons {α : Type u} {β : Type v} {f : β → α → β} {b : β} {a : α} {l : List α} : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := sorry

@[simp] theorem nth_zero_scanl {α : Type u} {β : Type v} {f : β → α → β} {b : β} {l : List α} : nth (scanl f b l) 0 = some b := sorry

@[simp] theorem nth_le_zero_scanl {α : Type u} {β : Type v} {f : β → α → β} {b : β} {l : List α} {h : 0 < length (scanl f b l)} : nth_le (scanl f b l) 0 h = b := sorry

theorem nth_succ_scanl {α : Type u} {β : Type v} {f : β → α → β} {b : β} {l : List α} {i : ℕ} : nth (scanl f b l) (i + 1) = option.bind (nth (scanl f b l) i) fun (x : β) => option.map (fun (y : α) => f x y) (nth l i) := sorry

theorem nth_le_succ_scanl {α : Type u} {β : Type v} {f : β → α → β} {b : β} {l : List α} {i : ℕ} {h : i + 1 < length (scanl f b l)} : nth_le (scanl f b l) (i + 1) h =
  f (nth_le (scanl f b l) i (nat.lt_of_succ_lt h))
    (nth_le l i (nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) := sorry

/- scanr -/

@[simp] theorem scanr_nil {α : Type u} {β : Type v} (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl

@[simp] theorem scanr_aux_cons {α : Type u} {β : Type v} (f : α → β → β) (b : β) (a : α) (l : List α) : scanr_aux f b (a :: l) = (foldr f b (a :: l), scanr f b l) := sorry

@[simp] theorem scanr_cons {α : Type u} {β : Type v} (f : α → β → β) (b : β) (a : α) (l : List α) : scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := sorry

-- foldl and foldr coincide when f is commutative and associative

theorem foldl1_eq_foldr1 {α : Type u} {f : α → α → α} (hassoc : associative f) (a : α) (b : α) (l : List α) : foldl f a (l ++ [b]) = foldr f b (a :: l) := sorry

theorem foldl_eq_of_comm_of_assoc {α : Type u} {f : α → α → α} (hcomm : commutative f) (hassoc : associative f) (a : α) (b : α) (l : List α) : foldl f a (b :: l) = f b (foldl f a l) := sorry

theorem foldl_eq_foldr {α : Type u} {f : α → α → α} (hcomm : commutative f) (hassoc : associative f) (a : α) (l : List α) : foldl f a l = foldr f a l := sorry

theorem foldl_eq_of_comm' {α : Type u} {β : Type v} {f : α → β → α} (hf : ∀ (a : α) (b c : β), f (f a b) c = f (f a c) b) (a : α) (b : β) (l : List β) : foldl f a (b :: l) = f (foldl f a l) b := sorry

theorem foldl_eq_foldr' {α : Type u} {β : Type v} {f : α → β → α} (hf : ∀ (a : α) (b c : β), f (f a b) c = f (f a c) b) (a : α) (l : List β) : foldl f a l = foldr (flip f) a l := sorry

theorem foldr_eq_of_comm' {α : Type u} {β : Type v} {f : α → β → β} (hf : ∀ (a b : α) (c : β), f a (f b c) = f b (f a c)) (a : β) (b : α) (l : List α) : foldr f a (b :: l) = foldr f (f b a) l := sorry

theorem foldl_assoc {α : Type u} {op : α → α → α} [ha : is_associative α op] {l : List α} {a₁ : α} {a₂ : α} : foldl op (op a₁ a₂) l = op a₁ (foldl op a₂ l) := sorry

theorem foldl_op_eq_op_foldr_assoc {α : Type u} {op : α → α → α} [ha : is_associative α op] {l : List α} {a₁ : α} {a₂ : α} : op (foldl op a₁ l) a₂ = op a₁ (foldr op a₂ l) := sorry

theorem foldl_assoc_comm_cons {α : Type u} {op : α → α → α} [ha : is_associative α op] [hc : is_commutative α op] {l : List α} {a₁ : α} {a₂ : α} : foldl op a₂ (a₁ :: l) = op a₁ (foldl op a₂ l) := sorry

/-! ### mfoldl, mfoldr, mmap -/

@[simp] theorem mfoldl_nil {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) {b : β} : mfoldl f b [] = pure b :=
  rfl

@[simp] theorem mfoldr_nil {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) {b : β} : mfoldr f b [] = pure b :=
  rfl

@[simp] theorem mfoldl_cons {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] {f : β → α → m β} {b : β} {a : α} {l : List α} : mfoldl f b (a :: l) =
  do 
    let b' ← f b a 
    mfoldl f b' l :=
  rfl

@[simp] theorem mfoldr_cons {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] {f : α → β → m β} {b : β} {a : α} {l : List α} : mfoldr f b (a :: l) = mfoldr f b l >>= f a :=
  rfl

theorem mfoldr_eq_foldr {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (b : β) (l : List α) : mfoldr f b l = foldr (fun (a : α) (mb : m β) => mb >>= f a) (pure b) l := sorry

theorem mfoldl_eq_foldl {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] [is_lawful_monad m] (f : β → α → m β) (b : β) (l : List α) : mfoldl f b l =
  foldl
    (fun (mb : m β) (a : α) =>
      do 
        let b ← mb 
        f b a)
    (pure b) l := sorry

@[simp] theorem mfoldl_append {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] [is_lawful_monad m] {f : β → α → m β} {b : β} {l₁ : List α} {l₂ : List α} : mfoldl f b (l₁ ++ l₂) =
  do 
    let x ← mfoldl f b l₁ 
    mfoldl f x l₂ := sorry

@[simp] theorem mfoldr_append {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] [is_lawful_monad m] {f : α → β → m β} {b : β} {l₁ : List α} {l₂ : List α} : mfoldr f b (l₁ ++ l₂) =
  do 
    let x ← mfoldr f b l₂ 
    mfoldr f x l₁ := sorry

/-! ### prod and sum -/

-- list.sum was already defined in defs.lean, but we couldn't tag it with `to_additive` yet.

@[simp] theorem sum_nil {α : Type u} [add_monoid α] : sum [] = 0 :=
  rfl

theorem sum_singleton {α : Type u} [add_monoid α] {a : α} : sum [a] = a :=
  zero_add a

@[simp] theorem prod_cons {α : Type u} [monoid α] {l : List α} {a : α} : prod (a :: l) = a * prod l := sorry

@[simp] theorem sum_append {α : Type u} [add_monoid α] {l₁ : List α} {l₂ : List α} : sum (l₁ ++ l₂) = sum l₁ + sum l₂ := sorry

@[simp] theorem sum_join {α : Type u} [add_monoid α] {l : List (List α)} : sum (join l) = sum (map sum l) := sorry

theorem prod_ne_zero {R : Type u_1} [domain R] {L : List R} : (∀ (x : R), x ∈ L → x ≠ 0) → prod L ≠ 0 := sorry

theorem prod_eq_foldr {α : Type u} [monoid α] {l : List α} : prod l = foldr Mul.mul 1 l := sorry

theorem prod_hom_rel {α : Type u_1} {β : Type u_2} {γ : Type u_3} [monoid β] [monoid γ] (l : List α) {r : β → γ → Prop} {f : α → β} {g : α → γ} (h₁ : r 1 1) (h₂ : ∀ {a : α} {b : β} {c : γ}, r b c → r (f a * b) (g a * c)) : r (prod (map f l)) (prod (map g l)) := sorry

theorem prod_hom {α : Type u} {β : Type v} [monoid α] [monoid β] (l : List α) (f : α →* β) : prod (map (⇑f) l) = coe_fn f (prod l) := sorry

-- `to_additive` chokes on the next few lemmas, so we do them by hand below

@[simp] theorem prod_take_mul_prod_drop {α : Type u} [monoid α] (L : List α) (i : ℕ) : prod (take i L) * prod (drop i L) = prod L := sorry

@[simp] theorem prod_take_succ {α : Type u} [monoid α] (L : List α) (i : ℕ) (p : i < length L) : prod (take (i + 1) L) = prod (take i L) * nth_le L i p := sorry

/-- A list with product not one must have positive length. -/
theorem length_pos_of_prod_ne_one {α : Type u} [monoid α] (L : List α) (h : prod L ≠ 1) : 0 < length L := sorry

theorem prod_update_nth {α : Type u} [monoid α] (L : List α) (n : ℕ) (a : α) : prod (update_nth L n a) = prod (take n L) * ite (n < length L) a 1 * prod (drop (n + 1) L) := sorry

/-- This is the `list.prod` version of `mul_inv_rev` -/
theorem sum_neg_reverse {α : Type u} [add_group α] (L : List α) : -sum L = sum (reverse (map (fun (x : α) => -x) L)) := sorry

/-- A non-commutative variant of `list.prod_reverse` -/
theorem prod_reverse_noncomm {α : Type u} [group α] (L : List α) : prod (reverse L) = (prod (map (fun (x : α) => x⁻¹) L)⁻¹) := sorry

/-- This is the `list.prod` version of `mul_inv` -/
theorem sum_neg {α : Type u} [add_comm_group α] (L : List α) : -sum L = sum (map (fun (x : α) => -x) L) := sorry

@[simp] theorem sum_take_add_sum_drop {α : Type u} [add_monoid α] (L : List α) (i : ℕ) : sum (take i L) + sum (drop i L) = sum L := sorry

@[simp] theorem sum_take_succ {α : Type u} [add_monoid α] (L : List α) (i : ℕ) (p : i < length L) : sum (take (i + 1) L) = sum (take i L) + nth_le L i p := sorry

theorem eq_of_sum_take_eq {α : Type u} [add_left_cancel_monoid α] {L : List α} {L' : List α} (h : length L = length L') (h' : ∀ (i : ℕ), i ≤ length L → sum (take i L) = sum (take i L')) : L = L' := sorry

theorem monotone_sum_take {α : Type u} [canonically_ordered_add_monoid α] (L : List α) : monotone fun (i : ℕ) => sum (take i L) := sorry

theorem one_le_prod_of_one_le {α : Type u} [ordered_comm_monoid α] {l : List α} (hl₁ : ∀ (x : α), x ∈ l → 1 ≤ x) : 1 ≤ prod l := sorry

theorem single_le_prod {α : Type u} [ordered_comm_monoid α] {l : List α} (hl₁ : ∀ (x : α), x ∈ l → 1 ≤ x) (x : α) (H : x ∈ l) : x ≤ prod l := sorry

theorem all_zero_of_le_zero_le_of_sum_eq_zero {α : Type u} [ordered_add_comm_monoid α] {l : List α} (hl₁ : ∀ (x : α), x ∈ l → 0 ≤ x) (hl₂ : sum l = 0) (x : α) (H : x ∈ l) : x = 0 :=
  le_antisymm (hl₂ ▸ single_le_sum hl₁ x hx) (hl₁ x hx)

theorem sum_eq_zero_iff {α : Type u} [canonically_ordered_add_monoid α] (l : List α) : sum l = 0 ↔ ∀ (x : α), x ∈ l → x = 0 := sorry

/-- A list with sum not zero must have positive length. -/
theorem length_pos_of_sum_ne_zero {α : Type u} [add_monoid α] (L : List α) (h : sum L ≠ 0) : 0 < length L := sorry

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ (i : ℕ), i ∈ L → 1 ≤ i) : length L ≤ sum L := sorry

-- Now we tie those lemmas back to their multiplicative versions.

/-- A list with positive sum must have positive length. -/
-- This is an easy consequence of `length_pos_of_sum_ne_zero`, but often useful in applications.

theorem length_pos_of_sum_pos {α : Type u} [ordered_cancel_add_comm_monoid α] (L : List α) (h : 0 < sum L) : 0 < length L :=
  length_pos_of_sum_ne_zero L (ne_of_gt h)

@[simp] theorem prod_erase {α : Type u} [DecidableEq α] [comm_monoid α] {a : α} {l : List α} : a ∈ l → a * prod (list.erase l a) = prod l := sorry

theorem dvd_prod {α : Type u} [comm_monoid α] {a : α} {l : List α} (ha : a ∈ l) : a ∣ prod l := sorry

@[simp] theorem sum_const_nat (m : ℕ) (n : ℕ) : sum (repeat m n) = m * n := sorry

theorem dvd_sum {α : Type u} [comm_semiring α] {a : α} {l : List α} (h : ∀ (x : α), x ∈ l → a ∣ x) : a ∣ sum l := sorry

@[simp] theorem length_join {α : Type u} (L : List (List α)) : length (join L) = sum (map length L) := sorry

@[simp] theorem length_bind {α : Type u} {β : Type v} (l : List α) (f : α → List β) : length (list.bind l f) = sum (map (length ∘ f) l) := sorry

theorem exists_lt_of_sum_lt {α : Type u} {β : Type v} [linear_ordered_cancel_add_comm_monoid β] {l : List α} (f : α → β) (g : α → β) (h : sum (map f l) < sum (map g l)) : ∃ (x : α), ∃ (H : x ∈ l), f x < g x := sorry

theorem exists_le_of_sum_le {α : Type u} {β : Type v} [linear_ordered_cancel_add_comm_monoid β] {l : List α} (hl : l ≠ []) (f : α → β) (g : α → β) (h : sum (map f l) ≤ sum (map g l)) : ∃ (x : α), ∃ (H : x ∈ l), f x ≤ g x := sorry

-- Several lemmas about sum/head/tail for `list ℕ`.

-- These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.

-- We'd like to state this as `L.head * L.tail.prod = L.prod`,

-- but because `L.head` relies on an inhabited instances and

-- returns a garbage value for the empty list, this is not possible.

-- Instead we write the statement in terms of `(L.nth 0).get_or_else 1`,

-- and below, restate the lemma just for `ℕ`.

theorem head_mul_tail_prod' {α : Type u} [monoid α] (L : List α) : option.get_or_else (nth L 0) 1 * prod (tail L) = prod L := sorry

theorem head_add_tail_sum (L : List ℕ) : head L + sum (tail L) = sum L := sorry

theorem head_le_sum (L : List ℕ) : head L ≤ sum L :=
  nat.le.intro (head_add_tail_sum L)

theorem tail_sum (L : List ℕ) : sum (tail L) = sum L - head L := sorry

@[simp] theorem alternating_prod_nil {G : Type u_1} [comm_group G] : alternating_prod [] = 1 :=
  rfl

@[simp] theorem alternating_sum_singleton {G : Type u_1} [add_comm_group G] (g : G) : alternating_sum [g] = g :=
  rfl

@[simp] theorem alternating_sum_cons_cons' {G : Type u_1} [add_comm_group G] (g : G) (h : G) (l : List G) : alternating_sum (g :: h :: l) = g + -h + alternating_sum l :=
  rfl

theorem alternating_sum_cons_cons {G : Type u_1} [add_comm_group G] (g : G) (h : G) (l : List G) : alternating_sum (g :: h :: l) = g - h + alternating_sum l := sorry

/-! ### join -/

theorem join_eq_nil {α : Type u} {L : List (List α)} : join L = [] ↔ ∀ (l : List α), l ∈ L → l = [] := sorry

@[simp] theorem join_append {α : Type u} (L₁ : List (List α)) (L₂ : List (List α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ := sorry

theorem join_join {α : Type u} (l : List (List (List α))) : join (join l) = join (map join l) := sorry

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
theorem take_sum_join {α : Type u} (L : List (List α)) (i : ℕ) : take (sum (take i (map length L))) (join L) = join (take i L) := sorry

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
theorem drop_sum_join {α : Type u} (L : List (List α)) (i : ℕ) : drop (sum (take i (map length L))) (join L) = join (drop i L) := sorry

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_nth_le {α : Type u} (L : List α) {i : ℕ} (hi : i < length L) : drop i (take (i + 1) L) = [nth_le L i hi] := sorry

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
theorem drop_take_succ_join_eq_nth_le {α : Type u} (L : List (List α)) {i : ℕ} (hi : i < length L) : drop (sum (take i (map length L))) (take (sum (take (i + 1) (map length L))) (join L)) = nth_le L i hi := sorry

/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt1 {α : Type u} (L : List (List α)) {i : ℕ} {j : ℕ} (hi : i < length L) (hj : j < length (nth_le L i hi)) : sum (take i (map length L)) + j < sum (take (i + 1) (map length L)) := sorry

/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt2 {α : Type u} (L : List (List α)) {i : ℕ} {j : ℕ} (hi : i < length L) (hj : j < length (nth_le L i hi)) : sum (take i (map length L)) + j < length (join L) := sorry

/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
theorem nth_le_join {α : Type u} (L : List (List α)) {i : ℕ} {j : ℕ} (hi : i < length L) (hj : j < length (nth_le L i hi)) : nth_le (join L) (sum (take i (map length L)) + j) (sum_take_map_length_lt2 L hi hj) = nth_le (nth_le L i hi) j hj := sorry

/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq {α : Type u} (L : List (List α)) (L' : List (List α)) : L = L' ↔ join L = join L' ∧ map length L = map length L' := sorry

/-! ### lexicographic ordering -/

/-- Given a strict order `<` on `α`, the lexicographic strict order on `list α`, for which
`[a0, ..., an] < [b0, ..., b_k]` if `a0 < b0` or `a0 = b0` and `[a1, ..., an] < [b1, ..., bk]`.
The definition is given for any relation `r`, not only strict orders. -/
inductive lex {α : Type u} (r : α → α → Prop) : List α → List α → Prop
where
| nil : ∀ {a : α} {l : List α}, lex r [] (a :: l)
| cons : ∀ {a : α} {l₁ l₂ : List α}, lex r l₁ l₂ → lex r (a :: l₁) (a :: l₂)
| rel : ∀ {a₁ : α} {l₁ : List α} {a₂ : α} {l₂ : List α}, r a₁ a₂ → lex r (a₁ :: l₁) (a₂ :: l₂)

namespace lex


theorem cons_iff {α : Type u} {r : α → α → Prop} [is_irrefl α r] {a : α} {l₁ : List α} {l₂ : List α} : lex r (a :: l₁) (a :: l₂) ↔ lex r l₁ l₂ := sorry

@[simp] theorem not_nil_right {α : Type u} (r : α → α → Prop) (l : List α) : ¬lex r l [] := sorry

protected instance is_order_connected {α : Type u} (r : α → α → Prop) [is_order_connected α r] [is_trichotomous α r] : is_order_connected (List α) (lex r) :=
  is_order_connected.mk fun (l₁ : List α) => sorry

protected instance is_trichotomous {α : Type u} (r : α → α → Prop) [is_trichotomous α r] : is_trichotomous (List α) (lex r) :=
  is_trichotomous.mk fun (l₁ : List α) => sorry

protected instance is_asymm {α : Type u} (r : α → α → Prop) [is_asymm α r] : is_asymm (List α) (lex r) :=
  is_asymm.mk fun (l₁ : List α) => sorry

protected instance is_strict_total_order {α : Type u} (r : α → α → Prop) [is_strict_total_order' α r] : is_strict_total_order' (List α) (lex r) :=
  is_strict_total_order'.mk

protected instance decidable_rel {α : Type u} [DecidableEq α] (r : α → α → Prop) [DecidableRel r] : DecidableRel (lex r) :=
  sorry

theorem append_right {α : Type u} (r : α → α → Prop) {s₁ : List α} {s₂ : List α} (t : List α) : lex r s₁ s₂ → lex r s₁ (s₂ ++ t) := sorry

theorem append_left {α : Type u} (R : α → α → Prop) {t₁ : List α} {t₂ : List α} (h : lex R t₁ t₂) (s : List α) : lex R (s ++ t₁) (s ++ t₂) := sorry

theorem imp {α : Type u} {r : α → α → Prop} {s : α → α → Prop} (H : ∀ (a b : α), r a b → s a b) (l₁ : List α) (l₂ : List α) : lex r l₁ l₂ → lex s l₁ l₂ := sorry

theorem to_ne {α : Type u} {l₁ : List α} {l₂ : List α} : lex ne l₁ l₂ → l₁ ≠ l₂ := sorry

theorem ne_iff {α : Type u} {l₁ : List α} {l₂ : List α} (H : length l₁ ≤ length l₂) : lex ne l₁ l₂ ↔ l₁ ≠ l₂ := sorry

end lex


--Note: this overrides an instance in core lean

protected instance has_lt' {α : Type u} [HasLess α] : HasLess (List α) :=
  { Less := lex Less }

theorem nil_lt_cons {α : Type u} [HasLess α] (a : α) (l : List α) : [] < a :: l :=
  lex.nil

protected instance linear_order {α : Type u} [linear_order α] : linear_order (List α) :=
  linear_order_of_STO' (lex Less)

--Note: this overrides an instance in core lean

protected instance has_le' {α : Type u} [linear_order α] : HasLessEq (List α) :=
  preorder.to_has_le (List α)

/-! ### all & any -/

@[simp] theorem all_nil {α : Type u} (p : α → Bool) : all [] p = tt :=
  rfl

@[simp] theorem all_cons {α : Type u} (p : α → Bool) (a : α) (l : List α) : all (a :: l) p = p a && all l p :=
  rfl

theorem all_iff_forall {α : Type u} {p : α → Bool} {l : List α} : ↥(all l p) ↔ ∀ (a : α), a ∈ l → ↥(p a) := sorry

theorem all_iff_forall_prop {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} : ↥(all l fun (a : α) => to_bool (p a)) ↔ ∀ (a : α), a ∈ l → p a := sorry

@[simp] theorem any_nil {α : Type u} (p : α → Bool) : any [] p = false :=
  rfl

@[simp] theorem any_cons {α : Type u} (p : α → Bool) (a : α) (l : List α) : any (a :: l) p = p a || any l p :=
  rfl

theorem any_iff_exists {α : Type u} {p : α → Bool} {l : List α} : ↥(any l p) ↔ ∃ (a : α), ∃ (H : a ∈ l), ↥(p a) := sorry

theorem any_iff_exists_prop {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} : ↥(any l fun (a : α) => to_bool (p a)) ↔ ∃ (a : α), ∃ (H : a ∈ l), p a := sorry

theorem any_of_mem {α : Type u} {p : α → Bool} {a : α} {l : List α} (h₁ : a ∈ l) (h₂ : ↥(p a)) : ↥(any l p) :=
  iff.mpr any_iff_exists (Exists.intro a (Exists.intro h₁ h₂))

protected instance decidable_forall_mem {α : Type u} {p : α → Prop} [decidable_pred p] (l : List α) : Decidable (∀ (x : α), x ∈ l → p x) :=
  decidable_of_iff ↥(all l fun (a : α) => to_bool (p a)) sorry

protected instance decidable_exists_mem {α : Type u} {p : α → Prop} [decidable_pred p] (l : List α) : Decidable (∃ (x : α), ∃ (H : x ∈ l), p x) :=
  decidable_of_iff ↥(any l fun (a : α) => to_bool (p a)) sorry

/-! ### map for partial functions -/

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {α : Type u} {β : Type v} {p : α → Prop} (f : (a : α) → p a → β) (l : List α) : (∀ (a : α), a ∈ l → p a) → List β :=
  sorry

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α : Type u} (l : List α) : List (Subtype fun (x : α) => x ∈ l) :=
  pmap Subtype.mk l sorry

theorem sizeof_lt_sizeof_of_mem {α : Type u} [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) : sizeof x < sizeof l := sorry

theorem pmap_eq_map {α : Type u} {β : Type v} (p : α → Prop) (f : α → β) (l : List α) (H : ∀ (a : α), a ∈ l → p a) : pmap (fun (a : α) (_x : p a) => f a) l H = map f l := sorry

theorem pmap_congr {α : Type u} {β : Type v} {p : α → Prop} {q : α → Prop} {f : (a : α) → p a → β} {g : (a : α) → q a → β} (l : List α) {H₁ : ∀ (a : α), a ∈ l → p a} {H₂ : ∀ (a : α), a ∈ l → q a} (h : ∀ (a : α) (h₁ : p a) (h₂ : q a), f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ := sorry

theorem map_pmap {α : Type u} {β : Type v} {γ : Type w} {p : α → Prop} (g : β → γ) (f : (a : α) → p a → β) (l : List α) (H : ∀ (a : α), a ∈ l → p a) : map g (pmap f l H) = pmap (fun (a : α) (h : p a) => g (f a h)) l H := sorry

theorem pmap_map {α : Type u} {β : Type v} {γ : Type w} {p : β → Prop} (g : (b : β) → p b → γ) (f : α → β) (l : List α) (H : ∀ (a : β), a ∈ map f l → p a) : pmap g (map f l) H =
  pmap (fun (a : α) (h : p (f a)) => g (f a) h) l fun (a : α) (h : a ∈ l) => H (f a) (mem_map_of_mem f h) := sorry

theorem pmap_eq_map_attach {α : Type u} {β : Type v} {p : α → Prop} (f : (a : α) → p a → β) (l : List α) (H : ∀ (a : α), a ∈ l → p a) : pmap f l H =
  map (fun (x : Subtype fun (x : α) => x ∈ l) => f (subtype.val x) (H (subtype.val x) (subtype.property x))) (attach l) := sorry

theorem attach_map_val {α : Type u} (l : List α) : map subtype.val (attach l) = l := sorry

@[simp] theorem mem_attach {α : Type u} (l : List α) (x : Subtype fun (x : α) => x ∈ l) : x ∈ attach l := sorry

@[simp] theorem mem_pmap {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α) → p a → β} {l : List α} {H : ∀ (a : α), a ∈ l → p a} {b : β} : b ∈ pmap f l H ↔ ∃ (a : α), ∃ (h : a ∈ l), f a (H a h) = b := sorry

@[simp] theorem length_pmap {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α) → p a → β} {l : List α} {H : ∀ (a : α), a ∈ l → p a} : length (pmap f l H) = length l := sorry

@[simp] theorem length_attach {α : Type u} (L : List α) : length (attach L) = length L :=
  length_pmap

@[simp] theorem pmap_eq_nil {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α) → p a → β} {l : List α} {H : ∀ (a : α), a ∈ l → p a} : pmap f l H = [] ↔ l = [] :=
  eq.mpr (id (Eq._oldrec (Eq.refl (pmap f l H = [] ↔ l = [])) (Eq.symm (propext length_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (pmap f l H) = 0 ↔ l = [])) length_pmap))
      (eq.mpr (id (Eq._oldrec (Eq.refl (length l = 0 ↔ l = [])) (propext length_eq_zero))) (iff.refl (l = []))))

@[simp] theorem attach_eq_nil {α : Type u} (l : List α) : attach l = [] ↔ l = [] :=
  pmap_eq_nil

theorem last_pmap {α : Type u_1} {β : Type u_2} (p : α → Prop) (f : (a : α) → p a → β) (l : List α) (hl₁ : ∀ (a : α), a ∈ l → p a) (hl₂ : l ≠ []) : last (pmap f l hl₁) (mt (iff.mp pmap_eq_nil) hl₂) = f (last l hl₂) (hl₁ (last l hl₂) (last_mem hl₂)) := sorry

theorem nth_pmap {α : Type u} {β : Type v} {p : α → Prop} (f : (a : α) → p a → β) {l : List α} (h : ∀ (a : α), a ∈ l → p a) (n : ℕ) : nth (pmap f l h) n = option.pmap f (nth l n) fun (x : α) (H : x ∈ nth l n) => h x (nth_mem H) := sorry

theorem nth_le_pmap {α : Type u} {β : Type v} {p : α → Prop} (f : (a : α) → p a → β) {l : List α} (h : ∀ (a : α), a ∈ l → p a) {n : ℕ} (hn : n < length (pmap f l h)) : nth_le (pmap f l h) n hn =
  f (nth_le l n (length_pmap ▸ hn)) (h (nth_le l n (length_pmap ▸ hn)) (nth_le_mem l n (length_pmap ▸ hn))) := sorry

/-! ### find -/

@[simp] theorem find_nil {α : Type u} (p : α → Prop) [decidable_pred p] : find p [] = none :=
  rfl

@[simp] theorem find_cons_of_pos {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} (l : List α) (h : p a) : find p (a :: l) = some a :=
  if_pos h

@[simp] theorem find_cons_of_neg {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} (l : List α) (h : ¬p a) : find p (a :: l) = find p l :=
  if_neg h

@[simp] theorem find_eq_none {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} : find p l = none ↔ ∀ (x : α), x ∈ l → ¬p x := sorry

theorem find_some {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} {a : α} (H : find p l = some a) : p a := sorry

@[simp] theorem find_mem {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} {a : α} (H : find p l = some a) : a ∈ l := sorry

/-! ### lookmap -/

@[simp] theorem lookmap_nil {α : Type u} (f : α → Option α) : lookmap f [] = [] :=
  rfl

@[simp] theorem lookmap_cons_none {α : Type u} (f : α → Option α) {a : α} (l : List α) (h : f a = none) : lookmap f (a :: l) = a :: lookmap f l := sorry

@[simp] theorem lookmap_cons_some {α : Type u} (f : α → Option α) {a : α} {b : α} (l : List α) (h : f a = some b) : lookmap f (a :: l) = b :: l := sorry

theorem lookmap_some {α : Type u} (l : List α) : lookmap some l = l :=
  list.cases_on l (idRhs (lookmap some [] = lookmap some []) rfl)
    fun (l_hd : α) (l_tl : List α) => idRhs (lookmap some (l_hd :: l_tl) = lookmap some (l_hd :: l_tl)) rfl

theorem lookmap_none {α : Type u} (l : List α) : lookmap (fun (_x : α) => none) l = l := sorry

theorem lookmap_congr {α : Type u} {f : α → Option α} {g : α → Option α} {l : List α} : (∀ (a : α), a ∈ l → f a = g a) → lookmap f l = lookmap g l := sorry

theorem lookmap_of_forall_not {α : Type u} (f : α → Option α) {l : List α} (H : ∀ (a : α), a ∈ l → f a = none) : lookmap f l = l :=
  Eq.trans (lookmap_congr H) (lookmap_none l)

theorem lookmap_map_eq {α : Type u} {β : Type v} (f : α → Option α) (g : α → β) (h : ∀ (a b : α), b ∈ f a → g a = g b) (l : List α) : map g (lookmap f l) = map g l := sorry

theorem lookmap_id' {α : Type u} (f : α → Option α) (h : ∀ (a b : α), b ∈ f a → a = b) (l : List α) : lookmap f l = l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lookmap f l = l)) (Eq.symm (map_id (lookmap f l)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (map id (lookmap f l) = l)) (lookmap_map_eq f id h l)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (map id l = l)) (map_id l))) (Eq.refl l)))

theorem length_lookmap {α : Type u} (f : α → Option α) (l : List α) : length (lookmap f l) = length l := sorry

/-! ### filter_map -/

@[simp] theorem filter_map_nil {α : Type u} {β : Type v} (f : α → Option β) : filter_map f [] = [] :=
  rfl

@[simp] theorem filter_map_cons_none {α : Type u} {β : Type v} {f : α → Option β} (a : α) (l : List α) (h : f a = none) : filter_map f (a :: l) = filter_map f l := sorry

@[simp] theorem filter_map_cons_some {α : Type u} {β : Type v} (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) : filter_map f (a :: l) = b :: filter_map f l := sorry

theorem filter_map_append {α : Type u_1} {β : Type u_2} (l : List α) (l' : List α) (f : α → Option β) : filter_map f (l ++ l') = filter_map f l ++ filter_map f l' := sorry

theorem filter_map_eq_map {α : Type u} {β : Type v} (f : α → β) : filter_map (some ∘ f) = map f := sorry

theorem filter_map_eq_filter {α : Type u} (p : α → Prop) [decidable_pred p] : filter_map (option.guard p) = filter p := sorry

theorem filter_map_filter_map {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β) (g : β → Option γ) (l : List α) : filter_map g (filter_map f l) = filter_map (fun (x : α) => option.bind (f x) g) l := sorry

theorem map_filter_map {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β) (g : β → γ) (l : List α) : map g (filter_map f l) = filter_map (fun (x : α) => option.map g (f x)) l := sorry

theorem filter_map_map {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → Option γ) (l : List α) : filter_map g (map f l) = filter_map (g ∘ f) l := sorry

theorem filter_filter_map {α : Type u} {β : Type v} (f : α → Option β) (p : β → Prop) [decidable_pred p] (l : List α) : filter p (filter_map f l) = filter_map (fun (x : α) => option.filter p (f x)) l := sorry

theorem filter_map_filter {α : Type u} {β : Type v} (p : α → Prop) [decidable_pred p] (f : α → Option β) (l : List α) : filter_map f (filter p l) = filter_map (fun (x : α) => ite (p x) (f x) none) l := sorry

@[simp] theorem filter_map_some {α : Type u} (l : List α) : filter_map some l = l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter_map some l = l)) (filter_map_eq_map fun (x : α) => x))) (map_id l)

@[simp] theorem mem_filter_map {α : Type u} {β : Type v} (f : α → Option β) (l : List α) {b : β} : b ∈ filter_map f l ↔ ∃ (a : α), a ∈ l ∧ f a = some b := sorry

theorem map_filter_map_of_inv {α : Type u} {β : Type v} (f : α → Option β) (g : β → α) (H : ∀ (x : α), option.map g (f x) = some x) (l : List α) : map g (filter_map f l) = l := sorry

theorem sublist.filter_map {α : Type u} {β : Type v} (f : α → Option β) {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) : filter_map f l₁ <+ filter_map f l₂ := sorry

theorem sublist.map {α : Type u} {β : Type v} (f : α → β) {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
  filter_map_eq_map f ▸ sublist.filter_map (some ∘ f) s

/-! ### reduce_option -/

@[simp] theorem reduce_option_cons_of_some {α : Type u} (x : α) (l : List (Option α)) : reduce_option (some x :: l) = x :: reduce_option l := sorry

@[simp] theorem reduce_option_cons_of_none {α : Type u} (l : List (Option α)) : reduce_option (none :: l) = reduce_option l := sorry

@[simp] theorem reduce_option_nil {α : Type u} : reduce_option [] = [] :=
  rfl

@[simp] theorem reduce_option_map {α : Type u} {β : Type v} {l : List (Option α)} {f : α → β} : reduce_option (map (option.map f) l) = map f (reduce_option l) := sorry

theorem reduce_option_append {α : Type u} (l : List (Option α)) (l' : List (Option α)) : reduce_option (l ++ l') = reduce_option l ++ reduce_option l' :=
  filter_map_append l l' id

theorem reduce_option_length_le {α : Type u} (l : List (Option α)) : length (reduce_option l) ≤ length l := sorry

theorem reduce_option_length_eq_iff {α : Type u} {l : List (Option α)} : length (reduce_option l) = length l ↔ ∀ (x : Option α), x ∈ l → ↥(option.is_some x) := sorry

theorem reduce_option_length_lt_iff {α : Type u} {l : List (Option α)} : length (reduce_option l) < length l ↔ none ∈ l := sorry

theorem reduce_option_singleton {α : Type u} (x : Option α) : reduce_option [x] = option.to_list x :=
  option.cases_on x (Eq.refl (reduce_option [none])) fun (x : α) => Eq.refl (reduce_option [some x])

theorem reduce_option_concat {α : Type u} (l : List (Option α)) (x : Option α) : reduce_option (concat l x) = reduce_option l ++ option.to_list x := sorry

theorem reduce_option_concat_of_some {α : Type u} (l : List (Option α)) (x : α) : reduce_option (concat l (some x)) = concat (reduce_option l) x := sorry

theorem reduce_option_mem_iff {α : Type u} {l : List (Option α)} {x : α} : x ∈ reduce_option l ↔ some x ∈ l := sorry

theorem reduce_option_nth_iff {α : Type u} {l : List (Option α)} {x : α} : (∃ (i : ℕ), nth l i = some (some x)) ↔ ∃ (i : ℕ), nth (reduce_option l) i = some x := sorry

/-! ### filter -/

theorem filter_eq_foldr {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : filter p l = foldr (fun (a : α) (out : List α) => ite (p a) (a :: out) out) [] l := sorry

theorem filter_congr {α : Type u} {p : α → Prop} {q : α → Prop} [decidable_pred p] [decidable_pred q] {l : List α} : (∀ (x : α), x ∈ l → (p x ↔ q x)) → filter p l = filter q l := sorry

@[simp] theorem filter_subset {α : Type u} {p : α → Prop} [decidable_pred p] (l : List α) : filter p l ⊆ l :=
  sublist.subset (filter_sublist l)

theorem of_mem_filter {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} : a ∈ filter p l → p a := sorry

theorem mem_of_mem_filter {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset l h

theorem mem_filter_of_mem {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} : a ∈ l → p a → a ∈ filter p l := sorry

@[simp] theorem mem_filter {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} : a ∈ filter p l ↔ a ∈ l ∧ p a := sorry

theorem filter_eq_self {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} : filter p l = l ↔ ∀ (a : α), a ∈ l → p a := sorry

theorem filter_eq_nil {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} : filter p l = [] ↔ ∀ (a : α), a ∈ l → ¬p a := sorry

theorem filter_sublist_filter {α : Type u} (p : α → Prop) [decidable_pred p] {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
  filter_map_eq_filter p ▸ sublist.filter_map (option.guard p) s

theorem filter_of_map {α : Type u} {β : Type v} (p : α → Prop) [decidable_pred p] (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) := sorry

@[simp] theorem filter_filter {α : Type u} (p : α → Prop) [decidable_pred p] (q : α → Prop) [decidable_pred q] (l : List α) : filter p (filter q l) = filter (fun (a : α) => p a ∧ q a) l := sorry

@[simp] theorem filter_true {α : Type u} {h : decidable_pred fun (a : α) => True} (l : List α) : filter (fun (a : α) => True) l = l := sorry

@[simp] theorem filter_false {α : Type u} {h : decidable_pred fun (a : α) => False} (l : List α) : filter (fun (a : α) => False) l = [] := sorry

@[simp] theorem span_eq_take_drop {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : span p l = (take_while p l, drop_while p l) := sorry

@[simp] theorem take_while_append_drop {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : take_while p l ++ drop_while p l = l := sorry

@[simp] theorem countp_nil {α : Type u} (p : α → Prop) [decidable_pred p] : countp p [] = 0 :=
  rfl

@[simp] theorem countp_cons_of_pos {α : Type u} (p : α → Prop) [decidable_pred p] {a : α} (l : List α) (pa : p a) : countp p (a :: l) = countp p l + 1 :=
  if_pos pa

@[simp] theorem countp_cons_of_neg {α : Type u} (p : α → Prop) [decidable_pred p] {a : α} (l : List α) (pa : ¬p a) : countp p (a :: l) = countp p l :=
  if_neg pa

theorem countp_eq_length_filter {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : countp p l = length (filter p l) := sorry

@[simp] theorem countp_append {α : Type u} (p : α → Prop) [decidable_pred p] (l₁ : List α) (l₂ : List α) : countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ := sorry

theorem countp_pos {α : Type u} (p : α → Prop) [decidable_pred p] {l : List α} : 0 < countp p l ↔ ∃ (a : α), ∃ (H : a ∈ l), p a := sorry

theorem countp_le_of_sublist {α : Type u} (p : α → Prop) [decidable_pred p] {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) : countp p l₁ ≤ countp p l₂ := sorry

@[simp] theorem countp_filter {α : Type u} (p : α → Prop) [decidable_pred p] {q : α → Prop} [decidable_pred q] (l : List α) : countp p (filter q l) = countp (fun (a : α) => p a ∧ q a) l := sorry

/-! ### count -/

@[simp] theorem count_nil {α : Type u} [DecidableEq α] (a : α) : count a [] = 0 :=
  rfl

theorem count_cons {α : Type u} [DecidableEq α] (a : α) (b : α) (l : List α) : count a (b :: l) = ite (a = b) (Nat.succ (count a l)) (count a l) :=
  rfl

theorem count_cons' {α : Type u} [DecidableEq α] (a : α) (b : α) (l : List α) : count a (b :: l) = count a l + ite (a = b) 1 0 := sorry

@[simp] theorem count_cons_self {α : Type u} [DecidableEq α] (a : α) (l : List α) : count a (a :: l) = Nat.succ (count a l) :=
  if_pos rfl

@[simp] theorem count_cons_of_ne {α : Type u} [DecidableEq α] {a : α} {b : α} (h : a ≠ b) (l : List α) : count a (b :: l) = count a l :=
  if_neg h

theorem count_tail {α : Type u} [DecidableEq α] (l : List α) (a : α) (h : 0 < length l) : count a (tail l) = count a l - ite (a = nth_le l 0 h) 1 0 := sorry

theorem count_le_of_sublist {α : Type u} [DecidableEq α] (a : α) {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → count a l₁ ≤ count a l₂ :=
  countp_le_of_sublist (Eq a)

theorem count_le_count_cons {α : Type u} [DecidableEq α] (a : α) (b : α) (l : List α) : count a l ≤ count a (b :: l) :=
  count_le_of_sublist a (sublist_cons b l)

theorem count_singleton {α : Type u} [DecidableEq α] (a : α) : count a [a] = 1 :=
  if_pos rfl

@[simp] theorem count_append {α : Type u} [DecidableEq α] (a : α) (l₁ : List α) (l₂ : List α) : count a (l₁ ++ l₂) = count a l₁ + count a l₂ :=
  countp_append (Eq a)

theorem count_concat {α : Type u} [DecidableEq α] (a : α) (l : List α) : count a (concat l a) = Nat.succ (count a l) := sorry

theorem count_pos {α : Type u} [DecidableEq α] {a : α} {l : List α} : 0 < count a l ↔ a ∈ l := sorry

@[simp] theorem count_eq_zero_of_not_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : ¬a ∈ l) : count a l = 0 :=
  by_contradiction fun (h' : ¬count a l = 0) => h (iff.mp count_pos (nat.pos_of_ne_zero h'))

theorem not_mem_of_count_eq_zero {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : count a l = 0) : ¬a ∈ l :=
  fun (h' : a ∈ l) => ne_of_gt (iff.mpr count_pos h') h

@[simp] theorem count_repeat {α : Type u} [DecidableEq α] (a : α) (n : ℕ) : count a (repeat a n) = n := sorry

theorem le_count_iff_repeat_sublist {α : Type u} [DecidableEq α] {a : α} {l : List α} {n : ℕ} : n ≤ count a l ↔ repeat a n <+ l := sorry

theorem repeat_count_eq_of_count_eq_length {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : count a l = length l) : repeat a (count a l) = l :=
  eq_of_sublist_of_length_eq (iff.mp le_count_iff_repeat_sublist (le_refl (count a l)))
    (Eq.trans (length_repeat a (count a l)) h)

@[simp] theorem count_filter {α : Type u} [DecidableEq α] {p : α → Prop} [decidable_pred p] {a : α} {l : List α} (h : p a) : count a (filter p l) = count a l := sorry

/-! ### prefix, suffix, infix -/

@[simp] theorem prefix_append {α : Type u} (l₁ : List α) (l₂ : List α) : l₁ <+: l₁ ++ l₂ :=
  Exists.intro l₂ rfl

@[simp] theorem suffix_append {α : Type u} (l₁ : List α) (l₂ : List α) : l₂ <:+ l₁ ++ l₂ :=
  Exists.intro l₁ rfl

theorem infix_append {α : Type u} (l₁ : List α) (l₂ : List α) (l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ :=
  Exists.intro l₁ (Exists.intro l₃ rfl)

@[simp] theorem infix_append' {α : Type u} (l₁ : List α) (l₂ : List α) (l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (l₂ <:+: l₁ ++ (l₂ ++ l₃))) (Eq.symm (append_assoc l₁ l₂ l₃)))) (infix_append l₁ l₂ l₃)

theorem nil_prefix {α : Type u} (l : List α) : [] <+: l :=
  Exists.intro l rfl

theorem nil_suffix {α : Type u} (l : List α) : [] <:+ l :=
  Exists.intro l (append_nil l)

theorem prefix_refl {α : Type u} (l : List α) : l <+: l :=
  Exists.intro [] (append_nil l)

theorem suffix_refl {α : Type u} (l : List α) : l <:+ l :=
  Exists.intro [] rfl

@[simp] theorem suffix_cons {α : Type u} (a : α) (l : List α) : l <:+ a :: l :=
  suffix_append [a]

theorem prefix_concat {α : Type u} (a : α) (l : List α) : l <+: concat l a := sorry

theorem infix_of_prefix {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+: l₂ → l₁ <:+: l₂ := sorry

theorem infix_of_suffix {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <:+ l₂ → l₁ <:+: l₂ := sorry

theorem infix_refl {α : Type u} (l : List α) : l <:+: l :=
  infix_of_prefix (prefix_refl l)

theorem nil_infix {α : Type u} (l : List α) : [] <:+: l :=
  infix_of_prefix (nil_prefix l)

theorem infix_cons {α : Type u} {L₁ : List α} {L₂ : List α} {x : α} : L₁ <:+: L₂ → L₁ <:+: x :: L₂ := sorry

theorem is_prefix.trans {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} : l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃ := sorry

theorem is_suffix.trans {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} : l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃ := sorry

theorem is_infix.trans {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} : l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃ := sorry

theorem sublist_of_infix {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <:+: l₂ → l₁ <+ l₂ := sorry

theorem sublist_of_prefix {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+: l₂ → l₁ <+ l₂ :=
  sublist_of_infix ∘ infix_of_prefix

theorem sublist_of_suffix {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <:+ l₂ → l₁ <+ l₂ :=
  sublist_of_infix ∘ infix_of_suffix

theorem reverse_suffix {α : Type u} {l₁ : List α} {l₂ : List α} : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ := sorry

theorem reverse_prefix {α : Type u} {l₁ : List α} {l₂ : List α} : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ := sorry

theorem length_le_of_infix {α : Type u} {l₁ : List α} {l₂ : List α} (s : l₁ <:+: l₂) : length l₁ ≤ length l₂ :=
  length_le_of_sublist (sublist_of_infix s)

theorem eq_nil_of_infix_nil {α : Type u} {l : List α} (s : l <:+: []) : l = [] :=
  eq_nil_of_sublist_nil (sublist_of_infix s)

theorem eq_nil_of_prefix_nil {α : Type u} {l : List α} (s : l <+: []) : l = [] :=
  eq_nil_of_infix_nil (infix_of_prefix s)

theorem eq_nil_of_suffix_nil {α : Type u} {l : List α} (s : l <:+ []) : l = [] :=
  eq_nil_of_infix_nil (infix_of_suffix s)

theorem infix_iff_prefix_suffix {α : Type u} (l₁ : List α) (l₂ : List α) : l₁ <:+: l₂ ↔ ∃ (t : List α), l₁ <+: t ∧ t <:+ l₂ := sorry

theorem eq_of_infix_of_length_eq {α : Type u} {l₁ : List α} {l₂ : List α} (s : l₁ <:+: l₂) : length l₁ = length l₂ → l₁ = l₂ :=
  eq_of_sublist_of_length_eq (sublist_of_infix s)

theorem eq_of_prefix_of_length_eq {α : Type u} {l₁ : List α} {l₂ : List α} (s : l₁ <+: l₂) : length l₁ = length l₂ → l₁ = l₂ :=
  eq_of_sublist_of_length_eq (sublist_of_prefix s)

theorem eq_of_suffix_of_length_eq {α : Type u} {l₁ : List α} {l₂ : List α} (s : l₁ <:+ l₂) : length l₁ = length l₂ → l₁ = l₂ :=
  eq_of_sublist_of_length_eq (sublist_of_suffix s)

theorem prefix_of_prefix_length_le {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} : l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂ := sorry

theorem prefix_or_prefix_of_prefix {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  or.imp (prefix_of_prefix_length_le h₁ h₂) (prefix_of_prefix_length_le h₂ h₁) (le_total (length l₁) (length l₂))

theorem suffix_of_suffix_length_le {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) : l₁ <:+ l₂ := sorry

theorem suffix_or_suffix_of_suffix {α : Type u} {l₁ : List α} {l₂ : List α} {l₃ : List α} (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  or.imp (iff.mp reverse_prefix) (iff.mp reverse_prefix)
    (prefix_or_prefix_of_prefix (iff.mpr reverse_prefix h₁) (iff.mpr reverse_prefix h₂))

theorem infix_of_mem_join {α : Type u} {L : List (List α)} {l : List α} : l ∈ L → l <:+: join L := sorry

theorem prefix_append_right_inj {α : Type u} {l₁ : List α} {l₂ : List α} (l : List α) : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ := sorry

theorem prefix_cons_inj {α : Type u} {l₁ : List α} {l₂ : List α} (a : α) : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]

theorem take_prefix {α : Type u} (n : ℕ) (l : List α) : take n l <+: l :=
  Exists.intro (drop n l) (take_append_drop n l)

theorem drop_suffix {α : Type u} (n : ℕ) (l : List α) : drop n l <:+ l :=
  Exists.intro (take n l) (take_append_drop n l)

theorem tail_suffix {α : Type u} (l : List α) : tail l <:+ l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tail l <:+ l)) (Eq.symm (drop_one l)))) (drop_suffix 1 l)

theorem tail_subset {α : Type u} (l : List α) : tail l ⊆ l :=
  sublist.subset (sublist_of_suffix (tail_suffix l))

theorem prefix_iff_eq_append {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ := sorry

theorem suffix_iff_eq_append {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ := sorry

theorem prefix_iff_eq_take {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ := sorry

theorem suffix_iff_eq_drop {α : Type u} {l₁ : List α} {l₂ : List α} : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ := sorry

protected instance decidable_prefix {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : Decidable (l₁ <+: l₂) :=
  sorry

-- Alternatively, use mem_tails

protected instance decidable_suffix {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : Decidable (l₁ <:+ l₂) :=
  sorry

theorem prefix_take_le_iff {α : Type u} {L : List (List (Option α))} {m : ℕ} {n : ℕ} (hm : m < length L) : take m L <+: take n L ↔ m ≤ n := sorry

theorem cons_prefix_iff {α : Type u} {l : List α} {l' : List α} {x : α} {y : α} : x :: l <+: y :: l' ↔ x = y ∧ l <+: l' := sorry

theorem map_prefix {α : Type u} {β : Type v} {l : List α} {l' : List α} (f : α → β) (h : l <+: l') : map f l <+: map f l' := sorry

theorem is_prefix.filter_map {α : Type u} {β : Type v} {l : List α} {l' : List α} (h : l <+: l') (f : α → Option β) : filter_map f l <+: filter_map f l' := sorry

theorem is_prefix.reduce_option {α : Type u} {l : List (Option α)} {l' : List (Option α)} (h : l <+: l') : reduce_option l <+: reduce_option l' :=
  is_prefix.filter_map h id

@[simp] theorem mem_inits {α : Type u} (s : List α) (t : List α) : s ∈ inits t ↔ s <+: t := sorry

@[simp] theorem mem_tails {α : Type u} (s : List α) (t : List α) : s ∈ tails t ↔ s <:+ t := sorry

theorem inits_cons {α : Type u} (a : α) (l : List α) : inits (a :: l) = [] :: map (fun (t : List α) => a :: t) (inits l) := sorry

theorem tails_cons {α : Type u} (a : α) (l : List α) : tails (a :: l) = (a :: l) :: tails l := sorry

@[simp] theorem inits_append {α : Type u} (s : List α) (t : List α) : inits (s ++ t) = inits s ++ map (fun (l : List α) => s ++ l) (tail (inits t)) := sorry

@[simp] theorem tails_append {α : Type u} (s : List α) (t : List α) : tails (s ++ t) = map (fun (l : List α) => l ++ t) (tails s) ++ tail (tails t) := sorry

-- the lemma names `inits_eq_tails` and `tails_eq_inits` are like `sublists_eq_sublists'`

theorem inits_eq_tails {α : Type u} (l : List α) : inits l = reverse (map reverse (tails (reverse l))) := sorry

theorem tails_eq_inits {α : Type u} (l : List α) : tails l = reverse (map reverse (inits (reverse l))) := sorry

theorem inits_reverse {α : Type u} (l : List α) : inits (reverse l) = reverse (map reverse (tails l)) := sorry

theorem tails_reverse {α : Type u} (l : List α) : tails (reverse l) = reverse (map reverse (inits l)) := sorry

theorem map_reverse_inits {α : Type u} (l : List α) : map reverse (inits l) = reverse (tails (reverse l)) := sorry

theorem map_reverse_tails {α : Type u} (l : List α) : map reverse (tails l) = reverse (inits (reverse l)) := sorry

protected instance decidable_infix {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : Decidable (l₁ <:+: l₂) :=
  sorry

/-! ### sublists -/

@[simp] theorem sublists'_nil {α : Type u} : sublists' [] = [[]] :=
  rfl

@[simp] theorem sublists'_singleton {α : Type u} (a : α) : sublists' [a] = [[], [a]] :=
  rfl

theorem map_sublists'_aux {α : Type u} {β : Type v} {γ : Type w} (g : List β → List γ) (l : List α) (f : List α → List β) (r : List (List β)) : map g (sublists'_aux l f r) = sublists'_aux l (g ∘ f) (map g r) := sorry

theorem sublists'_aux_append {α : Type u} {β : Type v} (r' : List (List β)) (l : List α) (f : List α → List β) (r : List (List β)) : sublists'_aux l f (r ++ r') = sublists'_aux l f r ++ r' := sorry

theorem sublists'_aux_eq_sublists' {α : Type u} {β : Type v} (l : List α) (f : List α → List β) (r : List (List β)) : sublists'_aux l f r = map f (sublists' l) ++ r := sorry

@[simp] theorem sublists'_cons {α : Type u} (a : α) (l : List α) : sublists' (a :: l) = sublists' l ++ map (List.cons a) (sublists' l) := sorry

@[simp] theorem mem_sublists' {α : Type u} {s : List α} {t : List α} : s ∈ sublists' t ↔ s <+ t := sorry

@[simp] theorem length_sublists' {α : Type u} (l : List α) : length (sublists' l) = bit0 1 ^ length l := sorry

@[simp] theorem sublists_nil {α : Type u} : sublists [] = [[]] :=
  rfl

@[simp] theorem sublists_singleton {α : Type u} (a : α) : sublists [a] = [[], [a]] :=
  rfl

theorem sublists_aux₁_eq_sublists_aux {α : Type u} {β : Type v} (l : List α) (f : List α → List β) : sublists_aux₁ l f = sublists_aux l fun (ys : List α) (r : List β) => f ys ++ r := sorry

theorem sublists_aux_cons_eq_sublists_aux₁ {α : Type u} (l : List α) : sublists_aux l List.cons = sublists_aux₁ l fun (x : List α) => [x] := sorry

theorem sublists_aux_eq_foldr.aux {α : Type u} {β : Type v} {a : α} {l : List α} (IH₁ : ∀ (f : List α → List β → List β), sublists_aux l f = foldr f [] (sublists_aux l List.cons)) (IH₂ : ∀ (f : List α → List (List α) → List (List α)), sublists_aux l f = foldr f [] (sublists_aux l List.cons)) (f : List α → List β → List β) : sublists_aux (a :: l) f = foldr f [] (sublists_aux (a :: l) List.cons) := sorry

theorem sublists_aux_eq_foldr {α : Type u} {β : Type v} (l : List α) (f : List α → List β → List β) : sublists_aux l f = foldr f [] (sublists_aux l List.cons) := sorry

theorem sublists_aux_cons_cons {α : Type u} (l : List α) (a : α) : sublists_aux (a :: l) List.cons =
  [a] :: foldr (fun (ys : List α) (r : List (List α)) => ys :: (a :: ys) :: r) [] (sublists_aux l List.cons) := sorry

theorem sublists_aux₁_append {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List α) (f : List α → List β) : sublists_aux₁ (l₁ ++ l₂) f =
  sublists_aux₁ l₁ f ++ sublists_aux₁ l₂ fun (x : List α) => f x ++ sublists_aux₁ l₁ (f ∘ fun (_x : List α) => _x ++ x) := sorry

theorem sublists_aux₁_concat {α : Type u} {β : Type v} (l : List α) (a : α) (f : List α → List β) : sublists_aux₁ (l ++ [a]) f = sublists_aux₁ l f ++ f [a] ++ sublists_aux₁ l fun (x : List α) => f (x ++ [a]) := sorry

theorem sublists_aux₁_bind {α : Type u} {β : Type v} {γ : Type w} (l : List α) (f : List α → List β) (g : β → List γ) : list.bind (sublists_aux₁ l f) g = sublists_aux₁ l fun (x : List α) => list.bind (f x) g := sorry

theorem sublists_aux_cons_append {α : Type u} (l₁ : List α) (l₂ : List α) : sublists_aux (l₁ ++ l₂) List.cons =
  sublists_aux l₁ List.cons ++
    do 
      let x ← sublists_aux l₂ List.cons
      (fun (_x : List α) => _x ++ x) <$> sublists l₁ := sorry

theorem sublists_append {α : Type u} (l₁ : List α) (l₂ : List α) : sublists (l₁ ++ l₂) =
  do 
    let x ← sublists l₂
    (fun (_x : List α) => _x ++ x) <$> sublists l₁ := sorry

@[simp] theorem sublists_concat {α : Type u} (l : List α) (a : α) : sublists (l ++ [a]) = sublists l ++ map (fun (x : List α) => x ++ [a]) (sublists l) := sorry

theorem sublists_reverse {α : Type u} (l : List α) : sublists (reverse l) = map reverse (sublists' l) := sorry

theorem sublists_eq_sublists' {α : Type u} (l : List α) : sublists l = map reverse (sublists' (reverse l)) := sorry

theorem sublists'_reverse {α : Type u} (l : List α) : sublists' (reverse l) = map reverse (sublists l) := sorry

theorem sublists'_eq_sublists {α : Type u} (l : List α) : sublists' l = map reverse (sublists (reverse l)) := sorry

theorem sublists_aux_ne_nil {α : Type u} (l : List α) : ¬[] ∈ sublists_aux l List.cons := sorry

@[simp] theorem mem_sublists {α : Type u} {s : List α} {t : List α} : s ∈ sublists t ↔ s <+ t := sorry

@[simp] theorem length_sublists {α : Type u} (l : List α) : length (sublists l) = bit0 1 ^ length l := sorry

theorem map_ret_sublist_sublists {α : Type u} (l : List α) : map list.ret l <+ sublists l := sorry

/-! ### sublists_len -/

/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
of `f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
def sublists_len_aux {α : Type u_1} {β : Type u_2} : ℕ → List α → (List α → β) → List β → List β :=
  sorry

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
def sublists_len {α : Type u_1} (n : ℕ) (l : List α) : List (List α) :=
  sublists_len_aux n l id []

theorem sublists_len_aux_append {α : Type u_1} {β : Type u_2} {γ : Type u_3} (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ) : sublists_len_aux n l (g ∘ f) (map g r ++ s) = map g (sublists_len_aux n l f r) ++ s := sorry

theorem sublists_len_aux_eq {α : Type u_1} {β : Type u_2} (l : List α) (n : ℕ) (f : List α → β) (r : List β) : sublists_len_aux n l f r = map f (sublists_len n l) ++ r := sorry

theorem sublists_len_aux_zero {β : Type v} {α : Type u_1} (l : List α) (f : List α → β) (r : List β) : sublists_len_aux 0 l f r = f [] :: r :=
  list.cases_on l (Eq.refl (sublists_len_aux 0 [] f r))
    fun (l_hd : α) (l_tl : List α) => Eq.refl (sublists_len_aux 0 (l_hd :: l_tl) f r)

@[simp] theorem sublists_len_zero {α : Type u_1} (l : List α) : sublists_len 0 l = [[]] :=
  sublists_len_aux_zero l id []

@[simp] theorem sublists_len_succ_nil {α : Type u_1} (n : ℕ) : sublists_len (n + 1) [] = [] :=
  rfl

@[simp] theorem sublists_len_succ_cons {α : Type u_1} (n : ℕ) (a : α) (l : List α) : sublists_len (n + 1) (a :: l) = sublists_len (n + 1) l ++ map (List.cons a) (sublists_len n l) := sorry

@[simp] theorem length_sublists_len {α : Type u_1} (n : ℕ) (l : List α) : length (sublists_len n l) = nat.choose (length l) n := sorry

theorem sublists_len_sublist_sublists' {α : Type u_1} (n : ℕ) (l : List α) : sublists_len n l <+ sublists' l := sorry

theorem sublists_len_sublist_of_sublist {α : Type u_1} (n : ℕ) {l₁ : List α} {l₂ : List α} (h : l₁ <+ l₂) : sublists_len n l₁ <+ sublists_len n l₂ := sorry

theorem length_of_sublists_len {α : Type u_1} {n : ℕ} {l : List α} {l' : List α} : l' ∈ sublists_len n l → length l' = n := sorry

theorem mem_sublists_len_self {α : Type u_1} {l : List α} {l' : List α} (h : l' <+ l) : l' ∈ sublists_len (length l') l := sorry

@[simp] theorem mem_sublists_len {α : Type u_1} {n : ℕ} {l : List α} {l' : List α} : l' ∈ sublists_len n l ↔ l' <+ l ∧ length l' = n := sorry

/-! ### permutations -/

@[simp] theorem permutations_aux_nil {α : Type u} (is : List α) : permutations_aux [] is = [] := sorry

@[simp] theorem permutations_aux_cons {α : Type u} (t : α) (ts : List α) (is : List α) : permutations_aux (t :: ts) is =
  foldr (fun (y : List α) (r : List (List α)) => prod.snd (permutations_aux2 t ts r y id))
    (permutations_aux ts (t :: is)) (permutations is) := sorry

/-! ### insert -/

@[simp] theorem insert_nil {α : Type u} [DecidableEq α] (a : α) : insert a [] = [a] :=
  rfl

theorem insert.def {α : Type u} [DecidableEq α] (a : α) (l : List α) : insert a l = ite (a ∈ l) l (a :: l) :=
  rfl

@[simp] theorem insert_of_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : insert a l = l := sorry

@[simp] theorem insert_of_not_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : ¬a ∈ l) : insert a l = a :: l := sorry

@[simp] theorem mem_insert_iff {α : Type u} [DecidableEq α] {a : α} {b : α} {l : List α} : a ∈ insert b l ↔ a = b ∨ a ∈ l := sorry

@[simp] theorem suffix_insert {α : Type u} [DecidableEq α] (a : α) (l : List α) : l <:+ insert a l := sorry

@[simp] theorem mem_insert_self {α : Type u} [DecidableEq α] (a : α) (l : List α) : a ∈ insert a l :=
  iff.mpr mem_insert_iff (Or.inl rfl)

theorem mem_insert_of_mem {α : Type u} [DecidableEq α] {a : α} {b : α} {l : List α} (h : a ∈ l) : a ∈ insert b l :=
  iff.mpr mem_insert_iff (Or.inr h)

theorem eq_or_mem_of_mem_insert {α : Type u} [DecidableEq α] {a : α} {b : α} {l : List α} (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
  iff.mp mem_insert_iff h

@[simp] theorem length_insert_of_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : length (insert a l) = length l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (length (insert a l) = length l)) (insert_of_mem h))) (Eq.refl (length l))

@[simp] theorem length_insert_of_not_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : ¬a ∈ l) : length (insert a l) = length l + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (length (insert a l) = length l + 1)) (insert_of_not_mem h)))
    (Eq.refl (length (a :: l)))

/-! ### erasep -/

@[simp] theorem erasep_nil {α : Type u} {p : α → Prop} [decidable_pred p] : erasep p [] = [] :=
  rfl

theorem erasep_cons {α : Type u} {p : α → Prop} [decidable_pred p] (a : α) (l : List α) : erasep p (a :: l) = ite (p a) l (a :: erasep p l) :=
  rfl

@[simp] theorem erasep_cons_of_pos {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} (h : p a) : erasep p (a :: l) = l := sorry

@[simp] theorem erasep_cons_of_neg {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} (h : ¬p a) : erasep p (a :: l) = a :: erasep p l := sorry

theorem erasep_of_forall_not {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} (h : ∀ (a : α), a ∈ l → ¬p a) : erasep p l = l := sorry

theorem exists_of_erasep {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} {a : α} (al : a ∈ l) (pa : p a) : ∃ (a : α),
  ∃ (l₁ : List α), ∃ (l₂ : List α), (∀ (b : α), b ∈ l₁ → ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ erasep p l = l₁ ++ l₂ := sorry

theorem exists_or_eq_self_of_erasep {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : erasep p l = l ∨
  ∃ (a : α),
    ∃ (l₁ : List α), ∃ (l₂ : List α), (∀ (b : α), b ∈ l₁ → ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ erasep p l = l₁ ++ l₂ := sorry

@[simp] theorem length_erasep_of_mem {α : Type u} {p : α → Prop} [decidable_pred p] {l : List α} {a : α} (al : a ∈ l) (pa : p a) : length (erasep p l) = Nat.pred (length l) := sorry

theorem erasep_append_left {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} (pa : p a) {l₁ : List α} (l₂ : List α) : a ∈ l₁ → erasep p (l₁ ++ l₂) = erasep p l₁ ++ l₂ := sorry

theorem erasep_append_right {α : Type u} {p : α → Prop} [decidable_pred p] {l₁ : List α} (l₂ : List α) : (∀ (b : α), b ∈ l₁ → ¬p b) → erasep p (l₁ ++ l₂) = l₁ ++ erasep p l₂ := sorry

theorem erasep_sublist {α : Type u} {p : α → Prop} [decidable_pred p] (l : List α) : erasep p l <+ l := sorry

theorem erasep_subset {α : Type u} {p : α → Prop} [decidable_pred p] (l : List α) : erasep p l ⊆ l :=
  sublist.subset (erasep_sublist l)

theorem sublist.erasep {α : Type u} {p : α → Prop} [decidable_pred p] {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) : erasep p l₁ <+ erasep p l₂ := sorry

theorem mem_of_mem_erasep {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} : a ∈ erasep p l → a ∈ l :=
  erasep_subset l

@[simp] theorem mem_erasep_of_neg {α : Type u} {p : α → Prop} [decidable_pred p] {a : α} {l : List α} (pa : ¬p a) : a ∈ erasep p l ↔ a ∈ l := sorry

theorem erasep_map {α : Type u} {β : Type v} {p : α → Prop} [decidable_pred p] (f : β → α) (l : List β) : erasep p (map f l) = map f (erasep (p ∘ f) l) := sorry

@[simp] theorem extractp_eq_find_erasep {α : Type u} {p : α → Prop} [decidable_pred p] (l : List α) : extractp p l = (find p l, erasep p l) := sorry

/-! ### erase -/

@[simp] theorem erase_nil {α : Type u} [DecidableEq α] (a : α) : list.erase [] a = [] :=
  rfl

theorem erase_cons {α : Type u} [DecidableEq α] (a : α) (b : α) (l : List α) : list.erase (b :: l) a = ite (b = a) l (b :: list.erase l a) :=
  rfl

@[simp] theorem erase_cons_head {α : Type u} [DecidableEq α] (a : α) (l : List α) : list.erase (a :: l) a = l := sorry

@[simp] theorem erase_cons_tail {α : Type u} [DecidableEq α] {a : α} {b : α} (l : List α) (h : b ≠ a) : list.erase (b :: l) a = b :: list.erase l a := sorry

theorem erase_eq_erasep {α : Type u} [DecidableEq α] (a : α) (l : List α) : list.erase l a = erasep (Eq a) l := sorry

@[simp] theorem erase_of_not_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : ¬a ∈ l) : list.erase l a = l := sorry

theorem exists_erase_eq {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : ∃ (l₁ : List α), ∃ (l₂ : List α), ¬a ∈ l₁ ∧ l = l₁ ++ a :: l₂ ∧ list.erase l a = l₁ ++ l₂ := sorry

@[simp] theorem length_erase_of_mem {α : Type u} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : length (list.erase l a) = Nat.pred (length l) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (length (list.erase l a) = Nat.pred (length l))) (erase_eq_erasep a l)))
    (length_erasep_of_mem h rfl)

theorem erase_append_left {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} (l₂ : List α) (h : a ∈ l₁) : list.erase (l₁ ++ l₂) a = list.erase l₁ a ++ l₂ := sorry

theorem erase_append_right {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} (l₂ : List α) (h : ¬a ∈ l₁) : list.erase (l₁ ++ l₂) a = l₁ ++ list.erase l₂ a := sorry

theorem erase_sublist {α : Type u} [DecidableEq α] (a : α) (l : List α) : list.erase l a <+ l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (list.erase l a <+ l)) (erase_eq_erasep a l))) (erasep_sublist l)

theorem erase_subset {α : Type u} [DecidableEq α] (a : α) (l : List α) : list.erase l a ⊆ l :=
  sublist.subset (erase_sublist a l)

theorem sublist.erase {α : Type u} [DecidableEq α] (a : α) {l₁ : List α} {l₂ : List α} (h : l₁ <+ l₂) : list.erase l₁ a <+ list.erase l₂ a := sorry

theorem mem_of_mem_erase {α : Type u} [DecidableEq α] {a : α} {b : α} {l : List α} : a ∈ list.erase l b → a ∈ l :=
  erase_subset b l

@[simp] theorem mem_erase_of_ne {α : Type u} [DecidableEq α] {a : α} {b : α} {l : List α} (ab : a ≠ b) : a ∈ list.erase l b ↔ a ∈ l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ list.erase l b ↔ a ∈ l)) (erase_eq_erasep b l))) (mem_erasep_of_neg (ne.symm ab))

theorem erase_comm {α : Type u} [DecidableEq α] (a : α) (b : α) (l : List α) : list.erase (list.erase l a) b = list.erase (list.erase l b) a := sorry

theorem map_erase {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] {f : α → β} (finj : function.injective f) {a : α} (l : List α) : map f (list.erase l a) = list.erase (map f l) (f a) := sorry

theorem map_foldl_erase {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] {f : α → β} (finj : function.injective f) {l₁ : List α} {l₂ : List α} : map f (foldl list.erase l₁ l₂) = foldl (fun (l : List β) (a : α) => list.erase l (f a)) (map f l₁) l₂ := sorry

@[simp] theorem count_erase_self {α : Type u} [DecidableEq α] (a : α) (s : List α) : count a (list.erase s a) = Nat.pred (count a s) := sorry

@[simp] theorem count_erase_of_ne {α : Type u} [DecidableEq α] {a : α} {b : α} (ab : a ≠ b) (s : List α) : count a (list.erase s b) = count a s := sorry

/-! ### diff -/

@[simp] theorem diff_nil {α : Type u} [DecidableEq α] (l : List α) : list.diff l [] = l :=
  rfl

@[simp] theorem diff_cons {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) (a : α) : list.diff l₁ (a :: l₂) = list.diff (list.erase l₁ a) l₂ := sorry

theorem diff_cons_right {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) (a : α) : list.diff l₁ (a :: l₂) = list.erase (list.diff l₁ l₂) a := sorry

theorem diff_erase {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) (a : α) : list.erase (list.diff l₁ l₂) a = list.diff (list.erase l₁ a) l₂ := sorry

@[simp] theorem nil_diff {α : Type u} [DecidableEq α] (l : List α) : list.diff [] l = [] := sorry

theorem diff_eq_foldl {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : list.diff l₁ l₂ = foldl list.erase l₁ l₂ := sorry

@[simp] theorem diff_append {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) (l₃ : List α) : list.diff l₁ (l₂ ++ l₃) = list.diff (list.diff l₁ l₂) l₃ := sorry

@[simp] theorem map_diff {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] {f : α → β} (finj : function.injective f) {l₁ : List α} {l₂ : List α} : map f (list.diff l₁ l₂) = list.diff (map f l₁) (map f l₂) := sorry

theorem diff_sublist {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : list.diff l₁ l₂ <+ l₁ := sorry

theorem diff_subset {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : list.diff l₁ l₂ ⊆ l₁ :=
  sublist.subset (diff_sublist l₁ l₂)

theorem mem_diff_of_mem {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} : a ∈ l₁ → ¬a ∈ l₂ → a ∈ list.diff l₁ l₂ := sorry

theorem sublist.diff_right {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} {l₃ : List α} : l₁ <+ l₂ → list.diff l₁ l₃ <+ list.diff l₂ l₃ := sorry

theorem erase_diff_erase_sublist_of_sublist {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → list.diff (list.erase l₂ a) (list.erase l₁ a) <+ list.diff l₂ l₁ := sorry

/-! ### enum -/

theorem length_enum_from {α : Type u} (n : ℕ) (l : List α) : length (enum_from n l) = length l := sorry

theorem length_enum {α : Type u} (l : List α) : length (enum l) = length l :=
  length_enum_from 0

@[simp] theorem enum_from_nth {α : Type u} (n : ℕ) (l : List α) (m : ℕ) : nth (enum_from n l) m = (fun (a : α) => (n + m, a)) <$> nth l m := sorry

@[simp] theorem enum_nth {α : Type u} (l : List α) (n : ℕ) : nth (enum l) n = (fun (a : α) => (n, a)) <$> nth l n := sorry

@[simp] theorem enum_from_map_snd {α : Type u} (n : ℕ) (l : List α) : map prod.snd (enum_from n l) = l := sorry

@[simp] theorem enum_map_snd {α : Type u} (l : List α) : map prod.snd (enum l) = l :=
  enum_from_map_snd 0

theorem mem_enum_from {α : Type u} {x : α} {i : ℕ} {j : ℕ} (xs : List α) : (i, x) ∈ enum_from j xs → j ≤ i ∧ i < j + length xs ∧ x ∈ xs := sorry

/-! ### product -/

@[simp] theorem nil_product {α : Type u} {β : Type v} (l : List β) : product [] l = [] :=
  rfl

@[simp] theorem product_cons {α : Type u} {β : Type v} (a : α) (l₁ : List α) (l₂ : List β) : product (a :: l₁) l₂ = map (fun (b : β) => (a, b)) l₂ ++ product l₁ l₂ :=
  rfl

@[simp] theorem product_nil {α : Type u} {β : Type v} (l : List α) : product l [] = [] := sorry

@[simp] theorem mem_product {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List β} {a : α} {b : β} : (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := sorry

theorem length_product {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) : length (product l₁ l₂) = length l₁ * length l₂ := sorry

/-! ### sigma -/

@[simp] theorem nil_sigma {α : Type u} {σ : α → Type u_1} (l : (a : α) → List (σ a)) : list.sigma [] l = [] :=
  rfl

@[simp] theorem sigma_cons {α : Type u} {σ : α → Type u_1} (a : α) (l₁ : List α) (l₂ : (a : α) → List (σ a)) : list.sigma (a :: l₁) l₂ = map (sigma.mk a) (l₂ a) ++ list.sigma l₁ l₂ :=
  rfl

@[simp] theorem sigma_nil {α : Type u} {σ : α → Type u_1} (l : List α) : (list.sigma l fun (a : α) => []) = [] := sorry

@[simp] theorem mem_sigma {α : Type u} {σ : α → Type u_1} {l₁ : List α} {l₂ : (a : α) → List (σ a)} {a : α} {b : σ a} : sigma.mk a b ∈ list.sigma l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := sorry

theorem length_sigma {α : Type u} {σ : α → Type u_1} (l₁ : List α) (l₂ : (a : α) → List (σ a)) : length (list.sigma l₁ l₂) = sum (map (fun (a : α) => length (l₂ a)) l₁) := sorry

/-! ### disjoint -/

theorem disjoint.symm {α : Type u} {l₁ : List α} {l₂ : List α} (d : disjoint l₁ l₂) : disjoint l₂ l₁ :=
  fun {a : α} (ᾰ : a ∈ l₂) (ᾰ_1 : a ∈ l₁) => idRhs False (d ᾰ_1 ᾰ)

theorem disjoint_comm {α : Type u} {l₁ : List α} {l₂ : List α} : disjoint l₁ l₂ ↔ disjoint l₂ l₁ :=
  { mp := disjoint.symm, mpr := disjoint.symm }

theorem disjoint_left {α : Type u} {l₁ : List α} {l₂ : List α} : disjoint l₁ l₂ ↔ ∀ {a : α}, a ∈ l₁ → ¬a ∈ l₂ :=
  iff.rfl

theorem disjoint_right {α : Type u} {l₁ : List α} {l₂ : List α} : disjoint l₁ l₂ ↔ ∀ {a : α}, a ∈ l₂ → ¬a ∈ l₁ :=
  disjoint_comm

theorem disjoint_iff_ne {α : Type u} {l₁ : List α} {l₂ : List α} : disjoint l₁ l₂ ↔ ∀ (a : α), a ∈ l₁ → ∀ (b : α), b ∈ l₂ → a ≠ b := sorry

theorem disjoint_of_subset_left {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (ss : l₁ ⊆ l) (d : disjoint l l₂) : disjoint l₁ l₂ :=
  fun {a : α} (ᾰ : a ∈ l₁) => idRhs (a ∈ l₂ → False) (d (ss ᾰ))

theorem disjoint_of_subset_right {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (ss : l₂ ⊆ l) (d : disjoint l₁ l) : disjoint l₁ l₂ :=
  fun {a : α} (ᾰ : a ∈ l₁) (ᾰ_1 : a ∈ l₂) => idRhs False (d ᾰ (ss ᾰ_1))

theorem disjoint_of_disjoint_cons_left {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : disjoint (a :: l₁) l₂ → disjoint l₁ l₂ :=
  disjoint_of_subset_left (subset_cons a l₁)

theorem disjoint_of_disjoint_cons_right {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : disjoint l₁ (a :: l₂) → disjoint l₁ l₂ :=
  disjoint_of_subset_right (subset_cons a l₂)

@[simp] theorem disjoint_nil_left {α : Type u} (l : List α) : disjoint [] l :=
  fun {a : α} => idRhs (a ∈ [] → a ∈ l → False) (not.elim (not_mem_nil a))

@[simp] theorem disjoint_nil_right {α : Type u} (l : List α) : disjoint l [] :=
  eq.mpr (id (Eq._oldrec (Eq.refl (disjoint l [])) (propext disjoint_comm))) (disjoint_nil_left l)

@[simp] theorem singleton_disjoint {α : Type u} {l : List α} {a : α} : disjoint [a] l ↔ ¬a ∈ l := sorry

@[simp] theorem disjoint_singleton {α : Type u} {l : List α} {a : α} : disjoint l [a] ↔ ¬a ∈ l := sorry

@[simp] theorem disjoint_append_left {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} : disjoint (l₁ ++ l₂) l ↔ disjoint l₁ l ∧ disjoint l₂ l := sorry

@[simp] theorem disjoint_append_right {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} : disjoint l (l₁ ++ l₂) ↔ disjoint l l₁ ∧ disjoint l l₂ := sorry

@[simp] theorem disjoint_cons_left {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : disjoint (a :: l₁) l₂ ↔ ¬a ∈ l₂ ∧ disjoint l₁ l₂ := sorry

@[simp] theorem disjoint_cons_right {α : Type u} {a : α} {l₁ : List α} {l₂ : List α} : disjoint l₁ (a :: l₂) ↔ ¬a ∈ l₁ ∧ disjoint l₁ l₂ := sorry

theorem disjoint_of_disjoint_append_left_left {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (d : disjoint (l₁ ++ l₂) l) : disjoint l₁ l :=
  and.left (iff.mp disjoint_append_left d)

theorem disjoint_of_disjoint_append_left_right {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (d : disjoint (l₁ ++ l₂) l) : disjoint l₂ l :=
  and.right (iff.mp disjoint_append_left d)

theorem disjoint_of_disjoint_append_right_left {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (d : disjoint l (l₁ ++ l₂)) : disjoint l l₁ :=
  and.left (iff.mp disjoint_append_right d)

theorem disjoint_of_disjoint_append_right_right {α : Type u} {l₁ : List α} {l₂ : List α} {l : List α} (d : disjoint l (l₁ ++ l₂)) : disjoint l l₂ :=
  and.right (iff.mp disjoint_append_right d)

theorem disjoint_take_drop {α : Type u} {l : List α} {m : ℕ} {n : ℕ} (hl : nodup l) (h : m ≤ n) : disjoint (take m l) (drop n l) := sorry

/-! ### union -/

@[simp] theorem nil_union {α : Type u} [DecidableEq α] (l : List α) : [] ∪ l = l :=
  rfl

@[simp] theorem cons_union {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) (a : α) : a :: l₁ ∪ l₂ = insert a (l₁ ∪ l₂) :=
  rfl

@[simp] theorem mem_union {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} {a : α} : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ := sorry

theorem mem_union_left {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} (h : a ∈ l₁) (l₂ : List α) : a ∈ l₁ ∪ l₂ :=
  iff.mpr mem_union (Or.inl h)

theorem mem_union_right {α : Type u} [DecidableEq α] {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
  iff.mpr mem_union (Or.inr h)

theorem sublist_suffix_of_union {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : ∃ (t : List α), t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂ := sorry

theorem suffix_union_right {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : l₂ <:+ l₁ ∪ l₂ :=
  Exists.imp (fun (a : List α) => and.right) (sublist_suffix_of_union l₁ l₂)

theorem union_sublist_append {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : l₁ ∪ l₂ <+ l₁ ++ l₂ := sorry

theorem forall_mem_union {α : Type u} [DecidableEq α] {p : α → Prop} {l₁ : List α} {l₂ : List α} : (∀ (x : α), x ∈ l₁ ∪ l₂ → p x) ↔ (∀ (x : α), x ∈ l₁ → p x) ∧ ∀ (x : α), x ∈ l₂ → p x := sorry

theorem forall_mem_of_forall_mem_union_left {α : Type u} [DecidableEq α] {p : α → Prop} {l₁ : List α} {l₂ : List α} (h : ∀ (x : α), x ∈ l₁ ∪ l₂ → p x) (x : α) (H : x ∈ l₁) : p x :=
  and.left (iff.mp forall_mem_union h)

theorem forall_mem_of_forall_mem_union_right {α : Type u} [DecidableEq α] {p : α → Prop} {l₁ : List α} {l₂ : List α} (h : ∀ (x : α), x ∈ l₁ ∪ l₂ → p x) (x : α) (H : x ∈ l₂) : p x :=
  and.right (iff.mp forall_mem_union h)

/-! ### inter -/

@[simp] theorem inter_nil {α : Type u} [DecidableEq α] (l : List α) : [] ∩ l = [] :=
  rfl

@[simp] theorem inter_cons_of_mem {α : Type u} [DecidableEq α] {a : α} (l₁ : List α) {l₂ : List α} (h : a ∈ l₂) : (a :: l₁) ∩ l₂ = a :: l₁ ∩ l₂ :=
  if_pos h

@[simp] theorem inter_cons_of_not_mem {α : Type u} [DecidableEq α] {a : α} (l₁ : List α) {l₂ : List α} (h : ¬a ∈ l₂) : (a :: l₁) ∩ l₂ = l₁ ∩ l₂ :=
  if_neg h

theorem mem_of_mem_inter_left {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} {a : α} : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
  mem_of_mem_filter

theorem mem_of_mem_inter_right {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} {a : α} : a ∈ l₁ ∩ l₂ → a ∈ l₂ :=
  of_mem_filter

theorem mem_inter_of_mem_of_mem {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} {a : α} : a ∈ l₁ → a ∈ l₂ → a ∈ l₁ ∩ l₂ :=
  mem_filter_of_mem

@[simp] theorem mem_inter {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} : a ∈ l₁ ∩ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ :=
  mem_filter

theorem inter_subset_left {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : l₁ ∩ l₂ ⊆ l₁ :=
  filter_subset l₁

theorem inter_subset_right {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : l₁ ∩ l₂ ⊆ l₂ :=
  fun (a : α) => mem_of_mem_inter_right

theorem subset_inter {α : Type u} [DecidableEq α] {l : List α} {l₁ : List α} {l₂ : List α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ :=
  fun (a : α) (h : a ∈ l) => iff.mpr mem_inter { left := h₁ h, right := h₂ h }

theorem inter_eq_nil_iff_disjoint {α : Type u} [DecidableEq α] {l₁ : List α} {l₂ : List α} : l₁ ∩ l₂ = [] ↔ disjoint l₁ l₂ := sorry

theorem forall_mem_inter_of_forall_left {α : Type u} [DecidableEq α] {p : α → Prop} {l₁ : List α} (h : ∀ (x : α), x ∈ l₁ → p x) (l₂ : List α) (x : α) : x ∈ l₁ ∩ l₂ → p x :=
  ball.imp_left (fun (x : α) => mem_of_mem_inter_left) h

theorem forall_mem_inter_of_forall_right {α : Type u} [DecidableEq α] {p : α → Prop} (l₁ : List α) {l₂ : List α} (h : ∀ (x : α), x ∈ l₂ → p x) (x : α) : x ∈ l₁ ∩ l₂ → p x :=
  ball.imp_left (fun (x : α) => mem_of_mem_inter_right) h

@[simp] theorem inter_reverse {α : Type u} [DecidableEq α] {xs : List α} {ys : List α} : list.inter xs (reverse ys) = list.inter xs ys := sorry

theorem choose_spec {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) (hp : ∃ (a : α), a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  subtype.property (choose_x p l hp)

theorem choose_mem {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) (hp : ∃ (a : α), a ∈ l ∧ p a) : choose p l hp ∈ l :=
  and.left (choose_spec p l hp)

theorem choose_property {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) (hp : ∃ (a : α), a ∈ l ∧ p a) : p (choose p l hp) :=
  and.right (choose_spec p l hp)

/-! ### map₂_left' -/

-- The definitional equalities for `map₂_left'` can already be used by the

-- simplifie because `map₂_left'` is marked `@[simp]`.

@[simp] theorem map₂_left'_nil_right {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β → γ) (as : List α) : map₂_left' f as [] = (map (fun (a : α) => f a none) as, []) :=
  list.cases_on as (Eq.refl (map₂_left' f [] []))
    fun (as_hd : α) (as_tl : List α) => Eq.refl (map₂_left' f (as_hd :: as_tl) [])

/-! ### map₂_right' -/

@[simp] theorem map₂_right'_nil_left {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (bs : List β) : map₂_right' f [] bs = (map (f none) bs, []) :=
  list.cases_on bs (Eq.refl (map₂_right' f [] []))
    fun (bs_hd : β) (bs_tl : List β) => Eq.refl (map₂_right' f [] (bs_hd :: bs_tl))

@[simp] theorem map₂_right'_nil_right {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (as : List α) : map₂_right' f as [] = ([], as) :=
  rfl

@[simp] theorem map₂_right'_nil_cons {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (b : β) (bs : List β) : map₂_right' f [] (b :: bs) = (f none b :: map (f none) bs, []) :=
  rfl

@[simp] theorem map₂_right'_cons_cons {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) : map₂_right' f (a :: as) (b :: bs) =
  let rec : List γ × List α := map₂_right' f as bs;
  (f (some a) b :: prod.fst rec, prod.snd rec) :=
  rfl

/-! ### zip_left' -/

@[simp] theorem zip_left'_nil_right {α : Type u} {β : Type v} (as : List α) : zip_left' as [] = (map (fun (a : α) => (a, none)) as, []) :=
  list.cases_on as (Eq.refl (zip_left' [] [])) fun (as_hd : α) (as_tl : List α) => Eq.refl (zip_left' (as_hd :: as_tl) [])

@[simp] theorem zip_left'_nil_left {α : Type u} {β : Type v} (bs : List β) : zip_left' [] bs = ([], bs) :=
  rfl

@[simp] theorem zip_left'_cons_nil {α : Type u} {β : Type v} (a : α) (as : List α) : zip_left' (a :: as) [] = ((a, none) :: map (fun (a : α) => (a, none)) as, []) :=
  rfl

@[simp] theorem zip_left'_cons_cons {α : Type u} {β : Type v} (a : α) (as : List α) (b : β) (bs : List β) : zip_left' (a :: as) (b :: bs) =
  let rec : List (α × Option β) × List β := zip_left' as bs;
  ((a, some b) :: prod.fst rec, prod.snd rec) :=
  rfl

/-! ### zip_right' -/

@[simp] theorem zip_right'_nil_left {α : Type u} {β : Type v} (bs : List β) : zip_right' [] bs = (map (fun (b : β) => (none, b)) bs, []) :=
  list.cases_on bs (Eq.refl (zip_right' [] []))
    fun (bs_hd : β) (bs_tl : List β) => Eq.refl (zip_right' [] (bs_hd :: bs_tl))

@[simp] theorem zip_right'_nil_right {α : Type u} {β : Type v} (as : List α) : zip_right' as [] = ([], as) :=
  rfl

@[simp] theorem zip_right'_nil_cons {α : Type u} {β : Type v} (b : β) (bs : List β) : zip_right' [] (b :: bs) = ((none, b) :: map (fun (b : β) => (none, b)) bs, []) :=
  rfl

@[simp] theorem zip_right'_cons_cons {α : Type u} {β : Type v} (a : α) (as : List α) (b : β) (bs : List β) : zip_right' (a :: as) (b :: bs) =
  let rec : List (Option α × β) × List α := zip_right' as bs;
  ((some a, b) :: prod.fst rec, prod.snd rec) :=
  rfl

/-! ### map₂_left -/

-- The definitional equalities for `map₂_left` can already be used by the

-- simplifier because `map₂_left` is marked `@[simp]`.

@[simp] theorem map₂_left_nil_right {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β → γ) (as : List α) : map₂_left f as [] = map (fun (a : α) => f a none) as :=
  list.cases_on as (Eq.refl (map₂_left f [] []))
    fun (as_hd : α) (as_tl : List α) => Eq.refl (map₂_left f (as_hd :: as_tl) [])

theorem map₂_left_eq_map₂_left' {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β → γ) (as : List α) (bs : List β) : map₂_left f as bs = prod.fst (map₂_left' f as bs) := sorry

theorem map₂_left_eq_map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β → γ) (as : List α) (bs : List β) : length as ≤ length bs → map₂_left f as bs = map₂ (fun (a : α) (b : β) => f a (some b)) as bs := sorry

/-! ### map₂_right -/

@[simp] theorem map₂_right_nil_left {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (bs : List β) : map₂_right f [] bs = map (f none) bs :=
  list.cases_on bs (Eq.refl (map₂_right f [] []))
    fun (bs_hd : β) (bs_tl : List β) => Eq.refl (map₂_right f [] (bs_hd :: bs_tl))

@[simp] theorem map₂_right_nil_right {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (as : List α) : map₂_right f as [] = [] :=
  rfl

@[simp] theorem map₂_right_nil_cons {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (b : β) (bs : List β) : map₂_right f [] (b :: bs) = f none b :: map (f none) bs :=
  rfl

@[simp] theorem map₂_right_cons_cons {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β) : map₂_right f (a :: as) (b :: bs) = f (some a) b :: map₂_right f as bs :=
  rfl

theorem map₂_right_eq_map₂_right' {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (as : List α) (bs : List β) : map₂_right f as bs = prod.fst (map₂_right' f as bs) := sorry

theorem map₂_right_eq_map₂ {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (as : List α) (bs : List β) (h : length bs ≤ length as) : map₂_right f as bs = map₂ (fun (a : α) (b : β) => f (some a) b) as bs := sorry

/-! ### zip_left -/

@[simp] theorem zip_left_nil_right {α : Type u} {β : Type v} (as : List α) : zip_left as [] = map (fun (a : α) => (a, none)) as :=
  list.cases_on as (Eq.refl (zip_left [] [])) fun (as_hd : α) (as_tl : List α) => Eq.refl (zip_left (as_hd :: as_tl) [])

@[simp] theorem zip_left_nil_left {α : Type u} {β : Type v} (bs : List β) : zip_left [] bs = [] :=
  rfl

@[simp] theorem zip_left_cons_nil {α : Type u} {β : Type v} (a : α) (as : List α) : zip_left (a :: as) [] = (a, none) :: map (fun (a : α) => (a, none)) as :=
  rfl

@[simp] theorem zip_left_cons_cons {α : Type u} {β : Type v} (a : α) (as : List α) (b : β) (bs : List β) : zip_left (a :: as) (b :: bs) = (a, some b) :: zip_left as bs :=
  rfl

theorem zip_left_eq_zip_left' {α : Type u} {β : Type v} (as : List α) (bs : List β) : zip_left as bs = prod.fst (zip_left' as bs) := sorry

/-! ### zip_right -/

@[simp] theorem zip_right_nil_left {α : Type u} {β : Type v} (bs : List β) : zip_right [] bs = map (fun (b : β) => (none, b)) bs :=
  list.cases_on bs (Eq.refl (zip_right [] [])) fun (bs_hd : β) (bs_tl : List β) => Eq.refl (zip_right [] (bs_hd :: bs_tl))

@[simp] theorem zip_right_nil_right {α : Type u} {β : Type v} (as : List α) : zip_right as [] = [] :=
  rfl

@[simp] theorem zip_right_nil_cons {α : Type u} {β : Type v} (b : β) (bs : List β) : zip_right [] (b :: bs) = (none, b) :: map (fun (b : β) => (none, b)) bs :=
  rfl

@[simp] theorem zip_right_cons_cons {α : Type u} {β : Type v} (a : α) (as : List α) (b : β) (bs : List β) : zip_right (a :: as) (b :: bs) = (some a, b) :: zip_right as bs :=
  rfl

theorem zip_right_eq_zip_right' {α : Type u} {β : Type v} (as : List α) (bs : List β) : zip_right as bs = prod.fst (zip_right' as bs) := sorry

/-! ### Miscellaneous lemmas -/

theorem ilast'_mem {α : Type u} (a : α) (l : List α) : ilast' a l ∈ a :: l := sorry

@[simp] theorem nth_le_attach {α : Type u} (L : List α) (i : ℕ) (H : i < length (attach L)) : subtype.val (nth_le (attach L) i H) = nth_le L i (length_attach L ▸ H) := sorry

end list


theorem monoid_hom.map_list_prod {α : Type u_1} {β : Type u_2} [monoid α] [monoid β] (f : α →* β) (l : List α) : coe_fn f (list.prod l) = list.prod (list.map (⇑f) l) :=
  Eq.symm (list.prod_hom l f)

namespace list


theorem sum_map_hom {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_monoid β] [add_monoid γ] (L : List α) (f : α → β) (g : β →+ γ) : sum (map (⇑g ∘ f) L) = coe_fn g (sum (map f L)) := sorry

theorem sum_map_mul_left {α : Type u_1} [semiring α] {β : Type u_2} (L : List β) (f : β → α) (r : α) : sum (map (fun (b : β) => r * f b) L) = r * sum (map f L) :=
  sum_map_hom L f (add_monoid_hom.mul_left r)

theorem sum_map_mul_right {α : Type u_1} [semiring α] {β : Type u_2} (L : List β) (f : β → α) (r : α) : sum (map (fun (b : β) => f b * r) L) = sum (map f L) * r :=
  sum_map_hom L f (add_monoid_hom.mul_right r)

@[simp] theorem mem_map_swap {α : Type u} {β : Type v} (x : α) (y : β) (xs : List (α × β)) : (y, x) ∈ map prod.swap xs ↔ (x, y) ∈ xs := sorry

theorem slice_eq {α : Type u_1} (xs : List α) (n : ℕ) (m : ℕ) : slice n m xs = take n xs ++ drop (n + m) xs := sorry

theorem sizeof_slice_lt {α : Type u_1} [SizeOf α] (i : ℕ) (j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < length xs) : sizeof (slice i j xs) < sizeof xs := sorry

