/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.sigma
import Mathlib.PostPort

universes u v l w 

namespace Mathlib

/-!
# Association lists
-/

/-- `alist β` is a key-value map stored as a `list` (i.e. a linked list).
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure alist {α : Type u} (β : α → Type v) where
  entries : List (sigma β)
  nodupkeys : list.nodupkeys entries

/-- Given `l : list (sigma β)`, create a term of type `alist β` by removing
entries with duplicate keys. -/
def list.to_alist {α : Type u} [DecidableEq α] {β : α → Type v} (l : List (sigma β)) : alist β :=
  alist.mk (list.erase_dupkeys l) sorry

namespace alist


theorem ext {α : Type u} {β : α → Type v} {s : alist β} {t : alist β} :
    entries s = entries t → s = t :=
  sorry

theorem ext_iff {α : Type u} {β : α → Type v} {s : alist β} {t : alist β} :
    s = t ↔ entries s = entries t :=
  { mp := congr_arg fun {s : alist β} => entries s, mpr := ext }

protected instance decidable_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    [(a : α) → DecidableEq (β a)] : DecidableEq (alist β) :=
  fun (xs ys : alist β) => eq.mpr sorry (list.decidable_eq (entries xs) (entries ys))

/-! ### keys -/

/-- The list of keys of an association list. -/
def keys {α : Type u} {β : α → Type v} (s : alist β) : List α := list.keys (entries s)

theorem keys_nodup {α : Type u} {β : α → Type v} (s : alist β) : list.nodup (keys s) := nodupkeys s

/-! ### mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
protected instance has_mem {α : Type u} {β : α → Type v} : has_mem α (alist β) :=
  has_mem.mk fun (a : α) (s : alist β) => a ∈ keys s

theorem mem_keys {α : Type u} {β : α → Type v} {a : α} {s : alist β} : a ∈ s ↔ a ∈ keys s := iff.rfl

theorem mem_of_perm {α : Type u} {β : α → Type v} {a : α} {s₁ : alist β} {s₂ : alist β}
    (p : entries s₁ ~ entries s₂) : a ∈ s₁ ↔ a ∈ s₂ :=
  list.perm.mem_iff (list.perm.map sigma.fst p)

/-! ### empty -/

/-- The empty association list. -/
protected instance has_emptyc {α : Type u} {β : α → Type v} : has_emptyc (alist β) :=
  has_emptyc.mk (mk [] list.nodupkeys_nil)

protected instance inhabited {α : Type u} {β : α → Type v} : Inhabited (alist β) := { default := ∅ }

theorem not_mem_empty {α : Type u} {β : α → Type v} (a : α) : ¬a ∈ ∅ := list.not_mem_nil a

@[simp] theorem empty_entries {α : Type u} {β : α → Type v} : entries ∅ = [] := rfl

@[simp] theorem keys_empty {α : Type u} {β : α → Type v} : keys ∅ = [] := rfl

/-! ### singleton -/

/-- The singleton association list. -/
def singleton {α : Type u} {β : α → Type v} (a : α) (b : β a) : alist β := mk [sigma.mk a b] sorry

@[simp] theorem singleton_entries {α : Type u} {β : α → Type v} (a : α) (b : β a) :
    entries (singleton a b) = [sigma.mk a b] :=
  rfl

@[simp] theorem keys_singleton {α : Type u} {β : α → Type v} (a : α) (b : β a) :
    keys (singleton a b) = [a] :=
  rfl

/-! ### lookup -/

/-- Look up the value associated to a key in an association list. -/
def lookup {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) : Option (β a) :=
  list.lookup a (entries s)

@[simp] theorem lookup_empty {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) :
    lookup a ∅ = none :=
  rfl

theorem lookup_is_some {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : alist β} :
    ↥(option.is_some (lookup a s)) ↔ a ∈ s :=
  list.lookup_is_some

theorem lookup_eq_none {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : alist β} :
    lookup a s = none ↔ ¬a ∈ s :=
  list.lookup_eq_none

theorem perm_lookup {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : alist β}
    {s₂ : alist β} (p : entries s₁ ~ entries s₂) : lookup a s₁ = lookup a s₂ :=
  list.perm_lookup a (nodupkeys s₁) (nodupkeys s₂) p

protected instance has_mem.mem.decidable {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (s : alist β) : Decidable (a ∈ s) :=
  decidable_of_iff ↥(option.is_some (lookup a s)) sorry

/-! ### replace -/

/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : alist β) :
    alist β :=
  mk (list.kreplace a b (entries s)) sorry

@[simp] theorem keys_replace {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a)
    (s : alist β) : keys (replace a b s) = keys s :=
  list.keys_kreplace a b (entries s)

@[simp] theorem mem_replace {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b : β a}
    {s : alist β} : a' ∈ replace a b s ↔ a' ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a' ∈ replace a b s ↔ a' ∈ s)) (propext mem_keys)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a' ∈ keys (replace a b s) ↔ a' ∈ s)) (keys_replace a b s)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a' ∈ keys s ↔ a' ∈ s)) (Eq.symm (propext mem_keys))))
        (iff.refl (a' ∈ s))))

theorem perm_replace {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s₁ : alist β}
    {s₂ : alist β} :
    entries s₁ ~ entries s₂ → entries (replace a b s₁) ~ entries (replace a b s₂) :=
  list.perm.kreplace (nodupkeys s₁)

/-- Fold a function over the key-value pairs in the map. -/
def foldl {α : Type u} {β : α → Type v} {δ : Type w} (f : δ → (a : α) → β a → δ) (d : δ)
    (m : alist β) : δ :=
  list.foldl (fun (r : δ) (a : sigma β) => f r (sigma.fst a) (sigma.snd a)) d (entries m)

/-! ### erase -/

/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) : alist β :=
  mk (list.kerase a (entries s)) sorry

@[simp] theorem keys_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) :
    keys (erase a s) = list.erase (keys s) a :=
  sorry

@[simp] theorem mem_erase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α}
    {s : alist β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
  sorry

theorem perm_erase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : alist β}
    {s₂ : alist β} : entries s₁ ~ entries s₂ → entries (erase a s₁) ~ entries (erase a s₂) :=
  list.perm.kerase (nodupkeys s₁)

@[simp] theorem lookup_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) :
    lookup a (erase a s) = none :=
  list.lookup_kerase a (nodupkeys s)

@[simp] theorem lookup_erase_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α}
    {s : alist β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  list.lookup_kerase_ne h

theorem erase_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (a' : α) (s : alist β) :
    erase a' (erase a s) = erase a (erase a' s) :=
  ext list.kerase_kerase

/-! ### insert -/

/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : alist β) :
    alist β :=
  mk (list.kinsert a b (entries s)) sorry

@[simp] theorem insert_entries {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {s : alist β} : entries (insert a b s) = sigma.mk a b :: list.kerase a (entries s) :=
  rfl

theorem insert_entries_of_neg {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {s : alist β} (h : ¬a ∈ s) : entries (insert a b s) = sigma.mk a b :: entries s :=
  sorry

@[simp] theorem mem_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α}
    {b' : β a'} (s : alist β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  list.mem_keys_kinsert

@[simp] theorem keys_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    (s : alist β) : keys (insert a b s) = a :: list.erase (keys s) a :=
  sorry

theorem perm_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s₁ : alist β}
    {s₂ : alist β} (p : entries s₁ ~ entries s₂) :
    entries (insert a b s₁) ~ entries (insert a b s₂) :=
  sorry

@[simp] theorem lookup_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    (s : alist β) : lookup a (insert a b s) = some b :=
  sorry

@[simp] theorem lookup_insert_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α}
    {b' : β a'} {s : alist β} (h : a ≠ a') : lookup a (insert a' b' s) = lookup a s :=
  list.lookup_kinsert_ne h

@[simp] theorem lookup_to_alist {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    (s : List (sigma β)) : lookup a (list.to_alist s) = list.lookup a s :=
  sorry

@[simp] theorem insert_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {b' : β a} (s : alist β) : insert a b' (insert a b s) = insert a b' s :=
  sorry

theorem insert_insert_of_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b : β a}
    {b' : β a'} (s : alist β) (h : a ≠ a') :
    entries (insert a' b' (insert a b s)) ~ entries (insert a b (insert a' b' s)) :=
  sorry

@[simp] theorem insert_singleton_eq {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {b' : β a} : insert a b (singleton a b') = singleton a b :=
  sorry

@[simp] theorem entries_to_alist {α : Type u} {β : α → Type v} [DecidableEq α]
    (xs : List (sigma β)) : entries (list.to_alist xs) = list.erase_dupkeys xs :=
  rfl

theorem to_alist_cons {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a)
    (xs : List (sigma β)) : list.to_alist (sigma.mk a b :: xs) = insert a b (list.to_alist xs) :=
  rfl

/-! ### extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) :
    Option (β a) × alist β :=
  (fun (this : list.nodupkeys (prod.snd (list.kextract a (entries s)))) => sorry) sorry

@[simp] theorem extract_eq_lookup_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (s : alist β) : extract a s = (lookup a s, erase a s) :=
  sorry

/-! ### union -/

/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union {α : Type u} {β : α → Type v} [DecidableEq α] (s₁ : alist β) (s₂ : alist β) : alist β :=
  mk (list.kunion (entries s₁) (entries s₂)) sorry

protected instance has_union {α : Type u} {β : α → Type v} [DecidableEq α] : has_union (alist β) :=
  has_union.mk union

@[simp] theorem union_entries {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : alist β}
    {s₂ : alist β} : entries (s₁ ∪ s₂) = list.kunion (entries s₁) (entries s₂) :=
  rfl

@[simp] theorem empty_union {α : Type u} {β : α → Type v} [DecidableEq α] {s : alist β} :
    ∅ ∪ s = s :=
  ext rfl

@[simp] theorem union_empty {α : Type u} {β : α → Type v} [DecidableEq α] {s : alist β} :
    s ∪ ∅ = s :=
  sorry

@[simp] theorem mem_union {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : alist β}
    {s₂ : alist β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  list.mem_keys_kunion

theorem perm_union {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : alist β} {s₂ : alist β}
    {s₃ : alist β} {s₄ : alist β} (p₁₂ : entries s₁ ~ entries s₂) (p₃₄ : entries s₃ ~ entries s₄) :
    entries (s₁ ∪ s₃) ~ entries (s₂ ∪ s₄) :=
  sorry

theorem union_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s₁ : alist β)
    (s₂ : alist β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext (Eq.symm list.kunion_kerase)

@[simp] theorem lookup_union_left {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {s₁ : alist β} {s₂ : alist β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  list.lookup_kunion_left

@[simp] theorem lookup_union_right {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {s₁ : alist β} {s₂ : alist β} : ¬a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  list.lookup_kunion_right

@[simp] theorem mem_lookup_union {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {s₁ : alist β} {s₂ : alist β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ ¬a ∈ s₁ ∧ b ∈ lookup a s₂ :=
  list.mem_lookup_kunion

theorem mem_lookup_union_middle {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {s₁ : alist β} {s₂ : alist β} {s₃ : alist β} :
    b ∈ lookup a (s₁ ∪ s₃) → ¬a ∈ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  list.mem_lookup_kunion_middle

theorem insert_union {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s₁ : alist β}
    {s₂ : alist β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
  sorry

theorem union_assoc {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : alist β} {s₂ : alist β}
    {s₃ : alist β} : entries (s₁ ∪ s₂ ∪ s₃) ~ entries (s₁ ∪ (s₂ ∪ s₃)) :=
  sorry

/-! ### disjoint -/

/-- Two associative lists are disjoint if they have no common keys. -/
def disjoint {α : Type u} {β : α → Type v} (s₁ : alist β) (s₂ : alist β) :=
  ∀ (k : α), k ∈ keys s₁ → ¬k ∈ keys s₂

theorem union_comm_of_disjoint {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : alist β}
    {s₂ : alist β} (h : disjoint s₁ s₂) : entries (s₁ ∪ s₂) ~ entries (s₂ ∪ s₁) :=
  sorry

end Mathlib