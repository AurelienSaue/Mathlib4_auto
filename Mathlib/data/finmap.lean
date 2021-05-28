/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.alist
import Mathlib.data.finset.basic
import Mathlib.data.pfun
import Mathlib.PostPort

universes u v l u_1 w 

namespace Mathlib

/-!
# Finite maps over `multiset`
-/

/-! ### multisets of sigma types-/

namespace multiset


/-- Multiset of keys of an association multiset. -/
def keys {α : Type u} {β : α → Type v} (s : multiset (sigma β)) : multiset α :=
  map sigma.fst s

@[simp] theorem coe_keys {α : Type u} {β : α → Type v} {l : List (sigma β)} : keys ↑l = ↑(list.keys l) :=
  rfl

/-- `nodupkeys s` means that `s` has no duplicate keys. -/
def nodupkeys {α : Type u} {β : α → Type v} (s : multiset (sigma β))  :=
  quot.lift_on s list.nodupkeys sorry

@[simp] theorem coe_nodupkeys {α : Type u} {β : α → Type v} {l : List (sigma β)} : nodupkeys ↑l ↔ list.nodupkeys l :=
  iff.rfl

end multiset


/-! ### finmap -/

/-- `finmap β` is the type of finite maps over a multiset. It is effectively
  a quotient of `alist β` by permutation of the underlying list. -/
structure finmap {α : Type u} (β : α → Type v) 
where
  entries : multiset (sigma β)
  nodupkeys : multiset.nodupkeys entries

/-- The quotient map from `alist` to `finmap`. -/
def alist.to_finmap {α : Type u} {β : α → Type v} (s : alist β) : finmap β :=
  finmap.mk (↑(alist.entries s)) (alist.nodupkeys s)

theorem alist.to_finmap_eq {α : Type u} {β : α → Type v} {s₁ : alist β} {s₂ : alist β} : alist.to_finmap s₁ = alist.to_finmap s₂ ↔ alist.entries s₁ ~ alist.entries s₂ := sorry

@[simp] theorem alist.to_finmap_entries {α : Type u} {β : α → Type v} (s : alist β) : finmap.entries (alist.to_finmap s) = ↑(alist.entries s) :=
  rfl

/-- Given `l : list (sigma β)`, create a term of type `finmap β` by removing
entries with duplicate keys. -/
def list.to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (s : List (sigma β)) : finmap β :=
  alist.to_finmap (list.to_alist s)

namespace finmap


/-! ### lifting from alist -/

/-- Lift a permutation-respecting function on `alist` to `finmap`. -/
def lift_on {α : Type u} {β : α → Type v} {γ : Type u_1} (s : finmap β) (f : alist β → γ) (H : ∀ (a b : alist β), alist.entries a ~ alist.entries b → f a = f b) : γ :=
  roption.get
    (quotient.lift_on (entries s)
      (fun (l : List (sigma β)) => roption.mk (list.nodupkeys l) fun (nd : list.nodupkeys l) => f (alist.mk l nd)) sorry)
    sorry

@[simp] theorem lift_on_to_finmap {α : Type u} {β : α → Type v} {γ : Type u_1} (s : alist β) (f : alist β → γ) (H : ∀ (a b : alist β), alist.entries a ~ alist.entries b → f a = f b) : lift_on (alist.to_finmap s) f H = f s :=
  alist.cases_on s
    fun (s_entries : List (sigma β)) (s_nodupkeys : list.nodupkeys s_entries) =>
      Eq.refl (lift_on (alist.to_finmap (alist.mk s_entries s_nodupkeys)) f H)

/-- Lift a permutation-respecting function on 2 `alist`s to 2 `finmap`s. -/
def lift_on₂ {α : Type u} {β : α → Type v} {γ : Type u_1} (s₁ : finmap β) (s₂ : finmap β) (f : alist β → alist β → γ) (H : ∀ (a₁ b₁ a₂ b₂ : alist β), alist.entries a₁ ~ alist.entries a₂ → alist.entries b₁ ~ alist.entries b₂ → f a₁ b₁ = f a₂ b₂) : γ :=
  lift_on s₁ (fun (l₁ : alist β) => lift_on s₂ (f l₁) sorry) sorry

@[simp] theorem lift_on₂_to_finmap {α : Type u} {β : α → Type v} {γ : Type u_1} (s₁ : alist β) (s₂ : alist β) (f : alist β → alist β → γ) (H : ∀ (a₁ b₁ a₂ b₂ : alist β), alist.entries a₁ ~ alist.entries a₂ → alist.entries b₁ ~ alist.entries b₂ → f a₁ b₁ = f a₂ b₂) : lift_on₂ (alist.to_finmap s₁) (alist.to_finmap s₂) f H = f s₁ s₂ := sorry

/-! ### induction -/

theorem induction_on {α : Type u} {β : α → Type v} {C : finmap β → Prop} (s : finmap β) (H : ∀ (a : alist β), C (alist.to_finmap a)) : C s := sorry

theorem induction_on₂ {α : Type u} {β : α → Type v} {C : finmap β → finmap β → Prop} (s₁ : finmap β) (s₂ : finmap β) (H : ∀ (a₁ a₂ : alist β), C (alist.to_finmap a₁) (alist.to_finmap a₂)) : C s₁ s₂ :=
  induction_on s₁ fun (l₁ : alist β) => induction_on s₂ fun (l₂ : alist β) => H l₁ l₂

theorem induction_on₃ {α : Type u} {β : α → Type v} {C : finmap β → finmap β → finmap β → Prop} (s₁ : finmap β) (s₂ : finmap β) (s₃ : finmap β) (H : ∀ (a₁ a₂ a₃ : alist β), C (alist.to_finmap a₁) (alist.to_finmap a₂) (alist.to_finmap a₃)) : C s₁ s₂ s₃ :=
  induction_on₂ s₁ s₂ fun (l₁ l₂ : alist β) => induction_on s₃ fun (l₃ : alist β) => H l₁ l₂ l₃

/-! ### extensionality -/

theorem ext {α : Type u} {β : α → Type v} {s : finmap β} {t : finmap β} : entries s = entries t → s = t := sorry

@[simp] theorem ext_iff {α : Type u} {β : α → Type v} {s : finmap β} {t : finmap β} : entries s = entries t ↔ s = t :=
  { mp := ext, mpr := congr_arg fun {s : finmap β} => entries s }

/-! ### mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
protected instance has_mem {α : Type u} {β : α → Type v} : has_mem α (finmap β) :=
  has_mem.mk fun (a : α) (s : finmap β) => a ∈ multiset.keys (entries s)

theorem mem_def {α : Type u} {β : α → Type v} {a : α} {s : finmap β} : a ∈ s ↔ a ∈ multiset.keys (entries s) :=
  iff.rfl

@[simp] theorem mem_to_finmap {α : Type u} {β : α → Type v} {a : α} {s : alist β} : a ∈ alist.to_finmap s ↔ a ∈ s :=
  iff.rfl

/-! ### keys -/

/-- The set of keys of a finite map. -/
def keys {α : Type u} {β : α → Type v} (s : finmap β) : finset α :=
  finset.mk (multiset.keys (entries s)) sorry

@[simp] theorem keys_val {α : Type u} {β : α → Type v} (s : alist β) : finset.val (keys (alist.to_finmap s)) = ↑(alist.keys s) :=
  rfl

@[simp] theorem keys_ext {α : Type u} {β : α → Type v} {s₁ : alist β} {s₂ : alist β} : keys (alist.to_finmap s₁) = keys (alist.to_finmap s₂) ↔ alist.keys s₁ ~ alist.keys s₂ := sorry

theorem mem_keys {α : Type u} {β : α → Type v} {a : α} {s : finmap β} : a ∈ keys s ↔ a ∈ s :=
  induction_on s fun (s : alist β) => alist.mem_keys

/-! ### empty -/

/-- The empty map. -/
protected instance has_emptyc {α : Type u} {β : α → Type v} : has_emptyc (finmap β) :=
  has_emptyc.mk (mk 0 list.nodupkeys_nil)

protected instance inhabited {α : Type u} {β : α → Type v} : Inhabited (finmap β) :=
  { default := ∅ }

@[simp] theorem empty_to_finmap {α : Type u} {β : α → Type v} : alist.to_finmap ∅ = ∅ :=
  rfl

@[simp] theorem to_finmap_nil {α : Type u} {β : α → Type v} [DecidableEq α] : list.to_finmap [] = ∅ :=
  rfl

theorem not_mem_empty {α : Type u} {β : α → Type v} {a : α} : ¬a ∈ ∅ :=
  multiset.not_mem_zero a

@[simp] theorem keys_empty {α : Type u} {β : α → Type v} : keys ∅ = ∅ :=
  rfl

/-! ### singleton -/

/-- The singleton map. -/
def singleton {α : Type u} {β : α → Type v} (a : α) (b : β a) : finmap β :=
  alist.to_finmap (alist.singleton a b)

@[simp] theorem keys_singleton {α : Type u} {β : α → Type v} (a : α) (b : β a) : keys (singleton a b) = singleton a :=
  rfl

@[simp] theorem mem_singleton {α : Type u} {β : α → Type v} (x : α) (y : α) (b : β y) : x ∈ singleton y b ↔ x = y := sorry

protected instance has_decidable_eq {α : Type u} {β : α → Type v} [DecidableEq α] [(a : α) → DecidableEq (β a)] : DecidableEq (finmap β) :=
  sorry

/-! ### lookup -/

/-- Look up the value associated to a key in a map. -/
def lookup {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : Option (β a) :=
  lift_on s (alist.lookup a) sorry

@[simp] theorem lookup_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) : lookup a (alist.to_finmap s) = alist.lookup a s :=
  rfl

@[simp] theorem lookup_list_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : List (sigma β)) : lookup a (list.to_finmap s) = list.lookup a s := sorry

@[simp] theorem lookup_empty {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) : lookup a ∅ = none :=
  rfl

theorem lookup_is_some {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : finmap β} : ↥(option.is_some (lookup a s)) ↔ a ∈ s :=
  induction_on s fun (s : alist β) => alist.lookup_is_some

theorem lookup_eq_none {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : finmap β} : lookup a s = none ↔ ¬a ∈ s :=
  induction_on s fun (s : alist β) => alist.lookup_eq_none

@[simp] theorem lookup_singleton_eq {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} : lookup a (singleton a b) = some b := sorry

protected instance has_mem.mem.decidable {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : Decidable (a ∈ s) :=
  decidable_of_iff ↥(option.is_some (lookup a s)) sorry

theorem mem_iff {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : finmap β} : a ∈ s ↔ ∃ (b : β a), lookup a s = some b :=
  induction_on s
    fun (s : alist β) =>
      iff.trans list.mem_keys (exists_congr fun (b : β a) => iff.symm (list.mem_lookup_iff (alist.nodupkeys s)))

theorem mem_of_lookup_eq_some {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s : finmap β} (h : lookup a s = some b) : a ∈ s :=
  iff.mpr mem_iff (Exists.intro b h)

theorem ext_lookup {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} {s₂ : finmap β} : (∀ (x : α), lookup x s₁ = lookup x s₂) → s₁ = s₂ := sorry

/-! ### replace -/

/-- Replace a key with a given value in a finite map.
  If the key is not present it does nothing. -/
def replace {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : finmap β) : finmap β :=
  lift_on s (fun (t : alist β) => alist.to_finmap (alist.replace a b t)) sorry

@[simp] theorem replace_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : alist β) : replace a b (alist.to_finmap s) = alist.to_finmap (alist.replace a b s) := sorry

@[simp] theorem keys_replace {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : finmap β) : keys (replace a b s) = keys s := sorry

@[simp] theorem mem_replace {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b : β a} {s : finmap β} : a' ∈ replace a b s ↔ a' ∈ s := sorry

/-! ### foldl -/

/-- Fold a commutative function over the key-value pairs in the map -/
def foldl {α : Type u} {β : α → Type v} {δ : Type w} (f : δ → (a : α) → β a → δ) (H : ∀ (d : δ) (a₁ : α) (b₁ : β a₁) (a₂ : α) (b₂ : β a₂), f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁) (d : δ) (m : finmap β) : δ :=
  multiset.foldl (fun (d : δ) (s : sigma β) => f d (sigma.fst s) (sigma.snd s)) sorry d (entries m)

/-- `any f s` returns `tt` iff there exists a value `v` in `s` such that `f v = tt`. -/
def any {α : Type u} {β : α → Type v} (f : (x : α) → β x → Bool) (s : finmap β) : Bool :=
  foldl (fun (x : Bool) (y : α) (z : β y) => to_bool (↥x ∨ ↥(f y z))) sorry false s

/-- `all f s` returns `tt` iff `f v = tt` for all values `v` in `s`. -/
def all {α : Type u} {β : α → Type v} (f : (x : α) → β x → Bool) (s : finmap β) : Bool :=
  foldl (fun (x : Bool) (y : α) (z : β y) => to_bool (↥x ∧ ↥(f y z))) sorry false s

/-! ### erase -/

/-- Erase a key from the map. If the key is not present it does nothing. -/
def erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : finmap β :=
  lift_on s (fun (t : alist β) => alist.to_finmap (alist.erase a t)) sorry

@[simp] theorem erase_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) : erase a (alist.to_finmap s) = alist.to_finmap (alist.erase a s) := sorry

@[simp] theorem keys_erase_to_finset {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : alist β) : keys (alist.to_finmap (alist.erase a s)) = finset.erase (keys (alist.to_finmap s)) a := sorry

@[simp] theorem keys_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : keys (erase a s) = finset.erase (keys s) a := sorry

@[simp] theorem mem_erase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {s : finmap β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := sorry

theorem not_mem_erase_self {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : finmap β} : ¬a ∈ erase a s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬a ∈ erase a s)) (propext mem_erase)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬(a ≠ a ∧ a ∈ s))) (propext not_and_distrib)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬a ≠ a ∨ ¬a ∈ s)) (propext not_not))) (Or.inl (Eq.refl a))))

@[simp] theorem lookup_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : lookup a (erase a s) = none :=
  induction_on s (alist.lookup_erase a)

@[simp] theorem lookup_erase_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {s : finmap β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  induction_on s fun (s : alist β) => alist.lookup_erase_ne h

theorem erase_erase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {s : finmap β} : erase a (erase a' s) = erase a' (erase a s) := sorry

/-! ### sdiff -/

/-- `sdiff s s'` consists of all key-value pairs from `s` and `s'` where the keys are in `s` or
`s'` but not both. -/
def sdiff {α : Type u} {β : α → Type v} [DecidableEq α] (s : finmap β) (s' : finmap β) : finmap β :=
  foldl (fun (s : finmap β) (x : α) (_x : β x) => erase x s) sorry s s'

protected instance has_sdiff {α : Type u} {β : α → Type v} [DecidableEq α] : has_sdiff (finmap β) :=
  has_sdiff.mk sdiff

/-! ### insert -/

/-- Insert a key-value pair into a finite map, replacing any existing pair with
  the same key. -/
def insert {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : finmap β) : finmap β :=
  lift_on s (fun (t : alist β) => alist.to_finmap (alist.insert a b t)) sorry

@[simp] theorem insert_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : alist β) : insert a b (alist.to_finmap s) = alist.to_finmap (alist.insert a b s) := sorry

theorem insert_entries_of_neg {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s : finmap β} : ¬a ∈ s → entries (insert a b s) = sigma.mk a b ::ₘ entries s := sorry

@[simp] theorem mem_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b' : β a'} {s : finmap β} : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  induction_on s alist.mem_insert

@[simp] theorem lookup_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} (s : finmap β) : lookup a (insert a b s) = some b := sorry

@[simp] theorem lookup_insert_of_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b : β a} (s : finmap β) (h : a' ≠ a) : lookup a' (insert a b s) = lookup a' s := sorry

@[simp] theorem insert_insert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {b' : β a} (s : finmap β) : insert a b' (insert a b s) = insert a b' s := sorry

theorem insert_insert_of_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b : β a} {b' : β a'} (s : finmap β) (h : a ≠ a') : insert a' b' (insert a b s) = insert a b (insert a' b' s) := sorry

theorem to_finmap_cons {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (xs : List (sigma β)) : list.to_finmap (sigma.mk a b :: xs) = insert a b (list.to_finmap xs) :=
  rfl

theorem mem_list_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (xs : List (sigma β)) : a ∈ list.to_finmap xs ↔ ∃ (b : β a), sigma.mk a b ∈ xs := sorry

@[simp] theorem insert_singleton_eq {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {b' : β a} : insert a b (singleton a b') = singleton a b := sorry

/-! ### extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : Option (β a) × finmap β :=
  lift_on s (fun (t : alist β) => prod.map id alist.to_finmap (alist.extract a t)) sorry

@[simp] theorem extract_eq_lookup_erase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (s : finmap β) : extract a s = (lookup a s, erase a s) := sorry

/-! ### union -/

/-- `s₁ ∪ s₂` is the key-based union of two finite maps. It is left-biased: if
there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`. -/
def union {α : Type u} {β : α → Type v} [DecidableEq α] (s₁ : finmap β) (s₂ : finmap β) : finmap β :=
  lift_on₂ s₁ s₂ (fun (s₁ s₂ : alist β) => alist.to_finmap (s₁ ∪ s₂)) sorry

protected instance has_union {α : Type u} {β : α → Type v} [DecidableEq α] : has_union (finmap β) :=
  has_union.mk union

@[simp] theorem mem_union {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : finmap β} {s₂ : finmap β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  induction_on₂ s₁ s₂ fun (_x _x_1 : alist β) => alist.mem_union

@[simp] theorem union_to_finmap {α : Type u} {β : α → Type v} [DecidableEq α] (s₁ : alist β) (s₂ : alist β) : alist.to_finmap s₁ ∪ alist.to_finmap s₂ = alist.to_finmap (s₁ ∪ s₂) := sorry

theorem keys_union {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} {s₂ : finmap β} : keys (s₁ ∪ s₂) = keys s₁ ∪ keys s₂ := sorry

@[simp] theorem lookup_union_left {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : finmap β} {s₂ : finmap β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  induction_on₂ s₁ s₂ fun (s₁ s₂ : alist β) => alist.lookup_union_left

@[simp] theorem lookup_union_right {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : finmap β} {s₂ : finmap β} : ¬a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  induction_on₂ s₁ s₂ fun (s₁ s₂ : alist β) => alist.lookup_union_right

theorem lookup_union_left_of_not_in {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s₁ : finmap β} {s₂ : finmap β} (h : ¬a ∈ s₂) : lookup a (s₁ ∪ s₂) = lookup a s₁ := sorry

@[simp] theorem mem_lookup_union {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s₁ : finmap β} {s₂ : finmap β} : b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ ¬a ∈ s₁ ∧ b ∈ lookup a s₂ :=
  induction_on₂ s₁ s₂ fun (s₁ s₂ : alist β) => alist.mem_lookup_union

theorem mem_lookup_union_middle {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s₁ : finmap β} {s₂ : finmap β} {s₃ : finmap β} : b ∈ lookup a (s₁ ∪ s₃) → ¬a ∈ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  induction_on₃ s₁ s₂ s₃ fun (s₁ s₂ s₃ : alist β) => alist.mem_lookup_union_middle

theorem insert_union {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a} {s₁ : finmap β} {s₂ : finmap β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ := sorry

theorem union_assoc {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} {s₂ : finmap β} {s₃ : finmap β} : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sorry

@[simp] theorem empty_union {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} : ∅ ∪ s₁ = s₁ := sorry

@[simp] theorem union_empty {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} : s₁ ∪ ∅ = s₁ := sorry

theorem erase_union_singleton {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (s : finmap β) (h : lookup a s = some b) : erase a s ∪ singleton a b = s := sorry

/-! ### disjoint -/

/-- `disjoint s₁ s₂` holds if `s₁` and `s₂` have no keys in common. -/
def disjoint {α : Type u} {β : α → Type v} (s₁ : finmap β) (s₂ : finmap β)  :=
  ∀ (x : α), x ∈ s₁ → ¬x ∈ s₂

theorem disjoint_empty {α : Type u} {β : α → Type v} (x : finmap β) : disjoint ∅ x :=
  fun (x_1 : α) (H : x_1 ∈ ∅) (ᾰ : x_1 ∈ x) => false.dcases_on (fun (H : x_1 ∈ ∅) => False) H

theorem disjoint.symm {α : Type u} {β : α → Type v} (x : finmap β) (y : finmap β) (h : disjoint x y) : disjoint y x :=
  fun (p : α) (hy : p ∈ y) (hx : p ∈ x) => h p hx hy

theorem disjoint.symm_iff {α : Type u} {β : α → Type v} (x : finmap β) (y : finmap β) : disjoint x y ↔ disjoint y x :=
  { mp := disjoint.symm x y, mpr := disjoint.symm y x }

protected instance disjoint.decidable_rel {α : Type u} {β : α → Type v} [DecidableEq α] : DecidableRel disjoint :=
  fun (x y : finmap β) => id multiset.decidable_dforall_multiset

theorem disjoint_union_left {α : Type u} {β : α → Type v} [DecidableEq α] (x : finmap β) (y : finmap β) (z : finmap β) : disjoint (x ∪ y) z ↔ disjoint x z ∧ disjoint y z := sorry

theorem disjoint_union_right {α : Type u} {β : α → Type v} [DecidableEq α] (x : finmap β) (y : finmap β) (z : finmap β) : disjoint x (y ∪ z) ↔ disjoint x y ∧ disjoint x z := sorry

theorem union_comm_of_disjoint {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} {s₂ : finmap β} : disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ := sorry

theorem union_cancel {α : Type u} {β : α → Type v} [DecidableEq α] {s₁ : finmap β} {s₂ : finmap β} {s₃ : finmap β} (h : disjoint s₁ s₃) (h' : disjoint s₂ s₃) : s₁ ∪ s₃ = s₂ ∪ s₃ ↔ s₁ = s₂ := sorry

