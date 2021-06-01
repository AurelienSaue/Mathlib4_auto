/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather

Functions on lists of sigma types.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.perm
import Mathlib.data.list.range
import Mathlib.data.sigma.default
import Mathlib.PostPort

universes u v u_1 u_2 

namespace Mathlib

namespace list


/- keys -/

/-- List of keys from a list of key-value pairs -/
def keys {α : Type u} {β : α → Type v} : List (sigma β) → List α := map sigma.fst

@[simp] theorem keys_nil {α : Type u} {β : α → Type v} : keys [] = [] := rfl

@[simp] theorem keys_cons {α : Type u} {β : α → Type v} {s : sigma β} {l : List (sigma β)} :
    keys (s :: l) = sigma.fst s :: keys l :=
  rfl

theorem mem_keys_of_mem {α : Type u} {β : α → Type v} {s : sigma β} {l : List (sigma β)} :
    s ∈ l → sigma.fst s ∈ keys l :=
  mem_map_of_mem sigma.fst

theorem exists_of_mem_keys {α : Type u} {β : α → Type v} {a : α} {l : List (sigma β)}
    (h : a ∈ keys l) : ∃ (b : β a), sigma.mk a b ∈ l :=
  sorry

theorem mem_keys {α : Type u} {β : α → Type v} {a : α} {l : List (sigma β)} :
    a ∈ keys l ↔ ∃ (b : β a), sigma.mk a b ∈ l :=
  sorry

theorem not_mem_keys {α : Type u} {β : α → Type v} {a : α} {l : List (sigma β)} :
    ¬a ∈ keys l ↔ ∀ (b : β a), ¬sigma.mk a b ∈ l :=
  iff.trans (not_iff_not_of_iff mem_keys) not_exists

theorem not_eq_key {α : Type u} {β : α → Type v} {a : α} {l : List (sigma β)} :
    ¬a ∈ keys l ↔ ∀ (s : sigma β), s ∈ l → a ≠ sigma.fst s :=
  sorry

/- nodupkeys -/

def nodupkeys {α : Type u} {β : α → Type v} (l : List (sigma β)) := nodup (keys l)

theorem nodupkeys_iff_pairwise {α : Type u} {β : α → Type v} {l : List (sigma β)} :
    nodupkeys l ↔ pairwise (fun (s s' : sigma β) => sigma.fst s ≠ sigma.fst s') l :=
  pairwise_map sigma.fst

theorem nodupkeys.pairwise_ne {α : Type u} {β : α → Type v} {l : List (sigma β)} (h : nodupkeys l) :
    pairwise (fun (s s' : sigma β) => sigma.fst s ≠ sigma.fst s') l :=
  iff.mp nodupkeys_iff_pairwise h

@[simp] theorem nodupkeys_nil {α : Type u} {β : α → Type v} : nodupkeys [] := pairwise.nil

@[simp] theorem nodupkeys_cons {α : Type u} {β : α → Type v} {s : sigma β} {l : List (sigma β)} :
    nodupkeys (s :: l) ↔ ¬sigma.fst s ∈ keys l ∧ nodupkeys l :=
  sorry

theorem nodupkeys.eq_of_fst_eq {α : Type u} {β : α → Type v} {l : List (sigma β)} (nd : nodupkeys l)
    {s : sigma β} {s' : sigma β} (h : s ∈ l) (h' : s' ∈ l) : sigma.fst s = sigma.fst s' → s = s' :=
  sorry

theorem nodupkeys.eq_of_mk_mem {α : Type u} {β : α → Type v} {a : α} {b : β a} {b' : β a}
    {l : List (sigma β)} (nd : nodupkeys l) (h : sigma.mk a b ∈ l) (h' : sigma.mk a b' ∈ l) :
    b = b' :=
  sorry

theorem nodupkeys_singleton {α : Type u} {β : α → Type v} (s : sigma β) : nodupkeys [s] :=
  nodup_singleton (sigma.fst s)

theorem nodupkeys_of_sublist {α : Type u} {β : α → Type v} {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} (h : l₁ <+ l₂) : nodupkeys l₂ → nodupkeys l₁ :=
  nodup_of_sublist (sublist.map sigma.fst h)

theorem nodup_of_nodupkeys {α : Type u} {β : α → Type v} {l : List (sigma β)} :
    nodupkeys l → nodup l :=
  nodup_of_nodup_map sigma.fst

theorem perm_nodupkeys {α : Type u} {β : α → Type v} {l₁ : List (sigma β)} {l₂ : List (sigma β)}
    (h : l₁ ~ l₂) : nodupkeys l₁ ↔ nodupkeys l₂ :=
  perm.nodup_iff (perm.map sigma.fst h)

theorem nodupkeys_join {α : Type u} {β : α → Type v} {L : List (List (sigma β))} :
    nodupkeys (join L) ↔
        (∀ (l : List (sigma β)), l ∈ L → nodupkeys l) ∧ pairwise disjoint (map keys L) :=
  sorry

theorem nodup_enum_map_fst {α : Type u} (l : List α) : nodup (map prod.fst (enum l)) := sorry

theorem mem_ext {α : Type u} {β : α → Type v} {l₀ : List (sigma β)} {l₁ : List (sigma β)}
    (nd₀ : nodup l₀) (nd₁ : nodup l₁) (h : ∀ (x : sigma β), x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ :=
  sorry

/- lookup -/

/-- `lookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def lookup {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) : List (sigma β) → Option (β a) :=
  sorry

@[simp] theorem lookup_nil {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) :
    lookup a [] = none :=
  rfl

@[simp] theorem lookup_cons_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    (l : List (sigma fun (a : α) => β a)) (a : α) (b : β a) :
    lookup a (sigma.mk a b :: l) = some b :=
  dif_pos rfl

@[simp] theorem lookup_cons_ne {α : Type u} {β : α → Type v} [DecidableEq α] (l : List (sigma β))
    {a : α} (s : sigma β) : a ≠ sigma.fst s → lookup a (s :: l) = lookup a l :=
  sorry

theorem lookup_is_some {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {l : List (sigma β)} :
    ↥(option.is_some (lookup a l)) ↔ a ∈ keys l :=
  sorry

theorem lookup_eq_none {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {l : List (sigma β)} :
    lookup a l = none ↔ ¬a ∈ keys l :=
  sorry

theorem of_mem_lookup {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l : List (sigma β)} : b ∈ lookup a l → sigma.mk a b ∈ l :=
  sorry

theorem mem_lookup {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l : List (sigma β)} (nd : nodupkeys l) (h : sigma.mk a b ∈ l) : b ∈ lookup a l :=
  sorry

theorem map_lookup_eq_find {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (l : List (sigma β)) :
    option.map (sigma.mk a) (lookup a l) = find (fun (s : sigma β) => a = sigma.fst s) l :=
  sorry

theorem mem_lookup_iff {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l : List (sigma β)} (nd : nodupkeys l) : b ∈ lookup a l ↔ sigma.mk a b ∈ l :=
  { mp := of_mem_lookup, mpr := mem_lookup nd }

theorem perm_lookup {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} (nd₁ : nodupkeys l₁) (nd₂ : nodupkeys l₂) (p : l₁ ~ l₂) :
    lookup a l₁ = lookup a l₂ :=
  sorry

theorem lookup_ext {α : Type u} {β : α → Type v} [DecidableEq α] {l₀ : List (sigma β)}
    {l₁ : List (sigma β)} (nd₀ : nodupkeys l₀) (nd₁ : nodupkeys l₁)
    (h : ∀ (x : α) (y : β x), y ∈ lookup x l₀ ↔ y ∈ lookup x l₁) : l₀ ~ l₁ :=
  sorry

/- lookup_all -/

/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookup_all {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) :
    List (sigma β) → List (β a) :=
  sorry

@[simp] theorem lookup_all_nil {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) :
    lookup_all a [] = [] :=
  rfl

@[simp] theorem lookup_all_cons_eq {α : Type u} {β : α → Type v} [DecidableEq α]
    (l : List (sigma fun (a : α) => β a)) (a : α) (b : β a) :
    lookup_all a (sigma.mk a b :: l) = b :: lookup_all a l :=
  dif_pos rfl

@[simp] theorem lookup_all_cons_ne {α : Type u} {β : α → Type v} [DecidableEq α]
    (l : List (sigma β)) {a : α} (s : sigma β) :
    a ≠ sigma.fst s → lookup_all a (s :: l) = lookup_all a l :=
  sorry

theorem lookup_all_eq_nil {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l : List (sigma β)} : lookup_all a l = [] ↔ ∀ (b : β a), ¬sigma.mk a b ∈ l :=
  sorry

theorem head_lookup_all {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (l : List (sigma β)) :
    head' (lookup_all a l) = lookup a l :=
  sorry

theorem mem_lookup_all {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l : List (sigma β)} : b ∈ lookup_all a l ↔ sigma.mk a b ∈ l :=
  sorry

theorem lookup_all_sublist {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (l : List (sigma β)) : map (sigma.mk a) (lookup_all a l) <+ l :=
  sorry

theorem lookup_all_length_le_one {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    {l : List (sigma β)} (h : nodupkeys l) : length (lookup_all a l) ≤ 1 :=
  sorry

theorem lookup_all_eq_lookup {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    {l : List (sigma β)} (h : nodupkeys l) : lookup_all a l = option.to_list (lookup a l) :=
  sorry

theorem lookup_all_nodup {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) {l : List (sigma β)}
    (h : nodupkeys l) : nodup (lookup_all a l) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nodup (lookup_all a l))) (lookup_all_eq_lookup a h)))
    (option.to_list_nodup (lookup a l))

theorem perm_lookup_all {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} (nd₁ : nodupkeys l₁) (nd₂ : nodupkeys l₂) (p : l₁ ~ l₂) :
    lookup_all a l₁ = lookup_all a l₂ :=
  sorry

/- kreplace -/

def kreplace {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) :
    List (sigma β) → List (sigma β) :=
  lookmap
    fun (s : sigma β) =>
      dite (a = sigma.fst s) (fun (h : a = sigma.fst s) => some (sigma.mk a b))
        fun (h : ¬a = sigma.fst s) => none

theorem kreplace_of_forall_not {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a)
    {l : List (sigma β)} (H : ∀ (b : β a), ¬sigma.mk a b ∈ l) : kreplace a b l = l :=
  sorry

theorem kreplace_self {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l : List (sigma β)} (nd : nodupkeys l) (h : sigma.mk a b ∈ l) : kreplace a b l = l :=
  sorry

theorem keys_kreplace {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a)
    (l : List (sigma β)) : keys (kreplace a b l) = keys l :=
  sorry

theorem kreplace_nodupkeys {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a)
    {l : List (sigma β)} : nodupkeys (kreplace a b l) ↔ nodupkeys l :=
  sorry

theorem perm.kreplace {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} (nd : nodupkeys l₁) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  sorry

/- kerase -/

/-- Remove the first pair with the key `a`. -/
def kerase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) :
    List (sigma β) → List (sigma β) :=
  erasep fun (s : sigma β) => a = sigma.fst s

@[simp] theorem kerase_nil {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} :
    kerase a [] = [] :=
  rfl

@[simp] theorem kerase_cons_eq {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : sigma β}
    {l : List (sigma β)} (h : a = sigma.fst s) : kerase a (s :: l) = l :=
  sorry

@[simp] theorem kerase_cons_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {s : sigma β}
    {l : List (sigma β)} (h : a ≠ sigma.fst s) : kerase a (s :: l) = s :: kerase a l :=
  sorry

@[simp] theorem kerase_of_not_mem_keys {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l : List (sigma β)} (h : ¬a ∈ keys l) : kerase a l = l :=
  sorry

theorem kerase_sublist {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (l : List (sigma β)) :
    kerase a l <+ l :=
  erasep_sublist l

theorem kerase_keys_subset {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (l : List (sigma β)) : keys (kerase a l) ⊆ keys l :=
  sublist.subset (sublist.map sigma.fst (kerase_sublist a l))

theorem mem_keys_of_mem_keys_kerase {α : Type u} {β : α → Type v} [DecidableEq α] {a₁ : α} {a₂ : α}
    {l : List (sigma β)} : a₁ ∈ keys (kerase a₂ l) → a₁ ∈ keys l :=
  kerase_keys_subset a₂ l

theorem exists_of_kerase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {l : List (sigma β)}
    (h : a ∈ keys l) :
    ∃ (b : β a),
        ∃ (l₁ : List (sigma β)),
          ∃ (l₂ : List (sigma β)),
            ¬a ∈ keys l₁ ∧ l = l₁ ++ sigma.mk a b :: l₂ ∧ kerase a l = l₁ ++ l₂ :=
  sorry

@[simp] theorem mem_keys_kerase_of_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a₁ : α}
    {a₂ : α} {l : List (sigma β)} (h : a₁ ≠ a₂) : a₁ ∈ keys (kerase a₂ l) ↔ a₁ ∈ keys l :=
  sorry

theorem keys_kerase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {l : List (sigma β)} :
    keys (kerase a l) = list.erase (keys l) a :=
  sorry

theorem kerase_kerase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α}
    {l : List (sigma β)} : kerase a (kerase a' l) = kerase a' (kerase a l) :=
  sorry

theorem kerase_nodupkeys {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    {l : List (sigma β)} : nodupkeys l → nodupkeys (kerase a l) :=
  nodupkeys_of_sublist (kerase_sublist a l)

theorem perm.kerase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} (nd : nodupkeys l₁) : l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ :=
  perm.erasep (fun (s : sigma β) => a = sigma.fst s)
    (pairwise.imp
      (fun (x y : sigma β) (h : sigma.fst x ≠ sigma.fst y) (ᾰ : a = sigma.fst x) =>
        Eq._oldrec h (Eq.symm ᾰ))
      (iff.mp nodupkeys_iff_pairwise nd))

@[simp] theorem not_mem_keys_kerase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    {l : List (sigma β)} (nd : nodupkeys l) : ¬a ∈ keys (kerase a l) :=
  sorry

@[simp] theorem lookup_kerase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    {l : List (sigma β)} (nd : nodupkeys l) : lookup a (kerase a l) = none :=
  iff.mpr lookup_eq_none (not_mem_keys_kerase a nd)

@[simp] theorem lookup_kerase_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α}
    {l : List (sigma β)} (h : a ≠ a') : lookup a (kerase a' l) = lookup a l :=
  sorry

theorem kerase_append_left {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    a ∈ keys l₁ → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂ :=
  sorry

theorem kerase_append_right {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    ¬a ∈ keys l₁ → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂ :=
  sorry

theorem kerase_comm {α : Type u} {β : α → Type v} [DecidableEq α] (a₁ : α) (a₂ : α)
    (l : List (sigma β)) : kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  sorry

theorem sizeof_kerase {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [SizeOf (sigma β)] (x : α)
    (xs : List (sigma β)) : sizeof (kerase x xs) ≤ sizeof xs :=
  sorry

/- kinsert -/

/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a) (l : List (sigma β)) :
    List (sigma β) :=
  sigma.mk a b :: kerase a l

@[simp] theorem kinsert_def {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l : List (sigma β)} : kinsert a b l = sigma.mk a b :: kerase a l :=
  rfl

theorem mem_keys_kinsert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b' : β a'}
    {l : List (sigma β)} : a ∈ keys (kinsert a' b' l) ↔ a = a' ∨ a ∈ keys l :=
  sorry

theorem kinsert_nodupkeys {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) (b : β a)
    {l : List (sigma β)} (nd : nodupkeys l) : nodupkeys (kinsert a b l) :=
  iff.mpr nodupkeys_cons { left := not_mem_keys_kerase a nd, right := kerase_nodupkeys a nd }

theorem perm.kinsert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} (nd₁ : nodupkeys l₁) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  perm.cons (sigma.mk a b) (perm.kerase nd₁ p)

theorem lookup_kinsert {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    (l : List (sigma β)) : lookup a (kinsert a b l) = some b :=
  sorry

theorem lookup_kinsert_ne {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {a' : α} {b' : β a'}
    {l : List (sigma β)} (h : a ≠ a') : lookup a (kinsert a' b' l) = lookup a l :=
  sorry

/- kextract -/

def kextract {α : Type u} {β : α → Type v} [DecidableEq α] (a : α) :
    List (sigma β) → Option (β a) × List (sigma β) :=
  sorry

@[simp] theorem kextract_eq_lookup_kerase {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (l : List (sigma β)) : kextract a l = (lookup a l, kerase a l) :=
  sorry

/- erase_dupkeys -/

/-- Remove entries with duplicate keys from `l : list (sigma β)`. -/
def erase_dupkeys {α : Type u} {β : α → Type v} [DecidableEq α] : List (sigma β) → List (sigma β) :=
  foldr (fun (x : sigma β) => kinsert (sigma.fst x) (sigma.snd x)) []

theorem erase_dupkeys_cons {α : Type u} {β : α → Type v} [DecidableEq α] {x : sigma β}
    (l : List (sigma β)) :
    erase_dupkeys (x :: l) = kinsert (sigma.fst x) (sigma.snd x) (erase_dupkeys l) :=
  rfl

theorem nodupkeys_erase_dupkeys {α : Type u} {β : α → Type v} [DecidableEq α] (l : List (sigma β)) :
    nodupkeys (erase_dupkeys l) :=
  sorry

theorem lookup_erase_dupkeys {α : Type u} {β : α → Type v} [DecidableEq α] (a : α)
    (l : List (sigma β)) : lookup a (erase_dupkeys l) = lookup a l :=
  sorry

theorem sizeof_erase_dupkeys {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [SizeOf (sigma β)]
    (xs : List (sigma β)) : sizeof (erase_dupkeys xs) ≤ sizeof xs :=
  sorry

/- kunion -/

/-- `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
def kunion {α : Type u} {β : α → Type v} [DecidableEq α] :
    List (sigma β) → List (sigma β) → List (sigma β) :=
  sorry

@[simp] theorem nil_kunion {α : Type u} {β : α → Type v} [DecidableEq α] {l : List (sigma β)} :
    kunion [] l = l :=
  rfl

@[simp] theorem kunion_nil {α : Type u} {β : α → Type v} [DecidableEq α] {l : List (sigma β)} :
    kunion l [] = l :=
  sorry

@[simp] theorem kunion_cons {α : Type u} {β : α → Type v} [DecidableEq α] {s : sigma β}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase (sigma.fst s) l₂) :=
  rfl

@[simp] theorem mem_keys_kunion {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    a ∈ keys (kunion l₁ l₂) ↔ a ∈ keys l₁ ∨ a ∈ keys l₂ :=
  sorry

@[simp] theorem kunion_kerase {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂) :=
  sorry

theorem kunion_nodupkeys {α : Type u} {β : α → Type v} [DecidableEq α] {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} (nd₁ : nodupkeys l₁) (nd₂ : nodupkeys l₂) : nodupkeys (kunion l₁ l₂) :=
  sorry

theorem perm.kunion_right {α : Type u} {β : α → Type v} [DecidableEq α] {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} (p : l₁ ~ l₂) (l : List (sigma β)) : kunion l₁ l ~ kunion l₂ l :=
  sorry

theorem perm.kunion_left {α : Type u} {β : α → Type v} [DecidableEq α] (l : List (sigma β))
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    nodupkeys l₁ → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂ :=
  sorry

theorem perm.kunion {α : Type u} {β : α → Type v} [DecidableEq α] {l₁ : List (sigma β)}
    {l₂ : List (sigma β)} {l₃ : List (sigma β)} {l₄ : List (sigma β)} (nd₃ : nodupkeys l₃)
    (p₁₂ : l₁ ~ l₂) (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
  perm.trans (perm.kunion_right p₁₂ l₃) (perm.kunion_left l₂ nd₃ p₃₄)

@[simp] theorem lookup_kunion_left {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} (h : a ∈ keys l₁) :
    lookup a (kunion l₁ l₂) = lookup a l₁ :=
  sorry

@[simp] theorem lookup_kunion_right {α : Type u} {β : α → Type v} [DecidableEq α] {a : α}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} (h : ¬a ∈ keys l₁) :
    lookup a (kunion l₁ l₂) = lookup a l₂ :=
  sorry

@[simp] theorem mem_lookup_kunion {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} :
    b ∈ lookup a (kunion l₁ l₂) ↔ b ∈ lookup a l₁ ∨ ¬a ∈ keys l₁ ∧ b ∈ lookup a l₂ :=
  sorry

theorem mem_lookup_kunion_middle {α : Type u} {β : α → Type v} [DecidableEq α] {a : α} {b : β a}
    {l₁ : List (sigma β)} {l₂ : List (sigma β)} {l₃ : List (sigma β)}
    (h₁ : b ∈ lookup a (kunion l₁ l₃)) (h₂ : ¬a ∈ keys l₂) :
    b ∈ lookup a (kunion (kunion l₁ l₂) l₃) :=
  sorry

end Mathlib