/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.Lean3Lib.init.data.nat.basic
import Mathlib.Lean3Lib.init.data.bool.basic
import Mathlib.Lean3Lib.init.propext

universes u u_1 v w 

namespace Mathlib

protected instance list.inhabited (α : Type u) : Inhabited (List α) := { default := [] }

namespace list


protected def has_dec_eq {α : Type u} [s : DecidableEq α] : DecidableEq (List α) := sorry

protected instance decidable_eq {α : Type u} [DecidableEq α] : DecidableEq (List α) :=
  list.has_dec_eq

@[simp] protected def append {α : Type u} : List α → List α → List α := sorry

protected instance has_append {α : Type u} : Append (List α) := { append := list.append }

protected def mem {α : Type u} : α → List α → Prop := sorry

protected instance has_mem {α : Type u} : has_mem α (List α) := has_mem.mk list.mem

protected instance decidable_mem {α : Type u} [DecidableEq α] (a : α) (l : List α) :
    Decidable (a ∈ l) :=
  sorry

protected instance has_emptyc {α : Type u} : has_emptyc (List α) := has_emptyc.mk []

protected def erase {α : Type u_1} [DecidableEq α] : List α → α → List α := sorry

protected def bag_inter {α : Type u_1} [DecidableEq α] : List α → List α → List α := sorry

protected def diff {α : Type u_1} [DecidableEq α] : List α → List α → List α := sorry

@[simp] def length {α : Type u} : List α → ℕ := sorry

def empty {α : Type u} : List α → Bool := sorry

@[simp] def nth {α : Type u} : List α → ℕ → Option α := sorry

@[simp] def nth_le {α : Type u} (l : List α) (n : ℕ) : n < length l → α := sorry

@[simp] def head {α : Type u} [Inhabited α] : List α → α := sorry

@[simp] def tail {α : Type u} : List α → List α := sorry

def reverse_core {α : Type u} : List α → List α → List α := sorry

def reverse {α : Type u} : List α → List α := fun (l : List α) => reverse_core l []

@[simp] def map {α : Type u} {β : Type v} (f : α → β) : List α → List β := sorry

@[simp] def map₂ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) :
    List α → List β → List γ :=
  sorry

def map_with_index_core {α : Type u} {β : Type v} (f : ℕ → α → β) : ℕ → List α → List β := sorry

/-- Given a function `f : ℕ → α → β` and `as : list α`, `as = [a₀, a₁, ...]`, returns the list
`[f 0 a₀, f 1 a₁, ...]`. -/
def map_with_index {α : Type u} {β : Type v} (f : ℕ → α → β) (as : List α) : List β :=
  map_with_index_core f 0 as

def join {α : Type u} : List (List α) → List α := sorry

def filter_map {α : Type u} {β : Type v} (f : α → Option β) : List α → List β := sorry

def filter {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α := sorry

def partition {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α × List α := sorry

def drop_while {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α := sorry

/-- `after p xs` is the suffix of `xs` after the first element that satisfies
  `p`, not including that element.

  ```lean
  after      (eq 1)       [0, 1, 2, 3] = [2, 3]
  drop_while (not ∘ eq 1) [0, 1, 2, 3] = [1, 2, 3]
  ```
-/
def after {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α := sorry

def span {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α × List α := sorry

def find_index {α : Type u} (p : α → Prop) [decidable_pred p] : List α → ℕ := sorry

def index_of {α : Type u} [DecidableEq α] (a : α) : List α → ℕ := find_index (Eq a)

def remove_all {α : Type u} [DecidableEq α] (xs : List α) (ys : List α) : List α :=
  filter (fun (_x : α) => ¬_x ∈ ys) xs

def update_nth {α : Type u} : List α → ℕ → α → List α := sorry

def remove_nth {α : Type u} : List α → ℕ → List α := sorry

@[simp] def drop {α : Type u} : ℕ → List α → List α := sorry

@[simp] def take {α : Type u} : ℕ → List α → List α := sorry

@[simp] def foldl {α : Type u} {β : Type v} (f : α → β → α) : α → List β → α := sorry

@[simp] def foldr {α : Type u} {β : Type v} (f : α → β → β) (b : β) : List α → β := sorry

def any {α : Type u} (l : List α) (p : α → Bool) : Bool :=
  foldr (fun (a : α) (r : Bool) => p a || r) false l

def all {α : Type u} (l : List α) (p : α → Bool) : Bool :=
  foldr (fun (a : α) (r : Bool) => p a && r) tt l

def bor (l : List Bool) : Bool := any l id

def band (l : List Bool) : Bool := all l id

def zip_with {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) : List α → List β → List γ :=
  sorry

def zip {α : Type u} {β : Type v} : List α → List β → List (α × β) := zip_with Prod.mk

def unzip {α : Type u} {β : Type v} : List (α × β) → List α × List β := sorry

protected def insert {α : Type u} [DecidableEq α] (a : α) (l : List α) : List α :=
  ite (a ∈ l) l (a :: l)

protected instance has_insert {α : Type u} [DecidableEq α] : has_insert α (List α) :=
  has_insert.mk list.insert

protected instance has_singleton {α : Type u} : has_singleton α (List α) :=
  has_singleton.mk fun (x : α) => [x]

protected instance is_lawful_singleton {α : Type u} [DecidableEq α] :
    is_lawful_singleton α (List α) :=
  is_lawful_singleton.mk
    fun (x : α) => (fun (this : ite (x ∈ []) [] [x] = [x]) => this) (if_neg not_false)

protected def union {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : List α :=
  foldr insert l₂ l₁

protected instance has_union {α : Type u} [DecidableEq α] : has_union (List α) :=
  has_union.mk list.union

protected def inter {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : List α :=
  filter (fun (_x : α) => _x ∈ l₂) l₁

protected instance has_inter {α : Type u} [DecidableEq α] : has_inter (List α) :=
  has_inter.mk list.inter

@[simp] def repeat {α : Type u} (a : α) : ℕ → List α := sorry

def range_core : ℕ → List ℕ → List ℕ := sorry

def range (n : ℕ) : List ℕ := range_core n []

def iota : ℕ → List ℕ := sorry

def enum_from {α : Type u} : ℕ → List α → List (ℕ × α) := sorry

def enum {α : Type u} : List α → List (ℕ × α) := enum_from 0

@[simp] def last {α : Type u} (l : List α) : l ≠ [] → α := sorry

def ilast {α : Type u} [Inhabited α] : List α → α := sorry

def init {α : Type u} : List α → List α := sorry

def intersperse {α : Type u} (sep : α) : List α → List α := sorry

def intercalate {α : Type u} (sep : List α) (xs : List (List α)) : List α :=
  join (intersperse sep xs)

protected def bind {α : Type u} {β : Type v} (a : List α) (b : α → List β) : List β :=
  join (map b a)

protected def ret {α : Type u} (a : α) : List α := [a]

protected def lt {α : Type u} [HasLess α] : List α → List α → Prop := sorry

protected instance has_lt {α : Type u} [HasLess α] : HasLess (List α) := { Less := list.lt }

protected instance has_decidable_lt {α : Type u} [HasLess α] [h : DecidableRel Less] (l₁ : List α)
    (l₂ : List α) : Decidable (l₁ < l₂) :=
  sorry

protected def le {α : Type u} [HasLess α] (a : List α) (b : List α) := ¬b < a

protected instance has_le {α : Type u} [HasLess α] : HasLessEq (List α) := { LessEq := list.le }

protected instance has_decidable_le {α : Type u} [HasLess α] [h : DecidableRel Less] (l₁ : List α)
    (l₂ : List α) : Decidable (l₁ ≤ l₂) :=
  not.decidable

theorem le_eq_not_gt {α : Type u} [HasLess α] (l₁ : List α) (l₂ : List α) : l₁ ≤ l₂ = (¬l₂ < l₁) :=
  rfl

theorem lt_eq_not_ge {α : Type u} [HasLess α] [DecidableRel Less] (l₁ : List α) (l₂ : List α) :
    l₁ < l₂ = (¬l₂ ≤ l₁) :=
  (fun (this : l₁ < l₂ = (¬¬l₁ < l₂)) => this)
    (Eq.symm (propext (decidable.not_not_iff (l₁ < l₂))) ▸ rfl)

/--  `is_prefix_of l₁ l₂` returns `tt` iff `l₁` is a prefix of `l₂`. -/
def is_prefix_of {α : Type u} [DecidableEq α] : List α → List α → Bool := sorry

/--  `is_suffix_of l₁ l₂` returns `tt` iff `l₁` is a suffix of `l₂`. -/
def is_suffix_of {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) : Bool :=
  is_prefix_of (reverse l₁) (reverse l₂)

end list


namespace bin_tree


def to_list {α : Type u} (t : bin_tree α) : List α := to_list_aux t []

end Mathlib