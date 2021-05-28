/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.basic
import PostPort

universes u v w 

namespace Mathlib

namespace list


namespace func


/- Definitions for using lists as finite
   representations of functions with domain ℕ. -/

def neg {α : Type u} [Neg α] (as : List α) : List α :=
  map (fun (a : α) => -a) as

@[simp] def set {α : Type u} [Inhabited α] (a : α) : List α → ℕ → List α :=
  sorry

@[simp] def get {α : Type u} [Inhabited α] : ℕ → List α → α :=
  sorry

def equiv {α : Type u} [Inhabited α] (as1 : List α) (as2 : List α)  :=
  ∀ (m : ℕ), get m as1 = get m as2

@[simp] def pointwise {α : Type u} {β : Type v} {γ : Type w} [Inhabited α] [Inhabited β] (f : α → β → γ) : List α → List β → List γ :=
  sorry

def add {α : Type u} [HasZero α] [Add α] : List α → List α → List α :=
  pointwise Add.add

def sub {α : Type u} [HasZero α] [Sub α] : List α → List α → List α :=
  pointwise Sub.sub

/- set -/

theorem length_set {α : Type u} {a : α} [Inhabited α] {m : ℕ} {as : List α} : length (set a as m) = max (length as) (m + 1) := sorry

@[simp] theorem get_nil {α : Type u} [Inhabited α] {k : ℕ} : get k [] = Inhabited.default :=
  nat.cases_on k (Eq.refl (get 0 [])) fun (k : ℕ) => Eq.refl (get (Nat.succ k) [])

theorem get_eq_default_of_le {α : Type u} [Inhabited α] (k : ℕ) {as : List α} : length as ≤ k → get k as = Inhabited.default := sorry

@[simp] theorem get_set {α : Type u} [Inhabited α] {a : α} {k : ℕ} {as : List α} : get k (set a as k) = a := sorry

theorem eq_get_of_mem {α : Type u} [Inhabited α] {a : α} {as : List α} : a ∈ as → ∃ (n : ℕ), α → a = get n as := sorry

theorem mem_get_of_le {α : Type u} [Inhabited α] {n : ℕ} {as : List α} : n < length as → get n as ∈ as := sorry

theorem mem_get_of_ne_zero {α : Type u} [Inhabited α] {n : ℕ} {as : List α} : get n as ≠ Inhabited.default → get n as ∈ as := sorry

theorem get_set_eq_of_ne {α : Type u} [Inhabited α] {a : α} {as : List α} (k : ℕ) (m : ℕ) : m ≠ k → get m (set a as k) = get m as := sorry

theorem get_map {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] {f : α → β} {n : ℕ} {as : List α} : n < length as → get n (map f as) = f (get n as) := sorry

theorem get_map' {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] {f : α → β} {n : ℕ} {as : List α} : f Inhabited.default = Inhabited.default → get n (map f as) = f (get n as) := sorry

theorem forall_val_of_forall_mem {α : Type u} [Inhabited α] {as : List α} {p : α → Prop} : p Inhabited.default → (∀ (x : α), x ∈ as → p x) → ∀ (n : ℕ), p (get n as) := sorry

/- equiv -/

theorem equiv_refl {α : Type u} {as : List α} [Inhabited α] : equiv as as :=
  fun (k : ℕ) => rfl

theorem equiv_symm {α : Type u} {as1 : List α} {as2 : List α} [Inhabited α] : equiv as1 as2 → equiv as2 as1 :=
  fun (h1 : equiv as1 as2) (k : ℕ) => Eq.symm (h1 k)

theorem equiv_trans {α : Type u} {as1 : List α} {as2 : List α} {as3 : List α} [Inhabited α] : equiv as1 as2 → equiv as2 as3 → equiv as1 as3 :=
  fun (h1 : equiv as1 as2) (h2 : equiv as2 as3) (k : ℕ) => Eq.trans (h1 k) (h2 k)

theorem equiv_of_eq {α : Type u} {as1 : List α} {as2 : List α} [Inhabited α] : as1 = as2 → equiv as1 as2 :=
  fun (h1 : as1 = as2) => eq.mpr (id (Eq._oldrec (Eq.refl (equiv as1 as2)) h1)) equiv_refl

theorem eq_of_equiv {α : Type u} [Inhabited α] {as1 : List α} {as2 : List α} : length as1 = length as2 → equiv as1 as2 → as1 = as2 := sorry

end func


-- We want to drop the `inhabited` instances for a moment,

-- so we close and open the namespace

namespace func


/- neg -/

@[simp] theorem get_neg {α : Type u} [add_group α] {k : ℕ} {as : List α} : get k (neg as) = -get k as := sorry

@[simp] theorem length_neg {α : Type u} [Neg α] (as : List α) : length (neg as) = length as := sorry

/- pointwise -/

theorem nil_pointwise {α : Type u} {β : Type v} {γ : Type w} [Inhabited α] [Inhabited β] {f : α → β → γ} (bs : List β) : pointwise f [] bs = map (f Inhabited.default) bs := sorry

theorem pointwise_nil {α : Type u} {β : Type v} {γ : Type w} [Inhabited α] [Inhabited β] {f : α → β → γ} (as : List α) : pointwise f as [] = map (fun (a : α) => f a Inhabited.default) as := sorry

theorem get_pointwise {α : Type u} {β : Type v} {γ : Type w} [Inhabited α] [Inhabited β] [Inhabited γ] {f : α → β → γ} (h1 : f Inhabited.default Inhabited.default = Inhabited.default) (k : ℕ) (as : List α) (bs : List β) : get k (pointwise f as bs) = f (get k as) (get k bs) := sorry

theorem length_pointwise {α : Type u} {β : Type v} {γ : Type w} [Inhabited α] [Inhabited β] {f : α → β → γ} {as : List α} {bs : List β} : length (pointwise f as bs) = max (length as) (length bs) := sorry

end func


namespace func


/- add -/

@[simp] theorem get_add {α : Type u} [add_monoid α] {k : ℕ} {xs : List α} {ys : List α} : get k (add xs ys) = get k xs + get k ys :=
  get_pointwise (zero_add Inhabited.default) k xs ys

@[simp] theorem length_add {α : Type u} [HasZero α] [Add α] {xs : List α} {ys : List α} : length (add xs ys) = max (length xs) (length ys) :=
  length_pointwise

@[simp] theorem nil_add {α : Type u} [add_monoid α] (as : List α) : add [] as = as := sorry

@[simp] theorem add_nil {α : Type u} [add_monoid α] (as : List α) : add as [] = as := sorry

theorem map_add_map {α : Type u} [add_monoid α] (f : α → α) (g : α → α) {as : List α} : add (map f as) (map g as) = map (fun (x : α) => f x + g x) as := sorry

/- sub -/

@[simp] theorem get_sub {α : Type u} [add_group α] {k : ℕ} {xs : List α} {ys : List α} : get k (sub xs ys) = get k xs - get k ys :=
  get_pointwise (sub_zero Inhabited.default) k xs ys

@[simp] theorem length_sub {α : Type u} [HasZero α] [Sub α] {xs : List α} {ys : List α} : length (sub xs ys) = max (length xs) (length ys) :=
  length_pointwise

@[simp] theorem nil_sub {α : Type} [add_group α] (as : List α) : sub [] as = neg as := sorry

@[simp] theorem sub_nil {α : Type} [add_group α] (as : List α) : sub as [] = as := sorry

