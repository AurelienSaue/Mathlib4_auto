/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

namespace list


/-- Auxiliary definition to define `argmax` -/
def argmax₂ {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (a : Option α) (b : α) : Option α :=
  option.cases_on a (some b) fun (c : α) => ite (f b ≤ f c) (some c) (some b)

/-- `argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmax f []` = none` -/
def argmax {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (l : List α) : Option α :=
  foldl (argmax₂ f) none l

/-- `argmin f l` returns `some a`, where `a` of `l` that minimises `f a`. If there are `a b` such
that `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
`argmin f []` = none` -/
def argmin {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (l : List α) : Option α :=
  argmax f l

@[simp] theorem argmax_two_self {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (a : α) : argmax₂ f (some a) a = ↑a :=
  if_pos (le_refl (f a))

@[simp] theorem argmax_nil {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) : argmax f [] = none :=
  rfl

@[simp] theorem argmin_nil {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) : argmin f [] = none :=
  rfl

@[simp] theorem argmax_singleton {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {a : α} : argmax f [a] = some a :=
  rfl

@[simp] theorem argmin_singleton {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {a : α} : argmin f [a] = ↑a :=
  rfl

@[simp] theorem foldl_argmax₂_eq_none {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {l : List α} {o : Option α} : foldl (argmax₂ f) o l = none ↔ l = [] ∧ o = none := sorry

theorem argmax_mem {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {l : List α} {m : α} : m ∈ argmax f l → m ∈ l := sorry

theorem argmin_mem {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {l : List α} {m : α} : m ∈ argmin f l → m ∈ l :=
  argmax_mem

@[simp] theorem argmax_eq_none {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {l : List α} : argmax f l = none ↔ l = [] := sorry

@[simp] theorem argmin_eq_none {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {l : List α} : argmin f l = none ↔ l = [] :=
  argmax_eq_none

theorem le_argmax_of_mem {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {a : α} {m : α} {l : List α} : a ∈ l → m ∈ argmax f l → f a ≤ f m :=
  le_of_foldl_argmax₂

theorem argmin_le_of_mem {α : Type u_1} {β : Type u_2} [linear_order β] {f : α → β} {a : α} {m : α} {l : List α} : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  le_argmax_of_mem

theorem argmax_concat {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (a : α) (l : List α) : argmax f (l ++ [a]) = option.cases_on (argmax f l) (some a) fun (c : α) => ite (f a ≤ f c) (some c) (some a) := sorry

theorem argmin_concat {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (a : α) (l : List α) : argmin f (l ++ [a]) = option.cases_on (argmin f l) (some a) fun (c : α) => ite (f c ≤ f a) (some c) (some a) :=
  argmax_concat f a l

theorem argmax_cons {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (a : α) (l : List α) : argmax f (a :: l) = option.cases_on (argmax f l) (some a) fun (c : α) => ite (f c ≤ f a) (some a) (some c) := sorry

theorem argmin_cons {α : Type u_1} {β : Type u_2} [linear_order β] (f : α → β) (a : α) (l : List α) : argmin f (a :: l) = option.cases_on (argmin f l) (some a) fun (c : α) => ite (f a ≤ f c) (some a) (some c) :=
  argmax_cons f a l

theorem index_of_argmax {α : Type u_1} {β : Type u_2} [linear_order β] [DecidableEq α] {f : α → β} {l : List α} {m : α} : m ∈ argmax f l → ∀ {a : α}, a ∈ l → f m ≤ f a → index_of m l ≤ index_of a l := sorry

theorem index_of_argmin {α : Type u_1} {β : Type u_2} [linear_order β] [DecidableEq α] {f : α → β} {l : List α} {m : α} : m ∈ argmin f l → ∀ {a : α}, a ∈ l → f a ≤ f m → index_of m l ≤ index_of a l :=
  index_of_argmax

theorem mem_argmax_iff {α : Type u_1} {β : Type u_2} [linear_order β] [DecidableEq α] {f : α → β} {m : α} {l : List α} : m ∈ argmax f l ↔ m ∈ l ∧ (∀ (a : α), a ∈ l → f a ≤ f m) ∧ ∀ (a : α), a ∈ l → f m ≤ f a → index_of m l ≤ index_of a l := sorry

theorem argmax_eq_some_iff {α : Type u_1} {β : Type u_2} [linear_order β] [DecidableEq α] {f : α → β} {m : α} {l : List α} : argmax f l = some m ↔
  m ∈ l ∧ (∀ (a : α), a ∈ l → f a ≤ f m) ∧ ∀ (a : α), a ∈ l → f m ≤ f a → index_of m l ≤ index_of a l :=
  mem_argmax_iff

theorem mem_argmin_iff {α : Type u_1} {β : Type u_2} [linear_order β] [DecidableEq α] {f : α → β} {m : α} {l : List α} : m ∈ argmin f l ↔ m ∈ l ∧ (∀ (a : α), a ∈ l → f m ≤ f a) ∧ ∀ (a : α), a ∈ l → f a ≤ f m → index_of m l ≤ index_of a l :=
  mem_argmax_iff

theorem argmin_eq_some_iff {α : Type u_1} {β : Type u_2} [linear_order β] [DecidableEq α] {f : α → β} {m : α} {l : List α} : argmin f l = some m ↔
  m ∈ l ∧ (∀ (a : α), a ∈ l → f m ≤ f a) ∧ ∀ (a : α), a ∈ l → f a ≤ f m → index_of m l ≤ index_of a l :=
  mem_argmin_iff

/-- `maximum l` returns an `with_bot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum {α : Type u_1} [linear_order α] (l : List α) : with_bot α :=
  argmax id l

/-- `minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum {α : Type u_1} [linear_order α] (l : List α) : with_top α :=
  argmin id l

@[simp] theorem maximum_nil {α : Type u_1} [linear_order α] : maximum [] = ⊥ :=
  rfl

@[simp] theorem minimum_nil {α : Type u_1} [linear_order α] : minimum [] = ⊤ :=
  rfl

@[simp] theorem maximum_singleton {α : Type u_1} [linear_order α] (a : α) : maximum [a] = ↑a :=
  rfl

@[simp] theorem minimum_singleton {α : Type u_1} [linear_order α] (a : α) : minimum [a] = ↑a :=
  rfl

theorem maximum_mem {α : Type u_1} [linear_order α] {l : List α} {m : α} : maximum l = ↑m → m ∈ l :=
  argmax_mem

theorem minimum_mem {α : Type u_1} [linear_order α] {l : List α} {m : α} : minimum l = ↑m → m ∈ l :=
  argmin_mem

@[simp] theorem maximum_eq_none {α : Type u_1} [linear_order α] {l : List α} : maximum l = none ↔ l = [] :=
  argmax_eq_none

@[simp] theorem minimum_eq_none {α : Type u_1} [linear_order α] {l : List α} : minimum l = none ↔ l = [] :=
  argmin_eq_none

theorem le_maximum_of_mem {α : Type u_1} [linear_order α] {a : α} {m : α} {l : List α} : a ∈ l → maximum l = ↑m → a ≤ m :=
  le_argmax_of_mem

theorem minimum_le_of_mem {α : Type u_1} [linear_order α] {a : α} {m : α} {l : List α} : a ∈ l → minimum l = ↑m → m ≤ a :=
  argmin_le_of_mem

theorem le_maximum_of_mem' {α : Type u_1} [linear_order α] {a : α} {l : List α} (ha : a ∈ l) : ↑a ≤ maximum l := sorry

theorem le_minimum_of_mem' {α : Type u_1} [linear_order α] {a : α} {l : List α} (ha : a ∈ l) : minimum l ≤ ↑a :=
  le_maximum_of_mem' ha

theorem maximum_concat {α : Type u_1} [linear_order α] (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) ↑a := sorry

theorem minimum_concat {α : Type u_1} [linear_order α] (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) ↑a :=
  maximum_concat a l

theorem maximum_cons {α : Type u_1} [linear_order α] (a : α) (l : List α) : maximum (a :: l) = max (↑a) (maximum l) := sorry

theorem minimum_cons {α : Type u_1} [linear_order α] (a : α) (l : List α) : minimum (a :: l) = min (↑a) (minimum l) :=
  maximum_cons a l

theorem maximum_eq_coe_iff {α : Type u_1} [linear_order α] {m : α} {l : List α} : maximum l = ↑m ↔ m ∈ l ∧ ∀ (a : α), a ∈ l → a ≤ m := sorry

theorem minimum_eq_coe_iff {α : Type u_1} [linear_order α] {m : α} {l : List α} : minimum l = ↑m ↔ m ∈ l ∧ ∀ (a : α), a ∈ l → m ≤ a :=
  maximum_eq_coe_iff

