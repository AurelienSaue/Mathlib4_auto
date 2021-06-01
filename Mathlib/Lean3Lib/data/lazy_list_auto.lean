/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default

universes u l v w 

namespace Mathlib

inductive lazy_list (α : Type u) where
| nil : lazy_list α
| cons : α → thunk (lazy_list α) → lazy_list α

namespace lazy_list


def singleton {α : Type u} : α → lazy_list α := sorry

def of_list {α : Type u} : List α → lazy_list α := sorry

def to_list {α : Type u} : lazy_list α → List α := sorry

def head {α : Type u} [Inhabited α] : lazy_list α → α := sorry

def tail {α : Type u} : lazy_list α → lazy_list α := sorry

def append {α : Type u} : lazy_list α → thunk (lazy_list α) → lazy_list α := sorry

def map {α : Type u} {β : Type v} (f : α → β) : lazy_list α → lazy_list β := sorry

def map₂ {α : Type u} {β : Type v} {δ : Type w} (f : α → β → δ) :
    lazy_list α → lazy_list β → lazy_list δ :=
  sorry

def zip {α : Type u} {β : Type v} : lazy_list α → lazy_list β → lazy_list (α × β) := map₂ Prod.mk

def join {α : Type u} : lazy_list (lazy_list α) → lazy_list α := sorry

def for {α : Type u} {β : Type v} (l : lazy_list α) (f : α → β) : lazy_list β := map f l

def approx {α : Type u} : ℕ → lazy_list α → List α := sorry

def filter {α : Type u} (p : α → Prop) [decidable_pred p] : lazy_list α → lazy_list α := sorry

def nth {α : Type u} : lazy_list α → ℕ → Option α := sorry

end Mathlib