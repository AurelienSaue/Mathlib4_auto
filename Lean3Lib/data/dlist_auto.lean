/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.default
import PostPort

universes u l 

namespace Mathlib

/--
A difference list is a function that, given a list, returns the original
contents of the difference list prepended to the given list.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/
structure dlist (α : Type u) 
where
  apply : List α → List α
  invariant : ∀ (l : List α), apply l = apply [] ++ l

namespace dlist


/-- Convert a list to a dlist -/
def of_list {α : Type u} (l : List α) : dlist α :=
  mk (append l) sorry

/-- Convert a lazily-evaluated list to a dlist -/
def lazy_of_list {α : Type u} (l : thunk (List α)) : dlist α :=
  mk (fun (xs : List α) => l Unit.unit ++ xs) sorry

/-- Convert a dlist to a list -/
def to_list {α : Type u} : dlist α → List α :=
  sorry

/--  Create a dlist containing no elements -/
def empty {α : Type u} : dlist α :=
  mk id sorry

/-- Create dlist with a single element -/
def singleton {α : Type u} (x : α) : dlist α :=
  mk (List.cons x) sorry

/-- `O(1)` Prepend a single element to a dlist -/
def cons {α : Type u} (x : α) : dlist α → dlist α :=
  sorry

/-- `O(1)` Append a single element to a dlist -/
def concat {α : Type u} (x : α) : dlist α → dlist α :=
  sorry

/-- `O(1)` Append dlists -/
protected def append {α : Type u} : dlist α → dlist α → dlist α :=
  sorry

protected instance has_append {α : Type u} : Append (dlist α) :=
  { append := dlist.append }

theorem to_list_of_list {α : Type u} (l : List α) : to_list (of_list l) = l := sorry

theorem of_list_to_list {α : Type u} (l : dlist α) : of_list (to_list l) = l := sorry

theorem to_list_empty {α : Type u} : to_list empty = [] := sorry

theorem to_list_singleton {α : Type u} (x : α) : to_list (singleton x) = [x] := sorry

theorem to_list_append {α : Type u} (l₁ : dlist α) (l₂ : dlist α) : to_list (l₁ ++ l₂) = to_list l₁ ++ to_list l₂ := sorry

theorem to_list_cons {α : Type u} (x : α) (l : dlist α) : to_list (cons x l) = x :: to_list l := sorry

theorem to_list_concat {α : Type u} (x : α) (l : dlist α) : to_list (concat x l) = to_list l ++ [x] := sorry

