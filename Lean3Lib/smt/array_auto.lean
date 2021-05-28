/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.default
import PostPort

universes u v 

namespace Mathlib

namespace smt


def array (α : Type u) (β : Type v)  :=
  α → β

def select {α : Type u} {β : Type v} (a : array α β) (i : α) : β :=
  a i

theorem arrayext {α : Type u} {β : Type v} (a₁ : array α β) (a₂ : array α β) : (∀ (i : α), select a₁ i = select a₂ i) → a₁ = a₂ :=
  funext

def store {α : Type u} {β : Type v} [DecidableEq α] (a : array α β) (i : α) (v : β) : array α β :=
  fun (j : α) => ite (j = i) v (select a j)

@[simp] theorem select_store {α : Type u} {β : Type v} [DecidableEq α] (a : array α β) (i : α) (v : β) : select (store a i v) i = v := sorry

@[simp] theorem select_store_ne {α : Type u} {β : Type v} [DecidableEq α] (a : array α β) (i : α) (j : α) (v : β) : j ≠ i → select (store a i v) j = select a j := sorry

