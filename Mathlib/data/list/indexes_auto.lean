/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.data.list.defs
import Mathlib.logic.basic
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

namespace list


/-- Specification of `foldr_with_index_aux`. -/
def foldr_with_index_aux_spec {α : Type u} {β : Type v} (f : ℕ → α → β → β) (start : ℕ) (b : β)
    (as : List α) : β :=
  foldr (function.uncurry f) b (enum_from start as)

theorem foldr_with_index_aux_spec_cons {α : Type u} {β : Type v} (f : ℕ → α → β → β) (start : ℕ)
    (b : β) (a : α) (as : List α) :
    foldr_with_index_aux_spec f start b (a :: as) =
        f start a (foldr_with_index_aux_spec f (start + 1) b as) :=
  rfl

theorem foldr_with_index_aux_eq_foldr_with_index_aux_spec {α : Type u} {β : Type v}
    (f : ℕ → α → β → β) (start : ℕ) (b : β) (as : List α) :
    foldr_with_index_aux f start b as = foldr_with_index_aux_spec f start b as :=
  sorry

theorem foldr_with_index_eq_foldr_enum {α : Type u} {β : Type v} (f : ℕ → α → β → β) (b : β)
    (as : List α) : foldr_with_index f b as = foldr (function.uncurry f) b (enum as) :=
  sorry

theorem indexes_values_eq_filter_enum {α : Type u} (p : α → Prop) [decidable_pred p] (as : List α) :
    indexes_values p as = filter (p ∘ prod.snd) (enum as) :=
  sorry

theorem find_indexes_eq_map_indexes_values {α : Type u} (p : α → Prop) [decidable_pred p]
    (as : List α) : find_indexes p as = map prod.fst (indexes_values p as) :=
  sorry

/-- Specification of `foldl_with_index_aux`. -/
def foldl_with_index_aux_spec {α : Type u} {β : Type v} (f : ℕ → α → β → α) (start : ℕ) (a : α)
    (bs : List β) : α :=
  foldl (fun (a : α) (p : ℕ × β) => f (prod.fst p) a (prod.snd p)) a (enum_from start bs)

theorem foldl_with_index_aux_spec_cons {α : Type u} {β : Type v} (f : ℕ → α → β → α) (start : ℕ)
    (a : α) (b : β) (bs : List β) :
    foldl_with_index_aux_spec f start a (b :: bs) =
        foldl_with_index_aux_spec f (start + 1) (f start a b) bs :=
  rfl

theorem foldl_with_index_aux_eq_foldl_with_index_aux_spec {α : Type u} {β : Type v}
    (f : ℕ → α → β → α) (start : ℕ) (a : α) (bs : List β) :
    foldl_with_index_aux f start a bs = foldl_with_index_aux_spec f start a bs :=
  sorry

theorem foldl_with_index_eq_foldl_enum {α : Type u} {β : Type v} (f : ℕ → α → β → α) (a : α)
    (bs : List β) :
    foldl_with_index f a bs =
        foldl (fun (a : α) (p : ℕ × β) => f (prod.fst p) a (prod.snd p)) a (enum bs) :=
  sorry

theorem mfoldr_with_index_eq_mfoldr_enum {m : Type u → Type v} [Monad m] {α : Type u_1} {β : Type u}
    (f : ℕ → α → β → m β) (b : β) (as : List α) :
    mfoldr_with_index f b as = mfoldr (function.uncurry f) b (enum as) :=
  sorry

theorem mfoldl_with_index_eq_mfoldl_enum {m : Type u → Type v} [Monad m] [is_lawful_monad m]
    {α : Type u_1} {β : Type u} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    mfoldl_with_index f b as =
        mfoldl (fun (b : β) (p : ℕ × α) => f (prod.fst p) b (prod.snd p)) b (enum as) :=
  sorry

/-- Specification of `mmap_with_index_aux`. -/
def mmap_with_index_aux_spec {m : Type u → Type v} [Applicative m] {α : Type u_1} {β : Type u}
    (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  list.traverse (function.uncurry f) (enum_from start as)

-- Note: `traverse` the class method would require a less universe-polymorphic

-- `m : Type u → Type u`.

theorem mmap_with_index_aux_spec_cons {m : Type u → Type v} [Applicative m] {α : Type u_1}
    {β : Type u} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mmap_with_index_aux_spec f start (a :: as) =
        List.cons <$> f start a <*> mmap_with_index_aux_spec f (start + 1) as :=
  rfl

theorem mmap_with_index_aux_eq_mmap_with_index_aux_spec {m : Type u → Type v} [Applicative m]
    {α : Type u_1} {β : Type u} (f : ℕ → α → m β) (start : ℕ) (as : List α) :
    mmap_with_index_aux f start as = mmap_with_index_aux_spec f start as :=
  sorry

theorem mmap_with_index_eq_mmap_enum {m : Type u → Type v} [Applicative m] {α : Type u_1}
    {β : Type u} (f : ℕ → α → m β) (as : List α) :
    mmap_with_index f as = list.traverse (function.uncurry f) (enum as) :=
  sorry

theorem mmap_with_index'_aux_eq_mmap_with_index_aux {m : Type u → Type v} [Applicative m]
    [is_lawful_applicative m] {α : Type u_1} (f : ℕ → α → m PUnit) (start : ℕ) (as : List α) :
    mmap_with_index'_aux f start as = mmap_with_index_aux f start as *> pure PUnit.unit :=
  sorry

theorem mmap_with_index'_eq_mmap_with_index {m : Type u → Type v} [Applicative m]
    [is_lawful_applicative m] {α : Type u_1} (f : ℕ → α → m PUnit) (as : List α) :
    mmap_with_index' f as = mmap_with_index f as *> pure PUnit.unit :=
  mmap_with_index'_aux_eq_mmap_with_index_aux f 0 as

end Mathlib