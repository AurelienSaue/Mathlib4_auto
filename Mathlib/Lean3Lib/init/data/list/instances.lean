/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.list.lemmas
 

universes u_1 u 

namespace Mathlib

protected instance list.monad : Monad List :=
  { toApplicative :=
      { toFunctor := { map := list.map, mapConst := fun (α β : Type u_1) => list.map ∘ function.const β },
        toPure := { pure := list.ret },
        toSeq :=
          { seq :=
              fun (α β : Type u_1) (f : List (α → β)) (x : List α) => list.bind f fun (_x : α → β) => list.map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : List α) (b : List β) =>
                (fun (α β : Type u_1) (f : List (α → β)) (x : List α) => list.bind f fun (_x : α → β) => list.map _x x) β
                  α (list.map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : List α) (b : List β) =>
                (fun (α β : Type u_1) (f : List (α → β)) (x : List α) => list.bind f fun (_x : α → β) => list.map _x x) β
                  β (list.map (function.const α id) a) b } },
    toBind := { bind := list.bind } }

protected instance list.is_lawful_monad : is_lawful_monad List := sorry

protected instance list.alternative : alternative List :=
  alternative.mk List.nil

namespace list


protected instance bin_tree_to_list {α : Type u} : has_coe (bin_tree α) (List α) :=
  has_coe.mk bin_tree.to_list

protected instance decidable_bex {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : Decidable (∃ (x : α), ∃ (H : x ∈ l), p x) :=
  sorry

protected instance decidable_ball {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : Decidable (∀ (x : α), x ∈ l → p x) :=
  dite (∃ (x : α), ∃ (H : x ∈ l), ¬p x) (fun (h : ∃ (x : α), ∃ (H : x ∈ l), ¬p x) => isFalse sorry)
    fun (h : ¬∃ (x : α), ∃ (H : x ∈ l), ¬p x) => is_true sorry

