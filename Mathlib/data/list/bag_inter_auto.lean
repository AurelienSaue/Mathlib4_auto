/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace list


/- bag_inter -/

@[simp] theorem nil_bag_inter {α : Type u} [DecidableEq α] (l : List α) :
    list.bag_inter [] l = [] :=
  list.cases_on l (Eq.refl (list.bag_inter [] []))
    fun (l_hd : α) (l_tl : List α) => Eq.refl (list.bag_inter [] (l_hd :: l_tl))

@[simp] theorem bag_inter_nil {α : Type u} [DecidableEq α] (l : List α) :
    list.bag_inter l [] = [] :=
  list.cases_on l (Eq.refl (list.bag_inter [] []))
    fun (l_hd : α) (l_tl : List α) => Eq.refl (list.bag_inter (l_hd :: l_tl) [])

@[simp] theorem cons_bag_inter_of_pos {α : Type u} [DecidableEq α] {a : α} (l₁ : List α)
    {l₂ : List α} (h : a ∈ l₂) :
    list.bag_inter (a :: l₁) l₂ = a :: list.bag_inter l₁ (list.erase l₂ a) :=
  list.cases_on l₂ (fun (h : a ∈ []) => if_pos h)
    (fun (l₂_hd : α) (l₂_tl : List α) (h : a ∈ l₂_hd :: l₂_tl) => if_pos h) h

@[simp] theorem cons_bag_inter_of_neg {α : Type u} [DecidableEq α] {a : α} (l₁ : List α)
    {l₂ : List α} (h : ¬a ∈ l₂) : list.bag_inter (a :: l₁) l₂ = list.bag_inter l₁ l₂ :=
  sorry

@[simp] theorem mem_bag_inter {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} :
    a ∈ list.bag_inter l₁ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ :=
  sorry

@[simp] theorem count_bag_inter {α : Type u} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} :
    count a (list.bag_inter l₁ l₂) = min (count a l₁) (count a l₂) :=
  sorry

theorem bag_inter_sublist_left {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) :
    list.bag_inter l₁ l₂ <+ l₁ :=
  sorry

theorem bag_inter_nil_iff_inter_nil {α : Type u} [DecidableEq α] (l₁ : List α) (l₂ : List α) :
    list.bag_inter l₁ l₂ = [] ↔ l₁ ∩ l₂ = [] :=
  sorry

end Mathlib