/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.forall2
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace list


/- sections -/

theorem mem_sections {α : Type u} {L : List (List α)} {f : List α} : f ∈ sections L ↔ forall₂ has_mem.mem f L := sorry

theorem mem_sections_length {α : Type u} {L : List (List α)} {f : List α} (h : f ∈ sections L) : length f = length L :=
  forall₂_length_eq (iff.mp mem_sections h)

theorem rel_sections {α : Type u} {β : Type v} {r : α → β → Prop} : relator.lift_fun (forall₂ (forall₂ r)) (forall₂ (forall₂ r)) sections sections := sorry

