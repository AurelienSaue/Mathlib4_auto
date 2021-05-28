/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Completion of topological groups:
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.uniform_space.completion
import Mathlib.topology.algebra.uniform_group
import PostPort

universes u u_1 v 

namespace Mathlib

protected instance uniform_space.completion.has_zero {α : Type u} [uniform_space α] [HasZero α] : HasZero (uniform_space.completion α) :=
  { zero := ↑0 }

protected instance uniform_space.completion.has_neg {α : Type u} [uniform_space α] [Neg α] : Neg (uniform_space.completion α) :=
  { neg := uniform_space.completion.map fun (a : α) => -a }

protected instance uniform_space.completion.has_add {α : Type u} [uniform_space α] [Add α] : Add (uniform_space.completion α) :=
  { add := uniform_space.completion.map₂ Add.add }

protected instance uniform_space.completion.has_sub {α : Type u} [uniform_space α] [Sub α] : Sub (uniform_space.completion α) :=
  { sub := uniform_space.completion.map₂ Sub.sub }

-- TODO: switch sides once #1103 is fixed

theorem uniform_space.completion.coe_zero {α : Type u} [uniform_space α] [HasZero α] : ↑0 = 0 :=
  rfl

namespace uniform_space.completion


theorem coe_neg {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] (a : α) : ↑(-a) = -↑a :=
  Eq.symm (map_coe uniform_continuous_neg a)

theorem coe_sub {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] (a : α) (b : α) : ↑(a - b) = ↑a - ↑b :=
  Eq.symm (map₂_coe_coe a b Sub.sub uniform_continuous_sub)

theorem coe_add {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] (a : α) (b : α) : ↑(a + b) = ↑a + ↑b :=
  Eq.symm (map₂_coe_coe a b Add.add uniform_continuous_add)

protected instance sub_neg_monoid {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] : sub_neg_monoid (completion α) :=
  sub_neg_monoid.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub

protected instance add_group {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] : add_group (completion α) :=
  add_group.mk sub_neg_monoid.add sorry sub_neg_monoid.zero sorry sorry sub_neg_monoid.neg sub_neg_monoid.sub sorry

protected instance uniform_add_group {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] : uniform_add_group (completion α) :=
  uniform_add_group.mk (uniform_continuous_map₂ Sub.sub)

protected instance is_add_group_hom_coe {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] : is_add_group_hom coe :=
  is_add_group_hom.mk

theorem is_add_group_hom_extension {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] {β : Type v} [uniform_space β] [add_group β] [uniform_add_group β] [complete_space β] [separated_space β] {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.extension f) :=
  (fun (hf : uniform_continuous f) => is_add_group_hom.mk) (uniform_continuous_of_continuous hf)

theorem is_add_group_hom_map {α : Type u_1} [uniform_space α] [add_group α] [uniform_add_group α] {β : Type v} [uniform_space β] [add_group β] [uniform_add_group β] {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.map f) :=
  is_add_group_hom_extension (continuous.comp (continuous_coe β) hf)

protected instance add_comm_group {α : Type u} [uniform_space α] [add_comm_group α] [uniform_add_group α] : add_comm_group (completion α) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry sorry

