/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes

Defining a group given by generators and relations
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.free_group
import Mathlib.group_theory.quotient_group
import PostPort

namespace Mathlib

/-- Given a set of relations, rels, over a type α, presented_group constructs the group with
generators α and relations rels as a quotient of free_group α.-/
def presented_group {α : Type} (rels : set (free_group α))  :=
  quotient_group.quotient (subgroup.normal_closure rels)

namespace presented_group


protected instance group {α : Type} (rels : set (free_group α)) : group (presented_group rels) :=
  quotient_group.quotient.group (subgroup.normal_closure rels)

/-- `of x` is the canonical map from α to a presented group with generators α. The term x is
mapped to the equivalence class of the image of x in free_group α. -/
def of {α : Type} {rels : set (free_group α)} (x : α) : presented_group rels :=
  quotient_group.mk (free_group.of x)

/-
Presented groups satisfy a universal property. If β is a group and f : α → β is a map such that the
images of f satisfy all the given relations, then f extends uniquely to a group homomorphism from
presented_group rels to β
-/

theorem closure_rels_subset_ker {α : Type} {β : Type} [group β] {f : α → β} {rels : set (free_group α)} (h : ∀ (r : free_group α), r ∈ rels → coe_fn (free_group.to_group f) r = 1) : subgroup.normal_closure rels ≤ monoid_hom.ker (free_group.to_group f) :=
  subgroup.normal_closure_le_normal
    fun (x : free_group α) (w : x ∈ rels) => iff.mpr (monoid_hom.mem_ker (free_group.to_group f)) (h x w)

theorem to_group_eq_one_of_mem_closure {α : Type} {β : Type} [group β] {f : α → β} {rels : set (free_group α)} (h : ∀ (r : free_group α), r ∈ rels → coe_fn (free_group.to_group f) r = 1) (x : free_group α) (H : x ∈ subgroup.normal_closure rels) : coe_fn (free_group.to_group f) x = 1 :=
  iff.mp (monoid_hom.mem_ker (free_group.to_group f)) (closure_rels_subset_ker h w)

/-- The extension of a map f : α → β that satisfies the given relations to a group homomorphism
from presented_group rels → β. -/
def to_group {α : Type} {β : Type} [group β] {f : α → β} {rels : set (free_group α)} (h : ∀ (r : free_group α), r ∈ rels → coe_fn (free_group.to_group f) r = 1) : presented_group rels →* β :=
  quotient_group.lift (subgroup.normal_closure rels) (monoid_hom.of ⇑(free_group.to_group f))
    (to_group_eq_one_of_mem_closure h)

@[simp] theorem to_group.of {α : Type} {β : Type} [group β] {f : α → β} {rels : set (free_group α)} (h : ∀ (r : free_group α), r ∈ rels → coe_fn (free_group.to_group f) r = 1) {x : α} : coe_fn (to_group h) (of x) = f x :=
  free_group.to_group.of

theorem to_group.unique {α : Type} {β : Type} [group β] {f : α → β} {rels : set (free_group α)} (h : ∀ (r : free_group α), r ∈ rels → coe_fn (free_group.to_group f) r = 1) (g : presented_group rels →* β) (hg : ∀ (x : α), coe_fn g (of x) = f x) {x : presented_group rels} : coe_fn g x = coe_fn (to_group h) x :=
  quotient_group.induction_on x
    fun (_x : free_group α) =>
      free_group.to_group.unique (monoid_hom.comp g (quotient_group.mk' (subgroup.normal_closure rels))) hg

protected instance inhabited {α : Type} (rels : set (free_group α)) : Inhabited (presented_group rels) :=
  { default := 1 }

