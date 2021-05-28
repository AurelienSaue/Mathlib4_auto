/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.perm.basic
import Mathlib.data.fintype.basic
import Mathlib.group_theory.subgroup
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Lemmas about subgroups within the permutations (self-equivalences) of a type `α`

This file provides extra lemmas about some `subgroup`s that exist within `equiv.perm α`.
`group_theory.subgroup` depends on `group_theory.perm.basic`, so these need to be in a separate
file.
-/

namespace equiv


namespace perm


@[simp] theorem sum_congr_hom.card_range {α : Type u_1} {β : Type u_2} [fintype ↥(monoid_hom.range (sum_congr_hom α β))] [fintype (perm α × perm β)] : fintype.card ↥(monoid_hom.range (sum_congr_hom α β)) = fintype.card (perm α × perm β) :=
  iff.mpr fintype.card_eq (Nonempty.intro (equiv.symm (set.range (⇑(sum_congr_hom α β)) sum_congr_hom_injective)))

@[simp] theorem sigma_congr_right_hom.card_range {α : Type u_1} {β : α → Type u_2} [fintype ↥(monoid_hom.range (sigma_congr_right_hom β))] [fintype ((a : α) → perm (β a))] : fintype.card ↥(monoid_hom.range (sigma_congr_right_hom β)) = fintype.card ((a : α) → perm (β a)) :=
  iff.mpr fintype.card_eq
    (Nonempty.intro (equiv.symm (set.range (⇑(sigma_congr_right_hom β)) sigma_congr_right_hom_injective)))

