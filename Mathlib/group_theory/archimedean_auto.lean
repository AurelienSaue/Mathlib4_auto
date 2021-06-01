/-
Copyright (c) 2020 Heather Macbeth, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.subgroup
import Mathlib.algebra.archimedean
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Archimedean groups

This file proves a few facts about ordered groups which satisfy the `archimedean` property, that is:
`class archimedean (α) [ordered_add_comm_monoid α] : Prop :=`
`(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n •ℕ y)`

They are placed here in a separate file (rather than incorporated as a continuation of
`algebra.archimedean`) because they rely on some imports from `group_theory` -- bundled subgroups
in particular.

The main result is `add_subgroup.cyclic_of_min`:  a subgroup of a decidable archimedean abelian
group is cyclic, if its set of positive elements has a minimal element.

This result is used in this file to deduce `int.subgroup_cyclic`, proving that every subgroup of `ℤ`
is cyclic.  (There are several other methods one could use to prove this fact, including more purely
algebraic methods, but none seem to exist in mathlib as of writing.  The closest is
`subgroup.is_cyclic`, but that has not been transferred to `add_subgroup`.)

The result is also used in `topology.instances.real` as an ingredient in the classification of
subgroups of `ℝ`.
-/

/-- Given a subgroup `H` of a decidable linearly ordered archimedean abelian group `G`, if there
exists a minimal element `a` of `H ∩ G_{>0}` then `H` is generated by `a`. -/
theorem add_subgroup.cyclic_of_min {G : Type u_1} [linear_ordered_add_comm_group G] [archimedean G]
    {H : add_subgroup G} {a : G} (ha : is_least (set_of fun (g : G) => g ∈ H ∧ 0 < g) a) :
    H = add_subgroup.closure (singleton a) :=
  sorry

/-- Every subgroup of `ℤ` is cyclic. -/
theorem int.subgroup_cyclic (H : add_subgroup ℤ) :
    ∃ (a : ℤ), H = add_subgroup.closure (singleton a) :=
  sorry

end Mathlib