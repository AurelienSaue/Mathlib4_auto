/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.basic
import Mathlib.order.omega_complete_partial_order
import Mathlib.PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
# Scott Topological Spaces

A type of topological spaces whose notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/

namespace Scott


/--  -/
def is_ωSup {α : Type u} [preorder α] (c : omega_complete_partial_order.chain α) (x : α) :=
  (∀ (i : ℕ), coe_fn c i ≤ x) ∧ ∀ (y : α), (∀ (i : ℕ), coe_fn c i ≤ y) → x ≤ y

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def is_open (α : Type u) [omega_complete_partial_order α] (s : set α) :=
  omega_complete_partial_order.continuous' fun (x : α) => x ∈ s

theorem is_open_univ (α : Type u) [omega_complete_partial_order α] : is_open α set.univ := sorry

theorem is_open_inter (α : Type u) [omega_complete_partial_order α] (s : set α) (t : set α) :
    is_open α s → is_open α t → is_open α (s ∩ t) :=
  sorry

theorem is_open_sUnion (α : Type u) [omega_complete_partial_order α] (s : set (set α)) :
    (∀ (t : set α), t ∈ s → is_open α t) → is_open α (⋃₀s) :=
  sorry

end Scott


/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
def Scott (α : Type u) := α

protected instance Scott.topological_space (α : Type u) [omega_complete_partial_order α] :
    topological_space (Scott α) :=
  topological_space.mk (Scott.is_open α) (Scott.is_open_univ α) (Scott.is_open_inter α)
    (Scott.is_open_sUnion α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def not_below {α : Type u_1} [omega_complete_partial_order α] (y : Scott α) : set (Scott α) :=
  set_of fun (x : Scott α) => ¬x ≤ y

theorem not_below_is_open {α : Type u_1} [omega_complete_partial_order α] (y : Scott α) :
    is_open (not_below y) :=
  sorry

theorem is_ωSup_ωSup {α : Type u_1} [omega_complete_partial_order α]
    (c : omega_complete_partial_order.chain α) :
    Scott.is_ωSup c (omega_complete_partial_order.ωSup c) :=
  { left := omega_complete_partial_order.le_ωSup c,
    right := omega_complete_partial_order.ωSup_le c }

theorem Scott_continuous_of_continuous {α : Type u_1} {β : Type u_2}
    [omega_complete_partial_order α] [omega_complete_partial_order β] (f : Scott α → Scott β)
    (hf : continuous f) : omega_complete_partial_order.continuous' f :=
  sorry

theorem continuous_of_Scott_continuous {α : Type u_1} {β : Type u_2}
    [omega_complete_partial_order α] [omega_complete_partial_order β] (f : Scott α → Scott β)
    (hf : omega_complete_partial_order.continuous' f) : continuous f :=
  sorry

end Mathlib