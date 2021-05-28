/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Theory of topological rings.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.group
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-- A topological semiring is a semiring where addition and multiplication are continuous. -/
class topological_semiring (α : Type u) [topological_space α] [semiring α] 
extends has_continuous_mul α, has_continuous_add α
where

/-- A topological ring is a ring where the ring operations are continuous. -/
class topological_ring (α : Type u) [topological_space α] [ring α] 
extends has_continuous_mul α, has_continuous_add α
where
  continuous_neg : continuous fun (a : α) => -a

protected instance topological_ring.to_topological_semiring (α : Type u) [topological_space α] [ring α] [t : topological_ring α] : topological_semiring α :=
  topological_semiring.mk

protected instance topological_ring.to_topological_add_group (α : Type u) [topological_space α] [ring α] [t : topological_ring α] : topological_add_group α :=
  topological_add_group.mk topological_ring.continuous_neg

/-- In a topological ring, the left-multiplication `add_monoid_hom` is continuous. -/
theorem mul_left_continuous {α : Type u} [topological_space α] [ring α] [topological_ring α] (x : α) : continuous ⇑(add_monoid_hom.mul_left x) :=
  continuous.mul continuous_const continuous_id

/-- In a topological ring, the right-multiplication `add_monoid_hom` is continuous. -/
theorem mul_right_continuous {α : Type u} [topological_space α] [ring α] [topological_ring α] (x : α) : continuous ⇑(add_monoid_hom.mul_right x) :=
  continuous.mul continuous_id continuous_const

/-- The closure of an ideal in a topological ring as an ideal. -/
def ideal.closure {α : Type u_1} [topological_space α] [comm_ring α] [topological_ring α] (S : ideal α) : ideal α :=
  submodule.mk (closure ↑S) sorry sorry sorry

@[simp] theorem ideal.coe_closure {α : Type u_1} [topological_space α] [comm_ring α] [topological_ring α] (S : ideal α) : ↑(ideal.closure S) = closure ↑S :=
  rfl

protected instance topological_ring_quotient_topology {α : Type u_1} [topological_space α] [comm_ring α] (N : ideal α) : topological_space (ideal.quotient N) :=
  id quotient.topological_space

theorem quotient_ring_saturate {α : Type u_1} [comm_ring α] (N : ideal α) (s : set α) : ⇑(ideal.quotient.mk N) ⁻¹' (⇑(ideal.quotient.mk N) '' s) =
  set.Union fun (x : ↥N) => (fun (y : α) => subtype.val x + y) '' s := sorry

theorem quotient_ring.is_open_map_coe {α : Type u_1} [topological_space α] [comm_ring α] (N : ideal α) [topological_ring α] : is_open_map ⇑(ideal.quotient.mk N) := sorry

theorem quotient_ring.quotient_map_coe_coe {α : Type u_1} [topological_space α] [comm_ring α] (N : ideal α) [topological_ring α] : quotient_map fun (p : α × α) => (coe_fn (ideal.quotient.mk N) (prod.fst p), coe_fn (ideal.quotient.mk N) (prod.snd p)) := sorry

protected instance topological_ring_quotient {α : Type u_1} [topological_space α] [comm_ring α] (N : ideal α) [topological_ring α] : topological_ring (ideal.quotient N) :=
  topological_ring.mk
    (eq.mpr
      ((fun (f f_1 : ideal.quotient N → ideal.quotient N) (e_3 : f = f_1) => congr_arg continuous e_3)
        (fun (a : ideal.quotient N) => -a)
        (quotient.lift (Quot.mk setoid.r ∘ fun (a : α) => -a) (submodule.quotient.has_neg._proof_1 N))
        (Eq.refl fun (a : ideal.quotient N) => -a))
      (continuous_quotient_lift (submodule.quotient.has_neg._proof_1 N)
        (continuous.comp continuous_quot_mk continuous_neg)))

