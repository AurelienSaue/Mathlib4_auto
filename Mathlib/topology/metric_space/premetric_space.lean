/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Premetric spaces.

Author: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.basic
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Premetric spaces

Metric spaces are often defined as quotients of spaces endowed with a "distance"
function satisfying the triangular inequality, but for which `dist x y = 0` does
not imply `x = y`. We call such a space a premetric space.
`dist x y = 0` defines an equivalence relation, and the quotient
is canonically a metric space.
-/

class premetric_space (α : Type u) 
extends has_dist α
where
  dist_self : ∀ (x : α), dist x x = 0
  dist_comm : ∀ (x y : α), dist x y = dist y x
  dist_triangle : ∀ (x y z : α), dist x z ≤ dist x y + dist y z

namespace premetric


protected theorem dist_nonneg {α : Type u} [premetric_space α] {x : α} {y : α} : 0 ≤ dist x y := sorry

/-- The canonical equivalence relation on a premetric space. -/
def dist_setoid (α : Type u) [premetric_space α] : setoid α :=
  setoid.mk (fun (x y : α) => dist x y = 0) sorry

/-- The canonical quotient of a premetric space, identifying points at distance `0`. -/
def metric_quot (α : Type u) [premetric_space α]  :=
  quotient (dist_setoid α)

protected instance has_dist_metric_quot {α : Type u} [premetric_space α] : has_dist (metric_quot α) :=
  has_dist.mk (quotient.lift₂ (fun (p q : α) => dist p q) sorry)

theorem metric_quot_dist_eq {α : Type u} [premetric_space α] (p : α) (q : α) : dist (quotient.mk p) (quotient.mk q) = dist p q :=
  rfl

protected instance metric_space_quot {α : Type u} [premetric_space α] : metric_space (metric_quot α) :=
  metric_space.mk sorry sorry sorry sorry
    (fun (x y : metric_quot α) =>
      ennreal.of_real (quotient.lift₂ (fun (p q : α) => dist p q) has_dist_metric_quot._proof_1 x y))
    (uniform_space_of_dist (quotient.lift₂ (fun (p q : α) => dist p q) has_dist_metric_quot._proof_1) sorry sorry sorry)

