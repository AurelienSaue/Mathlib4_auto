/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.lie.basic
import Mathlib.linear_algebra.direct_sum.finsupp
import PostPort

universes w w₁ v u 

namespace Mathlib

/-!
# Direct sums of Lie algebras and Lie modules

Direct sums of Lie algebras and Lie modules carry natural algbebra and module structures.

## Tags

lie algebra, lie module, direct sum
-/

namespace direct_sum


/-! The direct sum of Lie modules over a fixed Lie algebra carries a natural Lie module
structure. -/

protected instance lie_ring_module {ι : Type v} {L : Type w₁} {M : ι → Type w} [lie_ring L] [(i : ι) → add_comm_group (M i)] [(i : ι) → lie_ring_module L (M i)] : lie_ring_module L (direct_sum ι fun (i : ι) => M i) :=
  lie_ring_module.mk sorry sorry sorry

@[simp] theorem lie_module_bracket_apply {ι : Type v} {L : Type w₁} {M : ι → Type w} [lie_ring L] [(i : ι) → add_comm_group (M i)] [(i : ι) → lie_ring_module L (M i)] (x : L) (m : direct_sum ι fun (i : ι) => M i) (i : ι) : coe_fn (has_bracket.bracket x m) i = has_bracket.bracket x (coe_fn m i) :=
  dfinsupp.map_range_apply (fun (i : ι) (m' : M i) => has_bracket.bracket x m') (lie_ring_module._proof_1 x) m i

protected instance lie_module {R : Type u} {ι : Type v} [comm_ring R] {L : Type w₁} {M : ι → Type w} [lie_ring L] [lie_algebra R L] [(i : ι) → add_comm_group (M i)] [(i : ι) → module R (M i)] [(i : ι) → lie_ring_module L (M i)] [(i : ι) → lie_module R L (M i)] : lie_module R L (direct_sum ι fun (i : ι) => M i) :=
  lie_module.mk sorry sorry

/-- The inclusion of each component into a direct sum as a morphism of Lie modules. -/
def lie_module_of (R : Type u) (ι : Type v) [comm_ring R] (L : Type w₁) (M : ι → Type w) [lie_ring L] [lie_algebra R L] [(i : ι) → add_comm_group (M i)] [(i : ι) → module R (M i)] [(i : ι) → lie_ring_module L (M i)] [(i : ι) → lie_module R L (M i)] [DecidableEq ι] (j : ι) : lie_module_hom R L (M j) (direct_sum ι fun (i : ι) => M i) :=
  lie_module_hom.mk (linear_map.to_fun (lof R ι M j)) sorry sorry sorry

/-- The projection map onto one component, as a morphism of Lie modules. -/
def lie_module_component (R : Type u) (ι : Type v) [comm_ring R] (L : Type w₁) (M : ι → Type w) [lie_ring L] [lie_algebra R L] [(i : ι) → add_comm_group (M i)] [(i : ι) → module R (M i)] [(i : ι) → lie_ring_module L (M i)] [(i : ι) → lie_module R L (M i)] (j : ι) : lie_module_hom R L (direct_sum ι fun (i : ι) => M i) (M j) :=
  lie_module_hom.mk (linear_map.to_fun (component R ι M j)) sorry sorry sorry

/-! The direct sum of Lie algebras carries a natural Lie algebra structure. -/

protected instance lie_ring {ι : Type v} {L : ι → Type w} [(i : ι) → lie_ring (L i)] : lie_ring (direct_sum ι fun (i : ι) => L i) :=
  lie_ring.mk sorry sorry sorry sorry

@[simp] theorem bracket_apply {ι : Type v} {L : ι → Type w} [(i : ι) → lie_ring (L i)] (x : direct_sum ι fun (i : ι) => L i) (y : direct_sum ι fun (i : ι) => L i) (i : ι) : coe_fn (has_bracket.bracket x y) i = has_bracket.bracket (coe_fn x i) (coe_fn y i) :=
  dfinsupp.zip_with_apply (fun (i : ι) (x y : L i) => has_bracket.bracket x y) lie_ring._proof_7 x y i

protected instance lie_algebra {R : Type u} {ι : Type v} [comm_ring R] {L : ι → Type w} [(i : ι) → lie_ring (L i)] [(i : ι) → lie_algebra R (L i)] : lie_algebra R (direct_sum ι fun (i : ι) => L i) :=
  lie_algebra.mk sorry

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
def lie_algebra_of (R : Type u) (ι : Type v) [comm_ring R] (L : ι → Type w) [(i : ι) → lie_ring (L i)] [(i : ι) → lie_algebra R (L i)] [DecidableEq ι] (j : ι) : lie_algebra.morphism R (L j) (direct_sum ι fun (i : ι) => L i) :=
  lie_algebra.morphism.mk (linear_map.to_fun (lof R ι L j)) sorry sorry sorry

/-- The projection map onto one component, as a morphism of Lie algebras. -/
def lie_algebra_component (R : Type u) (ι : Type v) [comm_ring R] (L : ι → Type w) [(i : ι) → lie_ring (L i)] [(i : ι) → lie_algebra R (L i)] (j : ι) : lie_algebra.morphism R (direct_sum ι fun (i : ι) => L i) (L j) :=
  lie_algebra.morphism.mk (linear_map.to_fun (component R ι L j)) sorry sorry sorry

