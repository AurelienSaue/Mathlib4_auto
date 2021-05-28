/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.operator_norm
import Mathlib.analysis.normed_space.add_torsor
import Mathlib.topology.bases
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.tactic.omega.default
import Mathlib.PostPort

universes u v w x u_1 u_2 

namespace Mathlib

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nondiscrete field, in finite dimension, all norms are equivalent and all linear maps
are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional space over a
  complete field is continuous.
* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
theorem linear_map.continuous_on_pi {ι : Type w} [fintype ι] {𝕜 : Type u} [normed_field 𝕜] {E : Type v} [add_comm_group E] [vector_space 𝕜 E] [topological_space E] [topological_add_group E] [topological_vector_space 𝕜 E] (f : linear_map 𝕜 (ι → 𝕜) E) : continuous ⇑f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (continuous ⇑f)) (funext fun (x : ι → 𝕜) => linear_map.pi_apply_eq_sum_univ f x)))
    (continuous_finset_sum finset.univ
      fun (i : ι) (hi : i ∈ finset.univ) => continuous.smul (continuous_apply i) continuous_const)

/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
theorem continuous_equiv_fun_basis {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] [complete_space 𝕜] {ι : Type v} [fintype ι] (ξ : ι → E) (hξ : is_basis 𝕜 ξ) : continuous ⇑(is_basis.equiv_fun hξ) := sorry

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem linear_map.continuous_of_finite_dimensional {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F' : Type x} [add_comm_group F'] [vector_space 𝕜 F'] [topological_space F'] [topological_add_group F'] [topological_vector_space 𝕜 F'] [complete_space 𝕜] [finite_dimensional 𝕜 E] (f : linear_map 𝕜 E F') : continuous ⇑f := sorry

theorem affine_map.continuous_of_finite_dimensional {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] {PE : Type u_1} {PF : Type u_2} [metric_space PE] [normed_add_torsor E PE] [metric_space PF] [normed_add_torsor F PF] [finite_dimensional 𝕜 E] (f : affine_map 𝕜 PE PF) : continuous ⇑f :=
  iff.mp affine_map.continuous_linear_iff (linear_map.continuous_of_finite_dimensional (affine_map.linear f))

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def linear_map.to_continuous_linear_map {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F' : Type x} [add_comm_group F'] [vector_space 𝕜 F'] [topological_space F'] [topological_add_group F'] [topological_vector_space 𝕜 F'] [complete_space 𝕜] [finite_dimensional 𝕜 E] (f : linear_map 𝕜 E F') : continuous_linear_map 𝕜 E F' :=
  continuous_linear_map.mk (linear_map.mk (linear_map.to_fun f) sorry sorry)

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional space. -/
def linear_equiv.to_continuous_linear_equiv {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] [finite_dimensional 𝕜 E] (e : linear_equiv 𝕜 E F) : continuous_linear_equiv 𝕜 E F :=
  continuous_linear_equiv.mk (linear_equiv.mk (linear_equiv.to_fun e) sorry sorry (linear_equiv.inv_fun e) sorry sorry)

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if they have the same
(finite) dimension. -/
theorem finite_dimensional.nonempty_continuous_linear_equiv_of_findim_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] (cond : finite_dimensional.findim 𝕜 E = finite_dimensional.findim 𝕜 F) : Nonempty (continuous_linear_equiv 𝕜 E F) :=
  nonempty.map linear_equiv.to_continuous_linear_equiv (finite_dimensional.nonempty_linear_equiv_of_findim_eq cond)

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if and only if they
have the same (finite) dimension. -/
theorem finite_dimensional.nonempty_continuous_linear_equiv_iff_findim_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] : Nonempty (continuous_linear_equiv 𝕜 E F) ↔ finite_dimensional.findim 𝕜 E = finite_dimensional.findim 𝕜 F := sorry

/-- A continuous linear equivalence between two finite-dimensional normed spaces of the same
(finite) dimension. -/
def continuous_linear_equiv.of_findim_eq {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] (cond : finite_dimensional.findim 𝕜 E = finite_dimensional.findim 𝕜 F) : continuous_linear_equiv 𝕜 E F :=
  linear_equiv.to_continuous_linear_equiv (finite_dimensional.linear_equiv.of_findim_eq E F cond)

/-- Construct a continuous linear map given the value at a finite basis. -/
def is_basis.constrL {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] {ι : Type u_1} [fintype ι] {v : ι → E} (hv : is_basis 𝕜 v) (f : ι → F) : continuous_linear_map 𝕜 E F :=
  linear_map.to_continuous_linear_map (is_basis.constr hv f)

@[simp] theorem is_basis.coe_constrL {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {E : Type v} [normed_group E] [normed_space 𝕜 E] {F : Type w} [normed_group F] [normed_space 𝕜 F] [complete_space 𝕜] {ι : Type u_1} [fintype ι] {v : ι → E} (hv : is_basis 𝕜 v) (f : ι → F) : ↑(is_basis.constrL hv f) = is_basis.constr hv f :=
  rfl

/-- The continuous linear