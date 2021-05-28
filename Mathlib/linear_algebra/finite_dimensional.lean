/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.dimension
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.algebra.algebra.subalgebra
import Mathlib.PostPort

universes u_1 u_2 u v w v' 

namespace Mathlib

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a field `K`. There are (at least) three equivalent definitions of
finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `finite_dimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the third point of view, i.e., as `is_noetherian`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `finite_dimensional`):

- `exists_is_basis_finite` states that a finite-dimensional vector space has a finite basis
- `of_fintype_basis` states that the existence of a basis indexed by a finite type implies
  finite-dimensionality
- `of_finset_basis` states that the existence of a basis indexed by a `finset` implies
  finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a finite set implies
  finite-dimensionality
- `iff_fg` states that the space is finite-dimensional if and only if it is finitely generated

Also defined is `findim`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `dim`, which returns a `cardinal`. When the space has infinite dimension, its
`findim` is by convention set to `0`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `findim_quotient_add_findim`)
- linear equivs, in `linear_equiv.finite_dimensional` and `linear_equiv.findim_eq`
- image under a linear map (the rank-nullity formula is in `findim_range_add_findim_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `mul_eq_one_comm` and
`comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `submodule.fg_iff_finite_dimensional`.
-/

/-- `finite_dimensional` vector spaces are defined to be noetherian modules.
Use `finite_dimensional.iff_fg` or `finite_dimensional.of_fintype_basis` to prove finite dimension
from a conventional definition. -/
def finite_dimensional (K : Type u_1) (V : Type u_2) [field K] [add_comm_group V] [vector_space K V]  :=
  is_noetherian K V

namespace finite_dimensional


/-- A vector space is finite-dimensional if and only if its dimension (as a cardinal) is strictly
less than the first infinite cardinal `omega`. -/
theorem finite_dimensional_iff_dim_lt_omega {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] : finite_dimensional K V ↔ vector_space.dim K V < cardinal.omega := sorry

/-- The dimension of a finite-dimensional vector space, as a cardinal, is strictly less than the
first infinite cardinal `omega`. -/
theorem dim_lt_omega (K : Type u_1) (V : Type v) [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : vector_space.dim K V < cardinal.omega :=
  iff.mp finite_dimensional_iff_dim_lt_omega

/-- In a finite dimensional space, there exists a finite basis. A basis is in general given as a
function from an arbitrary type to the vector space. Here, we think of a basis as a set (instead of
a function), and use as parametrizing type this set (and as a function the coercion
  `coe : s → V`).
-/
theorem exists_is_basis_finite (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : ∃ (s : set V), is_basis K coe ∧ set.finite s :=
  Exists.dcases_on (exists_is_basis K V)
    fun (s : set V) (hs : is_basis K fun (i : ↥s) => ↑i) =>
      Exists.intro s { left := hs, right := finite_of_linear_independent (and.left hs) }

/-- In a finite dimensional space, there exists a finite basis. Provides the basis as a finset.
This is in contrast to `exists_is_basis_finite`, which provides a set and a `set.finite`.
-/
theorem exists_is_basis_finset (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : ∃ (b : finset V), is_basis K coe := sorry

/-- A finite dimensional vector space over a finite field is finite -/
def fintype_of_fintype (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] [fintype K] [finite_dimensional K V] : fintype V :=
  module.fintype_of_fintype sorry

/-- A vector space is finite-dimensional if and only if it is finitely generated. As the
finitely-generated property is a property of submodules, we formulate this in terms of the
maximal submodule, equal to the whole space as a set by definition.-/
theorem iff_fg {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] : finite_dimensional K V ↔ submodule.fg ⊤ := sorry

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
theorem of_fintype_basis {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) : finite_dimensional K V := sorry

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
theorem of_finite_basis {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} {s : set ι} {b : ↥s → V} (h : is_basis K b) (hs : set.finite s) : finite_dimensional K V :=
  of_fintype_basis h

/-- If a vector space has a finite basis, then it is finite-dimensional, finset style. -/
theorem of_finset_basis {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} {s : finset ι} {b : ↥↑s → V} (h : is_basis K b) : finite_dimensional K V :=
  of_finite_basis h (finset.finite_to_set s)

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
protected instance finite_dimensional_submodule {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (S : submodule K V) : finite_dimensional K ↥S :=
  iff.mpr finite_dimensional_iff_dim_lt_omega (lt_of_le_of_lt (dim_submodule_le S) (dim_lt_omega K V))

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
protected instance finite_dimensional_quotient {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (S : submodule K V) : finite_dimensional K (submodule.quotient S) :=
  iff.mpr finite_dimensional_iff_dim_lt_omega (lt_of_le_of_lt (dim_quotient_le S) (dim_lt_omega K V))

/-- The dimension of a finite-dimensional vector space as a natural number. Defined by convention to
be `0` if the space is infinite-dimensional. -/
def findim (K : Type u_1) (V : Type v) [field K] [add_comm_group V] [vector_space K V] : ℕ :=
  dite (vector_space.dim K V < cardinal.omega) (fun (h : vector_space.dim K V < cardinal.omega) => classical.some sorry)
    fun (h : ¬vector_space.dim K V < cardinal.omega) => 0

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its `findim`. -/
theorem findim_eq_dim (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : ↑(findim K V) = vector_space.dim K V :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(findim K V) = vector_space.dim K V)) (dif_pos (dim_lt_omega K V))))
    (Eq.symm (classical.some_spec (iff.mp cardinal.lt_omega (dim_lt_omega K V))))

theorem findim_of_infinite_dimensional {K : Type u_1} {V : Type u_2} [field K] [add_comm_group V] [vector_space K V] (h : ¬finite_dimensional K V) : findim K V = 0 :=
  dif_neg (mt (iff.mpr finite_dimensional_iff_dim_lt_omega) h)

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
theorem dim_eq_card_basis {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) : vector_space.dim K V = ↑(fintype.card ι) := sorry

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
theorem findim_eq_card_basis {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) : findim K V = fintype.card ι :=
  eq.mp (propext cardinal.nat_cast_inj)
    (eq.mp (Eq._oldrec (Eq.refl (vector_space.dim K V = ↑(fintype.card ι))) (Eq.symm (findim_eq_dim K V)))
      (dim_eq_card_basis h))

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`findim`. -/
theorem findim_eq_card_basis' {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {ι : Type w} {b : ι → V} (h : is_basis K b) : ↑(findim K V) = cardinal.mk ι := sorry

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. This lemma uses a `finset` instead of indexed types. -/
theorem findim_eq_card_finset_basis {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {b : finset V} (h : is_basis K subtype.val) : findim K V = finset.card b := sorry

theorem equiv_fin {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [finite_dimensional K V] {v : ι → V} (hv : is_basis K v) : ∃ (g : fin (findim K V) ≃ ι), is_basis K (v ∘ ⇑g) := sorry

theorem fin_basis (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : ∃ (v : fin (findim K V) → V), is_basis K v := sorry

theorem cardinal_mk_le_findim_of_linear_independent {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {ι : Type w} {b : ι → V} (h : linear_independent K b) : cardinal.mk ι ≤ ↑(findim K V) := sorry

theorem fintype_card_le_findim_of_linear_independent {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {ι : Type u_1} [fintype ι] {b : ι → V} (h : linear_independent K b) : fintype.card ι ≤ findim K V := sorry

theorem finset_card_le_findim_of_linear_independent {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {b : finset V} (h : linear_independent K fun (x : ↥↑b) => ↑x) : finset.card b ≤ findim K V :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finset.card b ≤ findim K V)) (Eq.symm (fintype.card_coe b))))
    (fintype_card_le_findim_of_linear_independent h)

theorem lt_omega_of_linear_independent {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type w} [finite_dimensional K V] {v : ι → V} (h : linear_independent K v) : cardinal.mk ι < cardinal.omega := sorry

theorem not_linear_independent_of_infinite {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type w} [inf : infinite ι] [finite_dimensional K V] (v : ι → V) : ¬linear_independent K v :=
  id
    fun (h_lin_indep : linear_independent K v) =>
      absurd (iff.mp cardinal.infinite_iff inf) (iff.mpr not_le (lt_omega_of_linear_independent h_lin_indep))

/-- A finite dimensional space has positive `findim` iff it has a nonzero element. -/
theorem findim_pos_iff_exists_ne_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : 0 < findim K V ↔ ∃ (x : V), x ≠ 0 := sorry

/-- A finite dimensional space has positive `findim` iff it is nontrivial. -/
theorem findim_pos_iff {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : 0 < findim K V ↔ nontrivial V := sorry

/-- A nontrivial finite dimensional space has positive `findim`. -/
theorem findim_pos {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] [h : nontrivial V] : 0 < findim K V :=
  iff.mpr findim_pos_iff h

/--
If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
theorem exists_nontrivial_relation_of_dim_lt_card {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {t : finset V} (h : findim K V < finset.card t) : ∃ (f : V → K), (finset.sum t fun (e : V) => f e • e) = 0 ∧ ∃ (x : V), ∃ (H : x ∈ t), f x ≠ 0 := sorry

/--
If a finset has cardinality larger than `findim + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {t : finset V} (h : findim K V + 1 < finset.card t) : ∃ (f : V → K),
  (finset.sum t fun (e : V) => f e • e) = 0 ∧ (finset.sum t fun (e : V) => f e) = 0 ∧ ∃ (x : V), ∃ (H : x ∈ t), f x ≠ 0 := sorry

/--
A slight strengthening of `exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
theorem exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card {L : Type u_1} [linear_ordered_field L] {W : Type v} [add_comm_group W] [vector_space L W] [finite_dimensional L W] {t : finset W} (h : findim L W + 1 < finset.card t) : ∃ (f : W → L),
  (finset.sum t fun (e : W) => f e • e) = 0 ∧ (finset.sum t fun (e : W) => f e) = 0 ∧ ∃ (x : W), ∃ (H : x ∈ t), 0 < f x := sorry

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
theorem eq_top_of_findim_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {S : submodule K V} (h : findim K ↥S = findim K V) : S = ⊤ := sorry

/-- A field is one-dimensional as a vector space over itself. -/
@[simp] theorem findim_of_field (K : Type u) [field K] : findim K K = 1 := sorry

/-- The vector space of functions on a fintype has finite dimension. -/
protected instance finite_dimensional_fintype_fun (K : Type u) [field K] {ι : Type u_1} [fintype ι] : finite_dimensional K (ι → K) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite_dimensional K (ι → K))) (propext finite_dimensional_iff_dim_lt_omega)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (vector_space.dim K (ι → K) < cardinal.omega)) dim_fun'))
      (cardinal.nat_lt_omega (fintype.card ι)))

/-- The vector space of functions on a fintype ι has findim equal to the cardinality of ι. -/
@[simp] theorem findim_fintype_fun_eq_card (K : Type u) [field K] {ι : Type v} [fintype ι] : findim K (ι → K) = fintype.card ι :=
  eq.mp (Eq._oldrec (Eq.refl (↑(findim K (ι → K)) = ↑(fintype.card ι))) (propext cardinal.nat_cast_inj))
    (eq.mp (Eq._oldrec (Eq.refl (vector_space.dim K (ι → K) = ↑(fintype.card ι))) (Eq.symm (findim_eq_dim K (ι → K))))
      dim_fun')

/-- The vector space of functions on `fin n` has findim equal to `n`. -/
@[simp] theorem findim_fin_fun (K : Type u) [field K] {n : ℕ} : findim K (fin n → K) = n := sorry

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite (K : Type u) {V : Type v} [field K] [add_comm_group V] [vector_space K V] {A : set V} (hA : set.finite A) : finite_dimensional K ↥(submodule.span K A) :=
  is_noetherian_span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
protected instance submodule.span.finite_dimensional (K : Type u) {V : Type v} [field K] [add_comm_group V] [vector_space K V] (x : V) : finite_dimensional K ↥(submodule.span K (singleton x)) :=
  span_of_finite K
    (eq.mpr (id (propext ((fun {α : Type v} (a : α) => iff_true_intro (set.finite_singleton a)) x))) trivial)

end finite_dimensional


theorem finite_dimensional_of_dim_eq_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (h : vector_space.dim K V = 0) : finite_dimensional K V :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (finite_dimensional K V)) (propext finite_dimensional.finite_dimensional_iff_dim_lt_omega)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (vector_space.dim K V < cardinal.omega)) h)) cardinal.omega_pos)

theorem finite_dimensional_of_dim_eq_one {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (h : vector_space.dim K V = 1) : finite_dimensional K V :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (finite_dimensional K V)) (propext finite_dimensional.finite_dimensional_iff_dim_lt_omega)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (vector_space.dim K V < cardinal.omega)) h)) cardinal.one_lt_omega)

theorem findim_eq_zero_of_dim_eq_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (h : vector_space.dim K V = 0) : finite_dimensional.findim K V = 0 := sorry

theorem finite_dimensional_bot (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] : finite_dimensional K ↥⊥ := sorry

@[simp] theorem findim_bot (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] : finite_dimensional.findim K ↥⊥ = 0 := sorry

theorem bot_eq_top_of_dim_eq_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (h : vector_space.dim K V = 0) : ⊥ = ⊤ := sorry

@[simp] theorem dim_eq_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {S : submodule K V} : vector_space.dim K ↥S = 0 ↔ S = ⊥ := sorry

@[simp] theorem findim_eq_zero {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {S : submodule K V} [finite_dimensional K ↥S] : finite_dimensional.findim K ↥S = 0 ↔ S = ⊥ := sorry

namespace submodule


/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (s : submodule K V) : fg s ↔ finite_dimensional K ↥s := sorry

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
theorem finite_dimensional_of_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {S₁ : submodule K V} {S₂ : submodule K V} [finite_dimensional K ↥S₂] (h : S₁ ≤ S₂) : finite_dimensional K ↥S₁ :=
  iff.mpr finite_dimensional.finite_dimensional_iff_dim_lt_omega
    (lt_of_le_of_lt (dim_le_of_submodule S₁ S₂ h) (finite_dimensional.dim_lt_omega K ↥S₂))

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
protected instance finite_dimensional_inf_left {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (S₁ : submodule K V) (S₂ : submodule K V) [finite_dimensional K ↥S₁] : finite_dimensional K ↥(S₁ ⊓ S₂) :=
  finite_dimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
protected instance finite_dimensional_inf_right {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (S₁ : submodule K V) (S₂ : submodule K V) [finite_dimensional K ↥S₂] : finite_dimensional K ↥(S₁ ⊓ S₂) :=
  finite_dimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
protected instance finite_dimensional_sup {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (S₁ : submodule K V) (S₂ : submodule K V) [h₁ : finite_dimensional K ↥S₁] [h₂ : finite_dimensional K ↥S₂] : finite_dimensional K ↥(S₁ ⊔ S₂) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (finite_dimensional K ↥(S₁ ⊔ S₂))) (Eq.symm (propext (fg_iff_finite_dimensional (S₁ ⊔ S₂))))))
    (fg_sup
      (eq.mp (Eq._oldrec (Eq.refl (finite_dimensional K ↥S₁)) (Eq.symm (propext (fg_iff_finite_dimensional S₁)))) h₁)
      (eq.mp (Eq._oldrec (Eq.refl (finite_dimensional K ↥S₂)) (Eq.symm (propext (fg_iff_finite_dimensional S₂)))) h₂))

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem findim_quotient_add_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (s : submodule K V) : finite_dimensional.findim K (quotient s) + finite_dimensional.findim K ↥s = finite_dimensional.findim K V := sorry

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
theorem findim_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (s : submodule K V) : finite_dimensional.findim K ↥s ≤ finite_dimensional.findim K V := sorry

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient space. -/
theorem findim_lt {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {s : submodule K V} (h : s < ⊤) : finite_dimensional.findim K ↥s < finite_dimensional.findim K V := sorry

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
theorem findim_quotient_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (s : submodule K V) : finite_dimensional.findim K (quotient s) ≤ finite_dimensional.findim K V := sorry

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem dim_sup_add_dim_inf_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (s : submodule K V) (t : submodule K V) [finite_dimensional K ↥s] [finite_dimensional K ↥t] : finite_dimensional.findim K ↥(s ⊔ t) + finite_dimensional.findim K ↥(s ⊓ t) =
  finite_dimensional.findim K ↥s + finite_dimensional.findim K ↥t := sorry

theorem eq_top_of_disjoint {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (s : submodule K V) (t : submodule K V) (hdim : finite_dimensional.findim K ↥s + finite_dimensional.findim K ↥t = finite_dimensional.findim K V) (hdisjoint : disjoint s t) : s ⊔ t = ⊤ := sorry

end submodule


namespace linear_equiv


/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finite_dimensional {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] (f : linear_equiv K V V₂) [finite_dimensional K V] : finite_dimensional K V₂ :=
  is_noetherian_of_linear_equiv f

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem findim_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] (f : linear_equiv K V V₂) [finite_dimensional K V] : finite_dimensional.findim K V = finite_dimensional.findim K V₂ := sorry

end linear_equiv


namespace finite_dimensional


/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_of_findim_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [finite_dimensional K V] [finite_dimensional K V₂] (cond : findim K V = findim K V₂) : Nonempty (linear_equiv K V V₂) := sorry

/--
Two finite-dimensional vector spaces are isomorphic if and only if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_iff_findim_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [finite_dimensional K V] [finite_dimensional K V₂] : Nonempty (linear_equiv K V V₂) ↔ findim K V = findim K V₂ := sorry

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
def linear_equiv.of_findim_eq {K : Type u} (V : Type v) [field K] [add_comm_group V] [vector_space K V] (V₂ : Type v') [add_comm_group V₂] [vector_space K V₂] [finite_dimensional K V] [finite_dimensional K V₂] (cond : findim K V = findim K V₂) : linear_equiv K V V₂ :=
  Classical.choice (nonempty_linear_equiv_of_findim_eq cond)

theorem eq_of_le_of_findim_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {S₁ : submodule K V} {S₂ : submodule K V} [finite_dimensional K ↥S₂] (hle : S₁ ≤ S₂) (hd : findim K ↥S₂ ≤ findim K ↥S₁) : S₁ = S₂ := sorry

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
theorem eq_of_le_of_findim_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {S₁ : submodule K V} {S₂ : submodule K V} [finite_dimensional K ↥S₂] (hle : S₁ ≤ S₂) (hd : findim K ↥S₁ = findim K ↥S₂) : S₁ = S₂ :=
  eq_of_le_of_findim_le hle (eq.ge hd)

end finite_dimensional


namespace linear_map


/-- On a finite-dimensional space, an injective linear map is surjective. -/
theorem surjective_of_injective {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : linear_map K V V} (hinj : function.injective ⇑f) : function.surjective ⇑f := sorry

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
theorem injective_iff_surjective {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : linear_map K V V} : function.injective ⇑f ↔ function.surjective ⇑f := sorry

theorem ker_eq_bot_iff_range_eq_top {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : linear_map K V V} : ker f = ⊥ ↔ range f = ⊤ := sorry

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
theorem mul_eq_one_of_mul_eq_one {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : linear_map K V V} {g : linear_map K V V} (hfg : f * g = 1) : g * f = 1 := sorry

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem mul_eq_one_comm {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : linear_map K V V} {g : linear_map K V V} : f * g = 1 ↔ g * f = 1 :=
  { mp := mul_eq_one_of_mul_eq_one, mpr := mul_eq_one_of_mul_eq_one }

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
theorem comp_eq_id_comm {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : linear_map K V V} {g : linear_map K V V} : comp f g = id ↔ comp g f = id :=
  mul_eq_one_comm

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
theorem finite_dimensional_of_surjective {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [h : finite_dimensional K V] (f : linear_map K V V₂) (hf : range f = ⊤) : finite_dimensional K V₂ :=
  is_noetherian_of_surjective V f hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
protected instance finite_dimensional_range {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [h : finite_dimensional K V] (f : linear_map K V V₂) : finite_dimensional K ↥(range f) :=
  linear_equiv.finite_dimensional (quot_ker_equiv_range f)

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem findim_range_add_findim_ker {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [finite_dimensional K V] (f : linear_map K V V₂) : finite_dimensional.findim K ↥(range f) + finite_dimensional.findim K ↥(ker f) = finite_dimensional.findim K V := sorry

end linear_map


namespace linear_equiv


/-- The linear equivalence corresponging to an injective endomorphism. -/
def of_injective_endo {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : linear_map K V V) (h_inj : linear_map.ker f = ⊥) : linear_equiv K V V :=
  trans (of_injective f h_inj) (of_top (linear_map.range f) sorry)

@[simp] theorem coe_of_injective_endo {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : linear_map K V V) (h_inj : linear_map.ker f = ⊥) : ⇑(of_injective_endo f h_inj) = ⇑f :=
  rfl

@[simp] theorem of_injective_endo_right_inv {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : linear_map K V V) (h_inj : linear_map.ker f = ⊥) : f * ↑(symm (of_injective_endo f h_inj)) = 1 :=
  linear_map.ext (apply_symm_apply (of_injective_endo f h_inj))

@[simp] theorem of_injective_endo_left_inv {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : linear_map K V V) (h_inj : linear_map.ker f = ⊥) : ↑(symm (of_injective_endo f h_inj)) * f = 1 :=
  linear_map.ext (symm_apply_apply (of_injective_endo f h_inj))

end linear_equiv


namespace linear_map


theorem is_unit_iff {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : linear_map K V V) : is_unit f ↔ ker f = ⊥ := sorry

end linear_map


@[simp] theorem findim_top {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] : finite_dimensional.findim K ↥⊤ = finite_dimensional.findim K V := sorry

namespace linear_map


theorem injective_iff_surjective_of_findim_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [finite_dimensional K V] [finite_dimensional K V₂] (H : finite_dimensional.findim K V = finite_dimensional.findim K V₂) {f : linear_map K V V₂} : function.injective ⇑f ↔ function.surjective ⇑f := sorry

theorem findim_le_findim_of_injective {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂] [finite_dimensional K V] [finite_dimensional K V₂] {f : linear_map K V V₂} (hf : function.injective ⇑f) : finite_dimensional.findim K V ≤ finite_dimensional.findim K V₂ := sorry

end linear_map


namespace alg_hom


theorem bijective {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] [finite_dimensional F E] (ϕ : alg_hom F E E) : function.bijective ⇑ϕ :=
  (fun (inj : function.injective ⇑(to_linear_map ϕ)) =>
      { left := inj, right := iff.mp (linear_map.injective_iff_surjective_of_findim_eq_findim rfl) inj })
    (ring_hom.injective (to_ring_hom ϕ))

end alg_hom


/-- Bijection between algebra equivalences and algebra homomorphisms -/
def alg_equiv_equiv_alg_hom (F : Type u) [field F] (E : Type v) [field E] [algebra F E] [finite_dimensional F E] : alg_equiv F E E ≃ alg_hom F E E :=
  equiv.mk (fun (ϕ : alg_equiv F E E) => alg_equiv.to_alg_hom ϕ)
    (fun (ϕ : alg_hom F E E) => alg_equiv.of_bijective ϕ (alg_hom.bijective ϕ)) sorry sorry

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
def field_of_finite_dimensional (F : Type u_1) (K : Type u_2) [field F] [integral_domain K] [algebra F K] [finite_dimensional F K] : field K :=
  field.mk integral_domain.add integral_domain.add_assoc integral_domain.zero integral_domain.zero_add
    integral_domain.add_zero integral_domain.neg integral_domain.sub integral_domain.add_left_neg integral_domain.add_comm
    integral_domain.mul integral_domain.mul_assoc integral_domain.one integral_domain.one_mul integral_domain.mul_one
    integral_domain.left_distrib integral_domain.right_distrib integral_domain.mul_comm
    (fun (x : K) => dite (x = 0) (fun (H : x = 0) => 0) fun (H : ¬x = 0) => classical.some sorry)
    integral_domain.exists_pair_ne sorry sorry

namespace submodule


theorem findim_mono {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] : monotone fun (s : submodule K V) => finite_dimensional.findim K ↥s :=
  fun (s t : submodule K V) (hst : s ≤ t) =>
    trans_rel_right LessEq (linear_equiv.findim_eq (linear_equiv.symm (comap_subtype_equiv_of_le hst)))
      (findim_le (comap (submodule.subtype t) s))

theorem lt_of_le_of_findim_lt_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : submodule K V} {t : submodule K V} (le : s ≤ t) (lt : finite_dimensional.findim K ↥s < finite_dimensional.findim K ↥t) : s < t := sorry

theorem lt_top_of_findim_lt_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : submodule K V} (lt : finite_dimensional.findim K ↥s < finite_dimensional.findim K V) : s < ⊤ :=
  lt_of_le_of_findim_lt_findim le_top
    (eq.mp (Eq._oldrec (Eq.refl (finite_dimensional.findim K ↥s < finite_dimensional.findim K V)) (Eq.symm findim_top))
      lt)

theorem findim_lt_findim_of_lt {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {s : submodule K V} {t : submodule K V} (hst : s < t) : finite_dimensional.findim K ↥s < finite_dimensional.findim K ↥t := sorry

end submodule


theorem findim_span_le_card {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (s : set V) [fin : fintype ↥s] : finite_dimensional.findim K ↥(submodule.span K s) ≤ finset.card (set.to_finset s) := sorry

theorem findim_span_eq_card {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [fintype ι] {b : ι → V} (hb : linear_independent K b) : finite_dimensional.findim K ↥(submodule.span K (set.range b)) = fintype.card ι := sorry

theorem findim_span_set_eq_card {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] (s : set V) [fin : fintype ↥s] (hs : linear_independent K coe) : finite_dimensional.findim K ↥(submodule.span K s) = finset.card (set.to_finset s) := sorry

theorem span_lt_of_subset_of_card_lt_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : set V} [fintype ↥s] {t : submodule K V} (subset : s ⊆ ↑t) (card_lt : finset.card (set.to_finset s) < finite_dimensional.findim K ↥t) : submodule.span K s < t :=
  submodule.lt_of_le_of_findim_lt_findim (iff.mpr submodule.span_le subset)
    (lt_of_le_of_lt (findim_span_le_card s) card_lt)

theorem span_lt_top_of_card_lt_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : set V} [fintype ↥s] (card_lt : finset.card (set.to_finset s) < finite_dimensional.findim K V) : submodule.span K s < ⊤ :=
  submodule.lt_top_of_findim_lt_findim (lt_of_le_of_lt (findim_span_le_card s) card_lt)

theorem findim_span_singleton {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {v : V} (hv : v ≠ 0) : finite_dimensional.findim K ↥(submodule.span K (singleton v)) = 1 := sorry

theorem linear_independent_of_span_eq_top_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [fintype ι] {b : ι → V} (span_eq : submodule.span K (set.range b) = ⊤) (card_eq : fintype.card ι = finite_dimensional.findim K V) : linear_independent K b := sorry

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
theorem linear_independent_iff_card_eq_findim_span {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [fintype ι] {b : ι → V} : linear_independent K b ↔ fintype.card ι = finite_dimensional.findim K ↥(submodule.span K (set.range b)) := sorry

theorem is_basis_of_span_eq_top_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [fintype ι] {b : ι → V} (span_eq : submodule.span K (set.range b) = ⊤) (card_eq : fintype.card ι = finite_dimensional.findim K V) : is_basis K b :=
  { left := linear_independent_of_span_eq_top_of_card_eq_findim span_eq card_eq, right := span_eq }

theorem finset_is_basis_of_span_eq_top_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : finset V} (span_eq : submodule.span K ↑s = ⊤) (card_eq : finset.card s = finite_dimensional.findim K V) : is_basis K coe :=
  is_basis_of_span_eq_top_of_card_eq_findim (Eq.symm subtype.range_coe_subtype ▸ span_eq)
    (trans (fintype.card_coe s) card_eq)

theorem set_is_basis_of_span_eq_top_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : set V} [fintype ↥s] (span_eq : submodule.span K s = ⊤) (card_eq : finset.card (set.to_finset s) = finite_dimensional.findim K V) : is_basis K fun (x : ↥s) => ↑x :=
  is_basis_of_span_eq_top_of_card_eq_findim (Eq.symm subtype.range_coe_subtype ▸ span_eq)
    (trans (Eq.symm (set.to_finset_card s)) card_eq)

theorem span_eq_top_of_linear_independent_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [hι : Nonempty ι] [fintype ι] {b : ι → V} (lin_ind : linear_independent K b) (card_eq : fintype.card ι = finite_dimensional.findim K V) : submodule.span K (set.range b) = ⊤ := sorry

theorem is_basis_of_linear_independent_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} [Nonempty ι] [fintype ι] {b : ι → V} (lin_ind : linear_independent K b) (card_eq : fintype.card ι = finite_dimensional.findim K V) : is_basis K b :=
  { left := lin_ind, right := span_eq_top_of_linear_independent_of_card_eq_findim lin_ind card_eq }

theorem finset_is_basis_of_linear_independent_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : finset V} (hs : finset.nonempty s) (lin_ind : linear_independent K coe) (card_eq : finset.card s = finite_dimensional.findim K V) : is_basis K coe :=
  is_basis_of_linear_independent_of_card_eq_findim lin_ind (trans (fintype.card_coe s) card_eq)

theorem set_is_basis_of_linear_independent_of_card_eq_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {s : set V} [Nonempty ↥s] [fintype ↥s] (lin_ind : linear_independent K coe) (card_eq : finset.card (set.to_finset s) = finite_dimensional.findim K V) : is_basis K coe :=
  is_basis_of_linear_independent_of_card_eq_findim lin_ind (trans (Eq.symm (set.to_finset_card s)) card_eq)

theorem subalgebra.dim_eq_one_of_eq_bot {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] {S : subalgebra F E} (h : S = ⊥) : vector_space.dim F ↥S = 1 := sorry

@[simp] theorem subalgebra.dim_bot {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] : vector_space.dim F ↥⊥ = 1 :=
  subalgebra.dim_eq_one_of_eq_bot rfl

theorem subalgebra_top_dim_eq_submodule_top_dim {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] : vector_space.dim F ↥⊤ = vector_space.dim F ↥⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (vector_space.dim F ↥⊤ = vector_space.dim F ↥⊤)) (Eq.symm algebra.coe_top)))
    (Eq.refl (vector_space.dim F ↥⊤))

theorem subalgebra_top_findim_eq_submodule_top_findim {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] : finite_dimensional.findim F ↥⊤ = finite_dimensional.findim F ↥⊤ := sorry

theorem subalgebra.dim_top {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] : vector_space.dim F ↥⊤ = vector_space.dim F E :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (vector_space.dim F ↥⊤ = vector_space.dim F E)) subalgebra_top_dim_eq_submodule_top_dim))
    dim_top

theorem subalgebra.finite_dimensional_bot {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] : finite_dimensional F ↥⊥ :=
  finite_dimensional_of_dim_eq_one subalgebra.dim_bot

@[simp] theorem subalgebra.findim_bot {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] : finite_dimensional.findim F ↥⊥ = 1 := sorry

theorem subalgebra.findim_eq_one_of_eq_bot {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] {S : subalgebra F E} (h : S = ⊥) : finite_dimensional.findim F ↥S = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite_dimensional.findim F ↥S = 1)) h)) subalgebra.findim_bot

theorem subalgebra.eq_bot_of_findim_one {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] {S : subalgebra F E} (h : finite_dimensional.findim F ↥S = 1) : S = ⊥ := sorry

theorem subalgebra.eq_bot_of_dim_one {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] {S : subalgebra F E} (h : vector_space.dim F ↥S = 1) : S = ⊥ := sorry

@[simp] theorem subalgebra.bot_eq_top_of_dim_eq_one {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] (h : vector_space.dim F E = 1) : ⊥ = ⊤ := sorry

@[simp] theorem subalgebra.bot_eq_top_of_findim_eq_one {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] (h : finite_dimensional.findim F E = 1) : ⊥ = ⊤ := sorry

@[simp] theorem subalgebra.dim_eq_one_iff {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] {S : subalgebra F E} : vector_space.dim F ↥S = 1 ↔ S = ⊥ :=
  { mp := subalgebra.eq_bot_of_dim_one, mpr := subalgebra.dim_eq_one_of_eq_bot }

@[simp] theorem subalgebra.findim_eq_one_iff {F : Type u_1} {E : Type u_2} [field F] [field E] [algebra F E] {S : subalgebra F E} : finite_dimensional.findim F ↥S = 1 ↔ S = ⊥ :=
  { mp := subalgebra.eq_bot_of_findim_one, mpr := subalgebra.findim_eq_one_of_eq_bot }

namespace module


namespace End


theorem exists_ker_pow_eq_ker_pow_succ {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : End K V) : ∃ (k : ℕ), k ≤ finite_dimensional.findim K V ∧ linear_map.ker (f ^ k) = linear_map.ker (f ^ Nat.succ k) := sorry

theorem ker_pow_constant {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {f : End K V} {k : ℕ} (h : linear_map.ker (f ^ k) = linear_map.ker (f ^ Nat.succ k)) (m : ℕ) : linear_map.ker (f ^ k) = linear_map.ker (f ^ (k + m)) := sorry

theorem ker_pow_eq_ker_pow_findim_of_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] {f : End K V} {m : ℕ} (hm : finite_dimensional.findim K V ≤ m) : linear_map.ker (f ^ m) = linear_map.ker (f ^ finite_dimensional.findim K V) := sorry

theorem ker_pow_le_ker_pow_findim {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] [finite_dimensional K V] (f : End K V) (m : ℕ) : linear_map.ker (f ^ m) ≤ linear_map.ker (f ^ finite_dimensional.findim K V) := sorry

