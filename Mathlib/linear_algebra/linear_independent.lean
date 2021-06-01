/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finsupp
import Mathlib.order.zorn
import Mathlib.data.finset.order
import Mathlib.data.equiv.fin
import Mathlib.PostPort

universes u_1 u_3 u_5 u_2 u_6 u u_4 

namespace Mathlib

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `linear_independent R v` as `ker (finsupp.total ι M R v) = ⊥`. Here `finsupp.total` is the
linear map sending a function `f : ι →₀ R` with finite support to the linear combination of vectors
from `v` with these coefficients. Then we prove that several other statements are equivalent to this
one, including injectivity of `finsupp.total ι M R v` and some versions with explicitly written
linear combinations.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `linear_independent R v` states that the elements of the family `v` are linearly independent.

* `linear_independent.repr hv x` returns the linear combination representing `x : span R (range v)`
on the linearly independent vectors `v`, given `hv : linear_independent R v`
(using classical choice). `linear_independent.repr hv` is provided as a linear map.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `fintype.linear_independent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : finset ι`;
* `linear_independent_empty_type`: a family indexed by an empty type is linearly independent;
* `linear_independent_unique_iff`: if `ι` is a singleton, then `linear_independent K v` is
  equivalent to `v (default ι) ≠ 0`;
* linear_independent_option`, `linear_independent_sum`, `linear_independent_fin_cons`,
  `linear_independent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linear_independent_insert`, `linear_independent_union`, `linear_independent_pair`,
  `linear_independent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `linear_independent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that any family of vectors includes a linear independent subfamily spanning the same
submodule.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to use sets, use the family `(λ x, x : s → M)` given a set `s : set M`. The lemmas
`linear_independent.to_subtype_range` and `linear_independent.of_subtype_range` connect those two
worlds.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

/-- `linear_independent R v` states the family of vectors `v` is linearly independent over `R`. -/
def linear_independent {ι : Type u_1} (R : Type u_3) {M : Type u_5} (v : ι → M) [ring R] [add_comm_group M] [module R M] :=
  linear_map.ker (finsupp.total ι M R v) = ⊥

theorem linear_independent_iff {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : linear_independent R v ↔ ∀ (l : ι →₀ R), coe_fn (finsupp.total ι M R v) l = 0 → l = 0 := sorry

theorem linear_independent_iff_injective_total {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : linear_independent R v ↔ function.injective ⇑(finsupp.total ι M R v) :=
  iff.trans linear_independent_iff
    (iff.symm (add_monoid_hom.injective_iff (linear_map.to_add_monoid_hom (finsupp.total ι M R v))))

theorem linear_independent.injective_total {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : linear_independent R v → function.injective ⇑(finsupp.total ι M R v) :=
  iff.mp linear_independent_iff_injective_total

theorem linear_independent_iff' {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : linear_independent R v ↔
  ∀ (s : finset ι) (g : ι → R), (finset.sum s fun (i : ι) => g i • v i) = 0 → ∀ (i : ι), i ∈ s → g i = 0 := sorry

theorem linear_independent_iff'' {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : linear_independent R v ↔
  ∀ (s : finset ι) (g : ι → R),
    (∀ (i : ι), ¬i ∈ s → g i = 0) → (finset.sum s fun (i : ι) => g i • v i) = 0 → ∀ (i : ι), g i = 0 := sorry

theorem linear_dependent_iff {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : ¬linear_independent R v ↔
  ∃ (s : finset ι), ∃ (g : ι → R), (finset.sum s fun (i : ι) => g i • v i) = 0 ∧ ∃ (i : ι), ∃ (H : i ∈ s), g i ≠ 0 := sorry

theorem fintype.linear_independent_iff {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] [fintype ι] : linear_independent R v ↔ ∀ (g : ι → R), (finset.sum finset.univ fun (i : ι) => g i • v i) = 0 → ∀ (i : ι), g i = 0 := sorry

theorem linear_independent_empty_type {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (h : ¬Nonempty ι) : linear_independent R v :=
  eq.mpr (id (Eq._oldrec (Eq.refl (linear_independent R v)) (propext linear_independent_iff)))
    fun (l : ι →₀ R) (ᾰ : coe_fn (finsupp.total ι M R v) l = 0) =>
      finsupp.ext fun (i : ι) => false.elim (h (Nonempty.intro i))

theorem linear_independent.ne_zero {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] [nontrivial R] (i : ι) (hv : linear_independent R v) : v i ≠ 0 := sorry

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
theorem linear_independent.comp {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (h : linear_independent R v) (f : ι' → ι) (hf : function.injective f) : linear_independent R (v ∘ f) := sorry

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the sumodule spaned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `linear_independent.map'` for a special case assuming `ker f = ⊥`. -/
theorem linear_independent.map {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (hv : linear_independent R v) {f : linear_map R M M'} (hf_inj : disjoint (submodule.span R (set.range v)) (linear_map.ker f)) : linear_independent R (⇑f ∘ v) := sorry

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `linear_independent.map` for a more general statement. -/
theorem linear_independent.map' {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (hv : linear_independent R v) (f : linear_map R M M') (hf_inj : linear_map.ker f = ⊥) : linear_independent R (⇑f ∘ v) := sorry

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
theorem linear_independent.of_comp {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (f : linear_map R M M') (hfv : linear_independent R (⇑f ∘ v)) : linear_independent R v := sorry

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected theorem linear_map.linear_independent_iff {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (f : linear_map R M M') (hf_inj : linear_map.ker f = ⊥) : linear_independent R (⇑f ∘ v) ↔ linear_independent R v := sorry

theorem linear_independent_of_subsingleton {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] [subsingleton R] : linear_independent R v :=
  iff.mpr linear_independent_iff fun (l : ι →₀ R) (hl : coe_fn (finsupp.total ι M R v) l = 0) => subsingleton.elim l 0

theorem linear_independent.injective {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] [nontrivial R] (hv : linear_independent R v) : function.injective v := sorry

theorem linear_independent_equiv {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] (e : ι ≃ ι') {f : ι' → M} : linear_independent R (f ∘ ⇑e) ↔ linear_independent R f := sorry

theorem linear_independent_equiv' {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ ⇑e = g) : linear_independent R g ↔ linear_independent R f :=
  h ▸ linear_independent_equiv e

theorem linear_independent_subtype_range {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {f : ι → M} (hf : function.injective f) : linear_independent R coe ↔ linear_independent R f :=
  iff.symm (linear_independent_equiv' (equiv.set.range f hf) rfl)

theorem linear_independent.of_subtype_range {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {f : ι → M} (hf : function.injective f) : linear_independent R coe → linear_independent R f :=
  iff.mp (linear_independent_subtype_range hf)

theorem linear_independent.to_subtype_range {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {f : ι → M} (hf : linear_independent R f) : linear_independent R coe :=
  or.dcases_on (subsingleton_or_nontrivial R)
    (fun (_inst : subsingleton R) => eq.mpr (id (propext (iff_true_intro linear_independent_of_subsingleton))) trivial)
    fun (_inst : nontrivial R) => iff.mpr (linear_independent_subtype_range (linear_independent.injective hf)) hf

theorem linear_independent.to_subtype_range' {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {f : ι → M} (hf : linear_independent R f) {t : set M} (ht : set.range f = t) : linear_independent R coe :=
  ht ▸ linear_independent.to_subtype_range hf

theorem linear_independent_image {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {s : set ι} {f : ι → M} (hf : set.inj_on f s) : (linear_independent R fun (x : ↥s) => f ↑x) ↔ linear_independent R fun (x : ↥(f '' s)) => ↑x :=
  linear_independent_equiv' (equiv.set.image_of_inj_on f s hf) rfl

theorem linear_independent.image {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {s : set ι} {f : ι → M} (hs : linear_independent R fun (x : ↥s) => f ↑x) : linear_independent R fun (x : ↥(f '' s)) => ↑x := sorry

theorem linear_independent_span {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hs : linear_independent R v) : linear_independent R fun (i : ι) => { val := v i, property := submodule.subset_span (set.mem_range_self i) } :=
  linear_independent.of_comp (submodule.subtype (submodule.span R (set.range v))) hs

/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem linear_independent_comp_subtype {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] {s : set ι} : linear_independent R (v ∘ coe) ↔
  ∀ (l : ι →₀ R), l ∈ finsupp.supported R R s → coe_fn (finsupp.total ι M R v) l = 0 → l = 0 := sorry

theorem linear_independent_subtype {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {s : set M} : (linear_independent R fun (x : ↥s) => ↑x) ↔
  ∀ (l : M →₀ R), l ∈ finsupp.supported R R s → coe_fn (finsupp.total M M R id) l = 0 → l = 0 :=
  linear_independent_comp_subtype

theorem linear_independent_comp_subtype_disjoint {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] {s : set ι} : linear_independent R (v ∘ coe) ↔ disjoint (finsupp.supported R R s) (linear_map.ker (finsupp.total ι M R v)) := sorry

theorem linear_independent_subtype_disjoint {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {s : set M} : (linear_independent R fun (x : ↥s) => ↑x) ↔ disjoint (finsupp.supported R R s) (linear_map.ker (finsupp.total M M R id)) :=
  linear_independent_comp_subtype_disjoint

theorem linear_independent_iff_total_on {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {s : set M} : (linear_independent R fun (x : ↥s) => ↑x) ↔ linear_map.ker (finsupp.total_on M M R id s) = ⊥ := sorry

theorem linear_independent.restrict_of_comp_subtype {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] {s : set ι} (hs : linear_independent R (v ∘ coe)) : linear_independent R (set.restrict v s) :=
  hs

theorem linear_independent_empty (R : Type u_3) (M : Type u_5) [ring R] [add_comm_group M] [module R M] : linear_independent R fun (x : ↥∅) => ↑x := sorry

theorem linear_independent.mono {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {t : set M} {s : set M} (h : t ⊆ s) : (linear_independent R fun (x : ↥s) => ↑x) → linear_independent R fun (x : ↥t) => ↑x :=
  eq.mpr (id (imp_congr_eq (propext linear_independent_subtype_disjoint) (propext linear_independent_subtype_disjoint)))
    (disjoint.mono_left (finsupp.supported_mono h))

theorem linear_independent.disjoint_span_image {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) {s : set ι} {t : set ι} (hs : disjoint s t) : disjoint (submodule.span R (v '' s)) (submodule.span R (v '' t)) := sorry

theorem linear_independent_sum {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {v : ι ⊕ ι' → M} : linear_independent R v ↔
  linear_independent R (v ∘ sum.inl) ∧
    linear_independent R (v ∘ sum.inr) ∧
      disjoint (submodule.span R (set.range (v ∘ sum.inl))) (submodule.span R (set.range (v ∘ sum.inr))) := sorry

theorem linear_independent.sum_type {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] {v' : ι' → M} (hv : linear_independent R v) (hv' : linear_independent R v') (h : disjoint (submodule.span R (set.range v)) (submodule.span R (set.range v'))) : linear_independent R (sum.elim v v') :=
  iff.mpr linear_independent_sum { left := hv, right := { left := hv', right := h } }

theorem linear_independent.union {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {s : set M} {t : set M} (hs : linear_independent R fun (x : ↥s) => ↑x) (ht : linear_independent R fun (x : ↥t) => ↑x) (hst : disjoint (submodule.span R s) (submodule.span R t)) : linear_independent R fun (x : ↥(s ∪ t)) => ↑x := sorry

theorem linear_independent_of_finite {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] (s : set M) (H : ∀ (t : set M), t ⊆ s → set.finite t → linear_independent R fun (x : ↥t) => ↑x) : linear_independent R fun (x : ↥s) => ↑x := sorry

theorem linear_independent_Union_of_directed {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {η : Type u_1} {s : η → set M} (hs : directed has_subset.subset s) (h : ∀ (i : η), linear_independent R fun (x : ↥(s i)) => ↑x) : linear_independent R fun (x : ↥(set.Union fun (i : η) => s i)) => ↑x := sorry

theorem linear_independent_sUnion_of_directed {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {s : set (set M)} (hs : directed_on has_subset.subset s) (h : ∀ (a : set M), a ∈ s → linear_independent R fun (x : ↥a) => ↑x) : linear_independent R fun (x : ↥(⋃₀s)) => ↑x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (linear_independent R fun (x : ↥(⋃₀s)) => ↑x)) set.sUnion_eq_Union))
    (linear_independent_Union_of_directed (directed_on.directed_coe hs)
      (eq.mpr (id (propext set_coe.forall)) (eq.mp (Eq.refl (∀ (a : set M), a ∈ s → linear_independent R coe)) h)))

theorem linear_independent_bUnion_of_directed {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {η : Type u_1} {s : set η} {t : η → set M} (hs : directed_on (t ⁻¹'o has_subset.subset) s) (h : ∀ (a : η), a ∈ s → linear_independent R fun (x : ↥(t a)) => ↑x) : linear_independent R fun (x : ↥(set.Union fun (a : η) => set.Union fun (H : a ∈ s) => t a)) => ↑x := sorry

theorem linear_independent_Union_finite_subtype {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {ι : Type u_1} {f : ι → set M} (hl : ∀ (i : ι), linear_independent R fun (x : ↥(f i)) => ↑x) (hd : ∀ (i : ι) (t : set ι),
  set.finite t →
    ¬i ∈ t → disjoint (submodule.span R (f i)) (supr fun (i : ι) => supr fun (H : i ∈ t) => submodule.span R (f i))) : linear_independent R fun (x : ↥(set.Union fun (i : ι) => f i)) => ↑x := sorry

theorem linear_independent_Union_finite {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] {η : Type u_1} {ιs : η → Type u_2} {f : (j : η) → ιs j → M} (hindep : ∀ (j : η), linear_independent R (f j)) (hd : ∀ (i : η) (t : set η),
  set.finite t →
    ¬i ∈ t →
      disjoint (submodule.span R (set.range (f i)))
        (supr fun (i : η) => supr fun (H : i ∈ t) => submodule.span R (set.range (f i)))) : linear_independent R fun (ji : sigma fun (j : η) => ιs j) => f (sigma.fst ji) (sigma.snd ji) := sorry

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
def linear_independent.total_equiv {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) : linear_equiv R (ι →₀ R) ↥(submodule.span R (set.range v)) :=
  linear_equiv.of_bijective (linear_map.cod_restrict (submodule.span R (set.range v)) (finsupp.total ι M R v) sorry) sorry
    sorry

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `linear_independent.total_equiv`. -/
def linear_independent.repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) : linear_map R (↥(submodule.span R (set.range v))) (ι →₀ R) :=
  ↑(linear_equiv.symm (linear_independent.total_equiv hv))

theorem linear_independent.total_repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) (x : ↥(submodule.span R (set.range v))) : coe_fn (finsupp.total ι M R v) (coe_fn (linear_independent.repr hv) x) = ↑x :=
  iff.mp subtype.ext_iff (linear_equiv.apply_symm_apply (linear_independent.total_equiv hv) x)

theorem linear_independent.total_comp_repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) : linear_map.comp (finsupp.total ι M R v) (linear_independent.repr hv) =
  submodule.subtype (submodule.span R (set.range v)) :=
  linear_map.ext (linear_independent.total_repr hv)

theorem linear_independent.repr_ker {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) : linear_map.ker (linear_independent.repr hv) = ⊥ := sorry

theorem linear_independent.repr_range {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) : linear_map.range (linear_independent.repr hv) = ⊤ := sorry

theorem linear_independent.repr_eq {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) {l : ι →₀ R} {x : ↥(submodule.span R (set.range v))} (eq : coe_fn (finsupp.total ι M R v) l = ↑x) : coe_fn (linear_independent.repr hv) x = l := sorry

theorem linear_independent.repr_eq_single {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : linear_independent R v) (i : ι) (x : ↥(submodule.span R (set.range v))) (hx : ↑x = v i) : coe_fn (linear_independent.repr hv) x = finsupp.single i 1 := sorry

-- TODO: why is this so slow?

theorem linear_independent_iff_not_smul_mem_span {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] : linear_independent R v ↔ ∀ (i : ι) (a : R), a • v i ∈ submodule.span R (v '' (set.univ \ singleton i)) → a = 0 := sorry

theorem surjective_of_linear_independent_of_span {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R] [add_comm_group M] [module R M] [nontrivial R] (hv : linear_independent R v) (f : ι' ↪ ι) (hss : set.range v ⊆ ↑(submodule.span R (set.range (v ∘ ⇑f)))) : function.surjective ⇑f := sorry

theorem eq_of_linear_independent_of_span_subtype {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] [nontrivial R] {s : set M} {t : set M} (hs : linear_independent R fun (x : ↥s) => ↑x) (h : t ⊆ s) (hst : s ⊆ ↑(submodule.span R t)) : s = t := sorry

theorem linear_independent.image_subtype {R : Type u_3} {M : Type u_5} {M' : Type u_6} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] {s : set M} {f : linear_map R M M'} (hs : linear_independent R fun (x : ↥s) => ↑x) (hf_inj : disjoint (submodule.span R s) (linear_map.ker f)) : linear_independent R fun (x : ↥(⇑f '' s)) => ↑x := sorry

theorem linear_independent.inl_union_inr {R : Type u_3} {M : Type u_5} {M' : Type u_6} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] {s : set M} {t : set M'} (hs : linear_independent R fun (x : ↥s) => ↑x) (ht : linear_independent R fun (x : ↥t) => ↑x) : linear_independent R fun (x : ↥(⇑(linear_map.inl R M M') '' s ∪ ⇑(linear_map.inr R M M') '' t)) => ↑x := sorry

theorem linear_independent_inl_union_inr' {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} {M' : Type u_6} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] {v : ι → M} {v' : ι' → M'} (hv : linear_independent R v) (hv' : linear_independent R v') : linear_independent R (sum.elim (⇑(linear_map.inl R M M') ∘ v) (⇑(linear_map.inr R M M') ∘ v')) := sorry

/-- Dedekind's linear independence of characters -/
-- See, for example, Keith Conrad's note <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>

theorem linear_independent_monoid_hom (G : Type u_1) [monoid G] (L : Type u_2) [comm_ring L] [no_zero_divisors L] : linear_independent L fun (f : G →* L) => ⇑f := sorry

-- We prove linear independence by showing that only the trivial linear combination vanishes.

-- To do this, we use `finset` induction,

-- Here

-- * `a` is a new character we will insert into the `finset` of characters `s`,

-- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero

-- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero

-- and it remains to prove that `g` vanishes on `insert a s`.

-- We now make the key calculation:

-- For any character `i` in the original `finset`, we have `g i • i = g i • a` as functions on the monoid `G`.

-- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`

-- there is some element of the monoid on which it differs from `a`.

-- From these two facts we deduce that `g` actually vanishes on `s`,

-- And so, using the fact that the linear combination over `s` and over `insert a s` both vanish,

-- we deduce that `g a = 0`.

-- Now we're done; the last two facts together imply that `g` vanishes on every element of `insert a s`.

theorem le_of_span_le_span {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] [nontrivial R] {s : set M} {t : set M} {u : set M} (hl : linear_independent R coe) (hsu : s ⊆ u) (htu : t ⊆ u) (hst : submodule.span R s ≤ submodule.span R t) : s ⊆ t := sorry

theorem span_le_span_iff {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M] [module R M] [nontrivial R] {s : set M} {t : set M} {u : set M} (hl : linear_independent R coe) (hsu : s ⊆ u) (htu : t ⊆ u) : submodule.span R s ≤ submodule.span R t ↔ s ⊆ t :=
  { mp := le_of_span_le_span hl hsu htu, mpr := submodule.span_mono }

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

theorem mem_span_insert_exchange {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {s : set V} {x : V} {y : V} : x ∈ submodule.span K (insert y s) → ¬x ∈ submodule.span K s → y ∈ submodule.span K (insert x s) := sorry

theorem linear_independent_iff_not_mem_span {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {v : ι → V} : linear_independent K v ↔ ∀ (i : ι), ¬v i ∈ submodule.span K (v '' (set.univ \ singleton i)) := sorry

theorem linear_independent_unique_iff {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {v : ι → V} [unique ι] : linear_independent K v ↔ v Inhabited.default ≠ 0 := sorry

theorem linear_independent_unique {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {v : ι → V} [unique ι] : v Inhabited.default ≠ 0 → linear_independent K v :=
  iff.mpr linear_independent_unique_iff

theorem linear_independent_singleton {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {x : V} (hx : x ≠ 0) : linear_independent K fun (x_1 : ↥(singleton x)) => ↑x_1 :=
  linear_independent_unique hx

theorem linear_independent_option' {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {v : ι → V} {x : V} : (linear_independent K fun (o : Option ι) => option.cases_on' o x v) ↔
  linear_independent K v ∧ ¬x ∈ submodule.span K (set.range v) := sorry

theorem linear_independent.option {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {v : ι → V} {x : V} (hv : linear_independent K v) (hx : ¬x ∈ submodule.span K (set.range v)) : linear_independent K fun (o : Option ι) => option.cases_on' o x v :=
  iff.mpr linear_independent_option' { left := hv, right := hx }

theorem linear_independent_option {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {v : Option ι → V} : linear_independent K v ↔ linear_independent K (v ∘ coe) ∧ ¬v none ∈ submodule.span K (set.range (v ∘ coe)) := sorry

theorem linear_independent.insert {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {s : set V} {x : V} (hs : linear_independent K fun (b : ↥s) => ↑b) (hx : ¬x ∈ submodule.span K s) : linear_independent K fun (b : ↥(insert x s)) => ↑b := sorry

theorem linear_independent_insert' {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {ι : Type u_1} {s : set ι} {a : ι} {f : ι → V} (has : ¬a ∈ s) : (linear_independent K fun (x : ↥(insert a s)) => f ↑x) ↔
  (linear_independent K fun (x : ↥s) => f ↑x) ∧ ¬f a ∈ submodule.span K (f '' s) := sorry

theorem linear_independent_insert {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {s : set V} {x : V} (hxs : ¬x ∈ s) : (linear_independent K fun (b : ↥(insert x s)) => ↑b) ↔
  (linear_independent K fun (b : ↥s) => ↑b) ∧ ¬x ∈ submodule.span K s := sorry

theorem linear_independent_pair {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {x : V} {y : V} (hx : x ≠ 0) (hy : ∀ (a : K), a • x ≠ y) : linear_independent K coe :=
  Eq.subst (set.pair_comm y x) (linear_independent.insert (linear_independent_singleton hx))
    (mt (iff.mp submodule.mem_span_singleton) (iff.mpr not_exists hy))

theorem linear_independent_fin_cons {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {x : V} {n : ℕ} {v : fin n → V} : linear_independent K (fin.cons x v) ↔ linear_independent K v ∧ ¬x ∈ submodule.span K (set.range v) := sorry

theorem linear_independent.fin_cons {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {x : V} {n : ℕ} {v : fin n → V} (hv : linear_independent K v) (hx : ¬x ∈ submodule.span K (set.range v)) : linear_independent K (fin.cons x v) :=
  iff.mpr linear_independent_fin_cons { left := hv, right := hx }

theorem linear_independent_fin_succ {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {n : ℕ} {v : fin (n + 1) → V} : linear_independent K v ↔ linear_independent K (fin.tail v) ∧ ¬v 0 ∈ submodule.span K (set.range (fin.tail v)) := sorry

theorem linear_independent_fin2 {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {f : fin (bit0 1) → V} : linear_independent K f ↔ f 1 ≠ 0 ∧ ∀ (a : K), a • f 1 ≠ f 0 := sorry

theorem exists_linear_independent {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {s : set V} {t : set V} (hs : linear_independent K fun (x : ↥s) => ↑x) (hst : s ⊆ t) : ∃ (b : set V), ∃ (H : b ⊆ t), s ⊆ b ∧ t ⊆ ↑(submodule.span K b) ∧ linear_independent K fun (x : ↥b) => ↑x := sorry

-- TODO(Mario): rewrite?

theorem exists_of_linear_independent_of_finite_span {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {s : set V} {t : finset V} (hs : linear_independent K fun (x : ↥s) => ↑x) (hst : s ⊆ ↑(submodule.span K ↑t)) : ∃ (t' : finset V), ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ finset.card t' = finset.card t := sorry

theorem exists_finite_card_le_of_finite_of_linear_independent_of_span {K : Type u_4} {V : Type u} [field K] [add_comm_group V] [vector_space K V] {s : set V} {t : set V} (ht : set.finite t) (hs : linear_independent K fun (x : ↥s) => ↑x) (hst : s ⊆ ↑(submodule.span K t)) : ∃ (h : set.finite s), finset.card (set.finite.to_finset h) ≤ finset.card (set.finite.to_finset ht) := sorry

