/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.linear_independent
import Mathlib.linear_algebra.projection
import Mathlib.data.fintype.card
import Mathlib.PostPort

universes u_1 u_3 u_5 u_2 u_6 u_7 u_4 u u_8 u_9 u_10 u_11 

namespace Mathlib

/-!

# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `is_basis R v` states that the vector family `v` is a basis, i.e. it is linearly independent and
  spans the entire space.

* `is_basis.repr hv x` is the basis version of `linear_independent.repr hv x`. It returns the
  linear combination representing `x : M` on a basis `v` of `M` (using classical choice).
  The argument `hv` must be a proof that `is_basis R v`. `is_basis.repr hv` is given as a linear
  map as well.

* `is_basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis `v : ι → M₁`, given `hv : is_basis R v`.

## Main statements

* `is_basis.ext` states that two linear maps are equal if they coincide on a basis.

* `exists_is_basis` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

/-- A family of vectors is a basis if it is linearly independent and all vectors are in the span. -/
def is_basis {ι : Type u_1} (R : Type u_3) {M : Type u_5} (v : ι → M) [ring R] [add_comm_group M]
    [module R M] :=
  linear_independent R v ∧ submodule.span R (set.range v) = ⊤

theorem is_basis.mem_span {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) (x : M) :
    x ∈ submodule.span R (set.range v) :=
  iff.mp submodule.eq_top_iff' (and.right hv)

theorem is_basis.comp {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5} {v : ι → M}
    [ring R] [add_comm_group M] [module R M] (hv : is_basis R v) (f : ι' → ι)
    (hf : function.bijective f) : is_basis R (v ∘ f) :=
  sorry

theorem is_basis.injective {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] [nontrivial R] (hv : is_basis R v) : function.injective v :=
  fun (x y : ι) (h : v x = v y) => linear_independent.injective (and.left hv) h

theorem is_basis.range {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) :
    is_basis R fun (x : ↥(set.range v)) => ↑x :=
  sorry

/-- Given a basis, any vector can be written as a linear combination of the basis vectors. They are
given by this linear map. This is one direction of `module_equiv_finsupp`. -/
def is_basis.repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) : linear_map R M (ι →₀ R) :=
  linear_map.comp (linear_independent.repr sorry)
    (linear_map.cod_restrict (submodule.span R (set.range v)) linear_map.id (is_basis.mem_span hv))

theorem is_basis.total_repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) (x : M) :
    coe_fn (finsupp.total ι M R v) (coe_fn (is_basis.repr hv) x) = x :=
  linear_independent.total_repr (and.left hv) { val := x, property := is_basis.mem_span hv x }

theorem is_basis.total_comp_repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) :
    linear_map.comp (finsupp.total ι M R v) (is_basis.repr hv) = linear_map.id :=
  linear_map.ext (is_basis.total_repr hv)

theorem is_basis.ext {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M}
    [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    {f : linear_map R M M'} {g : linear_map R M M'} (hv : is_basis R v)
    (h : ∀ (i : ι), coe_fn f (v i) = coe_fn g (v i)) : f = g :=
  linear_map.ext_on_range (and.right hv) h

theorem is_basis.repr_ker {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) : linear_map.ker (is_basis.repr hv) = ⊥ :=
  iff.mpr linear_map.ker_eq_bot (function.left_inverse.injective (is_basis.total_repr hv))

theorem is_basis.repr_range {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) :
    linear_map.range (is_basis.repr hv) = finsupp.supported R R set.univ :=
  sorry

theorem is_basis.repr_total {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) (x : ι →₀ R)
    (hx : x ∈ finsupp.supported R R set.univ) :
    coe_fn (is_basis.repr hv) (coe_fn (finsupp.total ι M R v) x) = x :=
  sorry

theorem is_basis.repr_eq_single {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) {i : ι} :
    coe_fn (is_basis.repr hv) (v i) = finsupp.single i 1 :=
  sorry

@[simp] theorem is_basis.repr_self_apply {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M}
    [ring R] [add_comm_group M] [module R M] (hv : is_basis R v) (i : ι) (j : ι) :
    coe_fn (coe_fn (is_basis.repr hv) (v i)) j = ite (i = j) 1 0 :=
  sorry

theorem is_basis.repr_eq_iff {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) {f : linear_map R M (ι →₀ R)} :
    is_basis.repr hv = f ↔ ∀ (i : ι), coe_fn f (v i) = finsupp.single i 1 :=
  sorry

theorem is_basis.repr_apply_eq {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) {f : M → ι → R}
    (hadd : ∀ (x y : M), f (x + y) = f x + f y) (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x)
    (f_eq : ∀ (i : ι), f (v i) = ⇑(finsupp.single i 1)) (x : M) (i : ι) :
    coe_fn (coe_fn (is_basis.repr hv) x) i = f x i :=
  sorry

theorem is_basis.range_repr_self {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) (i : ι) :
    coe_fn (is_basis.repr (is_basis.range hv)) (v i) =
        finsupp.single { val := v i, property := set.mem_range_self i } 1 :=
  sorry

@[simp] theorem is_basis.range_repr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M}
    [ring R] [add_comm_group M] [module R M] {x : M} (hv : is_basis R v) (i : ι) :
    coe_fn (coe_fn (is_basis.repr (is_basis.range hv)) x)
          { val := v i, property := set.mem_range_self i } =
        coe_fn (coe_fn (is_basis.repr hv) x) i :=
  sorry

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M}
    [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (hv : is_basis R v)
    (f : ι → M') : linear_map R M M' :=
  linear_map.comp (finsupp.total M' M' R id)
    (linear_map.comp (finsupp.lmap_domain R R f) (is_basis.repr hv))

theorem is_basis.constr_apply {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6}
    {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    (hv : is_basis R v) (f : ι → M') (x : M) :
    coe_fn (is_basis.constr hv f) x =
        finsupp.sum (coe_fn (is_basis.repr hv) x) fun (b : ι) (a : R) => a • f b :=
  sorry

@[simp] theorem constr_basis {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6}
    {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    {f : ι → M'} {i : ι} (hv : is_basis R v) : coe_fn (is_basis.constr hv f) (v i) = f i :=
  sorry

theorem constr_eq {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R]
    [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] {g : ι → M'}
    {f : linear_map R M M'} (hv : is_basis R v) (h : ∀ (i : ι), g i = coe_fn f (v i)) :
    is_basis.constr hv g = f :=
  is_basis.ext hv fun (i : ι) => Eq.trans (constr_basis hv) (h i)

theorem constr_self {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M}
    [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (hv : is_basis R v)
    (f : linear_map R M M') : (is_basis.constr hv fun (i : ι) => coe_fn f (v i)) = f :=
  constr_eq hv fun (x : ι) => rfl

theorem constr_zero {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M}
    [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (hv : is_basis R v) :
    (is_basis.constr hv fun (i : ι) => 0) = 0 :=
  constr_eq hv fun (x : ι) => rfl

theorem constr_add {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R]
    [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] {g : ι → M'} {f : ι → M'}
    (hv : is_basis R v) :
    (is_basis.constr hv fun (i : ι) => f i + g i) = is_basis.constr hv f + is_basis.constr hv g :=
  sorry

theorem constr_neg {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R]
    [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] {f : ι → M'}
    (hv : is_basis R v) : (is_basis.constr hv fun (i : ι) => -f i) = -is_basis.constr hv f :=
  sorry

theorem constr_sub {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R]
    [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] (hv : is_basis R v)
    {g : ι → M'} {f : ι → M'} (hs : is_basis R v) :
    (is_basis.constr hv fun (i : ι) => f i - g i) = is_basis.constr hs f - is_basis.constr hs g :=
  sorry

-- this only works on functions if `R` is a commutative ring

theorem constr_smul {ι : Type u_1} {R : Type u_2} {M : Type u_3} [comm_ring R] [add_comm_group M]
    [module R M] {v : ι → R} {f : ι → M} {a : R} (hv : is_basis R v) :
    (is_basis.constr hv fun (b : ι) => a • f b) = a • is_basis.constr hv f :=
  sorry

theorem constr_range {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6} {v : ι → M}
    [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M'] [Nonempty ι]
    (hv : is_basis R v) {f : ι → M'} :
    linear_map.range (is_basis.constr hv f) = submodule.span R (set.range f) :=
  sorry

/-- Canonical equivalence between a module and the linear combinations of basis vectors. -/
def module_equiv_finsupp {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hv : is_basis R v) : linear_equiv R M (ι →₀ R) :=
  linear_equiv.symm
    (linear_equiv.trans (linear_independent.total_equiv sorry)
      (linear_equiv.of_top (submodule.span R (set.range v)) sorry))

@[simp] theorem module_equiv_finsupp_apply_basis {ι : Type u_1} {R : Type u_3} {M : Type u_5}
    {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : is_basis R v) (i : ι) :
    coe_fn (module_equiv_finsupp hv) (v i) = finsupp.single i 1 :=
  sorry

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the indexing sets of the two bases. -/
def linear_equiv_of_is_basis {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5}
    {M' : Type u_6} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    {v : ι → M} {v' : ι' → M'} (hv : is_basis R v) (hv' : is_basis R v') (e : ι ≃ ι') :
    linear_equiv R M M' :=
  linear_equiv.mk (linear_map.to_fun (is_basis.constr hv (v' ∘ ⇑e))) sorry sorry
    ⇑(is_basis.constr hv' (v ∘ ⇑(equiv.symm e))) sorry sorry

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the two bases. -/
def linear_equiv_of_is_basis' {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5}
    {M' : Type u_6} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    {v : ι → M} {v' : ι' → M'} (f : M → M') (g : M' → M) (hv : is_basis R v) (hv' : is_basis R v')
    (hf : ∀ (i : ι), f (v i) ∈ set.range v') (hg : ∀ (i : ι'), g (v' i) ∈ set.range v)
    (hgf : ∀ (i : ι), g (f (v i)) = v i) (hfg : ∀ (i : ι'), f (g (v' i)) = v' i) :
    linear_equiv R M M' :=
  linear_equiv.mk (linear_map.to_fun (is_basis.constr hv (f ∘ v))) sorry sorry
    ⇑(is_basis.constr hv' (g ∘ v')) sorry sorry

@[simp] theorem linear_equiv_of_is_basis_comp {ι : Type u_1} {ι' : Type u_2} {R : Type u_3}
    {M : Type u_5} {M' : Type u_6} {M'' : Type u_7} [ring R] [add_comm_group M] [add_comm_group M']
    [add_comm_group M''] [module R M] [module R M'] [module R M''] {ι'' : Type u_4} {v : ι → M}
    {v' : ι' → M'} {v'' : ι'' → M''} (hv : is_basis R v) (hv' : is_basis R v')
    (hv'' : is_basis R v'') (e : ι ≃ ι') (f : ι' ≃ ι'') :
    linear_equiv.trans (linear_equiv_of_is_basis hv hv' e) (linear_equiv_of_is_basis hv' hv'' f) =
        linear_equiv_of_is_basis hv hv'' (equiv.trans e f) :=
  sorry

@[simp] theorem linear_equiv_of_is_basis_refl {ι : Type u_1} {R : Type u_3} {M : Type u_5}
    {v : ι → M} [ring R] [add_comm_group M] [module R M] (hv : is_basis R v) :
    linear_equiv_of_is_basis hv hv (equiv.refl ι) = linear_equiv.refl R M :=
  sorry

theorem linear_equiv_of_is_basis_trans_symm {ι : Type u_1} {ι' : Type u_2} {R : Type u_3}
    {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M']
    [module R M] [module R M'] (hv : is_basis R v) (e : ι ≃ ι') {v' : ι' → M'}
    (hv' : is_basis R v') :
    linear_equiv.trans (linear_equiv_of_is_basis hv hv' e)
          (linear_equiv_of_is_basis hv' hv (equiv.symm e)) =
        linear_equiv.refl R M :=
  sorry

theorem linear_equiv_of_is_basis_symm_trans {ι : Type u_1} {ι' : Type u_2} {R : Type u_3}
    {M : Type u_5} {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M']
    [module R M] [module R M'] (hv : is_basis R v) (e : ι ≃ ι') {v' : ι' → M'}
    (hv' : is_basis R v') :
    linear_equiv.trans (linear_equiv_of_is_basis hv' hv (equiv.symm e))
          (linear_equiv_of_is_basis hv hv' e) =
        linear_equiv.refl R M' :=
  sorry

theorem is_basis_inl_union_inr {ι : Type u_1} {ι' : Type u_2} {R : Type u_3} {M : Type u_5}
    {M' : Type u_6} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    {v : ι → M} {v' : ι' → M'} (hv : is_basis R v) (hv' : is_basis R v') :
    is_basis R (sum.elim (⇑(linear_map.inl R M M') ∘ v) (⇑(linear_map.inr R M M') ∘ v')) :=
  sorry

theorem is_basis_singleton_one {ι : Type u_1} (R : Type u_2) [unique ι] [ring R] :
    is_basis R fun (_x : ι) => 1 :=
  sorry

protected theorem linear_equiv.is_basis {ι : Type u_1} {R : Type u_3} {M : Type u_5} {M' : Type u_6}
    {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M] [module R M']
    (hs : is_basis R v) (f : linear_equiv R M M') : is_basis R (⇑f ∘ v) :=
  sorry

theorem is_basis_span {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] (hs : linear_independent R v) :
    is_basis R
        fun (i : ι) => { val := v i, property := submodule.subset_span (set.mem_range_self i) } :=
  sorry

theorem is_basis_empty {ι : Type u_1} {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M]
    [module R M] (h_empty : ¬Nonempty ι) (h : ∀ (x : M), x = 0) : is_basis R fun (x : ι) => 0 :=
  sorry

theorem is_basis_empty_bot {ι : Type u_1} {R : Type u_3} {M : Type u_5} [ring R] [add_comm_group M]
    [module R M] (h_empty : ¬Nonempty ι) : is_basis R fun (_x : ι) => 0 :=
  is_basis_empty h_empty
    fun (x : ↥⊥) => iff.mpr subtype.ext_iff_val (iff.mp (submodule.mem_bot R) (subtype.mem x))

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def is_basis.equiv_fun {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v) : linear_equiv R M (ι → R) :=
  linear_equiv.trans (module_equiv_finsupp h)
    (linear_equiv.mk finsupp.to_fun sorry sorry (equiv.inv_fun finsupp.equiv_fun_on_fintype) sorry
      sorry)

/-- A module over a finite ring that admits a finite basis is finite. -/
def module.fintype_of_fintype {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v) [fintype R] : fintype M :=
  fintype.of_equiv (ι → R) (equiv.symm (linear_equiv.to_equiv (is_basis.equiv_fun h)))

theorem module.card_fintype {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v) [fintype R] [fintype M] :
    fintype.card M = fintype.card R ^ fintype.card ι :=
  Eq.trans (fintype.card_congr (linear_equiv.to_equiv (is_basis.equiv_fun h))) fintype.card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp] theorem is_basis.equiv_fun_symm_apply {ι : Type u_1} {R : Type u_3} {M : Type u_5}
    {v : ι → M} [ring R] [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v)
    (x : ι → R) :
    coe_fn (linear_equiv.symm (is_basis.equiv_fun h)) x =
        finset.sum finset.univ fun (i : ι) => x i • v i :=
  sorry

theorem is_basis.equiv_fun_apply {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v) (u : M) :
    coe_fn (is_basis.equiv_fun h) u = ⇑(coe_fn (is_basis.repr h) u) :=
  rfl

theorem is_basis.equiv_fun_total {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M} [ring R]
    [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v) (u : M) :
    (finset.sum finset.univ fun (i : ι) => coe_fn (is_basis.equiv_fun h) u i • v i) = u :=
  sorry

@[simp] theorem is_basis.equiv_fun_self {ι : Type u_1} {R : Type u_3} {M : Type u_5} {v : ι → M}
    [ring R] [add_comm_group M] [module R M] [fintype ι] (h : is_basis R v) (i : ι) (j : ι) :
    coe_fn (is_basis.equiv_fun h) (v i) j = ite (i = j) 1 0 :=
  sorry

@[simp] theorem is_basis.constr_apply_fintype {ι : Type u_1} {R : Type u_3} {M : Type u_5}
    {M' : Type u_6} {v : ι → M} [ring R] [add_comm_group M] [add_comm_group M'] [module R M]
    [module R M'] [fintype ι] (h : is_basis R v) (f : ι → M') (x : M) :
    coe_fn (is_basis.constr h f) x =
        finset.sum finset.univ fun (i : ι) => coe_fn (is_basis.equiv_fun h) x i • f i :=
  sorry

theorem exists_subset_is_basis {K : Type u_4} {V : Type u} [field K] [add_comm_group V]
    [vector_space K V] {s : set V} (hs : linear_independent K fun (x : ↥s) => ↑x) :
    ∃ (b : set V), s ⊆ b ∧ is_basis K coe :=
  sorry

theorem exists_sum_is_basis {ι : Type u_1} {K : Type u_4} {V : Type u} [field K] [add_comm_group V]
    [vector_space K V] {v : ι → V} (hs : linear_independent K v) :
    ∃ (ι' : Type u), ∃ (v' : ι' → V), is_basis K (sum.elim v v') :=
  sorry

theorem exists_is_basis (K : Type u_4) (V : Type u) [field K] [add_comm_group V]
    [vector_space K V] : ∃ (b : set V), is_basis K fun (i : ↥b) => ↑i :=
  sorry

theorem linear_map.exists_left_inverse_of_injective {K : Type u_4} {V : Type u} {V' : Type u_8}
    [field K] [add_comm_group V] [add_comm_group V'] [vector_space K V] [vector_space K V']
    (f : linear_map K V V') (hf_inj : linear_map.ker f = ⊥) :
    ∃ (g : linear_map K V' V), linear_map.comp g f = linear_map.id :=
  sorry

theorem submodule.exists_is_compl {K : Type u_4} {V : Type u} [field K] [add_comm_group V]
    [vector_space K V] (p : submodule K V) : ∃ (q : submodule K V), is_compl p q :=
  sorry

theorem linear_map.exists_right_inverse_of_surjective {K : Type u_4} {V : Type u} {V' : Type u_8}
    [field K] [add_comm_group V] [add_comm_group V'] [vector_space K V] [vector_space K V']
    (f : linear_map K V V') (hf_surj : linear_map.range f = ⊤) :
    ∃ (g : linear_map K V' V), linear_map.comp f g = linear_map.id :=
  sorry

theorem quotient_prod_linear_equiv {K : Type u_4} {V : Type u} [field K] [add_comm_group V]
    [vector_space K V] (p : submodule K V) :
    Nonempty (linear_equiv K (submodule.quotient p × ↥p) V) :=
  sorry

theorem vector_space.card_fintype (K : Type u_4) (V : Type u) [field K] [add_comm_group V]
    [vector_space K V] [fintype K] [fintype V] : ∃ (n : ℕ), fintype.card V = fintype.card K ^ n :=
  exists.elim (exists_is_basis K V)
    fun (b : set V) (hb : is_basis K fun (i : ↥b) => ↑i) =>
      Exists.intro (fintype.card ↥b) (module.card_fintype hb)

namespace pi


theorem linear_independent_std_basis {R : Type u_3} {η : Type u_9} {ιs : η → Type u_10}
    {Ms : η → Type u_11} [ring R] [(i : η) → add_comm_group (Ms i)] [(i : η) → module R (Ms i)]
    [DecidableEq η] (v : (j : η) → ιs j → Ms j) (hs : ∀ (i : η), linear_independent R (v i)) :
    linear_independent R
        fun (ji : sigma fun (j : η) => ιs j) =>
          coe_fn (linear_map.std_basis R Ms (sigma.fst ji)) (v (sigma.fst ji) (sigma.snd ji)) :=
  sorry

theorem is_basis_std_basis {R : Type u_3} {η : Type u_9} {ιs : η → Type u_10} {Ms : η → Type u_11}
    [ring R] [(i : η) → add_comm_group (Ms i)] [(i : η) → module R (Ms i)] [fintype η]
    [DecidableEq η] (s : (j : η) → ιs j → Ms j) (hs : ∀ (j : η), is_basis R (s j)) :
    is_basis R
        fun (ji : sigma fun (j : η) => ιs j) =>
          coe_fn (linear_map.std_basis R Ms (sigma.fst ji)) (s (sigma.fst ji) (sigma.snd ji)) :=
  sorry

theorem is_basis_fun₀ (R : Type u_3) (η : Type u_9) [ring R] [fintype η] [DecidableEq η] :
    is_basis R
        fun (ji : sigma fun (j : η) => Unit) =>
          coe_fn (linear_map.std_basis R (fun (i : η) => R) (sigma.fst ji)) 1 :=
  is_basis_std_basis (fun (_x : η) (_x : Unit) => 1) fun (i : η) => is_basis_singleton_one R

theorem is_basis_fun (R : Type u_3) (η : Type u_9) [ring R] [fintype η] [DecidableEq η] :
    is_basis R fun (i : η) => coe_fn (linear_map.std_basis R (fun (i : η) => R) i) 1 :=
  sorry

@[simp] theorem is_basis_fun_repr (R : Type u_3) (η : Type u_9) [ring R] [fintype η] [DecidableEq η]
    (x : η → R) (i : η) : coe_fn (coe_fn (is_basis.repr (is_basis_fun R η)) x) i = x i :=
  sorry

end Mathlib