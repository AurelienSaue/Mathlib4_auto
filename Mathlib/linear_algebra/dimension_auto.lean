/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Johannes Hölzl, Sander Dahmen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.basis
import Mathlib.set_theory.cardinal_ordinal
import Mathlib.PostPort

universes u v w w' m v' u_1 u₁ u₁' v'' 

namespace Mathlib

/-!
# Dimension of modules and vector spaces

## Main definitions

* The dimension of a vector space is defined as `vector_space.dim : cardinal`.

## Main statements

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.
* `dim_quotient_add_dim`: if V₁ is a submodule of V, then dim (V/V₁) + dim V₁ = dim V.
* `dim_range_add_dim_ker`: the rank-nullity theorem.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/

/-- the dimension of a vector space, defined as a term of type `cardinal` -/
def vector_space.dim (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] :
    cardinal :=
  cardinal.min sorry
    fun (b : Subtype fun (b : set V) => is_basis K fun (i : ↥b) => ↑i) =>
      cardinal.mk ↥(subtype.val b)

theorem is_basis.le_span {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {v : ι → V} {J : set V} (hv : is_basis K v) (hJ : submodule.span K J = ⊤) :
    cardinal.mk ↥(set.range v) ≤ cardinal.mk ↥J :=
  sorry

/-- dimension theorem -/
theorem mk_eq_mk_of_basis {K : Type u} {V : Type v} {ι : Type w} {ι' : Type w'} [field K]
    [add_comm_group V] [vector_space K V] {v : ι → V} {v' : ι' → V} (hv : is_basis K v)
    (hv' : is_basis K v') : cardinal.lift (cardinal.mk ι) = cardinal.lift (cardinal.mk ι') :=
  sorry

theorem mk_eq_mk_of_basis' {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {ι' : Type w} {v : ι → V} {v' : ι' → V} (hv : is_basis K v)
    (hv' : is_basis K v') : cardinal.mk ι = cardinal.mk ι' :=
  iff.mp cardinal.lift_inj (mk_eq_mk_of_basis hv hv')

theorem is_basis.mk_eq_dim'' {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] {ι : Type v} {v : ι → V} (h : is_basis K v) :
    cardinal.mk ι = vector_space.dim K V :=
  sorry

theorem is_basis.mk_range_eq_dim {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {v : ι → V} (h : is_basis K v) :
    cardinal.mk ↥(set.range v) = vector_space.dim K V :=
  is_basis.mk_eq_dim'' (is_basis.range h)

theorem is_basis.mk_eq_dim {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {v : ι → V} (h : is_basis K v) :
    cardinal.lift (cardinal.mk ι) = cardinal.lift (vector_space.dim K V) :=
  sorry

theorem is_basis.mk_eq_dim' {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {v : ι → V} (h : is_basis K v) :
    cardinal.lift (cardinal.mk ι) = cardinal.lift (vector_space.dim K V) :=
  eq.mpr (id (propext cardinal.lift_max))
    (eq.mp (Eq.refl (cardinal.lift (cardinal.mk ι) = cardinal.lift (vector_space.dim K V)))
      (is_basis.mk_eq_dim h))

theorem dim_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] {n : ℕ}
    (H : ∀ (s : finset V), (linear_independent K fun (i : ↥↑s) => ↑i) → finset.card s ≤ n) :
    vector_space.dim K V ≤ ↑n :=
  sorry

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem linear_equiv.lift_dim_eq {K : Type u} {V : Type v} {V' : Type v'} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V']
    (f : linear_equiv K V V') :
    cardinal.lift (vector_space.dim K V) = cardinal.lift (vector_space.dim K V') :=
  sorry

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem linear_equiv.dim_eq {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_equiv K V V₁) :
    vector_space.dim K V = vector_space.dim K V₁ :=
  iff.mp cardinal.lift_inj (linear_equiv.lift_dim_eq f)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_lift_dim_eq {K : Type u} {V : Type v} {V' : Type v'} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V']
    (cond : cardinal.lift (vector_space.dim K V) = cardinal.lift (vector_space.dim K V')) :
    Nonempty (linear_equiv K V V') :=
  sorry

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_dim_eq {K : Type u} {V : Type v} {V₁ : Type v} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V₁] [vector_space K V₁]
    (cond : vector_space.dim K V = vector_space.dim K V₁) : Nonempty (linear_equiv K V V₁) :=
  nonempty_linear_equiv_of_lift_dim_eq (congr_arg cardinal.lift cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_lift_dim_eq {K : Type u} (V : Type v) (V' : Type v') [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V']
    (cond : cardinal.lift (vector_space.dim K V) = cardinal.lift (vector_space.dim K V')) :
    linear_equiv K V V' :=
  Classical.choice (nonempty_linear_equiv_of_lift_dim_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_dim_eq {K : Type u} (V : Type v) (V₁ : Type v) [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁]
    (cond : vector_space.dim K V = vector_space.dim K V₁) : linear_equiv K V V₁ :=
  Classical.choice (nonempty_linear_equiv_of_dim_eq cond)

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_lift_dim_eq {K : Type u} {V : Type v} {V' : Type v'}
    [field K] [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V'] :
    Nonempty (linear_equiv K V V') ↔
        cardinal.lift (vector_space.dim K V) = cardinal.lift (vector_space.dim K V') :=
  sorry

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_dim_eq {K : Type u} {V : Type v} {V₁ : Type v} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V₁] [vector_space K V₁] :
    Nonempty (linear_equiv K V V₁) ↔ vector_space.dim K V = vector_space.dim K V₁ :=
  sorry

@[simp] theorem dim_bot {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] :
    vector_space.dim K ↥⊥ = 0 :=
  sorry

@[simp] theorem dim_top {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] :
    vector_space.dim K ↥⊤ = vector_space.dim K V :=
  linear_equiv.dim_eq (linear_equiv.of_top ⊤ rfl)

theorem dim_of_field (K : Type u_1) [field K] : vector_space.dim K K = 1 := sorry

theorem dim_span {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {v : ι → V} (hv : linear_independent K v) :
    vector_space.dim K ↥(submodule.span K (set.range v)) = cardinal.mk ↥(set.range v) :=
  sorry

theorem dim_span_set {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    {s : set V} (hs : linear_independent K fun (x : ↥s) => ↑x) :
    vector_space.dim K ↥(submodule.span K s) = cardinal.mk ↥s :=
  sorry

theorem cardinal_lift_le_dim_of_linear_independent {K : Type u} {V : Type v} [field K]
    [add_comm_group V] [vector_space K V] {ι : Type w} {v : ι → V} (hv : linear_independent K v) :
    cardinal.lift (cardinal.mk ι) ≤ cardinal.lift (vector_space.dim K V) :=
  sorry

theorem cardinal_le_dim_of_linear_independent {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] {ι : Type v} {v : ι → V} (hv : linear_independent K v) :
    cardinal.mk ι ≤ vector_space.dim K V :=
  eq.mpr (id (Eq.refl (cardinal.mk ι ≤ vector_space.dim K V)))
    (eq.mp (propext cardinal.lift_le) (cardinal_lift_le_dim_of_linear_independent hv))

theorem cardinal_le_dim_of_linear_independent' {K : Type u} {V : Type v} [field K]
    [add_comm_group V] [vector_space K V] {s : set V}
    (hs : linear_independent K fun (x : ↥s) => ↑x) : cardinal.mk ↥s ≤ vector_space.dim K V :=
  sorry

theorem dim_span_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    (s : set V) : vector_space.dim K ↥(submodule.span K s) ≤ cardinal.mk ↥s :=
  sorry

theorem dim_span_of_finset {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    (s : finset V) : vector_space.dim K ↥(submodule.span K ↑s) < cardinal.omega :=
  sorry

theorem dim_prod {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] :
    vector_space.dim K (V × V₁) = vector_space.dim K V + vector_space.dim K V₁ :=
  sorry

theorem dim_quotient_add_dim {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (p : submodule K V) :
    vector_space.dim K (submodule.quotient p) + vector_space.dim K ↥p = vector_space.dim K V :=
  sorry

theorem dim_quotient_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    (p : submodule K V) : vector_space.dim K (submodule.quotient p) ≤ vector_space.dim K V :=
  sorry

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁) :
    vector_space.dim K ↥(linear_map.range f) + vector_space.dim K ↥(linear_map.ker f) =
        vector_space.dim K V :=
  sorry

theorem dim_range_le {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁) :
    vector_space.dim K ↥(linear_map.range f) ≤ vector_space.dim K V :=
  sorry

theorem dim_map_le {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁)
    (p : submodule K V) : vector_space.dim K ↥(submodule.map f p) ≤ vector_space.dim K ↥p :=
  sorry

theorem dim_range_of_surjective {K : Type u} {V : Type v} {V' : Type v'} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V']
    (f : linear_map K V V') (h : function.surjective ⇑f) :
    vector_space.dim K ↥(linear_map.range f) = vector_space.dim K V' :=
  sorry

theorem dim_eq_of_surjective {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁)
    (h : function.surjective ⇑f) :
    vector_space.dim K V = vector_space.dim K V₁ + vector_space.dim K ↥(linear_map.ker f) :=
  sorry

theorem dim_le_of_surjective {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁)
    (h : function.surjective ⇑f) : vector_space.dim K V₁ ≤ vector_space.dim K V :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (vector_space.dim K V₁ ≤ vector_space.dim K V))
        (dim_eq_of_surjective f h)))
    (self_le_add_right (vector_space.dim K V₁) (vector_space.dim K ↥(linear_map.ker f)))

theorem dim_eq_of_injective {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁)
    (h : function.injective ⇑f) : vector_space.dim K V = vector_space.dim K ↥(linear_map.range f) :=
  sorry

theorem dim_submodule_le {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    (s : submodule K V) : vector_space.dim K ↥s ≤ vector_space.dim K V :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (vector_space.dim K ↥s ≤ vector_space.dim K V))
        (Eq.symm (dim_quotient_add_dim s))))
    (self_le_add_left (vector_space.dim K ↥s) (vector_space.dim K (submodule.quotient s)))

theorem dim_le_of_injective {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁)
    (h : function.injective ⇑f) : vector_space.dim K V ≤ vector_space.dim K V₁ :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (vector_space.dim K V ≤ vector_space.dim K V₁))
        (dim_eq_of_injective f h)))
    (dim_submodule_le (linear_map.range f))

theorem dim_le_of_submodule {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (s : submodule K V) (t : submodule K V) (h : s ≤ t) :
    vector_space.dim K ↥s ≤ vector_space.dim K ↥t :=
  sorry

theorem linear_independent_le_dim {K : Type u} {V : Type v} {ι : Type w} [field K]
    [add_comm_group V] [vector_space K V] {v : ι → V} (hv : linear_independent K v) :
    cardinal.lift (cardinal.mk ι) ≤ cardinal.lift (vector_space.dim K V) :=
  sorry

theorem linear_independent_le_dim' {K : Type u} {V : Type v} {ι : Type w} [field K]
    [add_comm_group V] [vector_space K V] {v : ι → V} (hs : linear_independent K v) :
    cardinal.lift (cardinal.mk ι) ≤ cardinal.lift (vector_space.dim K V) :=
  cardinal.mk_range_eq_lift (linear_independent.injective hs) ▸
    dim_span hs ▸ iff.mpr cardinal.lift_le (dim_submodule_le (submodule.span K (set.range v)))

/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq`. -/
theorem dim_add_dim_split {K : Type u} {V : Type v} {V₁ : Type v} {V₂ : Type v} {V₃ : Type v}
    [field K] [add_comm_group V] [vector_space K V] [add_comm_group V₁] [vector_space K V₁]
    [add_comm_group V₂] [vector_space K V₂] [add_comm_group V₃] [vector_space K V₃]
    (db : linear_map K V₂ V) (eb : linear_map K V₃ V) (cd : linear_map K V₁ V₂)
    (ce : linear_map K V₁ V₃) (hde : ⊤ ≤ linear_map.range db ⊔ linear_map.range eb)
    (hgd : linear_map.ker cd = ⊥) (eq : linear_map.comp db cd = linear_map.comp eb ce)
    (eq₂ :
      ∀ (d : V₂) (e : V₃),
        coe_fn db d = coe_fn eb e → ∃ (c : V₁), coe_fn cd c = d ∧ coe_fn ce c = e) :
    vector_space.dim K V + vector_space.dim K V₁ = vector_space.dim K V₂ + vector_space.dim K V₃ :=
  sorry

theorem dim_sup_add_dim_inf_eq {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (s : submodule K V) (t : submodule K V) :
    vector_space.dim K ↥(s ⊔ t) + vector_space.dim K ↥(s ⊓ t) =
        vector_space.dim K ↥s + vector_space.dim K ↥t :=
  sorry

theorem dim_add_le_dim_add_dim {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (s : submodule K V) (t : submodule K V) :
    vector_space.dim K ↥(s ⊔ t) ≤ vector_space.dim K ↥s + vector_space.dim K ↥t :=
  sorry

theorem dim_pi {K : Type u} {η : Type u₁'} {φ : η → Type u_1} [field K] [fintype η]
    [(i : η) → add_comm_group (φ i)] [(i : η) → vector_space K (φ i)] :
    vector_space.dim K ((i : η) → φ i) = cardinal.sum fun (i : η) => vector_space.dim K (φ i) :=
  sorry

theorem dim_fun {K : Type u} [field K] {V : Type u} {η : Type u} [fintype η] [add_comm_group V]
    [vector_space K V] : vector_space.dim K (η → V) = ↑(fintype.card η) * vector_space.dim K V :=
  sorry

theorem dim_fun_eq_lift_mul {K : Type u} {V : Type v} {η : Type u₁'} [field K] [add_comm_group V]
    [vector_space K V] [fintype η] :
    vector_space.dim K (η → V) = ↑(fintype.card η) * cardinal.lift (vector_space.dim K V) :=
  sorry

theorem dim_fun' {K : Type u} {η : Type u₁'} [field K] [fintype η] :
    vector_space.dim K (η → K) = ↑(fintype.card η) :=
  sorry

theorem dim_fin_fun {K : Type u} [field K] (n : ℕ) : vector_space.dim K (fin n → K) = ↑n := sorry

theorem exists_mem_ne_zero_of_ne_bot {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] {s : submodule K V} (h : s ≠ ⊥) : ∃ (b : V), b ∈ s ∧ b ≠ 0 :=
  sorry

theorem exists_mem_ne_zero_of_dim_pos {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] {s : submodule K V} (h : 0 < vector_space.dim K ↥s) :
    ∃ (b : V), b ∈ s ∧ b ≠ 0 :=
  sorry

theorem exists_is_basis_fintype {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (h : vector_space.dim K V < cardinal.omega) :
    ∃ (s : set V), is_basis K subtype.val ∧ Nonempty (fintype ↥s) :=
  sorry

/-- `rank f` is the rank of a `linear_map f`, defined as the dimension of `f.range`. -/
def rank {K : Type u} {V : Type v} {V' : Type v'} [field K] [add_comm_group V] [vector_space K V]
    [add_comm_group V'] [vector_space K V'] (f : linear_map K V V') : cardinal :=
  vector_space.dim K ↥(linear_map.range f)

theorem rank_le_domain {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁) :
    rank f ≤ vector_space.dim K V :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (rank f ≤ vector_space.dim K V)) (Eq.symm (dim_range_add_dim_ker f))))
    (self_le_add_right (rank f) (vector_space.dim K ↥(linear_map.ker f)))

theorem rank_le_range {K : Type u} {V : Type v} {V₁ : Type v} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V₁] [vector_space K V₁] (f : linear_map K V V₁) :
    rank f ≤ vector_space.dim K V₁ :=
  dim_submodule_le (linear_map.range f)

theorem rank_add_le {K : Type u} {V : Type v} {V' : Type v'} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V'] [vector_space K V'] (f : linear_map K V V')
    (g : linear_map K V V') : rank (f + g) ≤ rank f + rank g :=
  sorry

@[simp] theorem rank_zero {K : Type u} {V : Type v} {V' : Type v'} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V'] [vector_space K V'] : rank 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (rank 0 = 0)) (rank.equations._eqn_1 0)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (vector_space.dim K ↥(linear_map.range 0) = 0)) linear_map.range_zero))
      (eq.mpr (id (Eq._oldrec (Eq.refl (vector_space.dim K ↥⊥ = 0)) dim_bot)) (Eq.refl 0)))

theorem rank_finset_sum_le {K : Type u} {V : Type v} {V' : Type v'} [field K] [add_comm_group V]
    [vector_space K V] [add_comm_group V'] [vector_space K V'] {η : Type u_1} (s : finset η)
    (f : η → linear_map K V V') :
    rank (finset.sum s fun (d : η) => f d) ≤ finset.sum s fun (d : η) => rank (f d) :=
  finset.sum_hom_rel (le_of_eq rank_zero)
    fun (i : η) (g : linear_map K V V') (c : cardinal) (h : rank g ≤ c) =>
      le_trans (rank_add_le (f i) g) (add_le_add_left h (rank (f i)))

theorem rank_comp_le1 {K : Type u} {V : Type v} {V' : Type v'} {V'' : Type v''} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V']
    [add_comm_group V''] [vector_space K V''] (g : linear_map K V V') (f : linear_map K V' V'') :
    rank (linear_map.comp f g) ≤ rank f :=
  sorry

theorem rank_comp_le2 {K : Type u} {V : Type v} {V' : Type v'} {V'₁ : Type v'} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group V'] [vector_space K V']
    [add_comm_group V'₁] [vector_space K V'₁] (g : linear_map K V V') (f : linear_map K V' V'₁) :
    rank (linear_map.comp f g) ≤ rank g :=
  sorry

theorem dim_zero_iff_forall_zero {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] : vector_space.dim K V = 0 ↔ ∀ (x : V), x = 0 :=
  sorry

theorem dim_pos_iff_exists_ne_zero {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] : 0 < vector_space.dim K V ↔ ∃ (x : V), x ≠ 0 :=
  sorry

theorem dim_pos_iff_nontrivial {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] : 0 < vector_space.dim K V ↔ nontrivial V :=
  sorry

theorem dim_pos {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    [h : nontrivial V] : 0 < vector_space.dim K V :=
  iff.mpr dim_pos_iff_nontrivial h

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
theorem dim_le_one_iff {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] :
    vector_space.dim K V ≤ 1 ↔ ∃ (v₀ : V), ∀ (v : V), ∃ (r : K), r • v₀ = v :=
  sorry

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
theorem dim_submodule_le_one_iff {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (s : submodule K V) :
    vector_space.dim K ↥s ≤ 1 ↔ ∃ (v₀ : V), ∃ (H : v₀ ∈ s), s ≤ submodule.span K (singleton v₀) :=
  sorry

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
theorem dim_submodule_le_one_iff' {K : Type u} {V : Type v} [field K] [add_comm_group V]
    [vector_space K V] (s : submodule K V) :
    vector_space.dim K ↥s ≤ 1 ↔ ∃ (v₀ : V), s ≤ submodule.span K (singleton v₀) :=
  sorry

/-- Version of linear_equiv.dim_eq without universe constraints. -/
theorem linear_equiv.dim_eq_lift {K : Type u} {V : Type v} {E : Type v'} [field K]
    [add_comm_group V] [vector_space K V] [add_comm_group E] [vector_space K E]
    (f : linear_equiv K V E) :
    cardinal.lift (vector_space.dim K V) = cardinal.lift (vector_space.dim K E) :=
  sorry

end Mathlib