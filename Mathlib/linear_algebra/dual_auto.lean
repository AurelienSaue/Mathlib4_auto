/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.tactic.apply_fun
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u v w l 

namespace Mathlib

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for a K-vector space `V`, `is_basis.to_dual` produces a map from `V` to `dual K V`.
* Given families of vectors `e` and `ε`, `dual_pair e ε` states that these families have the
  characteristic properties of a basis and a dual.

## Main results

* `to_dual_equiv` : the dual space is linearly equivalent to the primal space.
* `dual_pair.is_basis` and `dual_pair.eq_dual`: if `e` and `ε` form a dual pair, `e` is a basis and
  `ε` is its dual basis.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

-/

namespace module


/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
def dual (R : Type u_1) (M : Type u_2) [comm_ring R] [add_comm_group M] [module R M] :=
  linear_map R M R

namespace dual


protected instance inhabited (R : Type u_1) (M : Type u_2) [comm_ring R] [add_comm_group M]
    [module R M] : Inhabited (dual R M) :=
  id linear_map.inhabited

protected instance has_coe_to_fun (R : Type u_1) (M : Type u_2) [comm_ring R] [add_comm_group M]
    [module R M] : has_coe_to_fun (dual R M) :=
  has_coe_to_fun.mk (fun (x : dual R M) => M → R) linear_map.to_fun

/-- Maps a module M to the dual of the dual of M. See `vector_space.erange_coe` and
`vector_space.eval_equiv`. -/
def eval (R : Type u_1) (M : Type u_2) [comm_ring R] [add_comm_group M] [module R M] :
    linear_map R M (dual R (dual R M)) :=
  linear_map.flip linear_map.id

@[simp] theorem eval_apply (R : Type u_1) (M : Type u_2) [comm_ring R] [add_comm_group M]
    [module R M] (v : M) (a : dual R M) : coe_fn (coe_fn (eval R M) v) a = coe_fn a v :=
  sorry

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose {R : Type u_1} {M : Type u_2} [comm_ring R] [add_comm_group M] [module R M]
    {M' : Type u_3} [add_comm_group M'] [module R M'] :
    linear_map R (linear_map R M M') (linear_map R (dual R M') (dual R M)) :=
  linear_map.flip (linear_map.llcomp R M M' R)

theorem transpose_apply {R : Type u_1} {M : Type u_2} [comm_ring R] [add_comm_group M] [module R M]
    {M' : Type u_3} [add_comm_group M'] [module R M'] (u : linear_map R M M') (l : dual R M') :
    coe_fn (coe_fn transpose u) l = linear_map.comp l u :=
  rfl

theorem transpose_comp {R : Type u_1} {M : Type u_2} [comm_ring R] [add_comm_group M] [module R M]
    {M' : Type u_3} [add_comm_group M'] [module R M'] {M'' : Type u_4} [add_comm_group M'']
    [module R M''] (u : linear_map R M' M'') (v : linear_map R M M') :
    coe_fn transpose (linear_map.comp u v) =
        linear_map.comp (coe_fn transpose v) (coe_fn transpose u) :=
  rfl

end dual


end module


namespace is_basis


/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def to_dual {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V] [vector_space K V]
    [de : DecidableEq ι] (B : ι → V) (h : is_basis K B) : linear_map K V (module.dual K V) :=
  constr h fun (v : ι) => constr h fun (w : ι) => ite (w = v) 1 0

theorem to_dual_apply {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) (i : ι) (j : ι) :
    coe_fn (coe_fn (to_dual B h) (B i)) (B j) = ite (i = j) 1 0 :=
  sorry

@[simp] theorem to_dual_total_left {K : Type u} {V : Type v} {ι : Type w} [field K]
    [add_comm_group V] [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B)
    (f : ι →₀ K) (i : ι) :
    coe_fn (coe_fn (to_dual B h) (coe_fn (finsupp.total ι V K B) f)) (B i) = coe_fn f i :=
  sorry

@[simp] theorem to_dual_total_right {K : Type u} {V : Type v} {ι : Type w} [field K]
    [add_comm_group V] [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B)
    (f : ι →₀ K) (i : ι) :
    coe_fn (coe_fn (to_dual B h) (B i)) (coe_fn (finsupp.total ι V K B) f) = coe_fn f i :=
  sorry

theorem to_dual_apply_left {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) (v : V) (i : ι) :
    coe_fn (coe_fn (to_dual B h) v) (B i) = coe_fn (coe_fn (repr h) v) i :=
  sorry

theorem to_dual_apply_right {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) (i : ι) (v : V) :
    coe_fn (coe_fn (to_dual B h) (B i)) v = coe_fn (coe_fn (repr h) v) i :=
  sorry

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def to_dual_flip {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] (B : ι → V) (h : is_basis K B) (v : V) :
    linear_map K V K :=
  coe_fn (linear_map.flip (to_dual B h)) v

-- TODO: unify this with `finsupp.lapply`.

/-- Evaluation of finitely supported functions at a fixed point `i`, as a `K`-linear map. -/
def eval_finsupp_at {K : Type u} {ι : Type w} [field K] (i : ι) : linear_map K (ι →₀ K) K :=
  linear_map.mk (fun (f : ι →₀ K) => coe_fn f i) sorry sorry

/-- `h.coord_fun i` sends vectors to their `i`'th coordinate with respect to the basis `h`. -/
def coord_fun {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V] [vector_space K V]
    {B : ι → V} (h : is_basis K B) (i : ι) : linear_map K V K :=
  linear_map.comp (eval_finsupp_at i) (repr h)

theorem coord_fun_eq_repr {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {B : ι → V} (h : is_basis K B) (v : V) (i : ι) :
    coe_fn (coord_fun h i) v = coe_fn (coe_fn (repr h) v) i :=
  rfl

-- TODO: this lemma should be called something like `to_dual_flip_apply`

theorem to_dual_swap_eq_to_dual {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) (v : V) (w : V) :
    coe_fn (to_dual_flip B h v) w = coe_fn (coe_fn (to_dual B h) w) v :=
  rfl

theorem to_dual_eq_repr {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) (v : V) (i : ι) :
    coe_fn (coe_fn (to_dual B h) v) (B i) = coe_fn (coe_fn (repr h) v) i :=
  to_dual_apply_left h v i

theorem to_dual_eq_equiv_fun {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι] (v : V)
    (i : ι) : coe_fn (coe_fn (to_dual B h) v) (B i) = coe_fn (equiv_fun h) v i :=
  sorry

theorem to_dual_inj {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) (v : V)
    (a : coe_fn (to_dual B h) v = 0) : v = 0 :=
  sorry

theorem to_dual_ker {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) :
    linear_map.ker (to_dual B h) = ⊥ :=
  iff.mpr linear_map.ker_eq_bot' (to_dual_inj h)

theorem to_dual_range {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fin : fintype ι] :
    linear_map.range (to_dual B h) = ⊤ :=
  sorry

/-- Maps a basis for `V` to a basis for the dual space. -/
def dual_basis {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) : ι → module.dual K V :=
  fun (i : ι) => coe_fn (to_dual B h) (B i)

theorem dual_lin_independent {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) :
    linear_independent K (dual_basis h) :=
  linear_independent.map' (and.left h) (to_dual B h) (to_dual_ker h)

@[simp] theorem dual_basis_apply_self {K : Type u} {V : Type v} {ι : Type w} [field K]
    [add_comm_group V] [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B)
    (i : ι) (j : ι) : coe_fn (dual_basis h i) (B j) = ite (i = j) 1 0 :=
  to_dual_apply h i j

/-- A vector space is linearly equivalent to its dual space. -/
def to_dual_equiv {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] (B : ι → V) (h : is_basis K B) [fintype ι] :
    linear_equiv K V (module.dual K V) :=
  linear_equiv.of_bijective (to_dual B h) sorry sorry

theorem dual_basis_is_basis {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι] :
    is_basis K (dual_basis h) :=
  linear_equiv.is_basis h (to_dual_equiv B h)

@[simp] theorem total_dual_basis {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι] (f : ι →₀ K)
    (i : ι) :
    coe_fn (coe_fn (finsupp.total ι (module.dual K V) K (dual_basis h)) f) (B i) = coe_fn f i :=
  sorry

theorem dual_basis_repr {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι]
    (l : module.dual K V) (i : ι) :
    coe_fn (coe_fn (repr (dual_basis_is_basis h)) l) i = coe_fn l (B i) :=
  sorry

theorem dual_basis_equiv_fun {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι]
    (l : module.dual K V) (i : ι) :
    coe_fn (equiv_fun (dual_basis_is_basis h)) l i = coe_fn l (B i) :=
  sorry

theorem dual_basis_apply {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι] (i : ι)
    (v : V) : coe_fn (dual_basis h i) v = coe_fn (equiv_fun h) v i :=
  to_dual_apply_right h i v

@[simp] theorem to_dual_to_dual {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] [de : DecidableEq ι] {B : ι → V} (h : is_basis K B) [fintype ι] :
    linear_map.comp (to_dual (dual_basis h) (dual_basis_is_basis h)) (to_dual B h) =
        module.dual.eval K V :=
  sorry

theorem dual_dim_eq {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V]
    [vector_space K V] {B : ι → V} (h : is_basis K B) [fintype ι] :
    cardinal.lift (vector_space.dim K V) = vector_space.dim K (module.dual K V) :=
  sorry

end is_basis


namespace vector_space


theorem eval_ker {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V] :
    linear_map.ker (module.dual.eval K V) = ⊥ :=
  sorry

theorem dual_dim_eq {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    [finite_dimensional K V] : cardinal.lift (dim K V) = dim K (module.dual K V) :=
  sorry

theorem erange_coe {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    [finite_dimensional K V] : linear_map.range (module.dual.eval K V) = ⊤ :=
  sorry

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def eval_equiv {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
    [finite_dimensional K V] : linear_equiv K V (module.dual K (module.dual K V)) :=
  linear_equiv.of_bijective (module.dual.eval K V) eval_ker erange_coe

end vector_space


/-- `e` and `ε` have characteristic properties of a basis and its dual -/
structure dual_pair {K : Type u} {V : Type v} {ι : Type w} [DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] (e : ι → V) (ε : ι → module.dual K V)
    where
  eval : ∀ (i j : ι), coe_fn (ε i) (e j) = ite (i = j) 1 0
  total : ∀ {v : V}, (∀ (i : ι), coe_fn (ε i) v = 0) → v = 0
  finite : (v : V) → fintype ↥(set_of fun (i : ι) => coe_fn (ε i) v ≠ 0)

namespace dual_pair


/-- The coefficients of `v` on the basis `e` -/
def coeffs {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K] [add_comm_group V]
    [vector_space K V] {e : ι → V} {ε : ι → module.dual K V} (h : dual_pair e ε) (v : V) : ι →₀ K :=
  finsupp.mk (set.to_finset (set_of fun (i : ι) => coe_fn (ε i) v ≠ 0))
    (fun (i : ι) => coe_fn (ε i) v) sorry

@[simp] theorem coeffs_apply {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V} (h : dual_pair e ε)
    (v : V) (i : ι) : coe_fn (coeffs h v) i = coe_fn (ε i) v :=
  rfl

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ V K e l` -/
def lc {K : Type u} {V : Type v} {ι : Type w} [field K] [add_comm_group V] [vector_space K V]
    (e : ι → V) (l : ι →₀ K) : V :=
  finsupp.sum l fun (i : ι) (a : K) => a • e i

theorem dual_lc {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V} (h : dual_pair e ε)
    (l : ι →₀ K) (i : ι) : coe_fn (ε i) (lc e l) = coe_fn l i :=
  sorry

@[simp] theorem coeffs_lc {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V} (h : dual_pair e ε)
    (l : ι →₀ K) : coeffs h (lc e l) = l :=
  sorry

/-- For any v : V n, \sum_{p ∈ Q n} (ε p v) • e p = v -/
theorem decomposition {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V} (h : dual_pair e ε)
    (v : V) : lc e (coeffs h v) = v :=
  sorry

theorem mem_of_mem_span {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V} (h : dual_pair e ε)
    {H : set ι} {x : V} (hmem : x ∈ submodule.span K (e '' H)) (i : ι) :
    coe_fn (ε i) x ≠ 0 → i ∈ H :=
  sorry

theorem is_basis {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V}
    (h : dual_pair e ε) : is_basis K e :=
  sorry

theorem eq_dual {K : Type u} {V : Type v} {ι : Type w} [dι : DecidableEq ι] [field K]
    [add_comm_group V] [vector_space K V] {e : ι → V} {ε : ι → module.dual K V}
    (h : dual_pair e ε) : ε = is_basis.dual_basis (is_basis h) :=
  sorry

end Mathlib