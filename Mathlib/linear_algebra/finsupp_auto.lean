/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finsupp.basic
import Mathlib.linear_algebra.basic
import Mathlib.PostPort

universes u_1 u_2 u_4 u_3 u_5 u_6 

namespace Mathlib

/-!
# Properties of the semimodule `α →₀ M`

Given an `R`-semimodule `M`, the `R`-semimodule structure on `α →₀ M` is defined in
`data.finsupp.basic`.

In this file we define `finsupp.supported s` to be the set `{f : α →₀ M | f.support ⊆ s}`
interpreted as a submodule of `α →₀ M`. We also define `linear_map` versions of various maps:

* `finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `finsupp.single a` as a linear map;

* `finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `λ f, f a` as a linear map;

* `finsupp.lsubtype_domain (s : set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;

* `finsupp.restrict_dom`: `finsupp.filter` as a linear map to `finsupp.supported s`;

* `finsupp.lsum`: `finsupp.sum` or `finsupp.lift_add_hom` as a `linear_map`;

* `finsupp.total α M R (v : ι → M)`: sends `l : ι → R` to the linear combination of `v i` with
  coefficients `l i`;

* `finsupp.total_on`: a restricted version of `finsupp.total` with domain `finsupp.supported R R s`
  and codomain `submodule.span R (v '' s)`;

* `finsupp.supported_equiv_finsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;

* `finsupp.lmap_domain`: a linear map version of `finsupp.map_domain`;

* `finsupp.dom_lcongr`: a `linear_equiv` version of `finsupp.dom_congr`;

* `finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

* `finsupp.lcongr`: a `linear_equiv`alence between `α →₀ M` and `β →₀ N` constructed using `e : α ≃
  β` and `e' : M ≃ₗ[R] N`.

## Tags

function with finite support, semimodule, linear algebra
-/

namespace finsupp


/-- Interpret `finsupp.single a` as a linear map. -/
def lsingle {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] (a : α) : linear_map R M (α →₀ M) :=
  linear_map.mk (add_monoid_hom.to_fun (single_add_hom a)) sorry sorry

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere. -/
theorem lhom_ext {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]
    {φ : linear_map R (α →₀ M) N} {ψ : linear_map R (α →₀ M) N}
    (h : ∀ (a : α) (b : M), coe_fn φ (single a b) = coe_fn ψ (single a b)) : φ = ψ :=
  linear_map.to_add_monoid_hom_injective (add_hom_ext h)

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
theorem lhom_ext' {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]
    {φ : linear_map R (α →₀ M) N} {ψ : linear_map R (α →₀ M) N}
    (h : ∀ (a : α), linear_map.comp φ (lsingle a) = linear_map.comp ψ (lsingle a)) : φ = ψ :=
  lhom_ext fun (a : α) => linear_map.congr_fun (h a)

/-- Interpret `λ (f : α →₀ M), f a` as a linear map. -/
def lapply {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] (a : α) : linear_map R (α →₀ M) M :=
  linear_map.mk (add_monoid_hom.to_fun (apply_add_hom a)) sorry sorry

/-- Interpret `finsupp.subtype_domain s` as a linear map. -/
def lsubtype_domain {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] (s : set α) : linear_map R (α →₀ M) (↥s →₀ M) :=
  linear_map.mk (subtype_domain fun (x : α) => x ∈ s) sorry sorry

theorem lsubtype_domain_apply {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) (f : α →₀ M) :
    coe_fn (lsubtype_domain s) f = subtype_domain (fun (x : α) => x ∈ s) f :=
  rfl

@[simp] theorem lsingle_apply {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (a : α) (b : M) : coe_fn (lsingle a) b = single a b :=
  rfl

@[simp] theorem lapply_apply {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (a : α) (f : α →₀ M) : coe_fn (lapply a) f = coe_fn f a :=
  rfl

@[simp] theorem ker_lsingle {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (a : α) : linear_map.ker (lsingle a) = ⊥ :=
  linear_map.ker_eq_bot_of_injective (single_injective a)

theorem lsingle_range_le_ker_lapply {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) (t : set α) (h : disjoint s t) :
    (supr fun (a : α) => supr fun (H : a ∈ s) => linear_map.range (lsingle a)) ≤
        infi fun (a : α) => infi fun (H : a ∈ t) => linear_map.ker (lapply a) :=
  sorry

theorem infi_ker_lapply_le_bot {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] : (infi fun (a : α) => linear_map.ker (lapply a)) ≤ ⊥ :=
  sorry

theorem supr_lsingle_range {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] : (supr fun (a : α) => linear_map.range (lsingle a)) = ⊤ :=
  sorry

theorem disjoint_lsingle_lsingle {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) (t : set α) (hs : disjoint s t) :
    disjoint (supr fun (a : α) => supr fun (H : a ∈ s) => linear_map.range (lsingle a))
        (supr fun (a : α) => supr fun (H : a ∈ t) => linear_map.range (lsingle a)) :=
  sorry

theorem span_single_image {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set M) (a : α) :
    submodule.span R (single a '' s) = submodule.map (lsingle a) (submodule.span R s) :=
  sorry

/-- `finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.support ⊆ s`. -/
def supported {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] (s : set α) : submodule R (α →₀ M) :=
  submodule.mk (set_of fun (p : α →₀ M) => ↑(support p) ⊆ s) sorry sorry sorry

theorem mem_supported {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {s : set α} (p : α →₀ M) : p ∈ supported M R s ↔ ↑(support p) ⊆ s :=
  iff.rfl

theorem mem_supported' {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {s : set α} (p : α →₀ M) :
    p ∈ supported M R s ↔ ∀ (x : α), ¬x ∈ s → coe_fn p x = 0 :=
  sorry

theorem single_mem_supported {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {s : set α} {a : α} (b : M) (h : a ∈ s) :
    single a b ∈ supported M R s :=
  set.subset.trans support_single_subset (iff.mpr finset.singleton_subset_set_iff h)

theorem supported_eq_span_single {α : Type u_1} (R : Type u_4) [semiring R] (s : set α) :
    supported R R s = submodule.span R ((fun (i : α) => single i 1) '' s) :=
  sorry

/-- Interpret `finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
def restrict_dom {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] (s : set α) : linear_map R (α →₀ M) ↥(supported M R s) :=
  linear_map.cod_restrict (supported M R s)
    (linear_map.mk (filter fun (_x : α) => _x ∈ s) sorry sorry) sorry

@[simp] theorem restrict_dom_apply {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) (l : α →₀ M) :
    ↑(coe_fn (restrict_dom M R s) l) = filter (fun (_x : α) => _x ∈ s) l :=
  rfl

theorem restrict_dom_comp_subtype {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) :
    linear_map.comp (restrict_dom M R s) (submodule.subtype (supported M R s)) = linear_map.id :=
  sorry

theorem range_restrict_dom {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) : linear_map.range (restrict_dom M R s) = ⊤ :=
  sorry

theorem supported_mono {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] {s : set α} {t : set α} (st : s ⊆ t) : supported M R s ≤ supported M R t :=
  fun (l : α →₀ M) (h : l ∈ supported M R s) => set.subset.trans h st

@[simp] theorem supported_empty {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] : supported M R ∅ = ⊥ :=
  sorry

@[simp] theorem supported_univ {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] : supported M R set.univ = ⊤ :=
  iff.mpr eq_top_iff fun (l : α →₀ M) (_x : l ∈ ⊤) => set.subset_univ ↑(support l)

theorem supported_Union {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] {δ : Type u_3} (s : δ → set α) :
    supported M R (set.Union fun (i : δ) => s i) = supr fun (i : δ) => supported M R (s i) :=
  sorry

theorem supported_union {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) (t : set α) :
    supported M R (s ∪ t) = supported M R s ⊔ supported M R t :=
  sorry

theorem supported_Inter {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] {ι : Type u_3} (s : ι → set α) :
    supported M R (set.Inter fun (i : ι) => s i) = infi fun (i : ι) => supported M R (s i) :=
  sorry

theorem supported_inter {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) (t : set α) :
    supported M R (s ∩ t) = supported M R s ⊓ supported M R t :=
  sorry

theorem disjoint_supported_supported {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] {s : set α} {t : set α} (h : disjoint s t) :
    disjoint (supported M R s) (supported M R t) :=
  sorry

theorem disjoint_supported_supported_iff {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [nontrivial M] {s : set α} {t : set α} :
    disjoint (supported M R s) (supported M R t) ↔ disjoint s t :=
  sorry

/-- Interpret `finsupp.restrict_support_equiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
def supported_equiv_finsupp {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] (s : set α) :
    linear_equiv R (↥(supported M R s)) (↥s →₀ M) :=
  let F : ↥(supported M R s) ≃ (↥s →₀ M) := restrict_support_equiv s M;
  equiv.to_linear_equiv F sorry

/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `finsupp.sum`. This is an upgraded version of `finsupp.lift_add_hom`.
We define this as an additive equivalence. For a commutative `R`, this equivalence can be
upgraded further to a linear equivalence. -/
def lsum {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N] :
    (α → linear_map R M N) ≃+ linear_map R (α →₀ M) N :=
  add_equiv.mk
    (fun (F : α → linear_map R M N) =>
      linear_map.mk (fun (d : α →₀ M) => sum d fun (i : α) => ⇑(F i)) sorry sorry)
    (fun (F : linear_map R (α →₀ M) N) (x : α) => linear_map.comp F (lsingle x)) sorry sorry sorry

@[simp] theorem coe_lsum {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]
    (f : α → linear_map R M N) :
    ⇑(coe_fn lsum f) = fun (d : α →₀ M) => sum d fun (i : α) => ⇑(f i) :=
  rfl

theorem lsum_apply {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]
    (f : α → linear_map R M N) (l : α →₀ M) :
    coe_fn (coe_fn lsum f) l = sum l fun (b : α) => ⇑(f b) :=
  rfl

theorem lsum_single {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]
    (f : α → linear_map R M N) (i : α) (m : M) :
    coe_fn (coe_fn lsum f) (single i m) = coe_fn (f i) m :=
  sum_single_index (linear_map.map_zero (f i))

theorem lsum_symm_apply {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N]
    (f : linear_map R (α →₀ M) N) (x : α) :
    coe_fn (add_equiv.symm lsum) f x = linear_map.comp f (lsingle x) :=
  rfl

/-- Interpret `finsupp.lmap_domain` as a linear map. -/
def lmap_domain {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {α' : Type u_5} (f : α → α') : linear_map R (α →₀ M) (α' →₀ M) :=
  linear_map.mk (map_domain f) sorry map_domain_smul

@[simp] theorem lmap_domain_apply {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} (f : α → α') (l : α →₀ M) :
    coe_fn (lmap_domain M R f) l = map_domain f l :=
  rfl

@[simp] theorem lmap_domain_id {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] : lmap_domain M R id = linear_map.id :=
  linear_map.ext fun (l : α →₀ M) => map_domain_id

theorem lmap_domain_comp {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} {α'' : Type u_6} (f : α → α')
    (g : α' → α'') :
    lmap_domain M R (g ∘ f) = linear_map.comp (lmap_domain M R g) (lmap_domain M R f) :=
  linear_map.ext fun (l : α →₀ M) => map_domain_comp

theorem supported_comap_lmap_domain {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} (f : α → α') (s : set α') :
    supported M R (f ⁻¹' s) ≤ submodule.comap (lmap_domain M R f) (supported M R s) :=
  sorry

theorem lmap_domain_supported {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} [Nonempty α] (f : α → α') (s : set α) :
    submodule.map (lmap_domain M R f) (supported M R s) = supported M R (f '' s) :=
  sorry

theorem lmap_domain_disjoint_ker {α : Type u_1} (M : Type u_2) (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} (f : α → α') {s : set α}
    (H : ∀ (a b : α), a ∈ s → b ∈ s → f a = f b → a = b) :
    disjoint (supported M R s) (linear_map.ker (lmap_domain M R f)) :=
  sorry

/-- Interprets (l : α →₀ R) as linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
protected def total (α : Type u_1) (M : Type u_2) (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] (v : α → M) : linear_map R (α →₀ R) M :=
  coe_fn lsum fun (i : α) => linear_map.smul_right linear_map.id (v i)

theorem total_apply {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {v : α → M} (l : α →₀ R) :
    coe_fn (finsupp.total α M R v) l = sum l fun (i : α) (a : R) => a • v i :=
  rfl

theorem total_apply_of_mem_supported {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {v : α → M} {l : α →₀ R} {s : finset α}
    (hs : l ∈ supported R R ↑s) :
    coe_fn (finsupp.total α M R v) l = finset.sum s fun (i : α) => coe_fn l i • v i :=
  sorry

@[simp] theorem total_single {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {v : α → M} (c : R) (a : α) :
    coe_fn (finsupp.total α M R v) (single a c) = c • v a :=
  sorry

theorem total_unique {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] [unique α] (l : α →₀ R) (v : α → M) :
    coe_fn (finsupp.total α M R v) l = coe_fn l Inhabited.default • v Inhabited.default :=
  sorry

theorem total_range {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {v : α → M} (h : function.surjective v) :
    linear_map.range (finsupp.total α M R v) = ⊤ :=
  sorry

theorem range_total {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {v : α → M} :
    linear_map.range (finsupp.total α M R v) = submodule.span R (set.range v) :=
  sorry

theorem lmap_domain_total {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} {M' : Type u_6} [add_comm_monoid M']
    [semimodule R M'] {v : α → M} {v' : α' → M'} (f : α → α') (g : linear_map R M M')
    (h : ∀ (i : α), coe_fn g (v i) = v' (f i)) :
    linear_map.comp (finsupp.total α' M' R v') (lmap_domain R R f) =
        linear_map.comp g (finsupp.total α M R v) :=
  sorry

theorem total_emb_domain {α : Type u_1} (R : Type u_4) [semiring R] {α' : Type u_5} {M' : Type u_6}
    [add_comm_monoid M'] [semimodule R M'] {v' : α' → M'} (f : α ↪ α') (l : α →₀ R) :
    coe_fn (finsupp.total α' M' R v') (emb_domain f l) =
        coe_fn (finsupp.total α M' R (v' ∘ ⇑f)) l :=
  sorry

theorem total_map_domain {α : Type u_1} (R : Type u_4) [semiring R] {α' : Type u_5} {M' : Type u_6}
    [add_comm_monoid M'] [semimodule R M'] {v' : α' → M'} (f : α → α') (hf : function.injective f)
    (l : α →₀ R) :
    coe_fn (finsupp.total α' M' R v') (map_domain f l) = coe_fn (finsupp.total α M' R (v' ∘ f)) l :=
  sorry

theorem span_eq_map_total {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {v : α → M} (s : set α) :
    submodule.span R (v '' s) = submodule.map (finsupp.total α M R v) (supported R R s) :=
  sorry

theorem mem_span_iff_total {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {v : α → M} {s : set α} {x : M} :
    x ∈ submodule.span R (v '' s) ↔
        ∃ (l : α →₀ R), ∃ (H : l ∈ supported R R s), coe_fn (finsupp.total α M R v) l = x :=
  sorry

/-- `finsupp.total_on M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : set α` of indices.
-/
protected def total_on (α : Type u_1) (M : Type u_2) (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] (v : α → M) (s : set α) :
    linear_map R ↥(supported R R s) ↥(submodule.span R (v '' s)) :=
  linear_map.cod_restrict (submodule.span R (v '' s))
    (linear_map.comp (finsupp.total α M R v) (submodule.subtype (supported R R s))) sorry

theorem total_on_range {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {v : α → M} (s : set α) : linear_map.range (finsupp.total_on α M R v s) = ⊤ :=
  sorry

theorem total_comp {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R] [add_comm_monoid M]
    [semimodule R M] {α' : Type u_5} {v : α → M} (f : α' → α) :
    finsupp.total α' M R (v ∘ f) = linear_map.comp (finsupp.total α M R v) (lmap_domain R R f) :=
  sorry

theorem total_comap_domain {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {α' : Type u_5} {v : α → M} (f : α → α') (l : α' →₀ R)
    (hf : set.inj_on f (f ⁻¹' ↑(support l))) :
    coe_fn (finsupp.total α M R v) (comap_domain f l hf) =
        finset.sum (finset.preimage (support l) f hf) fun (i : α) => coe_fn l (f i) • v i :=
  sorry

theorem total_on_finset {α : Type u_1} {M : Type u_2} (R : Type u_4) [semiring R]
    [add_comm_monoid M] [semimodule R M] {s : finset α} {f : α → R} (g : α → M)
    (hf : ∀ (a : α), f a ≠ 0 → a ∈ s) :
    coe_fn (finsupp.total α M R g) (on_finset s f hf) = finset.sum s fun (x : α) => f x • g x :=
  sorry

/-- An equivalence of domains induces a linear equivalence of finitely supported functions. -/
protected def dom_lcongr {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] {α₁ : Type u_1} {α₂ : Type u_3} (e : α₁ ≃ α₂) :
    linear_equiv R (α₁ →₀ M) (α₂ →₀ M) :=
  add_equiv.to_linear_equiv (finsupp.dom_congr e) sorry

@[simp] theorem dom_lcongr_single {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] {α₁ : Type u_1} {α₂ : Type u_3} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
    coe_fn (finsupp.dom_lcongr e) (single i m) = single (coe_fn e i) m :=
  sorry

/-- An equivalence of sets induces a linear equivalence of `finsupp`s supported on those sets. -/
def congr {α : Type u_1} {M : Type u_2} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] {α' : Type u_3} (s : set α) (t : set α') (e : ↥s ≃ ↥t) :
    linear_equiv R ↥(supported M R s) ↥(supported M R t) :=
  linear_equiv.trans (supported_equiv_finsupp s)
    (linear_equiv.trans (finsupp.dom_lcongr e) (linear_equiv.symm (supported_equiv_finsupp t)))

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
def lcongr {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R] [add_comm_monoid M]
    [semimodule R M] [add_comm_monoid N] [semimodule R N] {ι : Type u_1} {κ : Type u_5} (e₁ : ι ≃ κ)
    (e₂ : linear_equiv R M N) : linear_equiv R (ι →₀ M) (κ →₀ N) :=
  linear_equiv.trans (finsupp.dom_lcongr e₁)
    (linear_equiv.mk (map_range (⇑e₂) (linear_equiv.map_zero e₂)) sorry sorry
      (map_range ⇑(linear_equiv.symm e₂) sorry) sorry sorry)

@[simp] theorem lcongr_single {M : Type u_2} {N : Type u_3} {R : Type u_4} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N] {ι : Type u_1}
    {κ : Type u_5} (e₁ : ι ≃ κ) (e₂ : linear_equiv R M N) (i : ι) (m : M) :
    coe_fn (lcongr e₁ e₂) (single i m) = single (coe_fn e₁ i) (coe_fn e₂ m) :=
  sorry

end finsupp


theorem linear_map.map_finsupp_total {R : Type u_1} {M : Type u_2} {N : Type u_3} [semiring R]
    [add_comm_monoid M] [semimodule R M] [add_comm_monoid N] [semimodule R N] (f : linear_map R M N)
    {ι : Type u_4} {g : ι → M} (l : ι →₀ R) :
    coe_fn f (coe_fn (finsupp.total ι M R g) l) = coe_fn (finsupp.total ι N R (⇑f ∘ g)) l :=
  sorry

theorem submodule.exists_finset_of_mem_supr {R : Type u_1} {M : Type u_2} [semiring R]
    [add_comm_monoid M] [semimodule R M] {ι : Type u_3} (p : ι → submodule R M) {m : M}
    (hm : m ∈ supr fun (i : ι) => p i) :
    ∃ (s : finset ι), m ∈ supr fun (i : ι) => supr fun (H : i ∈ s) => p i :=
  sorry

theorem mem_span_finset {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M]
    [semimodule R M] {s : finset M} {x : M} :
    x ∈ submodule.span R ↑s ↔ ∃ (f : M → R), (finset.sum s fun (i : M) => f i • i) = x :=
  sorry

end Mathlib