/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.content
import Mathlib.measure_theory.prod_group
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Haar measure

In this file we prove the existence of Haar measure for a locally compact Hausdorff topological
group.

For the construction, we follow the write-up by Jonathan Gleason,
*Existence and Uniqueness of Haar Measure*.
This is essentially the same argument as in
https://en.wikipedia.org/wiki/Haar_measure#A_construction_using_compact_subsets.

We construct the Haar measure first on compact sets. For this we define `(K : U)` as the (smallest)
number of left-translates of `U` are needed to cover `K` (`index` in the formalization).
Then we define a function `h` on compact sets as `lim_U (K : U) / (K₀ : U)`,
where `U` becomes a smaller and smaller open neighborhood of `1`, and `K₀` is a fixed compact set
with nonempty interior. This function is `chaar` in the formalization, and we define the limit
formally using Tychonoff's theorem.

This function `h` forms a content, which we can extend to an outer measure `μ`
(`haar_outer_measure`), and obtain the Haar measure from that (`haar_measure`).
We normalize the Haar measure so that the measure of `K₀` is `1`.
We show that for second countable spaces any left invariant Borel measure is a scalar multiple of
the Haar measure.

Note that `μ` need not coincide with `h` on compact sets, according to
[halmos1950measure, ch. X, §53 p.233]. However, we know that `h(K)` lies between `μ(Kᵒ)` and `μ(K)`,
where `ᵒ` denotes the interior.

## Main Declarations

* `haar_measure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haar_measure_self`: the Haar measure is normalized.
* `is_left_invariant_haar_measure`: the Haar measure is left invariant.
* `regular_haar_measure`: the Haar measure is a regular measure.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
* https://en.wikipedia.org/wiki/Haar_measure
-/

namespace measure_theory


namespace measure


/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/

namespace haar


/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
def index {G : Type u_1} [group G] (K : set G) (V : set G) : ℕ :=
  Inf
    (finset.card ''
      set_of
        fun (t : finset G) =>
          K ⊆ set.Union fun (g : G) => set.Union fun (H : g ∈ t) => (fun (h : G) => g * h) ⁻¹' V)

theorem index_empty {G : Type u_1} [group G] {V : set G} : index ∅ V = 0 := sorry

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haar_product` (below). -/
def prehaar {G : Type u_1} [group G] [topological_space G] (K₀ : set G) (U : set G)
    (K : topological_space.compacts G) : ℝ :=
  ↑(index (subtype.val K) U) / ↑(index K₀ U)

theorem prehaar_empty {G : Type u_1} [group G] [topological_space G]
    (K₀ : topological_space.positive_compacts G) {U : set G} : prehaar (subtype.val K₀) U ⊥ = 0 :=
  sorry

theorem prehaar_nonneg {G : Type u_1} [group G] [topological_space G]
    (K₀ : topological_space.positive_compacts G) {U : set G} (K : topological_space.compacts G) :
    0 ≤ prehaar (subtype.val K₀) U K :=
  sorry

/-- `haar_product K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haar_product K₀`. -/
def haar_product {G : Type u_1} [group G] [topological_space G] (K₀ : set G) :
    set (topological_space.compacts G → ℝ) :=
  set.pi set.univ fun (K : topological_space.compacts G) => set.Icc 0 ↑(index (subtype.val K) K₀)

@[simp] theorem mem_prehaar_empty {G : Type u_1} [group G] [topological_space G] {K₀ : set G}
    {f : topological_space.compacts G → ℝ} :
    f ∈ haar_product K₀ ↔
        ∀ (K : topological_space.compacts G), f K ∈ set.Icc 0 ↑(index (subtype.val K) K₀) :=
  sorry

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
def cl_prehaar {G : Type u_1} [group G] [topological_space G] (K₀ : set G)
    (V : topological_space.open_nhds_of 1) : set (topological_space.compacts G → ℝ) :=
  closure (prehaar K₀ '' set_of fun (U : set G) => U ⊆ subtype.val V ∧ is_open U ∧ 1 ∈ U)

/-!
### Lemmas about `index`
-/

/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
theorem index_defined {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K : set G} {V : set G} (hK : is_compact K) (hV : set.nonempty (interior V)) :
    ∃ (n : ℕ),
        n ∈
          finset.card ''
            set_of
              fun (t : finset G) =>
                K ⊆
                  set.Union
                    fun (g : G) => set.Union fun (H : g ∈ t) => (fun (h : G) => g * h) ⁻¹' V :=
  Exists.dcases_on (compact_covered_by_mul_left_translates hK hV)
    fun (t : finset G)
      (ht :
      K ⊆ set.Union fun (g : G) => set.Union fun (H : g ∈ t) => (fun (h : G) => g * h) ⁻¹' V) =>
      Exists.intro (finset.card t) (Exists.intro t { left := ht, right := rfl })

theorem index_elim {G : Type u_1} [group G] [topological_space G] [topological_group G] {K : set G}
    {V : set G} (hK : is_compact K) (hV : set.nonempty (interior V)) :
    ∃ (t : finset G),
        (K ⊆ set.Union fun (g : G) => set.Union fun (H : g ∈ t) => (fun (h : G) => g * h) ⁻¹' V) ∧
          finset.card t = index K V :=
  sorry

theorem le_index_mul {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) (K : topological_space.compacts G) {V : set G}
    (hV : set.nonempty (interior V)) :
    index (subtype.val K) V ≤ index (subtype.val K) (subtype.val K₀) * index (subtype.val K₀) V :=
  sorry

theorem index_pos {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K : topological_space.positive_compacts G) {V : set G} (hV : set.nonempty (interior V)) :
    0 < index (subtype.val K) V :=
  sorry

theorem index_mono {G : Type u_1} [group G] [topological_space G] [topological_group G] {K : set G}
    {K' : set G} {V : set G} (hK' : is_compact K') (h : K ⊆ K') (hV : set.nonempty (interior V)) :
    index K V ≤ index K' V :=
  sorry

theorem index_union_le {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₁ : topological_space.compacts G) (K₂ : topological_space.compacts G) {V : set G}
    (hV : set.nonempty (interior V)) :
    index (subtype.val K₁ ∪ subtype.val K₂) V ≤
        index (subtype.val K₁) V + index (subtype.val K₂) V :=
  sorry

theorem index_union_eq {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₁ : topological_space.compacts G) (K₂ : topological_space.compacts G) {V : set G}
    (hV : set.nonempty (interior V))
    (h : disjoint (subtype.val K₁ * (V⁻¹)) (subtype.val K₂ * (V⁻¹))) :
    index (subtype.val K₁ ∪ subtype.val K₂) V =
        index (subtype.val K₁) V + index (subtype.val K₂) V :=
  sorry

theorem mul_left_index_le {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K : set G} (hK : is_compact K) {V : set G} (hV : set.nonempty (interior V)) (g : G) :
    index ((fun (h : G) => g * h) '' K) V ≤ index K V :=
  sorry

theorem is_left_invariant_index {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K : set G} (hK : is_compact K) (g : G) {V : set G} (hV : set.nonempty (interior V)) :
    index ((fun (h : G) => g * h) '' K) V = index K V :=
  sorry

/-!
### Lemmas about `prehaar`
-/

theorem prehaar_le_index {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) {U : set G} (K : topological_space.compacts G)
    (hU : set.nonempty (interior U)) :
    prehaar (subtype.val K₀) U K ≤ ↑(index (subtype.val K) (subtype.val K₀)) :=
  sorry

theorem prehaar_pos {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) {U : set G} (hU : set.nonempty (interior U))
    {K : set G} (h1K : is_compact K) (h2K : set.nonempty (interior K)) :
    0 < prehaar (subtype.val K₀) U { val := K, property := h1K } :=
  sorry

theorem prehaar_mono {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} {U : set G} (hU : set.nonempty (interior U))
    {K₁ : topological_space.compacts G} {K₂ : topological_space.compacts G}
    (h : subtype.val K₁ ⊆ subtype.val K₂) :
    prehaar (subtype.val K₀) U K₁ ≤ prehaar (subtype.val K₀) U K₂ :=
  sorry

theorem prehaar_self {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} {U : set G} (hU : set.nonempty (interior U)) :
    prehaar (subtype.val K₀) U
          { val := subtype.val K₀, property := and.left (subtype.property K₀) } =
        1 :=
  sorry

theorem prehaar_sup_le {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} {U : set G} (K₁ : topological_space.compacts G)
    (K₂ : topological_space.compacts G) (hU : set.nonempty (interior U)) :
    prehaar (subtype.val K₀) U (K₁ ⊔ K₂) ≤
        prehaar (subtype.val K₀) U K₁ + prehaar (subtype.val K₀) U K₂ :=
  sorry

theorem prehaar_sup_eq {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} {U : set G} {K₁ : topological_space.compacts G}
    {K₂ : topological_space.compacts G} (hU : set.nonempty (interior U))
    (h : disjoint (subtype.val K₁ * (U⁻¹)) (subtype.val K₂ * (U⁻¹))) :
    prehaar (subtype.val K₀) U (K₁ ⊔ K₂) =
        prehaar (subtype.val K₀) U K₁ + prehaar (subtype.val K₀) U K₂ :=
  sorry

theorem is_left_invariant_prehaar {G : Type u_1} [group G] [topological_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} {U : set G}
    (hU : set.nonempty (interior U)) (g : G) (K : topological_space.compacts G) :
    prehaar (subtype.val K₀) U
          (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) =
        prehaar (subtype.val K₀) U K :=
  sorry

/-!
### Lemmas about `haar_product`
-/

theorem prehaar_mem_haar_product {G : Type u_1} [group G] [topological_space G]
    [topological_group G] (K₀ : topological_space.positive_compacts G) {U : set G}
    (hU : set.nonempty (interior U)) : prehaar (subtype.val K₀) U ∈ haar_product (subtype.val K₀) :=
  sorry

theorem nonempty_Inter_cl_prehaar {G : Type u_1} [group G] [topological_space G]
    [topological_group G] (K₀ : topological_space.positive_compacts G) :
    set.nonempty
        (haar_product (subtype.val K₀) ∩
          set.Inter fun (V : topological_space.open_nhds_of 1) => cl_prehaar (subtype.val K₀) V) :=
  sorry

/-!
### The Haar measure on compact sets
-/

/-- The Haar measure on compact sets, defined to be an arbitrary element in the intersection of
  all the sets `cl_prehaar K₀ V` in `haar_product K₀`. -/
def chaar {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) (K : topological_space.compacts G) : ℝ :=
  classical.some (nonempty_Inter_cl_prehaar K₀) K

theorem chaar_mem_haar_product {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) : chaar K₀ ∈ haar_product (subtype.val K₀) :=
  and.left (classical.some_spec (nonempty_Inter_cl_prehaar K₀))

theorem chaar_mem_cl_prehaar {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) (V : topological_space.open_nhds_of 1) :
    chaar K₀ ∈ cl_prehaar (subtype.val K₀) V :=
  sorry

theorem chaar_nonneg {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) (K : topological_space.compacts G) :
    0 ≤ chaar K₀ K :=
  sorry

theorem chaar_empty {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) : chaar K₀ ⊥ = 0 :=
  sorry

theorem chaar_self {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) :
    chaar K₀ { val := subtype.val K₀, property := and.left (subtype.property K₀) } = 1 :=
  sorry

theorem chaar_mono {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} {K₁ : topological_space.compacts G}
    {K₂ : topological_space.compacts G} (h : subtype.val K₁ ⊆ subtype.val K₂) :
    chaar K₀ K₁ ≤ chaar K₀ K₂ :=
  sorry

theorem chaar_sup_le {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} (K₁ : topological_space.compacts G)
    (K₂ : topological_space.compacts G) : chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ :=
  sorry

theorem chaar_sup_eq {G : Type u_1} [group G] [topological_space G] [topological_group G]
    [t2_space G] {K₀ : topological_space.positive_compacts G} {K₁ : topological_space.compacts G}
    {K₂ : topological_space.compacts G} (h : disjoint (subtype.val K₁) (subtype.val K₂)) :
    chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ :=
  sorry

theorem is_left_invariant_chaar {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} (g : G) (K : topological_space.compacts G) :
    chaar K₀ (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) =
        chaar K₀ K :=
  sorry

/-- The function `chaar` interpreted in `ennreal` -/
def echaar {G : Type u_1} [group G] [topological_space G] [topological_group G]
    (K₀ : topological_space.positive_compacts G) (K : topological_space.compacts G) : ennreal :=
  ↑((fun (this : nnreal) => this) { val := chaar K₀ K, property := chaar_nonneg K₀ K })

/-! We only prove the properties for `echaar` that we use at least twice below. -/

/-- The variant of `chaar_sup_le` for `echaar` -/
theorem echaar_sup_le {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} (K₁ : topological_space.compacts G)
    (K₂ : topological_space.compacts G) : echaar K₀ (K₁ ⊔ K₂) ≤ echaar K₀ K₁ + echaar K₀ K₂ :=
  sorry

/-- The variant of `chaar_mono` for `echaar` -/
theorem echaar_mono {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} {K₁ : topological_space.compacts G}
    {K₂ : topological_space.compacts G} (h : subtype.val K₁ ⊆ subtype.val K₂) :
    echaar K₀ K₁ ≤ echaar K₀ K₂ :=
  sorry

/-- The variant of `chaar_self` for `echaar` -/
theorem echaar_self {G : Type u_1} [group G] [topological_space G] [topological_group G]
    {K₀ : topological_space.positive_compacts G} :
    echaar K₀ { val := subtype.val K₀, property := and.left (subtype.property K₀) } = 1 :=
  sorry

/-- The variant of `is_left_invariant_chaar` for `echaar` -/
theorem is_left_invariant_echaar {G : Type u_1} [group G] [topological_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} (g : G)
    (K : topological_space.compacts G) :
    echaar K₀ (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) =
        echaar K₀ K :=
  eq.mpr (id (Eq.trans (propext ennreal.coe_eq_coe) (propext (iff.symm nnreal.coe_eq))))
    (eq.mp
      (Eq.refl
        (chaar K₀ (topological_space.compacts.map (Mul.mul g) (continuous_mul_left g) K) =
          chaar K₀ K))
      (is_left_invariant_chaar g K))

end haar


/-!
### The Haar outer measure
-/

/-- The Haar outer measure on `G`. It is not normalized, and is mainly used to construct
  `haar_measure`, which is a normalized measure. -/
def haar_outer_measure {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] (K₀ : topological_space.positive_compacts G) : outer_measure G :=
  outer_measure.of_content (haar.echaar K₀) sorry

theorem haar_outer_measure_eq_infi {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] (K₀ : topological_space.positive_compacts G) (A : set G) :
    coe_fn (haar_outer_measure K₀) A =
        infi
          fun (U : set G) =>
            infi
              fun (hU : is_open U) =>
                infi
                  fun (h : A ⊆ U) => inner_content (haar.echaar K₀) { val := U, property := hU } :=
  outer_measure.of_content_eq_infi haar.echaar_sup_le A

theorem echaar_le_haar_outer_measure {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G}
    (K : topological_space.compacts G) :
    haar.echaar K₀ K ≤ coe_fn (haar_outer_measure K₀) (subtype.val K) :=
  outer_measure.le_of_content_compacts haar.echaar_sup_le K

theorem haar_outer_measure_of_is_open {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} (U : set G)
    (hU : is_open U) :
    coe_fn (haar_outer_measure K₀) U =
        inner_content (haar.echaar K₀) { val := U, property := hU } :=
  outer_measure.of_content_opens haar.echaar_sup_le { val := U, property := hU }

theorem haar_outer_measure_le_echaar {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} {U : set G} (hU : is_open U)
    (K : topological_space.compacts G) (h : U ⊆ subtype.val K) :
    coe_fn (haar_outer_measure K₀) U ≤ haar.echaar K₀ K :=
  outer_measure.of_content_le haar.echaar_sup_le haar.echaar_mono { val := U, property := hU } K h

theorem haar_outer_measure_exists_open {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} {A : set G}
    (hA : coe_fn (haar_outer_measure K₀) A < ⊤) {ε : nnreal} (hε : 0 < ε) :
    ∃ (U : topological_space.opens G),
        A ⊆ ↑U ∧ coe_fn (haar_outer_measure K₀) ↑U ≤ coe_fn (haar_outer_measure K₀) A + ↑ε :=
  outer_measure.of_content_exists_open haar.echaar_sup_le hA hε

theorem haar_outer_measure_exists_compact {G : Type u_1} [group G] [topological_space G]
    [t2_space G] [topological_group G] {K₀ : topological_space.positive_compacts G}
    {U : topological_space.opens G} (hU : coe_fn (haar_outer_measure K₀) ↑U < ⊤) {ε : nnreal}
    (hε : 0 < ε) :
    ∃ (K : topological_space.compacts G),
        subtype.val K ⊆ ↑U ∧
          coe_fn (haar_outer_measure K₀) ↑U ≤ coe_fn (haar_outer_measure K₀) (subtype.val K) + ↑ε :=
  outer_measure.of_content_exists_compact haar.echaar_sup_le hU hε

theorem haar_outer_measure_caratheodory {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} (A : set G) :
    measurable_space.is_measurable' (outer_measure.caratheodory (haar_outer_measure K₀)) A ↔
        ∀ (U : topological_space.opens G),
          coe_fn (haar_outer_measure K₀) (↑U ∩ A) + coe_fn (haar_outer_measure K₀) (↑U \ A) ≤
            coe_fn (haar_outer_measure K₀) ↑U :=
  outer_measure.of_content_caratheodory haar.echaar_sup_le A

theorem one_le_haar_outer_measure_self {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} :
    1 ≤ coe_fn (haar_outer_measure K₀) (subtype.val K₀) :=
  sorry

theorem haar_outer_measure_pos_of_is_open {G : Type u_1} [group G] [topological_space G]
    [t2_space G] [topological_group G] {K₀ : topological_space.positive_compacts G} {U : set G}
    (hU : is_open U) (h2U : set.nonempty U) : 0 < coe_fn (haar_outer_measure K₀) U :=
  sorry

theorem haar_outer_measure_self_pos {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] {K₀ : topological_space.positive_compacts G} :
    0 < coe_fn (haar_outer_measure K₀) (subtype.val K₀) :=
  has_lt.lt.trans_le
    (haar_outer_measure_pos_of_is_open is_open_interior (and.right (subtype.property K₀)))
    (outer_measure.mono (haar_outer_measure K₀) interior_subset)

theorem haar_outer_measure_lt_top_of_is_compact {G : Type u_1} [group G] [topological_space G]
    [t2_space G] [topological_group G] [locally_compact_space G]
    {K₀ : topological_space.positive_compacts G} {K : set G} (hK : is_compact K) :
    coe_fn (haar_outer_measure K₀) K < ⊤ :=
  sorry

theorem haar_caratheodory_measurable {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G]
    (K₀ : topological_space.positive_compacts G) :
    S ≤ outer_measure.caratheodory (haar_outer_measure K₀) :=
  sorry

/-!
### The Haar measure
-/

/-- the Haar measure on `G`, scaled so that `haar_measure K₀ K₀ = 1`. -/
def haar_measure {G : Type u_1} [group G] [topological_space G] [t2_space G] [topological_group G]
    [S : measurable_space G] [borel_space G] (K₀ : topological_space.positive_compacts G) :
    measure G :=
  coe_fn (haar_outer_measure K₀) (subtype.val K₀)⁻¹ •
    outer_measure.to_measure (haar_outer_measure K₀) (haar_caratheodory_measurable K₀)

theorem haar_measure_apply {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G]
    {K₀ : topological_space.positive_compacts G} {s : set G} (hs : is_measurable s) :
    coe_fn (haar_measure K₀) s =
        coe_fn (haar_outer_measure K₀) s / coe_fn (haar_outer_measure K₀) (subtype.val K₀) :=
  sorry

theorem is_mul_left_invariant_haar_measure {G : Type u_1} [group G] [topological_space G]
    [t2_space G] [topological_group G] [S : measurable_space G] [borel_space G]
    (K₀ : topological_space.positive_compacts G) : is_mul_left_invariant ⇑(haar_measure K₀) :=
  sorry

theorem haar_measure_self {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G] [locally_compact_space G]
    {K₀ : topological_space.positive_compacts G} : coe_fn (haar_measure K₀) (subtype.val K₀) = 1 :=
  sorry

theorem haar_measure_pos_of_is_open {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G] [locally_compact_space G]
    {K₀ : topological_space.positive_compacts G} {U : set G} (hU : is_open U)
    (h2U : set.nonempty U) : 0 < coe_fn (haar_measure K₀) U :=
  sorry

theorem regular_haar_measure {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G] [locally_compact_space G]
    {K₀ : topological_space.positive_compacts G} : regular (haar_measure K₀) :=
  sorry

protected instance haar_measure.measure_theory.sigma_finite {G : Type u_1} [group G]
    [topological_space G] [t2_space G] [topological_group G] [S : measurable_space G]
    [borel_space G] [locally_compact_space G] [topological_space.separable_space G]
    (K₀ : topological_space.positive_compacts G) : sigma_finite (haar_measure K₀) :=
  regular.sigma_finite regular_haar_measure

/-- The Haar measure is unique up to scaling. More precisely: every σ-finite left invariant measure
  is a scalar multiple of the Haar measure. -/
theorem haar_measure_unique {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G] [locally_compact_space G]
    [topological_space.second_countable_topology G] {μ : measure G} [sigma_finite μ]
    (hμ : is_mul_left_invariant ⇑μ) (K₀ : topological_space.positive_compacts G) :
    μ = coe_fn μ (subtype.val K₀) • haar_measure K₀ :=
  sorry

theorem regular_of_left_invariant {G : Type u_1} [group G] [topological_space G] [t2_space G]
    [topological_group G] [S : measurable_space G] [borel_space G] [locally_compact_space G]
    [topological_space.second_countable_topology G] {μ : measure G} [sigma_finite μ]
    (hμ : is_mul_left_invariant ⇑μ) {K : set G} (hK : is_compact K)
    (h2K : set.nonempty (interior K)) (hμK : coe_fn μ K < ⊤) : regular μ :=
  sorry

end Mathlib