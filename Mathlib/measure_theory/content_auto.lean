/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.measure_space
import Mathlib.measure_theory.borel_space
import Mathlib.topology.opens
import Mathlib.topology.compacts
import Mathlib.PostPort

universes w 

namespace Mathlib

/-!
# Contents

In this file we work with *contents*. A content `λ` is a function from a certain class of subsets
(such as the the compact subsets) to `ennreal` (or `ℝ≥0`) that is
* additive: If `K₁` and `K₂` are disjoint sets in the domain of `λ`,
  then `λ(K₁ ∪ K₂) = λ(K₁) + λ(K₂)`;
* subadditive: If `K₁` and `K₂` are in the domain of `λ`, then `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)`;
* monotone: If `K₁ ⊆ K₂` are in the domain of `λ`, then `λ(K₁) ≤ λ(K₂)`.

We show that:
* Given a content `λ` on compact sets, we get a countably subadditive map that vanishes at `∅`.
  In Halmos (1950) this is called the *inner content* `λ*` of `λ`.
* Given an inner content, we define an outer measure.

We don't explicitly define the type of contents.
In this file we only work on contents on compact sets, and inner contents on open sets, and both
contents and inner contents map into the extended nonnegative reals. However, in other applications
other choices can be made, and it is not a priori clear what the best interface should be.

## Main definitions
* `measure_theory.inner_content`: define an inner content from an content
* `measure_theory.outer_measure.of_content`: construct an outer measure from a content

## References

* Paul Halmos (1950), Measure Theory, §53
* https://en.wikipedia.org/wiki/Content_(measure_theory)
-/

namespace measure_theory


/-- Constructing the inner content of a content. From a content defined on the compact sets, we
  obtain a function defined on all open sets, by taking the supremum of the content of all compact
  subsets. -/
def inner_content {G : Type w} [topological_space G] (μ : topological_space.compacts G → ennreal)
    (U : topological_space.opens G) : ennreal :=
  supr fun (K : topological_space.compacts G) => supr fun (h : subtype.val K ⊆ ↑U) => μ K

theorem le_inner_content {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal} (K : topological_space.compacts G)
    (U : topological_space.opens G) (h2 : subtype.val K ⊆ ↑U) : μ K ≤ inner_content μ U :=
  le_supr_of_le K (le_supr (fun (h2 : subtype.val K ⊆ ↑U) => μ K) h2)

theorem inner_content_le {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal}
    (h : ∀ (K₁ K₂ : topological_space.compacts G), subtype.val K₁ ⊆ subtype.val K₂ → μ K₁ ≤ μ K₂)
    (U : topological_space.opens G) (K : topological_space.compacts G) (h2 : ↑U ⊆ subtype.val K) :
    inner_content μ U ≤ μ K :=
  bsupr_le
    fun (K' : topological_space.compacts G) (hK' : subtype.val K' ⊆ ↑U) =>
      h K' K (set.subset.trans hK' h2)

theorem inner_content_of_is_compact {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal}
    (h : ∀ (K₁ K₂ : topological_space.compacts G), subtype.val K₁ ⊆ subtype.val K₂ → μ K₁ ≤ μ K₂)
    {K : set G} (h1K : is_compact K) (h2K : is_open K) :
    inner_content μ { val := K, property := h2K } = μ { val := K, property := h1K } :=
  sorry

theorem inner_content_empty {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal} (h : μ ⊥ = 0) : inner_content μ ∅ = 0 :=
  sorry

/-- This is "unbundled", because that it required for the API of `induced_outer_measure`. -/
theorem inner_content_mono {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal} {U : set G} {V : set G} (hU : is_open U)
    (hV : is_open V) (h2 : U ⊆ V) :
    inner_content μ { val := U, property := hU } ≤ inner_content μ { val := V, property := hV } :=
  supr_le_supr
    fun (K : topological_space.compacts G) =>
      supr_le_supr_const
        fun (hK : subtype.val K ⊆ ↑{ val := U, property := hU }) => set.subset.trans hK h2

theorem inner_content_exists_compact {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal} {U : topological_space.opens G}
    (hU : inner_content μ U < ⊤) {ε : nnreal} (hε : 0 < ε) :
    ∃ (K : topological_space.compacts G), subtype.val K ⊆ ↑U ∧ inner_content μ U ≤ μ K + ↑ε :=
  sorry

/-- The inner content of a supremum of opens is at most the sum of the individual inner
contents. -/
theorem inner_content_Sup_nat {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} (h1 : μ ⊥ = 0)
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    (U : ℕ → topological_space.opens G) :
    inner_content μ (supr fun (i : ℕ) => U i) ≤ tsum fun (i : ℕ) => inner_content μ (U i) :=
  sorry

/-- The inner content of a union of sets is at most the sum of the individual inner contents.
  This is the "unbundled" version of `inner_content_Sup_nat`.
  It required for the API of `induced_outer_measure`. -/
theorem inner_content_Union_nat {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} (h1 : μ ⊥ = 0)
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) {U : ℕ → set G}
    (hU : ∀ (i : ℕ), is_open (U i)) :
    inner_content μ { val := set.Union fun (i : ℕ) => U i, property := is_open_Union hU } ≤
        tsum fun (i : ℕ) => inner_content μ { val := U i, property := hU i } :=
  sorry

theorem inner_content_comap {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal} (f : G ≃ₜ G)
    (h :
      ∀ {K : topological_space.compacts G},
        μ (topological_space.compacts.map (⇑f) (homeomorph.continuous f) K) = μ K)
    (U : topological_space.opens G) :
    inner_content μ (topological_space.opens.comap (homeomorph.continuous f) U) =
        inner_content μ U :=
  sorry

theorem is_mul_left_invariant_inner_content {G : Type w} [topological_space G] [group G]
    [topological_group G] {μ : topological_space.compacts G → ennreal}
    (h :
      ∀ (g : G) {K : topological_space.compacts G},
        μ (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) = μ K)
    (g : G) (U : topological_space.opens G) :
    inner_content μ (topological_space.opens.comap (continuous_mul_left g) U) = inner_content μ U :=
  sorry

-- @[to_additive] (fails for now)

theorem inner_content_pos_of_is_mul_left_invariant {G : Type w} [topological_space G] [t2_space G]
    [group G] [topological_group G] {μ : topological_space.compacts G → ennreal} (h1 : μ ⊥ = 0)
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    (h3 :
      ∀ (g : G) {K : topological_space.compacts G},
        μ (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) = μ K)
    (K : topological_space.compacts G) (hK : 0 < μ K) (U : topological_space.opens G)
    (hU : set.nonempty ↑U) : 0 < inner_content μ U :=
  sorry

theorem inner_content_mono' {G : Type w} [topological_space G]
    {μ : topological_space.compacts G → ennreal} {U : set G} {V : set G} (hU : is_open U)
    (hV : is_open V) (h2 : U ⊆ V) :
    inner_content μ { val := U, property := hU } ≤ inner_content μ { val := V, property := hV } :=
  supr_le_supr
    fun (K : topological_space.compacts G) =>
      supr_le_supr_const
        fun (hK : subtype.val K ⊆ ↑{ val := U, property := hU }) => set.subset.trans hK h2

namespace outer_measure


/-- Extending a content on compact sets to an outer measure on all sets. -/
def of_content {G : Type w} [topological_space G] [t2_space G]
    (μ : topological_space.compacts G → ennreal) (h1 : μ ⊥ = 0) : outer_measure G :=
  induced_outer_measure
    (fun (U : set G) (hU : is_open U) => inner_content μ { val := U, property := hU }) is_open_empty
    (inner_content_empty h1)

theorem of_content_opens {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    (U : topological_space.opens G) : coe_fn (of_content μ h1) ↑U = inner_content μ U :=
  induced_outer_measure_eq' (fun (_x : ℕ → set G) => is_open_Union) (inner_content_Union_nat h1 h2)
    inner_content_mono (subtype.property U)

theorem of_content_le {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    (h : ∀ (K₁ K₂ : topological_space.compacts G), subtype.val K₁ ⊆ subtype.val K₂ → μ K₁ ≤ μ K₂)
    (U : topological_space.opens G) (K : topological_space.compacts G) (hUK : ↑U ⊆ subtype.val K) :
    coe_fn (of_content μ h1) ↑U ≤ μ K :=
  has_le.le.trans (eq.le (of_content_opens h2 U)) (inner_content_le h U K hUK)

theorem le_of_content_compacts {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    (K : topological_space.compacts G) : μ K ≤ coe_fn (of_content μ h1) (subtype.val K) :=
  sorry

theorem of_content_eq_infi {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) (A : set G) :
    coe_fn (of_content μ h1) A =
        infi
          fun (U : set G) =>
            infi
              fun (hU : is_open U) =>
                infi fun (h : A ⊆ U) => inner_content μ { val := U, property := hU } :=
  induced_outer_measure_eq_infi is_open_Union (inner_content_Union_nat h1 h2) inner_content_mono A

theorem of_content_interior_compacts {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    (h3 : ∀ (K₁ K₂ : topological_space.compacts G), subtype.val K₁ ⊆ subtype.val K₂ → μ K₁ ≤ μ K₂)
    (K : topological_space.compacts G) :
    coe_fn (of_content μ h1) (interior (subtype.val K)) ≤ μ K :=
  le_trans (le_of_eq (of_content_opens h2 (topological_space.opens.interior (subtype.val K))))
    (inner_content_le h3 (topological_space.opens.interior (subtype.val K)) K interior_subset)

theorem of_content_exists_compact {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂)
    {U : topological_space.opens G} (hU : coe_fn (of_content μ h1) ↑U < ⊤) {ε : nnreal}
    (hε : 0 < ε) :
    ∃ (K : topological_space.compacts G),
        subtype.val K ⊆ ↑U ∧
          coe_fn (of_content μ h1) ↑U ≤ coe_fn (of_content μ h1) (subtype.val K) + ↑ε :=
  sorry

theorem of_content_exists_open {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) {A : set G}
    (hA : coe_fn (of_content μ h1) A < ⊤) {ε : nnreal} (hε : 0 < ε) :
    ∃ (U : topological_space.opens G),
        A ⊆ ↑U ∧ coe_fn (of_content μ h1) ↑U ≤ coe_fn (of_content μ h1) A + ↑ε :=
  sorry

theorem of_content_preimage {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) (f : G ≃ₜ G)
    (h :
      ∀ {K : topological_space.compacts G},
        μ (topological_space.compacts.map (⇑f) (homeomorph.continuous f) K) = μ K)
    (A : set G) : coe_fn (of_content μ h1) (⇑f ⁻¹' A) = coe_fn (of_content μ h1) A :=
  sorry

theorem is_mul_left_invariant_of_content {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) [group G]
    [topological_group G]
    (h :
      ∀ (g : G) {K : topological_space.compacts G},
        μ (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) = μ K)
    (g : G) (A : set G) :
    coe_fn (of_content μ h1) ((fun (h : G) => g * h) ⁻¹' A) = coe_fn (of_content μ h1) A :=
  sorry

theorem of_content_caratheodory {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) (A : set G) :
    measurable_space.is_measurable' (outer_measure.caratheodory (of_content μ h1)) A ↔
        ∀ (U : topological_space.opens G),
          coe_fn (of_content μ h1) (↑U ∩ A) + coe_fn (of_content μ h1) (↑U \ A) ≤
            coe_fn (of_content μ h1) ↑U :=
  sorry

-- @[to_additive] (fails for now)

theorem of_content_pos_of_is_mul_left_invariant {G : Type w} [topological_space G] [t2_space G]
    {μ : topological_space.compacts G → ennreal} {h1 : μ ⊥ = 0}
    (h2 : ∀ (K₁ K₂ : topological_space.compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) [group G]
    [topological_group G]
    (h3 :
      ∀ (g : G) {K : topological_space.compacts G},
        μ (topological_space.compacts.map (fun (b : G) => g * b) (continuous_mul_left g) K) = μ K)
    (K : topological_space.compacts G) (hK : 0 < μ K) {U : set G} (h1U : is_open U)
    (h2U : set.nonempty U) : 0 < coe_fn (of_content μ h1) U :=
  sorry

end Mathlib