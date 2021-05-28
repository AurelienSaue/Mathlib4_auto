/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.closeds
import Mathlib.set_theory.cardinal
import Mathlib.topology.metric_space.gromov_hausdorff_realized
import Mathlib.topology.metric_space.completion
import Mathlib.PostPort

universes u v w l 

namespace Mathlib

/-!
# Gromov-Hausdorff distance

This file defines the Gromov-Hausdorff distance on the space of nonempty compact metric spaces
up to isometry.

We introduce the space of all nonempty compact metric spaces, up to isometry,
called `GH_space`, and endow it with a metric space structure. The distance,
known as the Gromov-Hausdorff distance, is defined as follows: given two
nonempty compact spaces `X` and `Y`, their distance is the minimum Hausdorff distance
between all possible isometric embeddings of `X` and `Y` in all metric spaces.
To define properly the Gromov-Hausdorff space, we consider the non-empty
compact subsets of `ℓ^∞(ℝ)` up to isometry, which is a well-defined type,
and define the distance as the infimum of the Hausdorff distance over all
embeddings in `ℓ^∞(ℝ)`. We prove that this coincides with the previous description,
as all separable metric spaces embed isometrically into `ℓ^∞(ℝ)`, through an
embedding called the Kuratowski embedding.
To prove that we have a distance, we should show that if spaces can be coupled
to be arbitrarily close, then they are isometric. More generally, the Gromov-Hausdorff
distance is realized, i.e., there is a coupling for which the Hausdorff distance
is exactly the Gromov-Hausdorff distance. This follows from a compactness
argument, essentially following from Arzela-Ascoli.

## Main results

We prove the most important properties of the Gromov-Hausdorff space: it is a polish space,
i.e., it is complete and second countable. We also prove the Gromov compactness criterion.

-/

namespace Gromov_Hausdorff


/- In this section, we define the Gromov-Hausdorff space, denoted `GH_space` as the quotient
of nonempty compact subsets of `ℓ^∞(ℝ)` by identifying isometric sets.
Using the Kuratwoski embedding, we get a canonical map `to_GH_space` mapping any nonempty
compact type to `GH_space`. -/

/-- Equivalence relation identifying two nonempty compact sets which are isometric -/
/-- This is indeed an equivalence relation -/
/-- setoid instance identifying two isometric nonempty compact subspaces of ℓ^∞(ℝ) -/
protected instance isometry_rel.setoid : setoid (topological_space.nonempty_compacts ℓ_infty_ℝ) :=
  setoid.mk isometry_rel is_equivalence_isometry_rel

/-- The Gromov-Hausdorff space -/
def GH_space  :=
  quotient isometry_rel.setoid

/-- Map any nonempty compact type to `GH_space` -/
def to_GH_space (α : Type u) [metric_space α] [compact_space α] [Nonempty α] : GH_space :=
  quotient.mk (nonempty_compacts.Kuratowski_embedding α)

protected instance GH_space.inhabited : Inhabited GH_space :=
  { default := Quot.mk setoid.r { val := singleton 0, property := sorry } }

/-- A metric space representative of any abstract point in `GH_space` -/
def GH_space.rep (p : GH_space)  :=
  ↥(subtype.val (quot.out p))

theorem eq_to_GH_space_iff {α : Type u} [metric_space α] [compact_space α] [Nonempty α] {p : topological_space.nonempty_compacts ℓ_infty_ℝ} : quotient.mk p = to_GH_space α ↔ ∃ (Ψ : α → ℓ_infty_ℝ), isometry Ψ ∧ set.range Ψ = subtype.val p := sorry

theorem eq_to_GH_space {p : topological_space.nonempty_compacts ℓ_infty_ℝ} : quotient.mk p = to_GH_space ↥(subtype.val p) :=
  iff.mpr eq_to_GH_space_iff
    (Exists.intro (fun (x : ↥(subtype.val p)) => ↑x) { left := isometry_subtype_coe, right := subtype.range_coe })

protected instance rep_GH_space_metric_space {p : GH_space} : metric_space (GH_space.rep p) :=
  subtype.metric_space

protected instance rep_GH_space_compact_space {p : GH_space} : compact_space (GH_space.rep p) :=
  topological_space.nonempty_compacts.to_compact_space

protected instance rep_GH_space_nonempty {p : GH_space} : Nonempty (GH_space.rep p) :=
  topological_space.nonempty_compacts.to_nonempty

theorem GH_space.to_GH_space_rep (p : GH_space) : to_GH_space (GH_space.rep p) = p :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (to_GH_space ↥(subtype.val (quot.out p)) = p)) (Eq.symm eq_to_GH_space)))
      (quot.out_eq p))

/-- Two nonempty compact spaces have the same image in `GH_space` if and only if they are
isometric. -/
theorem to_GH_space_eq_to_GH_space_iff_isometric {α : Type u} [metric_space α] [compact_space α] [Nonempty α] {β : Type u} [metric_space β] [compact_space β] [Nonempty β] : to_GH_space α = to_GH_space β ↔ Nonempty (α ≃ᵢ β) := sorry

/-- Distance on `GH_space`: the distance between two nonempty compact spaces is the infimum
Hausdorff distance between isometric copies of the two spaces in a metric space. For the definition,
we only consider embeddings in `ℓ^∞(ℝ)`, but we will prove below that it works for all spaces. -/
protected instance GH_space.has_dist : has_dist GH_space :=
  has_dist.mk
    fun (x y : GH_space) =>
      Inf
        ((fun (p : topological_space.nonempty_compacts ℓ_infty_ℝ × topological_space.nonempty_compacts ℓ_infty_ℝ) =>
            metric.Hausdorff_dist (subtype.val (prod.fst p)) (subtype.val (prod.snd p))) ''
          set.prod (set_of fun (a : topological_space.nonempty_compacts ℓ_infty_ℝ) => quotient.mk a = x)
            (set_of fun (b : topological_space.nonempty_compacts ℓ_infty_ℝ) => quotient.mk b = y))

/-- The Gromov-Hausdorff distance between two nonempty compact metric spaces, equal by definition to
the distance of the equivalence classes of these spaces in the Gromov-Hausdorff space. -/
def GH_dist (α : Type u) (β : Type v) [metric_space α] [Nonempty α] [compact_space α] [metric_space β] [Nonempty β] [compact_space β] : ℝ :=
  dist (to_GH_space α) (to_GH_space β)

theorem dist_GH_dist (p : GH_space) (q : GH_space) : dist p q = GH_dist (GH_space.rep p) (GH_space.rep q) := sorry

/-- The Gromov-Hausdorff distance between two spaces is bounded by the Hausdorff distance
of isometric copies of the spaces, in any metric space. -/
theorem GH_dist_le_Hausdorff_dist {α : Type u} [metric_space α] [compact_space α] [Nonempty α] {β : Type v} [metric_space β] [compact_space β] [Nonempty β] {γ : Type w} [metric_space γ] {Φ : α → γ} {Ψ : β → γ} (ha : isometry Φ) (hb : isometry Ψ) : GH_dist α β ≤ metric.Hausdorff_dist (set.range Φ) (set.range Ψ) := sorry

/-- The optimal coupling constructed above realizes exactly the Gromov-Hausdorff distance,
essentially by design. -/
theorem Hausdorff_dist_optimal {α : Type u} [metric_space α] [compact_space α] [Nonempty α] {β : Type v} [metric_space β] [compact_space β] [Nonempty β] : metric.Hausdorff_dist (set.range (optimal_GH_injl α β)) (set.range (optimal_GH_injr α β)) = GH_dist α β := sorry

/-- The Gromov-Hausdorff distance can also be realized by a coupling in `ℓ^∞(ℝ)`, by embedding
the optimal coupling through its Kuratowski embedding. -/
theorem GH_dist_eq_Hausdorff_dist (α : Type u) [metric_space α] [compact_space α] [Nonempty α] (β : Type v) [metric_space β] [compact_space β] [Nonempty β] : ∃ (Φ : α → ℓ_infty_ℝ),
  ∃ (Ψ : β → ℓ_infty_ℝ), isometry Φ ∧ isometry Ψ ∧ GH_dist α β = metric.Hausdorff_dist (set.range Φ) (set.range Ψ) := sorry

-- without the next two lines, `{ exact hΦ.is_closed }` in the next

-- proof is very slow, as the `t2_space` instance is very hard to find

/-- The Gromov-Hausdorff distance defines a genuine distance on the Gromov-Hausdorff space. -/
protected instance GH_space_metric_space : metric_space GH_space := sorry

end Gromov_Hausdorff


/-- In particular, nonempty compacts of a metric space map to `GH_space`. We register this
in the topological_space namespace to take advantage of the notation `p.to_GH_space`. -/
def topological_space.nonempty_compacts.to_GH_space {α : Type u} [metric_space α] (p : topological_spa