/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sébastien Gouëzel

Construction of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces -/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.gluing
import Mathlib.topology.metric_space.hausdorff_distance
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace Gromov_Hausdorff


/- This section shows that the Gromov-Hausdorff distance
is realized. For this, we consider candidate distances on the disjoint union
α ⊕ β of two compact nonempty metric spaces, almost realizing the Gromov-Hausdorff
distance, and show that they form a compact family by applying Arzela-Ascoli
theorem. The existence of a minimizer follows. -/

/-- The set of functions on α ⊕ β that are candidates distances to realize the
minimum of the Hausdorff distances between α and β in a coupling -/
def candidates (α : Type u) (β : Type v) [metric_space α] [compact_space α] [Nonempty α]
    [metric_space β] [compact_space β] [Nonempty β] : set (prod_space_fun α β) :=
  set_of
    fun (f : prod_space_fun α β) =>
      (((((∀ (x y : α), f (sum.inl x, sum.inl y) = dist x y) ∧
                ∀ (x y : β), f (sum.inr x, sum.inr y) = dist x y) ∧
              ∀ (x y : α ⊕ β), f (x, y) = f (y, x)) ∧
            ∀ (x y z : α ⊕ β), f (x, z) ≤ f (x, y) + f (y, z)) ∧
          ∀ (x : α ⊕ β), f (x, x) = 0) ∧
        ∀ (x y : α ⊕ β), f (x, y) ≤ ↑(max_var α β)

/-- Version of the set of candidates in bounded_continuous_functions, to apply
Arzela-Ascoli -/
/-- candidates are bounded by max_var α β -/
/-- Technical lemma to prove that candidates are Lipschitz -/
/-- Candidates are Lipschitz -/
/-- candidates give rise to elements of bounded_continuous_functions -/
def candidates_b_of_candidates {α : Type u} {β : Type v} [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] (f : prod_space_fun α β)
    (fA : f ∈ candidates α β) : Cb α β :=
  bounded_continuous_function.mk_of_compact f sorry

theorem candidates_b_of_candidates_mem {α : Type u} {β : Type v} [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] (f : prod_space_fun α β)
    (fA : f ∈ candidates α β) : candidates_b_of_candidates f fA ∈ candidates_b α β :=
  fA

/-- The distance on α ⊕ β is a candidate -/
def candidates_b_dist (α : Type u) (β : Type v) [metric_space α] [compact_space α] [Inhabited α]
    [metric_space β] [compact_space β] [Inhabited β] : Cb α β :=
  candidates_b_of_candidates (fun (p : (α ⊕ β) × (α ⊕ β)) => dist (prod.fst p) (prod.snd p)) sorry

theorem candidates_b_dist_mem_candidates_b {α : Type u} {β : Type v} [metric_space α]
    [compact_space α] [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] :
    candidates_b_dist α β ∈ candidates_b α β :=
  candidates_b_of_candidates_mem (fun (p : (α ⊕ β) × (α ⊕ β)) => dist (prod.fst p) (prod.snd p))
    (candidates_b_dist._proof_1 α β)

/-- To apply Arzela-Ascoli, we need to check that the set of candidates is closed and equicontinuous.
Equicontinuity follows from the Lipschitz control, we check closedness -/
/-- Compactness of candidates (in bounded_continuous_functions) follows -/
/-- We will then choose the candidate minimizing the Hausdorff distance. Except that we are not
in a metric space setting, so we need to define our custom version of Hausdorff distance,
called HD, and prove its basic properties. -/
def HD {α : Type u} {β : Type v} [metric_space α] [compact_space α] [Nonempty α] [metric_space β]
    [compact_space β] [Nonempty β] (f : Cb α β) : ℝ :=
  max (supr fun (x : α) => infi fun (y : β) => coe_fn f (sum.inl x, sum.inr y))
    (supr fun (y : β) => infi fun (x : α) => coe_fn f (sum.inl x, sum.inr y))

/- We will show that HD is continuous on bounded_continuous_functions, to deduce that its
minimum on the compact set candidates_b is attained. Since it is defined in terms of
infimum and supremum on ℝ, which is only conditionnally complete, we will need all the time
to check that the defining sets are bounded below or above. This is done in the next few
technical lemmas -/

theorem HD_below_aux1 {α : Type u} {β : Type v} [metric_space α] [compact_space α] [Nonempty α]
    [metric_space β] [compact_space β] [Nonempty β] {f : Cb α β} (C : ℝ) {x : α} :
    bdd_below (set.range fun (y : β) => coe_fn f (sum.inl x, sum.inr y) + C) :=
  sorry

theorem HD_below_aux2 {α : Type u} {β : Type v} [metric_space α] [compact_space α] [Nonempty α]
    [metric_space β] [compact_space β] [Nonempty β] {f : Cb α β} (C : ℝ) {y : β} :
    bdd_below (set.range fun (x : α) => coe_fn f (sum.inl x, sum.inr y) + C) :=
  sorry

/-- Explicit bound on HD (dist). This means that when looking for minimizers it will
be sufficient to look for functions with HD(f) bounded by this bound. -/
theorem HD_candidates_b_dist_le {α : Type u} {β : Type v} [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] :
    HD (candidates_b_dist α β) ≤ metric.diam set.univ + 1 + metric.diam set.univ :=
  sorry

/- To check that HD is continuous, we check that it is Lipschitz. As HD is a max, we
prove separately inequalities controlling the two terms (relying too heavily on copy-paste...) -/

/-- Conclude that HD, being Lipschitz, is continuous -/
/- Now that we have proved that the set of candidates is compact, and that HD is continuous,
we can finally select a candidate minimizing HD. This will be the candidate realizing the
optimal coupling. -/

/-- With the optimal candidate, construct a premetric space structure on α ⊕ β, on which the
predistance is given by the candidate. Then, we will identify points at 0 predistance
to obtain a genuine metric space -/
def premetric_optimal_GH_dist (α : Type u) (β : Type v) [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] : premetric_space (α ⊕ β) :=
  premetric_space.mk sorry sorry sorry

/-- A metric space which realizes the optimal coupling between α and β -/
def optimal_GH_coupling (α : Type u) (β : Type v) [metric_space α] [compact_space α] [Nonempty α]
    [metric_space β] [compact_space β] [Nonempty β] :=
  premetric.metric_quot (α ⊕ β)

/-- Injection of α in the optimal coupling between α and β -/
def optimal_GH_injl (α : Type u) (β : Type v) [metric_space α] [compact_space α] [Nonempty α]
    [metric_space β] [compact_space β] [Nonempty β] (x : α) : optimal_GH_coupling α β :=
  quotient.mk (sum.inl x)

/-- The injection of α in the optimal coupling between α and β is an isometry. -/
theorem isometry_optimal_GH_injl (α : Type u) (β : Type v) [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] : isometry (optimal_GH_injl α β) :=
  iff.mpr isometry_emetric_iff_metric
    fun (x y : α) => id (candidates_dist_inl (optimal_GH_dist_mem_candidates_b α β) x y)

/-- Injection of β  in the optimal coupling between α and β -/
def optimal_GH_injr (α : Type u) (β : Type v) [metric_space α] [compact_space α] [Nonempty α]
    [metric_space β] [compact_space β] [Nonempty β] (y : β) : optimal_GH_coupling α β :=
  quotient.mk (sum.inr y)

/-- The injection of β in the optimal coupling between α and β is an isometry. -/
theorem isometry_optimal_GH_injr (α : Type u) (β : Type v) [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] : isometry (optimal_GH_injr α β) :=
  iff.mpr isometry_emetric_iff_metric
    fun (x y : β) => id (candidates_dist_inr (optimal_GH_dist_mem_candidates_b α β) x y)

/-- The optimal coupling between two compact spaces α and β is still a compact space -/
protected instance compact_space_optimal_GH_coupling (α : Type u) (β : Type v) [metric_space α]
    [compact_space α] [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] :
    compact_space (optimal_GH_coupling α β) :=
  sorry

/-- For any candidate f, HD(f) is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
theorem Hausdorff_dist_optimal_le_HD (α : Type u) (β : Type v) [metric_space α] [compact_space α]
    [Nonempty α] [metric_space β] [compact_space β] [Nonempty β] {f : Cb α β}
    (h : f ∈ candidates_b α β) :
    metric.Hausdorff_dist (set.range (optimal_GH_injl α β)) (set.range (optimal_GH_injr α β)) ≤
        HD f :=
  sorry

end Mathlib