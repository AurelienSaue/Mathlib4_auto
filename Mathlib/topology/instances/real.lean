/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.basic
import Mathlib.topology.algebra.uniform_group
import Mathlib.topology.algebra.ring
import Mathlib.topology.algebra.continuous_functions
import Mathlib.ring_theory.subring
import Mathlib.group_theory.archimedean
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Topological properties of ℝ
-/

protected instance rat.metric_space : metric_space ℚ :=
  metric_space.induced coe sorry real.metric_space

theorem rat.dist_eq (x : ℚ) (y : ℚ) : dist x y = abs (↑x - ↑y) :=
  rfl

@[simp] theorem rat.dist_cast (x : ℚ) (y : ℚ) : dist ↑x ↑y = dist x y :=
  rfl

-- we want to ignore this instance for the next declaration

protected instance int.metric_space : metric_space ℤ :=
  let M : metric_space ℤ := metric_space.induced coe sorry real.metric_space;
  metric_space.replace_uniformity M sorry

theorem int.dist_eq (x : ℤ) (y : ℤ) : dist x y = abs (↑x - ↑y) :=
  rfl

@[simp] theorem int.dist_cast_real (x : ℤ) (y : ℤ) : dist ↑x ↑y = dist x y :=
  rfl

@[simp] theorem int.dist_cast_rat (x : ℤ) (y : ℤ) : dist ↑x ↑y = dist x y := sorry

theorem uniform_continuous_of_rat : uniform_continuous coe :=
  uniform_continuous_comap

theorem uniform_embedding_of_rat : uniform_embedding coe :=
  uniform_embedding_comap rat.cast_injective

theorem dense_embedding_of_rat : dense_embedding coe := sorry

theorem embedding_of_rat : embedding coe :=
  dense_embedding.to_embedding dense_embedding_of_rat

theorem continuous_of_rat : continuous coe :=
  uniform_continuous.continuous uniform_continuous_of_rat

theorem real.uniform_continuous_add : uniform_continuous fun (p : ℝ × ℝ) => prod.fst p + prod.snd p := sorry

-- TODO(Mario): Find a way to use rat_add_continuous_lemma

theorem rat.uniform_continuous_add : uniform_continuous fun (p : ℚ × ℚ) => prod.fst p + prod.snd p := sorry

theorem real.uniform_continuous_neg : uniform_continuous Neg.neg := sorry

theorem rat.uniform_continuous_neg : uniform_continuous Neg.neg := sorry

protected instance real.uniform_add_group : uniform_add_group ℝ :=
  uniform_add_group.mk' real.uniform_continuous_add real.uniform_continuous_neg

protected instance rat.uniform_add_group : uniform_add_group ℚ :=
  uniform_add_group.mk' rat.uniform_continuous_add rat.uniform_continuous_neg

protected instance real.topological_add_group : topological_add_group ℝ :=
  linear_ordered_add_comm_group.topological_add_group

protected instance rat.topological_add_group : topological_add_group ℚ :=
  uniform_add_group.to_topological_add_group

protected instance rat.order_topology : order_topology ℚ :=
  induced_order_topology coe (fun (x y : ℚ) => rat.cast_lt) exists_rat_btwn

theorem real.is_topological_basis_Ioo_rat : topological_space.is_topological_basis
  (set.Union fun (a : ℚ) => set.Union fun (b : ℚ) => set.Union fun (h : a < b) => singleton (set.Ioo ↑a ↑b)) := sorry

protected instance real.topological_space.second_countable_topology : topological_space.second_countable_topology ℝ := sorry

/- TODO(Mario): Prove that these are uniform isomorphisms instead of uniform embeddings
lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (λp:ℚ, p + r) :=
_

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding ((*) q) :=
_ -/

theorem real.mem_closure_iff {s : set ℝ} {x : ℝ} : x ∈ closure s ↔ ∀ (ε : ℝ) (H : ε > 0), ∃ (y : ℝ), ∃ (H : y ∈ s), abs (y - x) < ε := sorry

theorem real.uniform_continuous_inv (s : set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ (x : ℝ), x ∈ s → r ≤ abs x) : uniform_continuous fun (p : ↥s) => subtype.val p⁻¹ := sorry

theorem real.uniform_continuous_abs : uniform_continuous abs :=
  iff.mpr metric.uniform_continuous_iff
    fun (ε : ℝ) (ε0 : ε > 0) =>
      Exists.intro ε (Exists.intro ε0 fun (a b : ℝ) => lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub a b))

theorem rat.uniform_continuous_abs : uniform_continuous abs := sorry

theorem real.tendsto_inv {r : ℝ} (r0 : r ≠ 0) : filter.tendsto (fun (q : ℝ) => q⁻¹) (nhds r) (nhds (r⁻¹)) := sorry

theorem real.continuous_inv : continuous fun (a : Subtype fun (r : ℝ) => r ≠ 0) => subtype.val a⁻¹ := sorry

theorem real.continuous.inv {α : Type u} [topological_space α] {f : α → ℝ} (h : ∀ (a : α), f a ≠ 0) (hf : continuous f) : continuous fun (a : α) => f a⁻¹ :=
  (fun (this : continuous ((has_inv.inv ∘ subtype.val) ∘ fun (a : α) => { val := f a, property := h a })) => this)
    (continuous.comp real.continuous_inv (continuous_subtype_mk (fun (a : α) => h a) hf))

theorem real.uniform_continuous_mul_const {x : ℝ} : uniform_continuous (Mul.mul x) := sorry

theorem real.uniform_continuous_mul (s : set (ℝ × ℝ)) {r₁ : ℝ} {r₂ : ℝ} (H : ∀ (x : ℝ × ℝ), x ∈ s → abs (prod.fst x) < r₁ ∧ abs (prod.snd x) < r₂) : uniform_continuous fun (p : ↥s) => prod.fst (subtype.val p) * prod.snd (subtype.val p) := sorry

protected theorem real.continuous_mul : continuous fun (p : ℝ × ℝ) => prod.fst p * prod.snd p := sorry

protected instance real.topological_ring : topological_ring ℝ :=
  topological_ring.mk continuous_neg

protected instance real.topological_semiring : topological_semiring ℝ :=
  topological_ring.to_topological_semiring ℝ

theorem rat.continuous_mul : continuous fun (p : ℚ × ℚ) => prod.fst p * prod.snd p := sorry

protected instance rat.topological_ring : topological_ring ℚ :=
  topological_ring.mk continuous_neg

theorem real.ball_eq_Ioo (x : ℝ) (ε : ℝ) : metric.ball x ε = set.Ioo (x - ε) (x + ε) := sorry

theorem real.Ioo_eq_ball (x : ℝ) (y : ℝ) : set.Ioo x y = metric.ball ((x + y) / bit0 1) ((y - x) / bit0 1) := sorry

theorem real.totally_bounded_Ioo (a : ℝ) (b : ℝ) : totally_bounded (set.Ioo a b) := sorry

theorem real.totally_bounded_ball (x : ℝ) (ε : ℝ) : totally_bounded (metric.ball x ε) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (totally_bounded (metric.ball x ε))) (real.ball_eq_Ioo x ε)))
    (real.totally_bounded_Ioo (x - ε) (x + ε))

theorem real.totally_bounded_Ico (a : ℝ) (b : ℝ) : totally_bounded (set.Ico a b) := sorry

theorem real.totally_bounded_Icc (a : ℝ) (b : ℝ) : totally_bounded (set.Icc a b) := sorry

theorem rat.totally_bounded_Icc (a : ℚ) (b : ℚ) : totally_bounded (set.Icc a b) := sorry

protected instance real.complete_space : complete_space ℝ := sorry

theorem closure_of_rat_image_lt {q : ℚ} : closure (coe '' set_of fun (x : ℚ) => q < x) = set_of fun (r : ℝ) => ↑q ≤ r := sorry

/- TODO(Mario): Put these back only if needed later
lemma closure_of_rat_image_le_eq {q : ℚ} : closure ((coe:ℚ → ℝ) '' {x | q ≤ x}) = {r | ↑q ≤ r} :=
_

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
  closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
_-/

theorem compact_Icc {a : ℝ} {b : ℝ} : is_compact (set.Icc a b) :=
  compact_of_totally_bounded_is_closed (real.totally_bounded_Icc a b)
    (is_closed_inter (is_closed_ge' a) (is_closed_le' b))

theorem compact_pi_Icc {ι : Type u_1} {a : ι → ℝ} {b : ι → ℝ} : is_compact (set.Icc a b) :=
  Eq.subst (set.pi_univ_Icc a b) compact_univ_pi fun (i : ι) => compact_Icc

protected instance real.proper_space : proper_space ℝ :=
  proper_space.mk
    fun (x r : ℝ) => eq.mpr (id (Eq._oldrec (Eq.refl (is_compact (metric.closed_ball x r))) closed_ball_Icc)) compact_Icc

theorem real.bounded_iff_bdd_below_bdd_above {s : set ℝ} : metric.bounded s ↔ bdd_below s ∧ bdd_above s := sorry

theorem real.image_Icc {f : ℝ → ℝ} {a : ℝ} {b : ℝ} (hab : a ≤ b) (h : continuous_on f (set.Icc a b)) : f '' set.Icc a b = set.Icc (Inf (f '' set.Icc a b)) (Sup (f '' set.Icc a b)) := sorry

protected instance reals_semimodule : topological_semimodule ℝ ℝ :=
  topological_semimodule.mk continuous_mul

protected instance real_maps_algebra {α : Type u_1} [topological_space α] : algebra ℝ (continuous_map α ℝ) :=
  Mathlib.continuous_map_algebra

/-- Given a nontrivial subgroup `G ⊆ ℝ`, if `G ∩ ℝ_{>0}` has no minimum then `G` is dense. -/
theorem real.subgroup_dense_of_no_min {G : add_subgroup ℝ} {g₀ : ℝ} (g₀_in : g₀ ∈ G) (g₀_ne : g₀ ≠ 0) (H' : ¬∃ (a : ℝ), is_least (set_of fun (g : ℝ) => g ∈ G ∧ 0 < g) a) : dense ↑G := sorry

/-- Subgroups of `ℝ` are either dense or cyclic. See `real.subgroup_dense_of_no_min` and
`subgroup_cyclic_of_min` for more precise statements. -/
theorem real.subgroup_dense_or_cyclic (G : add_subgroup ℝ) : dense ↑G ∨ ∃ (a : ℝ), G = add_subgroup.closure (singleton a) := sorry

