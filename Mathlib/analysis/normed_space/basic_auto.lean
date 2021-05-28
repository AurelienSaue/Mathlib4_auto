/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.instances.nnreal
import Mathlib.topology.algebra.module
import Mathlib.topology.metric_space.antilipschitz
import PostPort

universes u_5 l u_1 u_2 u_3 u_4 u_6 u_7 

namespace Mathlib

/-!
# Normed spaces
-/

/-- Auxiliary class, endowing a type `α` with a function `norm : α → ℝ`. This class is designed to
be extended in more interesting classes specifying the properties of the norm. -/
class has_norm (α : Type u_5) 
where
  norm : α → ℝ

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class normed_group (α : Type u_5) 
extends metric_space α, has_norm α, add_comm_group α
where
  dist_eq : ∀ (x y : α), dist x y = norm (x - y)

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist {α : Type u_1} [has_norm α] [add_comm_group α] [metric_space α] (H1 : ∀ (x : α), norm x = dist x 0) (H2 : ∀ (x y z : α), dist x y ≤ dist (x + z) (y + z)) : normed_group α :=
  normed_group.mk sorry

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist' {α : Type u_1} [has_norm α] [add_comm_group α] [metric_space α] (H1 : ∀ (x : α), norm x = dist x 0) (H2 : ∀ (x y z : α), dist (x + z) (y + z) ≤ dist x y) : normed_group α :=
  normed_group.mk sorry

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure normed_group.core (α : Type u_5) [add_comm_group α] [has_norm α] 
where
  norm_eq_zero_iff : ∀ (x : α), norm x = 0 ↔ x = 0
  triangle : ∀ (x y : α), norm (x + y) ≤ norm x + norm y
  norm_neg : ∀ (x : α), norm (-x) = norm x

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
def normed_group.of_core (α : Type u_1) [add_comm_group α] [has_norm α] (C : normed_group.core α) : normed_group α :=
  normed_group.mk sorry

theorem dist_eq_norm {α : Type u_1} [normed_group α] (g : α) (h : α) : dist g h = norm (g - h) :=
  normed_group.dist_eq g h

theorem dist_eq_norm' {α : Type u_1} [normed_group α] (g : α) (h : α) : dist g h = norm (h - g) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist g h = norm (h - g))) (dist_comm g h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist h g = norm (h - g))) (dist_eq_norm h g))) (Eq.refl (norm (h - g))))

@[simp] theorem dist_zero_right {α : Type u_1} [normed_group α] (g : α) : dist g 0 = norm g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist g 0 = norm g)) (dist_eq_norm g 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (norm (g - 0) = norm g)) (sub_zero g))) (Eq.refl (norm g)))

theorem tendsto_norm_cocompact_at_top {α : Type u_1} [normed_group α] [proper_space α] : filter.tendsto norm (filter.cocompact α) filter.at_top := sorry

theorem norm_sub_rev {α : Type u_1} [normed_group α] (g : α) (h : α) : norm (g - h) = norm (h - g) := sorry

@[simp] theorem norm_neg {α : Type u_1} [normed_group α] (g : α) : norm (-g) = norm g := sorry

@[simp] theorem dist_add_left {α : Type u_1} [normed_group α] (g : α) (h₁ : α) (h₂ : α) : dist (g + h₁) (g + h₂) = dist h₁ h₂ := sorry

@[simp] theorem dist_add_right {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h : α) : dist (g₁ + h) (g₂ + h) = dist g₁ g₂ := sorry

@[simp] theorem dist_neg_neg {α : Type u_1} [normed_group α] (g : α) (h : α) : dist (-g) (-h) = dist g h := sorry

@[simp] theorem dist_sub_left {α : Type u_1} [normed_group α] (g : α) (h₁ : α) (h₂ : α) : dist (g - h₁) (g - h₂) = dist h₁ h₂ := sorry

@[simp] theorem dist_sub_right {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h : α) : dist (g₁ - h) (g₂ - h) = dist g₁ g₂ := sorry

/-- Triangle inequality for the norm. -/
theorem norm_add_le {α : Type u_1} [normed_group α] (g : α) (h : α) : norm (g + h) ≤ norm g + norm h := sorry

theorem norm_add_le_of_le {α : Type u_1} [normed_group α] {g₁ : α} {g₂ : α} {n₁ : ℝ} {n₂ : ℝ} (H₁ : norm g₁ ≤ n₁) (H₂ : norm g₂ ≤ n₂) : norm (g₁ + g₂) ≤ n₁ + n₂ :=
  le_trans (norm_add_le g₁ g₂) (add_le_add H₁ H₂)

theorem dist_add_add_le {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h₁ : α) (h₂ : α) : dist (g₁ + g₂) (h₁ + h₂) ≤ dist g₁ h₁ + dist g₂ h₂ := sorry

theorem dist_add_add_le_of_le {α : Type u_1} [normed_group α] {g₁ : α} {g₂ : α} {h₁ : α} {h₂ : α} {d₁ : ℝ} {d₂ : ℝ} (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) : dist (g₁ + g₂) (h₁ + h₂) ≤ d₁ + d₂ :=
  le_trans (dist_add_add_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

theorem dist_sub_sub_le {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h₁ : α) (h₂ : α) : dist (g₁ - g₂) (h₁ - h₂) ≤ dist g₁ h₁ + dist g₂ h₂ := sorry

theorem dist_sub_sub_le_of_le {α : Type u_1} [normed_group α] {g₁ : α} {g₂ : α} {h₁ : α} {h₂ : α} {d₁ : ℝ} {d₂ : ℝ} (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) : dist (g₁ - g₂) (h₁ - h₂) ≤ d₁ + d₂ :=
  le_trans (dist_sub_sub_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

theorem abs_dist_sub_le_dist_add_add {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h₁ : α) (h₂ : α) : abs (dist g₁ h₁ - dist g₂ h₂) ≤ dist (g₁ + g₂) (h₁ + h₂) := sorry

@[simp] theorem norm_nonneg {α : Type u_1} [normed_group α] (g : α) : 0 ≤ norm g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ≤ norm g)) (Eq.symm (dist_zero_right g)))) dist_nonneg

@[simp] theorem norm_eq_zero {α : Type u_1} [normed_group α] {g : α} : norm g = 0 ↔ g = 0 :=
  dist_zero_right g ▸ dist_eq_zero

@[simp] theorem norm_zero {α : Type u_1} [normed_group α] : norm 0 = 0 :=
  iff.mpr norm_eq_zero rfl

theorem norm_of_subsingleton {α : Type u_1} [normed_group α] [subsingleton α] (x : α) : norm x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm x = 0)) (subsingleton.elim x 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (norm 0 = 0)) norm_zero)) (Eq.refl 0))

theorem norm_sum_le {α : Type u_1} [normed_group α] {β : Type u_2} (s : finset β) (f : β → α) : norm (finset.sum s fun (a : β) => f a) ≤ finset.sum s fun (a : β) => norm (f a) :=
  finset.le_sum_of_subadditive norm norm_zero norm_add_le

theorem norm_sum_le_of_le {α : Type u_1} [normed_group α] {β : Type u_2} (s : finset β) {f : β → α} {n : β → ℝ} (h : ∀ (b : β), b ∈ s → norm (f b) ≤ n b) : norm (finset.sum s fun (b : β) => f b) ≤ finset.sum s fun (b : β) => n b :=
  le_trans (norm_sum_le s f) (finset.sum_le_sum h)

@[simp] theorem norm_pos_iff {α : Type u_1} [normed_group α] {g : α} : 0 < norm g ↔ g ≠ 0 :=
  dist_zero_right g ▸ dist_pos

@[simp] theorem norm_le_zero_iff {α : Type u_1} [normed_group α] {g : α} : norm g ≤ 0 ↔ g = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm g ≤ 0 ↔ g = 0)) (Eq.symm (dist_zero_right g)))) dist_le_zero

theorem eq_of_norm_sub_le_zero {α : Type u_1} [normed_group α] {g : α} {h : α} (a : norm (g - h) ≤ 0) : g = h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g = h)) (Eq.symm (propext sub_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (g - h = 0)) (Eq.symm (propext norm_le_zero_iff)))) a)

theorem norm_sub_le {α : Type u_1} [normed_group α] (g : α) (h : α) : norm (g - h) ≤ norm g + norm h := sorry

theorem norm_sub_le_of_le {α : Type u_1} [normed_group α] {g₁ : α} {g₂ : α} {n₁ : ℝ} {n₂ : ℝ} (H₁ : norm g₁ ≤ n₁) (H₂ : norm g₂ ≤ n₂) : norm (g₁ - g₂) ≤ n₁ + n₂ :=
  le_trans (norm_sub_le g₁ g₂) (add_le_add H₁ H₂)

theorem dist_le_norm_add_norm {α : Type u_1} [normed_group α] (g : α) (h : α) : dist g h ≤ norm g + norm h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist g h ≤ norm g + norm h)) (dist_eq_norm g h))) (norm_sub_le g h)

theorem abs_norm_sub_norm_le {α : Type u_1} [normed_group α] (g : α) (h : α) : abs (norm g - norm h) ≤ norm (g - h) := sorry

theorem norm_sub_norm_le {α : Type u_1} [normed_group α] (g : α) (h : α) : norm g - norm h ≤ norm (g - h) :=
  le_trans (le_abs_self (norm g - norm h)) (abs_norm_sub_norm_le g h)

theorem dist_norm_norm_le {α : Type u_1} [normed_group α] (g : α) (h : α) : dist (norm g) (norm h) ≤ norm (g - h) :=
  abs_norm_sub_norm_le g h

theorem eq_of_norm_sub_eq_zero {α : Type u_1} [normed_group α] {u : α} {v : α} (h : norm (u - v) = 0) : u = v :=
  eq_of_dist_eq_zero (eq.mpr (id (Eq._oldrec (Eq.refl (dist u v = 0)) (dist_eq_norm u v))) h)

theorem norm_sub_eq_zero_iff {α : Type u_1} [normed_group α] {u : α} {v : α} : norm (u - v) = 0 ↔ u = v := sorry

theorem norm_le_insert {α : Type u_1} [normed_group α] (u : α) (v : α) : norm v ≤ norm u + norm (u - v) := sorry

theorem ball_0_eq {α : Type u_1} [normed_group α] (ε : ℝ) : metric.ball 0 ε = set_of fun (x : α) => norm x < ε := sorry

theorem mem_ball_iff_norm {α : Type u_1} [normed_group α] {g : α} {h : α} {r : ℝ} : h ∈ metric.ball g r ↔ norm (h - g) < r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (h ∈ metric.ball g r ↔ norm (h - g) < r)) (propext metric.mem_ball)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist h g < r ↔ norm (h - g) < r)) (dist_eq_norm h g)))
      (iff.refl (norm (h - g) < r)))

theorem mem_ball_iff_norm' {α : Type u_1} [normed_group α] {g : α} {h : α} {r : ℝ} : h ∈ metric.ball g r ↔ norm (g - h) < r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (h ∈ metric.ball g r ↔ norm (g - h) < r)) (propext metric.mem_ball')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist g h < r ↔ norm (g - h) < r)) (dist_eq_norm g h)))
      (iff.refl (norm (g - h) < r)))

theorem mem_closed_ball_iff_norm {α : Type u_1} [normed_group α] {g : α} {h : α} {r : ℝ} : h ∈ metric.closed_ball g r ↔ norm (h - g) ≤ r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (h ∈ metric.closed_ball g r ↔ norm (h - g) ≤ r)) (propext metric.mem_closed_ball)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist h g ≤ r ↔ norm (h - g) ≤ r)) (dist_eq_norm h g)))
      (iff.refl (norm (h - g) ≤ r)))

theorem mem_closed_ball_iff_norm' {α : Type u_1} [normed_group α] {g : α} {h : α} {r : ℝ} : h ∈ metric.closed_ball g r ↔ norm (g - h) ≤ r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (h ∈ metric.closed_ball g r ↔ norm (g - h) ≤ r)) (propext metric.mem_closed_ball')))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist g h ≤ r ↔ norm (g - h) ≤ r)) (dist_eq_norm g h)))
      (iff.refl (norm (g - h) ≤ r)))

theorem norm_le_of_mem_closed_ball {α : Type u_1} [normed_group α] {g : α} {h : α} {r : ℝ} (H : h ∈ metric.closed_ball g r) : norm h ≤ norm g + r := sorry

theorem norm_lt_of_mem_ball {α : Type u_1} [normed_group α] {g : α} {h : α} {r : ℝ} (H : h ∈ metric.ball g r) : norm h < norm g + r := sorry

@[simp] theorem mem_sphere_iff_norm {α : Type u_1} [normed_group α] (v : α) (w : α) (r : ℝ) : w ∈ metric.sphere v r ↔ norm (w - v) = r := sorry

@[simp] theorem mem_sphere_zero_iff_norm {α : Type u_1} [normed_group α] {w : α} {r : ℝ} : w ∈ metric.sphere 0 r ↔ norm w = r := sorry

@[simp] theorem norm_eq_of_mem_sphere {α : Type u_1} [normed_group α] {r : ℝ} (x : ↥(metric.sphere 0 r)) : norm ↑x = r :=
  iff.mp mem_sphere_zero_iff_norm (subtype.property x)

theorem nonzero_of_mem_sphere {α : Type u_1} [normed_group α] {r : ℝ} (hr : 0 < r) (x : ↥(metric.sphere 0 r)) : ↑x ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑x ≠ 0)) (Eq.symm (propext norm_pos_iff))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < norm ↑x)) (norm_eq_of_mem_sphere x))) hr)

theorem nonzero_of_mem_unit_sphere {α : Type u_1} [normed_group α] (x : ↥(metric.sphere 0 1)) : ↑x ≠ 0 :=
  nonzero_of_mem_sphere (eq.mpr (id (eq_true_intro zero_lt_one')) trivial) x

/-- We equip the sphere, in a normed group, with a formal operation of negation, namely the
antipodal map. -/
protected instance metric.sphere.has_neg {α : Type u_1} [normed_group α] {r : ℝ} : Neg ↥(metric.sphere 0 r) :=
  { neg := fun (w : ↥(metric.sphere 0 r)) => { val := -↑w, property := sorry } }

@[simp] theorem coe_neg_sphere {α : Type u_1} [normed_group α] {r : ℝ} (v : ↥(metric.sphere 0 r)) : ↑(-v) = -↑v :=
  rfl

theorem normed_group.tendsto_nhds_zero {α : Type u_1} {γ : Type u_3} [normed_group α] {f : γ → α} {l : filter γ} : filter.tendsto f l (nhds 0) ↔ ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (x : γ) => norm (f x) < ε) l := sorry

theorem normed_group.tendsto_nhds_nhds {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] {f : α → β} {x : α} {y : β} : filter.tendsto f (nhds x) (nhds y) ↔
  ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (x' : α), norm (x' - x) < δ → norm (f x' - y) < ε := sorry

/-- A homomorphism `f` of normed groups is Lipschitz, if there exists a constant `C` such that for
all `x`, one has `∥f x∥ ≤ C * ∥x∥`.
The analogous condition for a linear map of normed spaces is in `normed_space.operator_norm`. -/
theorem add_monoid_hom.lipschitz_of_bound {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] (f : α →+ β) (C : ℝ) (h : ∀ (x : α), norm (coe_fn f x) ≤ C * norm x) : lipschitz_with (nnreal.of_real C) ⇑f := sorry

theorem lipschitz_on_with_iff_norm_sub_le {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] {f : α → β} {C : nnreal} {s : set α} : lipschitz_on_with C f s ↔ ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → norm (f x - f y) ≤ ↑C * norm (x - y) := sorry

theorem lipschitz_on_with.norm_sub_le {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] {f : α → β} {C : nnreal} {s : set α} (h : lipschitz_on_with C f s) {x : α} {y : α} (x_in : x ∈ s) (y_in : y ∈ s) : norm (f x - f y) ≤ ↑C * norm (x - y) :=
  iff.mp lipschitz_on_with_iff_norm_sub_le h x x_in y y_in

/-- A homomorphism `f` of normed groups is continuous, if there exists a constant `C` such that for
all `x`, one has `∥f x∥ ≤ C * ∥x∥`.
The analogous condition for a linear map of normed spaces is in `normed_space.operator_norm`. -/
theorem add_monoid_hom.continuous_of_bound {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] (f : α →+ β) (C : ℝ) (h : ∀ (x : α), norm (coe_fn f x) ≤ C * norm x) : continuous ⇑f :=
  lipschitz_with.continuous (add_monoid_hom.lipschitz_of_bound f C h)

/-- Version of the norm taking values in nonnegative reals. -/
def nnnorm {α : Type u_1} [normed_group α] (a : α) : nnreal :=
  { val := norm a, property := norm_nonneg a }

@[simp] theorem coe_nnnorm {α : Type u_1} [normed_group α] (a : α) : ↑(nnnorm a) = norm a :=
  rfl

theorem nndist_eq_nnnorm {α : Type u_1} [normed_group α] (a : α) (b : α) : nndist a b = nnnorm (a - b) :=
  nnreal.eq (dist_eq_norm a b)

@[simp] theorem nnnorm_eq_zero {α : Type u_1} [normed_group α] {a : α} : nnnorm a = 0 ↔ a = 0 := sorry

@[simp] theorem nnnorm_zero {α : Type u_1} [normed_group α] : nnnorm 0 = 0 :=
  nnreal.eq norm_zero

theorem nnnorm_add_le {α : Type u_1} [normed_group α] (g : α) (h : α) : nnnorm (g + h) ≤ nnnorm g + nnnorm h :=
  iff.mpr nnreal.coe_le_coe (norm_add_le g h)

@[simp] theorem nnnorm_neg {α : Type u_1} [normed_group α] (g : α) : nnnorm (-g) = nnnorm g :=
  nnreal.eq (norm_neg g)

theorem nndist_nnnorm_nnnorm_le {α : Type u_1} [normed_group α] (g : α) (h : α) : nndist (nnnorm g) (nnnorm h) ≤ nnnorm (g - h) :=
  iff.mpr nnreal.coe_le_coe (dist_norm_norm_le g h)

theorem of_real_norm_eq_coe_nnnorm {β : Type u_2} [normed_group β] (x : β) : ennreal.of_real (norm x) = ↑(nnnorm x) :=
  ennreal.of_real_eq_coe_nnreal (norm_nonneg x)

theorem edist_eq_coe_nnnorm_sub {β : Type u_2} [normed_group β] (x : β) (y : β) : edist x y = ↑(nnnorm (x - y)) := sorry

theorem edist_eq_coe_nnnorm {β : Type u_2} [normed_group β] (x : β) : edist x 0 = ↑(nnnorm x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (edist x 0 = ↑(nnnorm x))) (edist_eq_coe_nnnorm_sub x 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nnnorm (x - 0)) = ↑(nnnorm x))) (sub_zero x))) (Eq.refl ↑(nnnorm x)))

theorem mem_emetric_ball_0_iff {β : Type u_2} [normed_group β] {x : β} {r : ennreal} : x ∈ emetric.ball 0 r ↔ ↑(nnnorm x) < r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ emetric.ball 0 r ↔ ↑(nnnorm x) < r)) (propext emetric.mem_ball)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (edist x 0 < r ↔ ↑(nnnorm x) < r)) (edist_eq_coe_nnnorm x)))
      (iff.refl (↑(nnnorm x) < r)))

theorem nndist_add_add_le {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h₁ : α) (h₂ : α) : nndist (g₁ + g₂) (h₁ + h₂) ≤ nndist g₁ h₁ + nndist g₂ h₂ :=
  iff.mpr nnreal.coe_le_coe (dist_add_add_le g₁ g₂ h₁ h₂)

theorem edist_add_add_le {α : Type u_1} [normed_group α] (g₁ : α) (g₂ : α) (h₁ : α) (h₂ : α) : edist (g₁ + g₂) (h₁ + h₂) ≤ edist g₁ h₁ + edist g₂ h₂ := sorry

theorem nnnorm_sum_le {α : Type u_1} [normed_group α] {β : Type u_2} (s : finset β) (f : β → α) : nnnorm (finset.sum s fun (a : β) => f a) ≤ finset.sum s fun (a : β) => nnnorm (f a) :=
  finset.le_sum_of_subadditive nnnorm nnnorm_zero nnnorm_add_le

theorem lipschitz_with.neg {β : Type u_2} [normed_group β] {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) : lipschitz_with K fun (x : α) => -f x := sorry

theorem lipschitz_with.add {β : Type u_2} [normed_group β] {α : Type u_1} [emetric_space α] {Kf : nnreal} {f : α → β} (hf : lipschitz_with Kf f) {Kg : nnreal} {g : α → β} (hg : lipschitz_with Kg g) : lipschitz_with (Kf + Kg) fun (x : α) => f x + g x :=
  fun (x y : α) =>
    trans_rel_left LessEq (le_trans (edist_add_add_le (f x) (g x) (f y) (g y)) (add_le_add (hf x y) (hg x y)))
      (Eq.symm (add_mul (↑Kf) (↑Kg) (edist x y)))

theorem lipschitz_with.sub {β : Type u_2} [normed_group β] {α : Type u_1} [emetric_space α] {Kf : nnreal} {f : α → β} (hf : lipschitz_with Kf f) {Kg : nnreal} {g : α → β} (hg : lipschitz_with Kg g) : lipschitz_with (Kf + Kg) fun (x : α) => f x - g x := sorry

theorem antilipschitz_with.add_lipschitz_with {β : Type u_2} [normed_group β] {α : Type u_1} [metric_space α] {Kf : nnreal} {f : α → β} (hf : antilipschitz_with Kf f) {Kg : nnreal} {g : α → β} (hg : lipschitz_with Kg g) (hK : Kg < (Kf⁻¹)) : antilipschitz_with (Kf⁻¹ - Kg⁻¹) fun (x : α) => f x + g x := sorry

/-- A submodule of a normed group is also a normed group, with the restriction of the norm.
As all instances can be inferred from the submodule `s`, they are put as implicit instead of
typeclasses. -/
protected instance submodule.normed_group {𝕜 : Type u_1} {_x : ring 𝕜} {E : Type u_2} [normed_group E] : {_x_1 : module 𝕜 E} → (s : submodule 𝕜 E) → normed_group ↥s :=
  fun (s : submodule 𝕜 E) => normed_group.mk sorry

/-- normed group instance on the product of two normed groups, using the sup norm. -/
protected instance prod.normed_group {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] : normed_group (α × β) :=
  normed_group.mk sorry

theorem prod.norm_def {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] (x : α × β) : norm x = max (norm (prod.fst x)) (norm (prod.snd x)) :=
  rfl

theorem prod.nnnorm_def {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] (x : α × β) : nnnorm x = max (nnnorm (prod.fst x)) (nnnorm (prod.snd x)) := sorry

theorem norm_fst_le {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] (x : α × β) : norm (prod.fst x) ≤ norm x :=
  le_max_left (norm (prod.fst x)) (norm (prod.snd x))

theorem norm_snd_le {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] (x : α × β) : norm (prod.snd x) ≤ norm x :=
  le_max_right (norm (prod.fst x)) (norm (prod.snd x))

theorem norm_prod_le_iff {α : Type u_1} {β : Type u_2} [normed_group α] [normed_group β] {x : α × β} {r : ℝ} : norm x ≤ r ↔ norm (prod.fst x) ≤ r ∧ norm (prod.snd x) ≤ r :=
  max_le_iff

/-- normed group instance on the product of finitely many normed groups, using the sup norm. -/
protected instance pi.normed_group {ι : Type u_4} {π : ι → Type u_1} [fintype ι] [(i : ι) → normed_group (π i)] : normed_group ((i : ι) → π i) :=
  normed_group.mk sorry

/-- The norm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
theorem pi_norm_le_iff {ι : Type u_4} {π : ι → Type u_1} [fintype ι] [(i : ι) → normed_group (π i)] {r : ℝ} (hr : 0 ≤ r) {x : (i : ι) → π i} : norm x ≤ r ↔ ∀ (i : ι), norm (x i) ≤ r := sorry

/-- The norm of an element in a product space is `< r` if and only if the norm of each
component is. -/
theorem pi_norm_lt_iff {ι : Type u_4} {π : ι → Type u_1} [fintype ι] [(i : ι) → normed_group (π i)] {r : ℝ} (hr : 0 < r) {x : (i : ι) → π i} : norm x < r ↔ ∀ (i : ι), norm (x i) < r := sorry

theorem norm_le_pi_norm {ι : Type u_4} {π : ι → Type u_1} [fintype ι] [(i : ι) → normed_group (π i)] (x : (i : ι) → π i) (i : ι) : norm (x i) ≤ norm x :=
  iff.mp (pi_norm_le_iff (norm_nonneg x)) (le_refl (norm x)) i

@[simp] theorem pi_norm_const {α : Type u_1} {ι : Type u_4} [normed_group α] [Nonempty ι] [fintype ι] (a : α) : (norm fun (i : ι) => a) = norm a := sorry

@[simp] theorem pi_nnnorm_const {α : Type u_1} {ι : Type u_4} [normed_group α] [Nonempty ι] [fintype ι] (a : α) : (nnnorm fun (i : ι) => a) = nnnorm a :=
  nnreal.eq (pi_norm_const a)

theorem tendsto_iff_norm_tendsto_zero {β : Type u_2} {ι : Type u_4} [normed_group β] {f : ι → β} {a : filter ι} {b : β} : filter.tendsto f a (nhds b) ↔ filter.tendsto (fun (e : ι) => norm (f e - b)) a (nhds 0) := sorry

theorem tendsto_zero_iff_norm_tendsto_zero {β : Type u_2} {γ : Type u_3} [normed_group β] {f : γ → β} {a : filter γ} : filter.tendsto f a (nhds 0) ↔ filter.tendsto (fun (e : γ) => norm (f e)) a (nhds 0) := sorry

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `g` which tends to `0`, then `f` tends to `0`.
In this pair of lemmas (`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of
similar lemmas in `topology.metric_space.basic` and `topology.algebra.ordered`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
theorem squeeze_zero_norm' {α : Type u_1} {γ : Type u_3} [normed_group α] {f : γ → α} {g : γ → ℝ} {t₀ : filter γ} (h : filter.eventually (fun (n : γ) => norm (f n) ≤ g n) t₀) (h' : filter.tendsto g t₀ (nhds 0)) : filter.tendsto f t₀ (nhds 0) :=
  iff.mpr tendsto_zero_iff_norm_tendsto_zero
    (squeeze_zero' (filter.eventually_of_forall fun (n : γ) => norm_nonneg (f n)) h h')

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `g` which
tends to `0`, then `f` tends to `0`.  -/
theorem squeeze_zero_norm {α : Type u_1} {γ : Type u_3} [normed_group α] {f : γ → α} {g : γ → ℝ} {t₀ : filter γ} (h : ∀ (n : γ), norm (f n) ≤ g n) (h' : filter.tendsto g t₀ (nhds 0)) : filter.tendsto f t₀ (nhds 0) :=
  squeeze_zero_norm' (filter.eventually_of_forall h) h'

theorem tendsto_norm_sub_self {α : Type u_1} [normed_group α] (x : α) : filter.tendsto (fun (g : α) => norm (g - x)) (nhds x) (nhds 0) := sorry

theorem tendsto_norm {α : Type u_1} [normed_group α] {x : α} : filter.tendsto (fun (g : α) => norm g) (nhds x) (nhds (norm x)) := sorry

theorem tendsto_norm_zero {α : Type u_1} [normed_group α] : filter.tendsto (fun (g : α) => norm g) (nhds 0) (nhds 0) := sorry

theorem continuous_norm {α : Type u_1} [normed_group α] : continuous fun (g : α) => norm g := sorry

theorem continuous_nnnorm {α : Type u_1} [normed_group α] : continuous nnnorm :=
  continuous_subtype_mk (fun (a : α) => norm_nonneg a) continuous_norm

theorem tendsto_norm_nhds_within_zero {α : Type u_1} [normed_group α] : filter.tendsto norm (nhds_within 0 (singleton 0ᶜ)) (nhds_within 0 (set.Ioi 0)) :=
  filter.tendsto.inf (continuous.tendsto' continuous_norm 0 0 norm_zero)
    (iff.mpr filter.tendsto_principal_principal fun (x : α) => iff.mpr norm_pos_iff)

theorem filter.tendsto.norm {α : Type u_1} {γ : Type u_3} [normed_group α] {l : filter γ} {f : γ → α} {a : α} (h : filter.tendsto f l (nhds a)) : filter.tendsto (fun (x : γ) => norm (f x)) l (nhds (norm a)) :=
  filter.tendsto.comp tendsto_norm h

theorem filter.tendsto.nnnorm {α : Type u_1} {γ : Type u_3} [normed_group α] {l : filter γ} {f : γ → α} {a : α} (h : filter.tendsto f l (nhds a)) : filter.tendsto (fun (x : γ) => nnnorm (f x)) l (nhds (nnnorm a)) :=
  filter.tendsto.comp (continuous.continuous_at continuous_nnnorm) h

theorem continuous.norm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} (h : continuous f) : continuous fun (x : γ) => norm (f x) :=
  continuous.comp continuous_norm h

theorem continuous.nnnorm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} (h : continuous f) : continuous fun (x : γ) => nnnorm (f x) :=
  continuous.comp continuous_nnnorm h

theorem continuous_at.norm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} {a : γ} (h : continuous_at f a) : continuous_at (fun (x : γ) => norm (f x)) a :=
  filter.tendsto.norm h

theorem continuous_at.nnnorm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} {a : γ} (h : continuous_at f a) : continuous_at (fun (x : γ) => nnnorm (f x)) a :=
  filter.tendsto.nnnorm h

theorem continuous_within_at.norm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} {s : set γ} {a : γ} (h : continuous_within_at f s a) : continuous_within_at (fun (x : γ) => norm (f x)) s a :=
  filter.tendsto.norm h

theorem continuous_within_at.nnnorm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} {s : set γ} {a : γ} (h : continuous_within_at f s a) : continuous_within_at (fun (x : γ) => nnnorm (f x)) s a :=
  filter.tendsto.nnnorm h

theorem continuous_on.norm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} {s : set γ} (h : continuous_on f s) : continuous_on (fun (x : γ) => norm (f x)) s :=
  fun (x : γ) (hx : x ∈ s) => continuous_within_at.norm (h x hx)

theorem continuous_on.nnnorm {α : Type u_1} {γ : Type u_3} [normed_group α] [topological_space γ] {f : γ → α} {s : set γ} (h : continuous_on f s) : continuous_on (fun (x : γ) => nnnorm (f x)) s :=
  fun (x : γ) (hx : x ∈ s) => continuous_within_at.nnnorm (h x hx)

/-- If `∥y∥→∞`, then we can assume `y≠x` for any fixed `x`. -/
theorem eventually_ne_of_tendsto_norm_at_top {α : Type u_1} {γ : Type u_3} [normed_group α] {l : filter γ} {f : γ → α} (h : filter.tendsto (fun (y : γ) => norm (f y)) l filter.at_top) (x : α) : filter.eventually (fun (y : γ) => f y ≠ x) l := sorry

/-- A normed group is a uniform additive group, i.e., addition and subtraction are uniformly
continuous. -/
protected instance normed_uniform_group {α : Type u_1} [normed_group α] : uniform_add_group α :=
  uniform_add_group.mk
    (lipschitz_with.uniform_continuous (lipschitz_with.sub lipschitz_with.prod_fst lipschitz_with.prod_snd))

protected instance normed_top_monoid {α : Type u_1} [normed_group α] : has_continuous_add α :=
  topological_add_group.to_has_continuous_add

protected instance normed_top_group {α : Type u_1} [normed_group α] : topological_add_group α :=
  uniform_add_group.to_topological_add_group

theorem nat.norm_cast_le {α : Type u_1} [normed_group α] [HasOne α] (n : ℕ) : norm ↑n ≤ ↑n * norm 1 := sorry

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_ring (α : Type u_5) 
extends ring α, has_norm α, metric_space α
where
  dist_eq : ∀ (x y : α), dist x y = norm (x - y)
  norm_mul : ∀ (a b : α), norm (a * b) ≤ norm a * norm b

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_comm_ring (α : Type u_5) 
extends normed_ring α
where
  mul_comm : ∀ (x y : α), x * y = y * x

/-- A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class norm_one_class (α : Type u_5) [has_norm α] [HasOne α] 
where
  norm_one : norm 1 = 1

@[simp] theorem nnnorm_one {α : Type u_1} [normed_group α] [HasOne α] [norm_one_class α] : nnnorm 1 = 1 :=
  nnreal.eq norm_one

protected instance normed_comm_ring.to_comm_ring {α : Type u_1} [β : normed_comm_ring α] : comm_ring α :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry normed_comm_ring.mul_comm

protected instance normed_ring.to_normed_group {α : Type u_1} [β : normed_ring α] : normed_group α :=
  normed_group.mk normed_ring.dist_eq

protected instance prod.norm_one_class {α : Type u_1} {β : Type u_2} [normed_group α] [HasOne α] [norm_one_class α] [normed_group β] [HasOne β] [norm_one_class β] : norm_one_class (α × β) :=
  norm_one_class.mk
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : ℝ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℝ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (norm 1) 1
            (Eq.trans
              (Eq.trans (prod.norm_def 1)
                ((fun (a a_1 : ℝ) (e_2 : a = a_1) (b b_1 : ℝ) (e_3 : b = b_1) => congr (congr_arg max e_2) e_3)
                  (norm (prod.fst 1)) 1
                  (Eq.trans ((fun (ᾰ ᾰ_1 : α) (e_2 : ᾰ = ᾰ_1) => congr_arg norm e_2) (prod.fst 1) 1 prod.fst_one)
                    norm_one)
                  (norm (prod.snd 1)) 1
                  (Eq.trans ((fun (ᾰ ᾰ_1 : β) (e_2 : ᾰ = ᾰ_1) => congr_arg norm e_2) (prod.snd 1) 1 prod.snd_one)
                    norm_one)))
              (max_eq_right (le_refl 1)))
            1 1 (Eq.refl 1))
          (propext (eq_self_iff_true 1))))
      trivial)

theorem norm_mul_le {α : Type u_1} [normed_ring α] (a : α) (b : α) : norm (a * b) ≤ norm a * norm b :=
  normed_ring.norm_mul a b

theorem list.norm_prod_le' {α : Type u_1} [normed_ring α] {l : List α} : l ≠ [] → norm (list.prod l) ≤ list.prod (list.map norm l) := sorry

theorem list.norm_prod_le {α : Type u_1} [normed_ring α] [norm_one_class α] (l : List α) : norm (list.prod l) ≤ list.prod (list.map norm l) := sorry

theorem finset.norm_prod_le' {ι : Type u_4} {α : Type u_1} [normed_comm_ring α] (s : finset ι) (hs : finset.nonempty s) (f : ι → α) : norm (finset.prod s fun (i : ι) => f i) ≤ finset.prod s fun (i : ι) => norm (f i) := sorry

theorem finset.norm_prod_le {ι : Type u_4} {α : Type u_1} [normed_comm_ring α] [norm_one_class α] (s : finset ι) (f : ι → α) : norm (finset.prod s fun (i : ι) => f i) ≤ finset.prod s fun (i : ι) => norm (f i) := sorry

/-- If `α` is a normed ring, then `∥a^n∥≤ ∥a∥^n` for `n > 0`. See also `norm_pow_le`. -/
theorem norm_pow_le' {α : Type u_1} [normed_ring α] (a : α) {n : ℕ} : 0 < n → norm (a ^ n) ≤ norm a ^ n := sorry

/-- If `α` is a normed ring with `∥1∥=1`, then `∥a^n∥≤ ∥a∥^n`. See also `norm_pow_le'`. -/
theorem norm_pow_le {α : Type u_1} [normed_ring α] [norm_one_class α] (a : α) (n : ℕ) : norm (a ^ n) ≤ norm a ^ n := sorry

theorem eventually_norm_pow_le {α : Type u_1} [normed_ring α] (a : α) : filter.eventually (fun (n : ℕ) => norm (a ^ n) ≤ norm a ^ n) filter.at_top :=
  iff.mpr filter.eventually_at_top (Exists.intro 1 fun (b : ℕ) (h : b ≥ 1) => norm_pow_le' a (iff.mp nat.succ_le_iff h))

theorem units.norm_pos {α : Type u_1} [normed_ring α] [nontrivial α] (x : units α) : 0 < norm ↑x :=
  iff.mpr norm_pos_iff (units.ne_zero x)

/-- In a normed ring, the left-multiplication `add_monoid_hom` is bounded. -/
theorem mul_left_bound {α : Type u_1} [normed_ring α] (x : α) (y : α) : norm (coe_fn (add_monoid_hom.mul_left x) y) ≤ norm x * norm y :=
  norm_mul_le x

/-- In a normed ring, the right-multiplication `add_monoid_hom` is bounded. -/
theorem mul_right_bound {α : Type u_1} [normed_ring α] (x : α) (y : α) : norm (coe_fn (add_monoid_hom.mul_right x) y) ≤ norm x * norm y := sorry

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
protected instance prod.normed_ring {α : Type u_1} {β : Type u_2} [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
  normed_ring.mk sorry sorry

protected instance normed_ring_top_monoid {α : Type u_1} [normed_ring α] : has_continuous_mul α := sorry

/-- A normed ring is a topological ring. -/
protected instance normed_top_ring {α : Type u_1} [normed_ring α] : topological_ring α := sorry

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class normed_field (α : Type u_5) 
extends metric_space α, has_norm α, field α
where
  dist_eq : ∀ (x y : α), dist x y = norm (x - y)
  norm_mul' : ∀ (a b : α), norm (a * b) = norm a * norm b

/-- A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class nondiscrete_normed_field (α : Type u_5) 
extends normed_field α
where
  non_trivial : ∃ (x : α), 1 < norm x

namespace normed_field


@[simp] theorem norm_mul {α : Type u_1} [normed_field α] (a : α) (b : α) : norm (a * b) = norm a * norm b :=
  norm_mul' a b

protected instance to_normed_comm_ring {α : Type u_1} [normed_field α] : normed_comm_ring α :=
  normed_comm_ring.mk sorry

protected instance to_norm_one_class {α : Type u_1} [normed_field α] : norm_one_class α :=
  norm_one_class.mk
    (mul_left_cancel' (mt (iff.mp norm_eq_zero) one_ne_zero)
      (eq.mpr (id (Eq._oldrec (Eq.refl (norm 1 * norm 1 = norm 1 * 1)) (Eq.symm (norm_mul 1 1))))
        (eq.mpr (id (Eq._oldrec (Eq.refl (norm (1 * 1) = norm 1 * 1)) (mul_one 1)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (norm 1 = norm 1 * 1)) (mul_one (norm 1)))) (Eq.refl (norm 1))))))

@[simp] theorem nnnorm_mul {α : Type u_1} [normed_field α] (a : α) (b : α) : nnnorm (a * b) = nnnorm a * nnnorm b :=
  nnreal.eq (norm_mul a b)

/-- `norm` as a `monoid_hom`. -/
@[simp] theorem norm_hom_apply {α : Type u_1} [normed_field α] : ∀ (ᾰ : α), coe_fn norm_hom ᾰ = norm ᾰ :=
  fun (ᾰ : α) => Eq.refl (coe_fn norm_hom ᾰ)

/-- `nnnorm` as a `monoid_hom`. -/
def nnnorm_hom {α : Type u_1} [normed_field α] : monoid_with_zero_hom α nnreal :=
  monoid_with_zero_hom.mk nnnorm sorry sorry nnnorm_mul

@[simp] theorem norm_pow {α : Type u_1} [normed_field α] (a : α) (n : ℕ) : norm (a ^ n) = norm a ^ n :=
  monoid_hom.map_pow (monoid_with_zero_hom.to_monoid_hom norm_hom) a

@[simp] theorem nnnorm_pow {α : Type u_1} [normed_field α] (a : α) (n : ℕ) : nnnorm (a ^ n) = nnnorm a ^ n :=
  monoid_hom.map_pow (monoid_with_zero_hom.to_monoid_hom nnnorm_hom) a n

@[simp] theorem norm_prod {α : Type u_1} {β : Type u_2} [normed_field α] (s : finset β) (f : β → α) : norm (finset.prod s fun (b : β) => f b) = finset.prod s fun (b : β) => norm (f b) :=
  monoid_hom.map_prod (monoid_with_zero_hom.to_monoid_hom norm_hom) f s

@[simp] theorem nnnorm_prod {α : Type u_1} {β : Type u_2} [normed_field α] (s : finset β) (f : β → α) : nnnorm (finset.prod s fun (b : β) => f b) = finset.prod s fun (b : β) => nnnorm (f b) :=
  monoid_hom.map_prod (monoid_with_zero_hom.to_monoid_hom nnnorm_hom) f s

@[simp] theorem norm_div {α : Type u_1} [normed_field α] (a : α) (b : α) : norm (a / b) = norm a / norm b :=
  monoid_with_zero_hom.map_div norm_hom a b

@[simp] theorem nnnorm_div {α : Type u_1} [normed_field α] (a : α) (b : α) : nnnorm (a / b) = nnnorm a / nnnorm b :=
  monoid_with_zero_hom.map_div nnnorm_hom a b

@[simp] theorem norm_inv {α : Type u_1} [normed_field α] (a : α) : norm (a⁻¹) = (norm a⁻¹) :=
  monoid_with_zero_hom.map_inv' norm_hom a

@[simp] theorem nnnorm_inv {α : Type u_1} [normed_field α] (a : α) : nnnorm (a⁻¹) = (nnnorm a⁻¹) := sorry

@[simp] theorem norm_fpow {α : Type u_1} [normed_field α] (a : α) (n : ℤ) : norm (a ^ n) = norm a ^ n :=
  monoid_with_zero_hom.map_fpow norm_hom

@[simp] theorem nnnorm_fpow {α : Type u_1} [normed_field α] (a : α) (n : ℤ) : nnnorm (a ^ n) = nnnorm a ^ n :=
  monoid_with_zero_hom.map_fpow nnnorm_hom

protected instance has_continuous_inv' {α : Type u_1} [normed_field α] : has_continuous_inv' α :=
  has_continuous_inv'.mk sorry

end normed_field


theorem normed_field.exists_one_lt_norm (α : Type u_1) [nondiscrete_normed_field α] : ∃ (x : α), 1 < norm x :=
  nondiscrete_normed_field.non_trivial

theorem normed_field.exists_norm_lt_one (α : Type u_1) [nondiscrete_normed_field α] : ∃ (x : α), 0 < norm x ∧ norm x < 1 := sorry

theorem normed_field.exists_lt_norm (α : Type u_1) [nondiscrete_normed_field α] (r : ℝ) : ∃ (x : α), r < norm x := sorry

theorem normed_field.exists_norm_lt (α : Type u_1) [nondiscrete_normed_field α] {r : ℝ} (hr : 0 < r) : ∃ (x : α), 0 < norm x ∧ norm x < r := sorry

instance normed_field.punctured_nhds_ne_bot {α : Type u_1} [nondiscrete_normed_field α] (x : α) : filter.ne_bot (nhds_within x (singleton xᶜ)) := sorry

instance normed_field.nhds_within_is_unit_ne_bot {α : Type u_1} [nondiscrete_normed_field α] : filter.ne_bot (nhds_within 0 (set_of fun (x : α) => is_unit x)) := sorry

protected instance real.normed_field : normed_field ℝ :=
  normed_field.mk sorry abs_mul

protected instance real.nondiscrete_normed_field : nondiscrete_normed_field ℝ :=
  nondiscrete_normed_field.mk sorry

namespace real


theorem norm_eq_abs (r : ℝ) : norm r = abs r :=
  rfl

theorem norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : norm x = x :=
  abs_of_nonneg hx

@[simp] theorem norm_coe_nat (n : ℕ) : norm ↑n = ↑n :=
  abs_of_nonneg (nat.cast_nonneg n)

@[simp] theorem nnnorm_coe_nat (n : ℕ) : nnnorm ↑n = ↑n := sorry

@[simp] theorem norm_two : norm (bit0 1) = bit0 1 :=
  abs_of_pos zero_lt_two

@[simp] theorem nnnorm_two : nnnorm (bit0 1) = bit0 1 := sorry

@[simp] theorem nnreal.norm_eq (x : nnreal) : norm ↑x = ↑x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm ↑x = ↑x)) (norm_eq_abs ↑x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑x = ↑x)) (nnreal.abs_eq x))) (Eq.refl ↑x))

theorem nnnorm_coe_eq_self {x : nnreal} : nnnorm ↑x = x :=
  subtype.ext (norm_of_nonneg (zero_le x))

theorem nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : nnnorm x = { val := x, property := hx } :=
  nnnorm_coe_eq_self

theorem ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : ↑(nnnorm x) = ennreal.of_real x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(nnnorm x) = ennreal.of_real x)) (Eq.symm (of_real_norm_eq_coe_nnnorm x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ennreal.of_real (norm x) = ennreal.of_real x)) (norm_of_nonneg hx)))
      (Eq.refl (ennreal.of_real x)))

end real


@[simp] theorem norm_norm {α : Type u_1} [normed_group α] (x : α) : norm (norm x) = norm x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm (norm x) = norm x)) (real.norm_of_nonneg (norm_nonneg x)))) (Eq.refl (norm x))

@[simp] theorem nnnorm_norm {α : Type u_1} [normed_group α] (a : α) : nnnorm (norm a) = nnnorm a := sorry

protected instance int.normed_comm_ring : normed_comm_ring ℤ :=
  normed_comm_ring.mk mul_comm

theorem int.norm_cast_real (m : ℤ) : norm ↑m = norm m :=
  rfl

protected instance int.norm_one_class : norm_one_class ℤ :=
  norm_one_class.mk
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : ℝ) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℝ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (norm 1) 1
            (Eq.trans
              (Eq.trans (Eq.symm (int.norm_cast_real 1))
                ((fun (ᾰ ᾰ_1 : ℝ) (e_2 : ᾰ = ᾰ_1) => congr_arg norm e_2) (↑1) 1 int.cast_one))
              norm_one)
            1 1 (Eq.refl 1))
          (propext (eq_self_iff_true 1))))
      trivial)

protected instance rat.normed_field : normed_field ℚ :=
  normed_field.mk sorry sorry

protected instance rat.nondiscrete_normed_field : nondiscrete_normed_field ℚ :=
  nondiscrete_normed_field.mk sorry

@[simp] theorem rat.norm_cast_real (r : ℚ) : norm ↑r = norm r :=
  rfl

@[simp] theorem int.norm_cast_rat (m : ℤ) : norm ↑m = norm m := sorry

-- Here, we set a rather high priority for the instance `[normed_space α β] : semimodule α β`

-- to take precedence over `semiring.to_semimodule` as this leads to instance paths with better

-- unification properties.

-- see Note[vector space definition] for why we extend `semimodule`.

/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class normed_space (α : Type u_5) (β : Type u_6) [normed_field α] [normed_group β] 
extends semimodule α β
where
  norm_smul_le : ∀ (a : α) (b : β), norm (a • b) ≤ norm a * norm b

protected instance normed_field.to_normed_space {α : Type u_1} [normed_field α] : normed_space α α :=
  normed_space.mk sorry

theorem norm_smul {α : Type u_1} {β : Type u_2} [normed_field α] [normed_group β] [normed_space α β] (s : α) (x : β) : norm (s • x) = norm s * norm x := sorry

@[simp] theorem abs_norm_eq_norm {β : Type u_2} [normed_group β] (z : β) : abs (norm z) = norm z :=
  iff.mpr (abs_eq (norm_nonneg z)) (Or.inl rfl)

theorem dist_smul {α : Type u_1} {β : Type u_2} [normed_field α] [normed_group β] [normed_space α β] (s : α) (x : β) (y : β) : dist (s • x) (s • y) = norm s * dist x y := sorry

theorem nnnorm_smul {α : Type u_1} {β : Type u_2} [normed_field α] [normed_group β] [normed_space α β] (s : α) (x : β) : nnnorm (s • x) = nnnorm s * nnnorm x :=
  nnreal.eq (norm_smul s x)

theorem nndist_smul {α : Type u_1} {β : Type u_2} [normed_field α] [normed_group β] [normed_space α β] (s : α) (x : β) (y : β) : nndist (s • x) (s • y) = nnnorm s * nndist x y :=
  nnreal.eq (dist_smul s x y)

theorem norm_smul_of_nonneg {β : Type u_2} [normed_group β] [normed_space ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) : norm (t • x) = t * norm x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm (t • x) = t * norm x)) (norm_smul t x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (norm t * norm x = t * norm x)) (real.norm_eq_abs t)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (abs t * norm x = t * norm x)) (abs_of_nonneg ht))) (Eq.refl (t * norm x))))

protected instance normed_space.topological_vector_space {α : Type u_1} [normed_field α] {E : Type u_5} [normed_group E] [normed_space α E] : topological_vector_space α E := sorry

theorem closure_ball {E : Type u_5} [normed_group E] [normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : closure (metric.ball x r) = metric.closed_ball x r := sorry

theorem frontier_ball {E : Type u_5} [normed_group E] [normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : frontier (metric.ball x r) = metric.sphere x r := sorry

theorem interior_closed_ball {E : Type u_5} [normed_group E] [normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : interior (metric.closed_ball x r) = metric.ball x r := sorry

theorem interior_closed_ball' {E : Type u_5} [normed_group E] [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) : interior (metric.closed_ball x r) = metric.ball x r := sorry

theorem frontier_closed_ball {E : Type u_5} [normed_group E] [normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) : frontier (metric.closed_ball x r) = metric.sphere x r := sorry

theorem frontier_closed_ball' {E : Type u_5} [normed_group E] [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) : frontier (metric.closed_ball x r) = metric.sphere x r := sorry

theorem ne_neg_of_mem_sphere (α : Type u_1) [normed_field α] {E : Type u_5} [normed_group E] [normed_space α E] [char_zero α] {r : ℝ} (hr : 0 < r) (x : ↥(metric.sphere 0 r)) : x ≠ -x := sorry

theorem ne_neg_of_mem_unit_sphere (α : Type u_1) [normed_field α] {E : Type u_5} [normed_group E] [normed_space α E] [char_zero α] (x : ↥(metric.sphere 0 1)) : x ≠ -x :=
  ne_neg_of_mem_sphere α (eq.mpr (id (eq_true_intro zero_lt_one')) trivial) x

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
theorem rescale_to_shell {α : Type u_1} [normed_field α] {E : Type u_5} [normed_group E] [normed_space α E] {c : α} (hc : 1 < norm c) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) : ∃ (d : α), d ≠ 0 ∧ norm (d • x) < ε ∧ ε / norm c ≤ norm (d • x) ∧ norm d⁻¹ ≤ ε⁻¹ * norm c * norm x := sorry

/-- The product of two normed spaces is a normed space, with the sup norm. -/
protected instance prod.normed_space {α : Type u_1} [normed_field α] {E : Type u_5} {F : Type u_6} [normed_group E] [normed_space α E] [normed_group F] [normed_space α F] : normed_space α (E × F) :=
  normed_space.mk sorry

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
protected instance pi.normed_space {α : Type u_1} {ι : Type u_4} [normed_field α] {E : ι → Type u_2} [fintype ι] [(i : ι) → normed_group (E i)] [(i : ι) → normed_space α (E i)] : normed_space α ((i : ι) → E i) :=
  normed_space.mk sorry

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
protected instance submodule.normed_space {𝕜 : Type u_1} [normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (s : submodule 𝕜 E) : normed_space 𝕜 ↥s :=
  normed_space.mk sorry

/-- A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the embedding of
`𝕜` in `𝕜'` is an isometry. -/
class normed_algebra (𝕜 : Type u_5) (𝕜' : Type u_6) [normed_field 𝕜] [normed_ring 𝕜'] 
extends algebra 𝕜 𝕜'
where
  norm_algebra_map_eq : ∀ (x : 𝕜), norm (coe_fn (algebra_map 𝕜 𝕜') x) = norm x

@[simp] theorem norm_algebra_map_eq {𝕜 : Type u_1} (𝕜' : Type u_2) [normed_field 𝕜] [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] (x : 𝕜) : norm (coe_fn (algebra_map 𝕜 𝕜') x) = norm x :=
  normed_algebra.norm_algebra_map_eq x

protected instance normed_algebra.to_normed_space (𝕜 : Type u_5) [normed_field 𝕜] (𝕜' : Type u_6) [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] : normed_space 𝕜 𝕜' :=
  normed_space.mk sorry

protected instance normed_algebra.id (𝕜 : Type u_5) [normed_field 𝕜] : normed_algebra 𝕜 𝕜 :=
  normed_algebra.mk sorry

@[simp] theorem normed_algebra.norm_one (𝕜 : Type u_5) [normed_field 𝕜] {𝕜' : Type u_6} [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : norm 1 = 1 := sorry

theorem normed_algebra.norm_one_class (𝕜 : Type u_5) [normed_field 𝕜] {𝕜' : Type u_6} [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : norm_one_class 𝕜' :=
  norm_one_class.mk (normed_algebra.norm_one 𝕜)

theorem normed_algebra.zero_ne_one (𝕜 : Type u_5) [normed_field 𝕜] {𝕜' : Type u_6} [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : 0 ≠ 1 := sorry

theorem normed_algebra.nontrivial (𝕜 : Type u_5) [normed_field 𝕜] {𝕜' : Type u_6} [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : nontrivial 𝕜' :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 (normed_algebra.zero_ne_one 𝕜)))

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `semimodule.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def normed_space.restrict_scalars (𝕜 : Type u_5) (𝕜' : Type u_6) [normed_field 𝕜] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] (E : Type u_7) [normed_group E] [normed_space 𝕜' E] : normed_space 𝕜 E :=
  normed_space.mk sorry

protected instance restrict_scalars.normed_group {𝕜 : Type u_1} {𝕜' : Type u_2} {E : Type u_3} [I : normed_group E] : normed_group (restrict_scalars 𝕜 𝕜' E) :=
  I

protected instance semimodule.restrict_scalars.normed_space_orig {𝕜 : Type u_1} {𝕜' : Type u_2} {E : Type u_3} [normed_field 𝕜'] [normed_group E] [I : normed_space 𝕜' E] : normed_space 𝕜' (restrict_scalars 𝕜 𝕜' E) :=
  I

protected instance restrict_scalars.normed_space (𝕜 : Type u_5) (𝕜' : Type u_6) [normed_field 𝕜] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜'] (E : Type u_7) [normed_group E] [normed_space 𝕜' E] : normed_space 𝕜 (restrict_scalars 𝕜 𝕜' E) :=
  normed_space.restrict_scalars 𝕜 𝕜' E

theorem cauchy_seq_finset_iff_vanishing_norm {α : Type u_1} {ι : Type u_4} [normed_group α] {f : ι → α} : (cauchy_seq fun (s : finset ι) => finset.sum s fun (i : ι) => f i) ↔
  ∀ (ε : ℝ), ε > 0 → ∃ (s : finset ι), ∀ (t : finset ι), disjoint t s → norm (finset.sum t fun (i : ι) => f i) < ε := sorry

theorem summable_iff_vanishing_norm {α : Type u_1} {ι : Type u_4} [normed_group α] [complete_space α] {f : ι → α} : summable f ↔
  ∀ (ε : ℝ), ε > 0 → ∃ (s : finset ι), ∀ (t : finset ι), disjoint t s → norm (finset.sum t fun (i : ι) => f i) < ε := sorry

theorem cauchy_seq_finset_of_norm_bounded {α : Type u_1} {ι : Type u_4} [normed_group α] {f : ι → α} (g : ι → ℝ) (hg : summable g) (h : ∀ (i : ι), norm (f i) ≤ g i) : cauchy_seq fun (s : finset ι) => finset.sum s fun (i : ι) => f i := sorry

theorem cauchy_seq_finset_of_summable_norm {α : Type u_1} {ι : Type u_4} [normed_group α] {f : ι → α} (hf : summable fun (a : ι) => norm (f a)) : cauchy_seq fun (s : finset ι) => finset.sum s fun (a : ι) => f a :=
  cauchy_seq_finset_of_norm_bounded (fun (a : ι) => norm (f a)) hf fun (i : ι) => le_refl (norm (f i))

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
theorem has_sum_of_subseq_of_summable {α : Type u_1} {γ : Type u_3} {ι : Type u_4} [normed_group α] {f : ι → α} (hf : summable fun (a : ι) => norm (f a)) {s : γ → finset ι} {p : filter γ} [filter.ne_bot p] (hs : filter.tendsto s p filter.at_top) {a : α} (ha : filter.tendsto (fun (b : γ) => finset.sum (s b) fun (i : ι) => f i) p (nhds a)) : has_sum f a :=
  tendsto_nhds_of_cauchy_seq_of_subseq (cauchy_seq_finset_of_summable_norm hf) hs ha

theorem has_sum_iff_tendsto_nat_of_summable_norm {α : Type u_1} [normed_group α] {f : ℕ → α} {a : α} (hf : summable fun (i : ℕ) => norm (f i)) : has_sum f a ↔ filter.tendsto (fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i) filter.at_top (nhds a) := sorry

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
theorem summable_of_norm_bounded {α : Type u_1} {ι : Type u_4} [normed_group α] [complete_space α] {f : ι → α} (g : ι → ℝ) (hg : summable g) (h : ∀ (i : ι), norm (f i) ≤ g i) : summable f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (summable f)) (propext summable_iff_cauchy_seq_finset)))
    (cauchy_seq_finset_of_norm_bounded g hg h)

theorem has_sum.norm_le_of_bounded {α : Type u_1} {ι : Type u_4} [normed_group α] {f : ι → α} {g : ι → ℝ} {a : α} {b : ℝ} (hf : has_sum f a) (hg : has_sum g b) (h : ∀ (i : ι), norm (f i) ≤ g i) : norm a ≤ b :=
  le_of_tendsto_of_tendsto' (filter.tendsto.norm hf) hg
    fun (s : finset ι) => norm_sum_le_of_le s fun (i : ι) (hi : i ∈ s) => h i

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `∥f i∥ ≤ g i`, then `∥∑' i, f i∥ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem tsum_of_norm_bounded {α : Type u_1} {ι : Type u_4} [normed_group α] {f : ι → α} {g : ι → ℝ} {a : ℝ} (hg : has_sum g a) (h : ∀ (i : ι), norm (f i) ≤ g i) : norm (tsum fun (i : ι) => f i) ≤ a := sorry

/-- If `∑' i, ∥f i∥` is summable, then `∥∑' i, f i∥ ≤ (∑' i, ∥f i∥)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
theorem norm_tsum_le_tsum_norm {α : Type u_1} {ι : Type u_4} [normed_group α] {f : ι → α} (hf : summable fun (i : ι) => norm (f i)) : norm (tsum fun (i : ι) => f i) ≤ tsum fun (i : ι) => norm (f i) :=
  tsum_of_norm_bounded (summable.has_sum hf) fun (i : ι) => le_rfl

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
theorem summable_of_norm_bounded_eventually {α : Type u_1} {ι : Type u_4} [normed_group α] [complete_space α] {f : ι → α} (g : ι → ℝ) (hg : summable g) (h : filter.eventually (fun (i : ι) => norm (f i) ≤ g i) filter.cofinite) : summable f := sorry

theorem summable_of_nnnorm_bounded {α : Type u_1} {ι : Type u_4} [normed_group α] [complete_space α] {f : ι → α} (g : ι → nnreal) (hg : summable g) (h : ∀ (i : ι), nnnorm (f i) ≤ g i) : summable f :=
  summable_of_norm_bounded (fun (i : ι) => ↑(g i)) (iff.mpr nnreal.summable_coe hg) fun (i : ι) => h i

theorem summable_of_summable_norm {α : Type u_1} {ι : Type u_4} [normed_group α] [complete_space α] {f : ι → α} (hf : summable fun (a : ι) => norm (f a)) : summable f :=
  summable_of_norm_bounded (fun (a : ι) => norm (f a)) hf fun (i : ι) => le_refl (norm (f i))

theorem summable_of_summable_nnnorm {α : Type u_1} {ι : Type u_4} [normed_group α] [complete_space α] {f : ι → α} (hf : summable fun (a : ι) => nnnorm (f a)) : summable f :=
  summable_of_nnnorm_bounded (fun (a : ι) => nnnorm (f a)) hf fun (i : ι) => le_refl (nnnorm (f i))

