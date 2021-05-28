/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.emetric_space
import Mathlib.topology.algebra.ordered
import Mathlib.PostPort

universes u u_1 l v u_2 

namespace Mathlib

/-- Construct a uniform structure from a distance function and metric space axioms -/
def uniform_space_of_dist {α : Type u} (dist : α → α → ℝ) (dist_self : ∀ (x : α), dist x x = 0) (dist_comm : ∀ (x y : α), dist x y = dist y x) (dist_triangle : ∀ (x y z : α), dist x z ≤ dist x y + dist y z) : uniform_space α :=
  uniform_space.of_core
    (uniform_space.core.mk
      (infi
        fun (ε : ℝ) =>
          infi fun (H : ε > 0) => filter.principal (set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε))
      sorry sorry sorry)

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
class has_dist (α : Type u_1) 
where
  dist : α → α → ℝ

-- the uniform structure and the emetric space structure are embedded in the metric space structure

-- to avoid instance diamond issues. See Note [forgetful inheritance].

/-- Metric space

Each metric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `metric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. In the same way, each metric space induces an emetric space structure.
It is included in the structure, but filled in by default.
-/
class metric_space (α : Type u) 
extends uniform_space #2, metric_space.to_uniform_space._default #2 #1 #0 α _to_has_dist = id (uniform_space_of_dist dist #0 α _to_has_dist), uniform_space α, has_dist α
where
  dist_self : ∀ (x : α), dist x x = 0
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
  dist_comm : ∀ (x y : α), dist x y = dist y x
  dist_triangle : ∀ (x y z : α), dist x z ≤ dist x y + dist y z
  edist : α → α → ennreal
  edist_dist : autoParam (∀ (x y : α), edist x y = ennreal.of_real (dist x y))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])
  to_uniform_space : uniform_space α
  uniformity_dist : autoParam
  (uniformity α =
    infi
      fun (ε : ℝ) =>
        infi fun (H : ε > 0) => filter.principal (set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])

protected instance metric_space.to_uniform_space' {α : Type u} [metric_space α] : uniform_space α :=
  metric_space.to_uniform_space

protected instance metric_space.to_has_edist {α : Type u} [metric_space α] : has_edist α :=
  has_edist.mk metric_space.edist

@[simp] theorem dist_self {α : Type u} [metric_space α] (x : α) : dist x x = 0 :=
  metric_space.dist_self x

theorem eq_of_dist_eq_zero {α : Type u} [metric_space α] {x : α} {y : α} : dist x y = 0 → x = y :=
  metric_space.eq_of_dist_eq_zero

theorem dist_comm {α : Type u} [metric_space α] (x : α) (y : α) : dist x y = dist y x :=
  metric_space.dist_comm x y

theorem edist_dist {α : Type u} [metric_space α] (x : α) (y : α) : edist x y = ennreal.of_real (dist x y) :=
  metric_space.edist_dist x y

@[simp] theorem dist_eq_zero {α : Type u} [metric_space α] {x : α} {y : α} : dist x y = 0 ↔ x = y :=
  { mp := eq_of_dist_eq_zero, mpr := fun (this : x = y) => this ▸ dist_self x }

@[simp] theorem zero_eq_dist {α : Type u} [metric_space α] {x : α} {y : α} : 0 = dist x y ↔ x = y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 = dist x y ↔ x = y)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (dist x y = 0 ↔ x = y)) (propext dist_eq_zero))) (iff.refl (x = y)))

theorem dist_triangle {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : dist x z ≤ dist x y + dist y z :=
  metric_space.dist_triangle x y z

theorem dist_triangle_left {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : dist x y ≤ dist z x + dist z y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist x y ≤ dist z x + dist z y)) (dist_comm z x))) (dist_triangle x z y)

theorem dist_triangle_right {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : dist x y ≤ dist x z + dist y z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (dist x y ≤ dist x z + dist y z)) (dist_comm y z))) (dist_triangle x z y)

theorem dist_triangle4 {α : Type u} [metric_space α] (x : α) (y : α) (z : α) (w : α) : dist x w ≤ dist x y + dist y z + dist z w :=
  le_trans (dist_triangle x z w) (add_le_add_right (dist_triangle x y z) (dist z w))

theorem dist_triangle4_left {α : Type u} [metric_space α] (x₁ : α) (y₁ : α) (x₂ : α) (y₂ : α) : dist x₂ y₂ ≤ dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) := sorry

theorem dist_triangle4_right {α : Type u} [metric_space α] (x₁ : α) (y₁ : α) (x₂ : α) (y₂ : α) : dist x₁ y₁ ≤ dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ := sorry

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
theorem dist_le_Ico_sum_dist {α : Type u} [metric_space α] (f : ℕ → α) {m : ℕ} {n : ℕ} (h : m ≤ n) : dist (f m) (f n) ≤ finset.sum (finset.Ico m n) fun (i : ℕ) => dist (f i) (f (i + 1)) := sorry

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
theorem dist_le_range_sum_dist {α : Type u} [metric_space α] (f : ℕ → α) (n : ℕ) : dist (f 0) (f n) ≤ finset.sum (finset.range n) fun (i : ℕ) => dist (f i) (f (i + 1)) :=
  finset.Ico.zero_bot n ▸ dist_le_Ico_sum_dist f (nat.zero_le n)

/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_Ico_sum_of_dist_le {α : Type u} [metric_space α] {f : ℕ → α} {m : ℕ} {n : ℕ} (hmn : m ≤ n) {d : ℕ → ℝ} (hd : ∀ {k : ℕ}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) : dist (f m) (f n) ≤ finset.sum (finset.Ico m n) fun (i : ℕ) => d i := sorry

/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem dist_le_range_sum_of_dist_le {α : Type u} [metric_space α] {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ} (hd : ∀ {k : ℕ}, k < n → dist (f k) (f (k + 1)) ≤ d k) : dist (f 0) (f n) ≤ finset.sum (finset.range n) fun (i : ℕ) => d i :=
  finset.Ico.zero_bot n ▸ dist_le_Ico_sum_of_dist_le (zero_le n) fun (_x : ℕ) (_x_1 : 0 ≤ _x) => hd

theorem swap_dist {α : Type u} [metric_space α] : function.swap dist = dist :=
  funext fun (x : α) => funext fun (y : α) => dist_comm y x

theorem abs_dist_sub_le {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : abs (dist x z - dist y z) ≤ dist x y :=
  iff.mpr abs_sub_le_iff
    { left := iff.mpr sub_le_iff_le_add (dist_triangle x y z),
      right := iff.mpr sub_le_iff_le_add (dist_triangle_left y z x) }

theorem dist_nonneg {α : Type u} [metric_space α] {x : α} {y : α} : 0 ≤ dist x y := sorry

@[simp] theorem dist_le_zero {α : Type u} [metric_space α] {x : α} {y : α} : dist x y ≤ 0 ↔ x = y := sorry

@[simp] theorem dist_pos {α : Type u} [metric_space α] {x : α} {y : α} : 0 < dist x y ↔ x ≠ y := sorry

@[simp] theorem abs_dist {α : Type u} [metric_space α] {a : α} {b : α} : abs (dist a b) = dist a b :=
  abs_of_nonneg dist_nonneg

theorem eq_of_forall_dist_le {α : Type u} [metric_space α] {x : α} {y : α} (h : ∀ (ε : ℝ), ε > 0 → dist x y ≤ ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

/-- Distance as a nonnegative real number. -/
def nndist {α : Type u} [metric_space α] (a : α) (b : α) : nnreal :=
  { val := dist a b, property := dist_nonneg }

/--Express `nndist` in terms of `edist`-/
theorem nndist_edist {α : Type u} [metric_space α] (x : α) (y : α) : nndist x y = ennreal.to_nnreal (edist x y) := sorry

/--Express `edist` in terms of `nndist`-/
theorem edist_nndist {α : Type u} [metric_space α] (x : α) (y : α) : edist x y = ↑(nndist x y) := sorry

@[simp] theorem ennreal_coe_nndist {α : Type u} [metric_space α] (x : α) (y : α) : ↑(nndist x y) = edist x y :=
  Eq.symm (edist_nndist x y)

@[simp] theorem edist_lt_coe {α : Type u} [metric_space α] {x : α} {y : α} {c : nnreal} : edist x y < ↑c ↔ nndist x y < c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (edist x y < ↑c ↔ nndist x y < c)) (edist_nndist x y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nndist x y) < ↑c ↔ nndist x y < c)) (propext ennreal.coe_lt_coe)))
      (iff.refl (nndist x y < c)))

@[simp] theorem edist_le_coe {α : Type u} [metric_space α] {x : α} {y : α} {c : nnreal} : edist x y ≤ ↑c ↔ nndist x y ≤ c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (edist x y ≤ ↑c ↔ nndist x y ≤ c)) (edist_nndist x y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(nndist x y) ≤ ↑c ↔ nndist x y ≤ c)) (propext ennreal.coe_le_coe)))
      (iff.refl (nndist x y ≤ c)))

/--In a metric space, the extended distance is always finite-/
theorem edist_ne_top {α : Type u} [metric_space α] (x : α) (y : α) : edist x y ≠ ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (edist x y ≠ ⊤)) (edist_dist x y))) ennreal.coe_ne_top

/--In a metric space, the extended distance is always finite-/
theorem edist_lt_top {α : Type u_1} [metric_space α] (x : α) (y : α) : edist x y < ⊤ :=
  iff.mpr ennreal.lt_top_iff_ne_top (edist_ne_top x y)

/--`nndist x x` vanishes-/
@[simp] theorem nndist_self {α : Type u} [metric_space α] (a : α) : nndist a a = 0 :=
  iff.mp (nnreal.coe_eq_zero (nndist a a)) (dist_self a)

/--Express `dist` in terms of `nndist`-/
theorem dist_nndist {α : Type u} [metric_space α] (x : α) (y : α) : dist x y = ↑(nndist x y) :=
  rfl

@[simp] theorem coe_nndist {α : Type u} [metric_space α] (x : α) (y : α) : ↑(nndist x y) = dist x y :=
  Eq.symm (dist_nndist x y)

@[simp] theorem dist_lt_coe {α : Type u} [metric_space α] {x : α} {y : α} {c : nnreal} : dist x y < ↑c ↔ nndist x y < c :=
  iff.rfl

@[simp] theorem dist_le_coe {α : Type u} [metric_space α] {x : α} {y : α} {c : nnreal} : dist x y ≤ ↑c ↔ nndist x y ≤ c :=
  iff.rfl

/--Express `nndist` in terms of `dist`-/
theorem nndist_dist {α : Type u} [metric_space α] (x : α) (y : α) : nndist x y = nnreal.of_real (dist x y) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nndist x y = nnreal.of_real (dist x y))) (dist_nndist x y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nndist x y = nnreal.of_real ↑(nndist x y))) nnreal.of_real_coe))
      (Eq.refl (nndist x y)))

/--Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {α : Type u} [metric_space α] {x : α} {y : α} : nndist x y = 0 → x = y := sorry

theorem nndist_comm {α : Type u} [metric_space α] (x : α) (y : α) : nndist x y = nndist y x := sorry

/--Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp] theorem nndist_eq_zero {α : Type u} [metric_space α] {x : α} {y : α} : nndist x y = 0 ↔ x = y := sorry

@[simp] theorem zero_eq_nndist {α : Type u} [metric_space α] {x : α} {y : α} : 0 = nndist x y ↔ x = y := sorry

/--Triangle inequality for the nonnegative distance-/
theorem nndist_triangle {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : nndist x z ≤ nndist x y + nndist y z :=
  dist_triangle x y z

theorem nndist_triangle_left {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : nndist x y ≤ nndist z x + nndist z y :=
  dist_triangle_left x y z

theorem nndist_triangle_right {α : Type u} [metric_space α] (x : α) (y : α) (z : α) : nndist x y ≤ nndist x z + nndist y z :=
  dist_triangle_right x y z

/--Express `dist` in terms of `edist`-/
theorem dist_edist {α : Type u} [metric_space α] (x : α) (y : α) : dist x y = ennreal.to_real (edist x y) := sorry

namespace metric


/- instantiate metric space as a topology -/

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball {α : Type u} [metric_space α] (x : α) (ε : ℝ) : set α :=
  set_of fun (y : α) => dist y x < ε

@[simp] theorem mem_ball {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} : y ∈ ball x ε ↔ dist y x < ε :=
  iff.rfl

theorem mem_ball' {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} : y ∈ ball x ε ↔ dist x y < ε :=
  eq.mpr (id (Eq._oldrec (Eq.refl (y ∈ ball x ε ↔ dist x y < ε)) (dist_comm x y))) (iff.refl (y ∈ ball x ε))

@[simp] theorem nonempty_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} (h : 0 < ε) : set.nonempty (ball x ε) := sorry

theorem ball_eq_ball {α : Type u} [metric_space α] (ε : ℝ) (x : α) : uniform_space.ball x (set_of fun (p : α × α) => dist (prod.snd p) (prod.fst p) < ε) = ball x ε :=
  rfl

theorem ball_eq_ball' {α : Type u} [metric_space α] (ε : ℝ) (x : α) : uniform_space.ball x (set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε) = ball x ε := sorry

/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closed_ball {α : Type u} [metric_space α] (x : α) (ε : ℝ) : set α :=
  set_of fun (y : α) => dist y x ≤ ε

@[simp] theorem mem_closed_ball {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} : y ∈ closed_ball x ε ↔ dist y x ≤ ε :=
  iff.rfl

/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere {α : Type u} [metric_space α] (x : α) (ε : ℝ) : set α :=
  set_of fun (y : α) => dist y x = ε

@[simp] theorem mem_sphere {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} : y ∈ sphere x ε ↔ dist y x = ε :=
  iff.rfl

theorem mem_closed_ball' {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} : y ∈ closed_ball x ε ↔ dist x y ≤ ε :=
  eq.mpr (id (Eq._oldrec (Eq.refl (y ∈ closed_ball x ε ↔ dist x y ≤ ε)) (dist_comm x y))) (iff.refl (y ∈ closed_ball x ε))

theorem nonempty_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} (h : 0 ≤ ε) : set.nonempty (closed_ball x ε) := sorry

theorem ball_subset_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : ball x ε ⊆ closed_ball x ε :=
  fun (y : α) (hy : dist y x < ε) => le_of_lt hy

theorem sphere_subset_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : sphere x ε ⊆ closed_ball x ε :=
  fun (y : α) => le_of_eq

theorem sphere_disjoint_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : disjoint (sphere x ε) (ball x ε) := sorry

@[simp] theorem ball_union_sphere {α : Type u} [metric_space α] {x : α} {ε : ℝ} : ball x ε ∪ sphere x ε = closed_ball x ε :=
  set.ext fun (y : α) => iff.symm le_iff_lt_or_eq

@[simp] theorem sphere_union_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : sphere x ε ∪ ball x ε = closed_ball x ε :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sphere x ε ∪ ball x ε = closed_ball x ε)) (set.union_comm (sphere x ε) (ball x ε))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (ball x ε ∪ sphere x ε = closed_ball x ε)) ball_union_sphere))
      (Eq.refl (closed_ball x ε)))

@[simp] theorem closed_ball_diff_sphere {α : Type u} [metric_space α] {x : α} {ε : ℝ} : closed_ball x ε \ sphere x ε = ball x ε := sorry

@[simp] theorem closed_ball_diff_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : closed_ball x ε \ ball x ε = sphere x ε := sorry

theorem pos_of_mem_ball {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} (hy : y ∈ ball x ε) : 0 < ε :=
  lt_of_le_of_lt dist_nonneg hy

theorem mem_ball_self {α : Type u} [metric_space α] {x : α} {ε : ℝ} (h : 0 < ε) : x ∈ ball x ε :=
  (fun (this : dist x x < ε) => this) (eq.mpr (id (Eq._oldrec (Eq.refl (dist x x < ε)) (dist_self x))) h)

theorem mem_closed_ball_self {α : Type u} [metric_space α] {x : α} {ε : ℝ} (h : 0 ≤ ε) : x ∈ closed_ball x ε :=
  (fun (this : dist x x ≤ ε) => this) (eq.mpr (id (Eq._oldrec (Eq.refl (dist x x ≤ ε)) (dist_self x))) h)

theorem mem_ball_comm {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} : x ∈ ball y ε ↔ y ∈ ball x ε := sorry

theorem ball_subset_ball {α : Type u} [metric_space α] {x : α} {ε₁ : ℝ} {ε₂ : ℝ} (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
  fun (y : α) (yx : dist y x < ε₁) => lt_of_lt_of_le yx h

theorem closed_ball_subset_closed_ball {α : Type u} [metric_space α] {x : α} {ε₁ : ℝ} {ε₂ : ℝ} (h : ε₁ ≤ ε₂) : closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
  fun (y : α) (yx : dist y x ≤ ε₁) => le_trans yx h

theorem ball_disjoint {α : Type u} [metric_space α] {x : α} {y : α} {ε₁ : ℝ} {ε₂ : ℝ} (h : ε₁ + ε₂ ≤ dist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ := sorry

theorem ball_disjoint_same {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} (h : ε ≤ dist x y / bit0 1) : ball x ε ∩ ball y ε = ∅ :=
  ball_disjoint
    (eq.mpr (id (Eq._oldrec (Eq.refl (ε + ε ≤ dist x y)) (Eq.symm (two_mul ε))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 1 * ε ≤ dist x y)) (Eq.symm (propext (le_div_iff' zero_lt_two))))) h))

theorem ball_subset {α : Type u} [metric_space α] {x : α} {y : α} {ε₁ : ℝ} {ε₂ : ℝ} (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ :=
  fun (z : α) (zx : z ∈ ball x ε₁) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (z ∈ ball y ε₂)) (Eq.symm (add_sub_cancel'_right ε₁ ε₂))))
      (lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h))

theorem ball_half_subset {α : Type u} [metric_space α] {x : α} {ε : ℝ} (y : α) (h : y ∈ ball x (ε / bit0 1)) : ball y (ε / bit0 1) ⊆ ball x ε :=
  ball_subset (eq.mpr (id (Eq._oldrec (Eq.refl (dist y x ≤ ε - ε / bit0 1)) (sub_self_div_two ε))) (le_of_lt h))

theorem exists_ball_subset_ball {α : Type u} [metric_space α] {x : α} {y : α} {ε : ℝ} (h : y ∈ ball x ε) : ∃ (ε' : ℝ), ∃ (H : ε' > 0), ball y ε' ⊆ ball x ε := sorry

@[simp] theorem ball_eq_empty_iff_nonpos {α : Type u} [metric_space α] {x : α} {ε : ℝ} : ball x ε = ∅ ↔ ε ≤ 0 :=
  iff.trans set.eq_empty_iff_forall_not_mem
    { mp := fun (h : ∀ (x_1 : α), ¬x_1 ∈ ball x ε) => le_of_not_gt fun (ε0 : ε > 0) => h x (mem_ball_self ε0),
      mpr := fun (ε0 : ε ≤ 0) (y : α) (h : y ∈ ball x ε) => not_lt_of_le ε0 (pos_of_mem_ball h) }

@[simp] theorem closed_ball_eq_empty_iff_neg {α : Type u} [metric_space α] {x : α} {ε : ℝ} : closed_ball x ε = ∅ ↔ ε < 0 := sorry

@[simp] theorem ball_zero {α : Type u} [metric_space α] {x : α} : ball x 0 = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ball x 0 = ∅)) (propext ball_eq_empty_iff_nonpos))) (le_refl 0)

@[simp] theorem closed_ball_zero {α : Type u} [metric_space α] {x : α} : closed_ball x 0 = singleton x :=
  set.ext fun (y : α) => dist_le_zero

theorem uniformity_basis_dist {α : Type u} [metric_space α] : filter.has_basis (uniformity α) (fun (ε : ℝ) => 0 < ε)
  fun (ε : ℝ) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε := sorry

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_succ`,
and `uniformity_basis_dist_inv_nat_pos`. -/
protected theorem mk_uniformity_basis {α : Type u} [metric_space α] {β : Type u_1} {p : β → Prop} {f : β → ℝ} (hf₀ : ∀ (i : β), p i → 0 < f i) (hf : ∀ {ε : ℝ}, 0 < ε → ∃ (i : β), ∃ (hi : p i), f i ≤ ε) : filter.has_basis (uniformity α) p fun (i : β) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < f i := sorry

theorem uniformity_basis_dist_inv_nat_succ {α : Type u} [metric_space α] : filter.has_basis (uniformity α) (fun (_x : ℕ) => True)
  fun (n : ℕ) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < 1 / (↑n + 1) :=
  metric.mk_uniformity_basis (fun (n : ℕ) (_x : True) => div_pos zero_lt_one (nat.cast_add_one_pos n))
    fun (ε : ℝ) (ε0 : 0 < ε) =>
      Exists.imp (fun (n : ℕ) (hn : 1 / (↑n + 1) < ε) => Exists.intro trivial (le_of_lt hn)) (exists_nat_one_div_lt ε0)

theorem uniformity_basis_dist_inv_nat_pos {α : Type u} [metric_space α] : filter.has_basis (uniformity α) (fun (n : ℕ) => 0 < n)
  fun (n : ℕ) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < 1 / ↑n := sorry

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i | p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on this constructor.
More can be easily added if needed in the future. -/
protected theorem mk_uniformity_basis_le {α : Type u} [metric_space α] {β : Type u_1} {p : β → Prop} {f : β → ℝ} (hf₀ : ∀ (x : β), p x → 0 < f x) (hf : ∀ (ε : ℝ), 0 < ε → ∃ (x : β), ∃ (hx : p x), f x ≤ ε) : filter.has_basis (uniformity α) p fun (x : β) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) ≤ f x := sorry

/-- Contant size closed neighborhoods of the diagonal form a basis
of the uniformity filter. -/
theorem uniformity_basis_dist_le {α : Type u} [metric_space α] : filter.has_basis (uniformity α) (fun (ε : ℝ) => 0 < ε)
  fun (ε : ℝ) => set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) ≤ ε :=
  metric.mk_uniformity_basis_le (fun (_x : ℝ) => id)
    fun (ε : ℝ) (ε₀ : 0 < ε) => Exists.intro ε (Exists.intro ε₀ (le_refl ε))

theorem mem_uniformity_dist {α : Type u} [metric_space α] {s : set (α × α)} : s ∈ uniformity α ↔ ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ {a b : α}, dist a b < ε → (a, b) ∈ s :=
  filter.has_basis.mem_uniformity_iff uniformity_basis_dist

/-- A constant size neighborhood of the diagonal is an entourage. -/
theorem dist_mem_uniformity {α : Type u} [metric_space α] {ε : ℝ} (ε0 : 0 < ε) : (set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε) ∈ uniformity α :=
  iff.mpr mem_uniformity_dist (Exists.intro ε (Exists.intro ε0 fun (a b : α) => id))

theorem uniform_continuous_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} : uniform_continuous f ↔ ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε :=
  filter.has_basis.uniform_continuous_iff uniformity_basis_dist uniformity_basis_dist

theorem uniform_continuous_on_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {s : set α} : uniform_continuous_on f s ↔
  ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (x y : α), x ∈ s → y ∈ s → dist x y < δ → dist (f x) (f y) < ε := sorry

theorem uniform_embedding_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} : uniform_embedding f ↔
  function.injective f ∧
    uniform_continuous f ∧
      ∀ (δ : ℝ) (H : δ > 0), ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := sorry

/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff' {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} : uniform_embedding f ↔
  (∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
    ∀ (δ : ℝ) (H : δ > 0), ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := sorry

theorem totally_bounded_iff {α : Type u} [metric_space α] {s : set α} : totally_bounded s ↔
  ∀ (ε : ℝ) (H : ε > 0),
    ∃ (t : set α), set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => ball y ε := sorry

/-- A metric space space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
theorem totally_bounded_of_finite_discretization {α : Type u} [metric_space α] {s : set α} (H : ∀ (ε : ℝ), ε > 0 → ∃ (β : Type u), Exists (∃ (F : ↥s → β), ∀ (x y : ↥s), F x = F y → dist ↑x ↑y < ε)) : totally_bounded s := sorry

theorem finite_approx_of_totally_bounded {α : Type u} [metric_space α] {s : set α} (hs : totally_bounded s) (ε : ℝ) (H : ε > 0) : ∃ (t : set α), ∃ (H : t ⊆ s), set.finite t ∧ s ⊆ set.Union fun (y : α) => set.Union fun (H : y ∈ t) => ball y ε :=
  eq.mp (Eq._oldrec (Eq.refl (totally_bounded s)) (propext totally_bounded_iff_subset)) hs
    (set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε) (dist_mem_uniformity ε_pos)

/-- Expressing locally uniform convergence on a set using `dist`. -/
theorem tendsto_locally_uniformly_on_iff {α : Type u} {β : Type v} [metric_space α] {ι : Type u_1} [topological_space β] {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} : tendsto_locally_uniformly_on F f p s ↔
  ∀ (ε : ℝ) (H : ε > 0) (x : β) (H : x ∈ s),
    ∃ (t : set β),
      ∃ (H : t ∈ nhds_within x s), filter.eventually (fun (n : ι) => ∀ (y : β), y ∈ t → dist (f y) (F n y) < ε) p := sorry

/-- Expressing uniform convergence on a set using `dist`. -/
theorem tendsto_uniformly_on_iff {α : Type u} {β : Type v} [metric_space α] {ι : Type u_1} {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} : tendsto_uniformly_on F f p s ↔
  ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (n : ι) => ∀ (x : β), x ∈ s → dist (f x) (F n x) < ε) p := sorry

/-- Expressing locally uniform convergence using `dist`. -/
theorem tendsto_locally_uniformly_iff {α : Type u} {β : Type v} [metric_space α] {ι : Type u_1} [topological_space β] {F : ι → β → α} {f : β → α} {p : filter ι} : tendsto_locally_uniformly F f p ↔
  ∀ (ε : ℝ) (H : ε > 0) (x : β),
    ∃ (t : set β), ∃ (H : t ∈ nhds x), filter.eventually (fun (n : ι) => ∀ (y : β), y ∈ t → dist (f y) (F n y) < ε) p := sorry

/-- Expressing uniform convergence using `dist`. -/
theorem tendsto_uniformly_iff {α : Type u} {β : Type v} [metric_space α] {ι : Type u_1} {F : ι → β → α} {f : β → α} {p : filter ι} : tendsto_uniformly F f p ↔ ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (n : ι) => ∀ (x : β), dist (f x) (F n x) < ε) p := sorry

protected theorem cauchy_iff {α : Type u} [metric_space α] {f : filter α} : cauchy f ↔
  filter.ne_bot f ∧ ∀ (ε : ℝ) (H : ε > 0), ∃ (t : set α), ∃ (H : t ∈ f), ∀ (x y : α), x ∈ t → y ∈ t → dist x y < ε :=
  filter.has_basis.cauchy_iff uniformity_basis_dist

theorem nhds_basis_ball {α : Type u} [metric_space α] {x : α} : filter.has_basis (nhds x) (fun (ε : ℝ) => 0 < ε) (ball x) :=
  nhds_basis_uniformity uniformity_basis_dist

theorem mem_nhds_iff {α : Type u} [metric_space α] {x : α} {s : set α} : s ∈ nhds x ↔ ∃ (ε : ℝ), ∃ (H : ε > 0), ball x ε ⊆ s :=
  filter.has_basis.mem_iff nhds_basis_ball

theorem eventually_nhds_iff {α : Type u} [metric_space α] {x : α} {p : α → Prop} : filter.eventually (fun (y : α) => p y) (nhds x) ↔ ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ {y : α}, dist y x < ε → p y :=
  mem_nhds_iff

theorem eventually_nhds_iff_ball {α : Type u} [metric_space α] {x : α} {p : α → Prop} : filter.eventually (fun (y : α) => p y) (nhds x) ↔ ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ (y : α), y ∈ ball x ε → p y :=
  mem_nhds_iff

theorem nhds_basis_closed_ball {α : Type u} [metric_space α] {x : α} : filter.has_basis (nhds x) (fun (ε : ℝ) => 0 < ε) (closed_ball x) :=
  nhds_basis_uniformity uniformity_basis_dist_le

theorem nhds_basis_ball_inv_nat_succ {α : Type u} [metric_space α] {x : α} : filter.has_basis (nhds x) (fun (_x : ℕ) => True) fun (n : ℕ) => ball x (1 / (↑n + 1)) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ

theorem nhds_basis_ball_inv_nat_pos {α : Type u} [metric_space α] {x : α} : filter.has_basis (nhds x) (fun (n : ℕ) => 0 < n) fun (n : ℕ) => ball x (1 / ↑n) :=
  nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos

theorem is_open_iff {α : Type u} [metric_space α] {s : set α} : is_open s ↔ ∀ (x : α) (H : x ∈ s), ∃ (ε : ℝ), ∃ (H : ε > 0), ball x ε ⊆ s := sorry

theorem is_open_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : is_open (ball x ε) :=
  iff.mpr is_open_iff fun (y : α) => exists_ball_subset_ball

theorem ball_mem_nhds {α : Type u} [metric_space α] (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ nhds x :=
  mem_nhds_sets is_open_ball (mem_ball_self ε0)

theorem closed_ball_mem_nhds {α : Type u} [metric_space α] (x : α) {ε : ℝ} (ε0 : 0 < ε) : closed_ball x ε ∈ nhds x :=
  filter.mem_sets_of_superset (ball_mem_nhds x ε0) ball_subset_closed_ball

theorem nhds_within_basis_ball {α : Type u} [metric_space α] {x : α} {s : set α} : filter.has_basis (nhds_within x s) (fun (ε : ℝ) => 0 < ε) fun (ε : ℝ) => ball x ε ∩ s :=
  nhds_within_has_basis nhds_basis_ball s

theorem mem_nhds_within_iff {α : Type u} [metric_space α] {x : α} {s : set α} {t : set α} : s ∈ nhds_within x t ↔ ∃ (ε : ℝ), ∃ (H : ε > 0), ball x ε ∩ t ⊆ s :=
  filter.has_basis.mem_iff nhds_within_basis_ball

theorem tendsto_nhds_within_nhds_within {α : Type u} {β : Type v} [metric_space α] {s : set α} [metric_space β] {t : set β} {f : α → β} {a : α} {b : β} : filter.tendsto f (nhds_within a s) (nhds_within b t) ↔
  ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {x : α}, x ∈ s → dist x a < δ → f x ∈ t ∧ dist (f x) b < ε := sorry

theorem tendsto_nhds_within_nhds {α : Type u} {β : Type v} [metric_space α] {s : set α} [metric_space β] {f : α → β} {a : α} {b : β} : filter.tendsto f (nhds_within a s) (nhds b) ↔
  ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) b < ε := sorry

theorem tendsto_nhds_nhds {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {a : α} {b : β} : filter.tendsto f (nhds a) (nhds b) ↔
  ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {x : α}, dist x a < δ → dist (f x) b < ε :=
  filter.has_basis.tendsto_iff nhds_basis_ball nhds_basis_ball

theorem continuous_at_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {a : α} : continuous_at f a ↔ ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {x : α}, dist x a < δ → dist (f x) (f a) < ε := sorry

theorem continuous_within_at_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {a : α} {s : set α} : continuous_within_at f s a ↔
  ∀ (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ {x : α}, x ∈ s → dist x a < δ → dist (f x) (f a) < ε := sorry

theorem continuous_on_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {s : set α} : continuous_on f s ↔
  ∀ (b : α) (H : b ∈ s) (ε : ℝ) (H : ε > 0),
    ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (a : α), a ∈ s → dist a b < δ → dist (f a) (f b) < ε := sorry

theorem continuous_iff {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} : continuous f ↔ ∀ (b : α) (ε : ℝ) (H : ε > 0), ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (a : α), dist a b < δ → dist (f a) (f b) < ε :=
  iff.trans continuous_iff_continuous_at (forall_congr fun (b : α) => tendsto_nhds_nhds)

theorem tendsto_nhds {α : Type u} {β : Type v} [metric_space α] {f : filter β} {u : β → α} {a : α} : filter.tendsto u f (nhds a) ↔ ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (x : β) => dist (u x) a < ε) f :=
  filter.has_basis.tendsto_right_iff nhds_basis_ball

theorem continuous_at_iff' {α : Type u} {β : Type v} [metric_space α] [topological_space β] {f : β → α} {b : β} : continuous_at f b ↔ ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (x : β) => dist (f x) (f b) < ε) (nhds b) := sorry

theorem continuous_within_at_iff' {α : Type u} {β : Type v} [metric_space α] [topological_space β] {f : β → α} {b : β} {s : set β} : continuous_within_at f s b ↔
  ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (x : β) => dist (f x) (f b) < ε) (nhds_within b s) := sorry

theorem continuous_on_iff' {α : Type u} {β : Type v} [metric_space α] [topological_space β] {f : β → α} {s : set β} : continuous_on f s ↔
  ∀ (b : β), b ∈ s → ∀ (ε : ℝ), ε > 0 → filter.eventually (fun (x : β) => dist (f x) (f b) < ε) (nhds_within b s) := sorry

theorem continuous_iff' {α : Type u} {β : Type v} [metric_space α] [topological_space β] {f : β → α} : continuous f ↔ ∀ (a : β) (ε : ℝ), ε > 0 → filter.eventually (fun (x : β) => dist (f x) (f a) < ε) (nhds a) :=
  iff.trans continuous_iff_continuous_at (forall_congr fun (b : β) => tendsto_nhds)

theorem tendsto_at_top {α : Type u} {β : Type v} [metric_space α] [Nonempty β] [semilattice_sup β] {u : β → α} {a : α} : filter.tendsto u filter.at_top (nhds a) ↔ ∀ (ε : ℝ), ε > 0 → ∃ (N : β), ∀ (n : β), n ≥ N → dist (u n) a < ε := sorry

theorem is_open_singleton_iff {X : Type u_1} [metric_space X] {x : X} : is_open (singleton x) ↔ ∃ (ε : ℝ), ∃ (H : ε > 0), ∀ (y : X), dist y x < ε → y = x := sorry

/-- Given a point `x` in a discrete subset `s` of a metric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
theorem exists_ball_inter_eq_singleton_of_mem_discrete {α : Type u} [metric_space α] {s : set α} [discrete_topology ↥s] {x : α} (hx : x ∈ s) : ∃ (ε : ℝ), ∃ (H : ε > 0), ball x ε ∩ s = singleton x :=
  filter.has_basis.exists_inter_eq_singleton_of_mem_discrete nhds_basis_ball hx

/-- Given a point `x` in a discrete subset `s` of a metric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
theorem exists_closed_ball_inter_eq_singleton_of_discrete {α : Type u} [metric_space α] {s : set α} [discrete_topology ↥s] {x : α} (hx : x ∈ s) : ∃ (ε : ℝ), ∃ (H : ε > 0), closed_ball x ε ∩ s = singleton x :=
  filter.has_basis.exists_inter_eq_singleton_of_mem_discrete nhds_basis_closed_ball hx

end metric


protected instance metric_space.to_separated {α : Type u} [metric_space α] : separated_space α :=
  iff.mpr separated_def
    fun (x y : α) (h : ∀ (r : set (α × α)), r ∈ uniformity α → (x, y) ∈ r) =>
      eq_of_forall_dist_le
        fun (ε : ℝ) (ε0 : ε > 0) =>
          le_of_lt (h (set_of fun (p : α × α) => dist (prod.fst p) (prod.snd p) < ε) (metric.dist_mem_uniformity ε0))

/-Instantiate a metric space as an emetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/

/-- Expressing the uniformity in terms of `edist` -/
protected theorem metric.uniformity_basis_edist {α : Type u} [metric_space α] : filter.has_basis (uniformity α) (fun (ε : ennreal) => 0 < ε)
  fun (ε : ennreal) => set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε := sorry

theorem metric.uniformity_edist {α : Type u} [metric_space α] : uniformity α =
  infi
    fun (ε : ennreal) =>
      infi fun (H : ε > 0) => filter.principal (set_of fun (p : α × α) => edist (prod.fst p) (prod.snd p) < ε) :=
  filter.has_basis.eq_binfi metric.uniformity_basis_edist

/-- A metric space induces an emetric space -/
protected instance metric_space.to_emetric_space {α : Type u} [metric_space α] : emetric_space α :=
  emetric_space.mk sorry sorry sorry sorry metric_space.to_uniform_space

/-- Balls defined using the distance or the edistance coincide -/
theorem metric.emetric_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : emetric.ball x (ennreal.of_real ε) = metric.ball x ε := sorry

/-- Balls defined using the distance or the edistance coincide -/
theorem metric.emetric_ball_nnreal {α : Type u} [metric_space α] {x : α} {ε : nnreal} : emetric.ball x ↑ε = metric.ball x ↑ε := sorry

/-- Closed balls defined using the distance or the edistance coincide -/
theorem metric.emetric_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} (h : 0 ≤ ε) : emetric.closed_ball x (ennreal.of_real ε) = metric.closed_ball x ε := sorry

/-- Closed balls defined using the distance or the edistance coincide -/
theorem metric.emetric_closed_ball_nnreal {α : Type u} [metric_space α] {x : α} {ε : nnreal} : emetric.closed_ball x ↑ε = metric.closed_ball x ↑ε := sorry

/-- Build a new metric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def metric_space.replace_uniformity {α : Type u_1} [U : uniform_space α] (m : metric_space α) (H : uniformity α = uniformity α) : metric_space α :=
  metric_space.mk dist_self eq_of_dist_eq_zero dist_comm dist_triangle edist U

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
def emetric_space.to_metric_space_of_dist {α : Type u} [e : emetric_space α] (dist : α → α → ℝ) (edist_ne_top : ∀ (x y : α), edist x y ≠ ⊤) (h : ∀ (x y : α), dist x y = ennreal.to_real (edist x y)) : metric_space α :=
  let m : metric_space α :=
    metric_space.mk sorry sorry sorry sorry (fun (x y : α) => edist x y) (uniform_space_of_dist dist sorry sorry sorry);
  metric_space.replace_uniformity m sorry

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
def emetric_space.to_metric_space {α : Type u} [e : emetric_space α] (h : ∀ (x y : α), edist x y ≠ ⊤) : metric_space α :=
  emetric_space.to_metric_space_of_dist (fun (x y : α) => ennreal.to_real (edist x y)) h sorry

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem metric.complete_of_convergent_controlled_sequences {α : Type u} [metric_space α] (B : ℕ → ℝ) (hB : ∀ (n : ℕ), 0 < B n) (H : ∀ (u : ℕ → α),
  (∀ (N n m : ℕ), N ≤ n → N ≤ m → dist (u n) (u m) < B N) → ∃ (x : α), filter.tendsto u filter.at_top (nhds x)) : complete_space α := sorry

theorem metric.complete_of_cauchy_seq_tendsto {α : Type u} [metric_space α] : (∀ (u : ℕ → α), cauchy_seq u → ∃ (a : α), filter.tendsto u filter.at_top (nhds a)) → complete_space α :=
  emetric.complete_of_cauchy_seq_tendsto

/-- Instantiate the reals as a metric space. -/
protected instance real.metric_space : metric_space ℝ :=
  metric_space.mk sorry sorry sorry sorry (fun (x y : ℝ) => ennreal.of_real ((fun (x y : ℝ) => abs (x - y)) x y))
    (uniform_space_of_dist (fun (x y : ℝ) => abs (x - y)) sorry sorry sorry)

theorem real.dist_eq (x : ℝ) (y : ℝ) : dist x y = abs (x - y) :=
  rfl

theorem real.dist_0_eq_abs (x : ℝ) : dist x 0 = abs x := sorry

protected instance real.order_topology : order_topology ℝ := sorry

theorem closed_ball_Icc {x : ℝ} {r : ℝ} : metric.closed_ball x r = set.Icc (x - r) (x + r) := sorry

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
theorem squeeze_zero' {α : Type u_1} {f : α → ℝ} {g : α → ℝ} {t₀ : filter α} (hf : filter.eventually (fun (t : α) => 0 ≤ f t) t₀) (hft : filter.eventually (fun (t : α) => f t ≤ g t) t₀) (g0 : filter.tendsto g t₀ (nhds 0)) : filter.tendsto f t₀ (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
theorem squeeze_zero {α : Type u_1} {f : α → ℝ} {g : α → ℝ} {t₀ : filter α} (hf : ∀ (t : α), 0 ≤ f t) (hft : ∀ (t : α), f t ≤ g t) (g0 : filter.tendsto g t₀ (nhds 0)) : filter.tendsto f t₀ (nhds 0) :=
  squeeze_zero' (filter.eventually_of_forall hf) (filter.eventually_of_forall hft) g0

theorem metric.uniformity_eq_comap_nhds_zero {α : Type u} [metric_space α] : uniformity α = filter.comap (fun (p : α × α) => dist (prod.fst p) (prod.snd p)) (nhds 0) := sorry

theorem cauchy_seq_iff_tendsto_dist_at_top_0 {α : Type u} {β : Type v} [metric_space α] [Nonempty β] [semilattice_sup β] {u : β → α} : cauchy_seq u ↔ filter.tendsto (fun (n : β × β) => dist (u (prod.fst n)) (u (prod.snd n))) filter.at_top (nhds 0) := sorry

theorem tendsto_uniformity_iff_dist_tendsto_zero {α : Type u} [metric_space α] {ι : Type u_1} {f : ι → α × α} {p : filter ι} : filter.tendsto f p (uniformity α) ↔ filter.tendsto (fun (x : ι) => dist (prod.fst (f x)) (prod.snd (f x))) p (nhds 0) := sorry

theorem filter.tendsto.congr_dist {α : Type u} [metric_space α] {ι : Type u_1} {f₁ : ι → α} {f₂ : ι → α} {p : filter ι} {a : α} (h₁ : filter.tendsto f₁ p (nhds a)) (h : filter.tendsto (fun (x : ι) => dist (f₁ x) (f₂ x)) p (nhds 0)) : filter.tendsto f₂ p (nhds a) :=
  filter.tendsto.congr_uniformity h₁ (iff.mpr tendsto_uniformity_iff_dist_tendsto_zero h)

theorem tendsto_of_tendsto_of_dist {α : Type u} [metric_space α] {ι : Type u_1} {f₁ : ι → α} {f₂ : ι → α} {p : filter ι} {a : α} (h₁ : filter.tendsto f₁ p (nhds a)) (h : filter.tendsto (fun (x : ι) => dist (f₁ x) (f₂ x)) p (nhds 0)) : filter.tendsto f₂ p (nhds a) :=
  filter.tendsto.congr_dist

theorem tendsto_iff_of_dist {α : Type u} [metric_space α] {ι : Type u_1} {f₁ : ι → α} {f₂ : ι → α} {p : filter ι} {a : α} (h : filter.tendsto (fun (x : ι) => dist (f₁ x) (f₂ x)) p (nhds 0)) : filter.tendsto f₁ p (nhds a) ↔ filter.tendsto f₂ p (nhds a) :=
  uniform.tendsto_congr (iff.mpr tendsto_uniformity_iff_dist_tendsto_zero h)

/-- In a metric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
theorem metric.cauchy_seq_iff {α : Type u} {β : Type v} [metric_space α] [Nonempty β] [semilattice_sup β] {u : β → α} : cauchy_seq u ↔ ∀ (ε : ℝ), ε > 0 → ∃ (N : β), ∀ (m n : β), m ≥ N → n ≥ N → dist (u m) (u n) < ε :=
  filter.has_basis.cauchy_seq_iff metric.uniformity_basis_dist

/-- A variation around the metric characterization of Cauchy sequences -/
theorem metric.cauchy_seq_iff' {α : Type u} {β : Type v} [metric_space α] [Nonempty β] [semilattice_sup β] {u : β → α} : cauchy_seq u ↔ ∀ (ε : ℝ), ε > 0 → ∃ (N : β), ∀ (n : β), n ≥ N → dist (u n) (u N) < ε :=
  filter.has_basis.cauchy_seq_iff' metric.uniformity_basis_dist

/-- If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence.  -/
theorem cauchy_seq_of_le_tendsto_0 {α : Type u} {β : Type v} [metric_space α] [Nonempty β] [semilattice_sup β] {s : β → α} (b : β → ℝ) (h : ∀ (n m N : β), N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) (h₀ : filter.tendsto b filter.at_top (nhds 0)) : cauchy_seq s := sorry

/-- A Cauchy sequence on the natural numbers is bounded. -/
theorem cauchy_seq_bdd {α : Type u} [metric_space α] {u : ℕ → α} (hu : cauchy_seq u) : ∃ (R : ℝ), ∃ (H : R > 0), ∀ (m n : ℕ), dist (u m) (u n) < R := sorry

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem cauchy_seq_iff_le_tendsto_0 {α : Type u} [metric_space α] {s : ℕ → α} : cauchy_seq s ↔
  ∃ (b : ℕ → ℝ),
    (∀ (n : ℕ), 0 ≤ b n) ∧
      (∀ (n m N : ℕ), N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧ filter.tendsto b filter.at_top (nhds 0) := sorry

/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
def metric_space.induced {α : Type u_1} {β : Type u_2} (f : α → β) (hf : function.injective f) (m : metric_space β) : metric_space α :=
  metric_space.mk sorry sorry sorry sorry (fun (x y : α) => edist (f x) (f y))
    (uniform_space.comap f metric_space.to_uniform_space)

protected instance subtype.metric_space {α : Type u_1} {p : α → Prop} [t : metric_space α] : metric_space (Subtype p) :=
  metric_space.induced coe sorry t

theorem subtype.dist_eq {α : Type u} [metric_space α] {p : α → Prop} (x : Subtype p) (y : Subtype p) : dist x y = dist ↑x ↑y :=
  rfl

protected instance nnreal.metric_space : metric_space nnreal :=
  eq.mpr sorry subtype.metric_space

theorem nnreal.dist_eq (a : nnreal) (b : nnreal) : dist a b = abs (↑a - ↑b) :=
  rfl

theorem nnreal.nndist_eq (a : nnreal) (b : nnreal) : nndist a b = max (a - b) (b - a) := sorry

protected instance prod.metric_space_max {α : Type u} {β : Type v} [metric_space α] [metric_space β] : metric_space (α × β) :=
  metric_space.mk sorry sorry sorry sorry
    (fun (x y : α × β) => max (edist (prod.fst x) (prod.fst y)) (edist (prod.snd x) (prod.snd y))) prod.uniform_space

theorem prod.dist_eq {α : Type u} {β : Type v} [metric_space α] [metric_space β] {x : α × β} {y : α × β} : dist x y = max (dist (prod.fst x) (prod.fst y)) (dist (prod.snd x) (prod.snd y)) :=
  rfl

theorem ball_prod_same {α : Type u} {β : Type v} [metric_space α] [metric_space β] (x : α) (y : β) (r : ℝ) : set.prod (metric.ball x r) (metric.ball y r) = metric.ball (x, y) r := sorry

theorem closed_ball_prod_same {α : Type u} {β : Type v} [metric_space α] [metric_space β] (x : α) (y : β) (r : ℝ) : set.prod (metric.closed_ball x r) (metric.closed_ball y r) = metric.closed_ball (x, y) r := sorry

theorem uniform_continuous_dist {α : Type u} [metric_space α] : uniform_continuous fun (p : α × α) => dist (prod.fst p) (prod.snd p) := sorry

theorem uniform_continuous.dist {α : Type u} {β : Type v} [metric_space α] [uniform_space β] {f : β → α} {g : β → α} (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous fun (b : β) => dist (f b) (g b) :=
  uniform_continuous.comp uniform_continuous_dist (uniform_continuous.prod_mk hf hg)

theorem continuous_dist {α : Type u} [metric_space α] : continuous fun (p : α × α) => dist (prod.fst p) (prod.snd p) :=
  uniform_continuous.continuous uniform_continuous_dist

theorem continuous.dist {α : Type u} {β : Type v} [metric_space α] [topological_space β] {f : β → α} {g : β → α} (hf : continuous f) (hg : continuous g) : continuous fun (b : β) => dist (f b) (g b) :=
  continuous.comp continuous_dist (continuous.prod_mk hf hg)

theorem filter.tendsto.dist {α : Type u} {β : Type v} [metric_space α] {f : β → α} {g : β → α} {x : filter β} {a : α} {b : α} (hf : filter.tendsto f x (nhds a)) (hg : filter.tendsto g x (nhds b)) : filter.tendsto (fun (x : β) => dist (f x) (g x)) x (nhds (dist a b)) :=
  filter.tendsto.comp (continuous.tendsto continuous_dist (a, b)) (filter.tendsto.prod_mk_nhds hf hg)

theorem nhds_comap_dist {α : Type u} [metric_space α] (a : α) : filter.comap (fun (a' : α) => dist a' a) (nhds 0) = nhds a := sorry

theorem tendsto_iff_dist_tendsto_zero {α : Type u} {β : Type v} [metric_space α] {f : β → α} {x : filter β} {a : α} : filter.tendsto f x (nhds a) ↔ filter.tendsto (fun (b : β) => dist (f b) a) x (nhds 0) := sorry

theorem uniform_continuous_nndist {α : Type u} [metric_space α] : uniform_continuous fun (p : α × α) => nndist (prod.fst p) (prod.snd p) :=
  uniform_continuous_subtype_mk uniform_continuous_dist fun (p : α × α) => dist_nonneg

theorem uniform_continuous.nndist {α : Type u} {β : Type v} [metric_space α] [uniform_space β] {f : β → α} {g : β → α} (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous fun (b : β) => nndist (f b) (g b) :=
  uniform_continuous.comp uniform_continuous_nndist (uniform_continuous.prod_mk hf hg)

theorem continuous_nndist {α : Type u} [metric_space α] : continuous fun (p : α × α) => nndist (prod.fst p) (prod.snd p) :=
  uniform_continuous.continuous uniform_continuous_nndist

theorem continuous.nndist {α : Type u} {β : Type v} [metric_space α] [topological_space β] {f : β → α} {g : β → α} (hf : continuous f) (hg : continuous g) : continuous fun (b : β) => nndist (f b) (g b) :=
  continuous.comp continuous_nndist (continuous.prod_mk hf hg)

theorem filter.tendsto.nndist {α : Type u} {β : Type v} [metric_space α] {f : β → α} {g : β → α} {x : filter β} {a : α} {b : α} (hf : filter.tendsto f x (nhds a)) (hg : filter.tendsto g x (nhds b)) : filter.tendsto (fun (x : β) => nndist (f x) (g x)) x (nhds (nndist a b)) :=
  filter.tendsto.comp (continuous.tendsto continuous_nndist (a, b)) (filter.tendsto.prod_mk_nhds hf hg)

namespace metric


theorem is_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : is_closed (closed_ball x ε) :=
  is_closed_le (continuous.dist continuous_id continuous_const) continuous_const

theorem is_closed_sphere {α : Type u} [metric_space α] {x : α} {ε : ℝ} : is_closed (sphere x ε) :=
  is_closed_eq (continuous.dist continuous_id continuous_const) continuous_const

@[simp] theorem closure_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : closure (closed_ball x ε) = closed_ball x ε :=
  is_closed.closure_eq is_closed_ball

theorem closure_ball_subset_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : closure (ball x ε) ⊆ closed_ball x ε :=
  closure_minimal ball_subset_closed_ball is_closed_ball

theorem frontier_ball_subset_sphere {α : Type u} [metric_space α] {x : α} {ε : ℝ} : frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (continuous.dist continuous_id continuous_const) continuous_const

theorem frontier_closed_ball_subset_sphere {α : Type u} [metric_space α] {x : α} {ε : ℝ} : frontier (closed_ball x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (continuous.dist continuous_id continuous_const) continuous_const

theorem ball_subset_interior_closed_ball {α : Type u} [metric_space α] {x : α} {ε : ℝ} : ball x ε ⊆ interior (closed_ball x ε) :=
  interior_maximal ball_subset_closed_ball is_open_ball

/-- ε-characterization of the closure in metric spaces-/
theorem mem_closure_iff {α : Type u} [metric_space α] {s : set α} {a : α} : a ∈ closure s ↔ ∀ (ε : ℝ) (H : ε > 0), ∃ (b : α), ∃ (H : b ∈ s), dist a b < ε := sorry

theorem mem_closure_range_iff {β : Type v} {α : Type u} [metric_space α] {e : β → α} {a : α} : a ∈ closure (set.range e) ↔ ∀ (ε : ℝ), ε > 0 → ∃ (k : β), dist a (e k) < ε := sorry

theorem mem_closure_range_iff_nat {β : Type v} {α : Type u} [metric_space α] {e : β → α} {a : α} : a ∈ closure (set.range e) ↔ ∀ (n : ℕ), ∃ (k : β), dist a (e k) < 1 / (↑n + 1) := sorry

theorem mem_of_closed' {α : Type u} [metric_space α] {s : set α} (hs : is_closed s) {a : α} : a ∈ s ↔ ∀ (ε : ℝ) (H : ε > 0), ∃ (b : α), ∃ (H : b ∈ s), dist a b < ε := sorry

end metric


/-- A finite product of metric spaces is a metric space, with the sup distance. -/
protected instance metric_space_pi {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] : metric_space ((b : β) → π b) :=
  emetric_space.to_metric_space_of_dist
    (fun (f g : (b : β) → π b) => ↑(finset.sup finset.univ fun (b : β) => nndist (f b) (g b))) sorry sorry

theorem nndist_pi_def {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] (f : (b : β) → π b) (g : (b : β) → π b) : nndist f g = finset.sup finset.univ fun (b : β) => nndist (f b) (g b) :=
  subtype.eta (finset.sup finset.univ fun (b : β) => nndist (f b) (g b)) dist_nonneg

theorem dist_pi_def {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] (f : (b : β) → π b) (g : (b : β) → π b) : dist f g = ↑(finset.sup finset.univ fun (b : β) => nndist (f b) (g b)) :=
  rfl

@[simp] theorem dist_pi_const {α : Type u} {β : Type v} [metric_space α] [fintype β] [Nonempty β] (a : α) (b : α) : (dist (fun (x : β) => a) fun (_x : β) => b) = dist a b := sorry

@[simp] theorem nndist_pi_const {α : Type u} {β : Type v} [metric_space α] [fintype β] [Nonempty β] (a : α) (b : α) : (nndist (fun (x : β) => a) fun (_x : β) => b) = nndist a b :=
  nnreal.eq (dist_pi_const a b)

theorem dist_pi_lt_iff {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] {f : (b : β) → π b} {g : (b : β) → π b} {r : ℝ} (hr : 0 < r) : dist f g < r ↔ ∀ (b : β), dist (f b) (g b) < r := sorry

theorem dist_pi_le_iff {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] {f : (b : β) → π b} {g : (b : β) → π b} {r : ℝ} (hr : 0 ≤ r) : dist f g ≤ r ↔ ∀ (b : β), dist (f b) (g b) ≤ r := sorry

theorem nndist_le_pi_nndist {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] (f : (b : β) → π b) (g : (b : β) → π b) (b : β) : nndist (f b) (g b) ≤ nndist f g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nndist (f b) (g b) ≤ nndist f g)) (nndist_pi_def f g)))
    (finset.le_sup (finset.mem_univ b))

theorem dist_le_pi_dist {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] (f : (b : β) → π b) (g : (b : β) → π b) (b : β) : dist (f b) (g b) ≤ dist f g := sorry

/-- An open ball in a product space is a product of open balls. The assumption `0 < r`
is necessary for the case of the empty product. -/
theorem ball_pi {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] (x : (b : β) → π b) {r : ℝ} (hr : 0 < r) : metric.ball x r = set_of fun (y : (b : β) → π b) => ∀ (b : β), y b ∈ metric.ball (x b) r := sorry

/-- A closed ball in a product space is a product of closed balls. The assumption `0 ≤ r`
is necessary for the case of the empty product. -/
theorem closed_ball_pi {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] (x : (b : β) → π b) {r : ℝ} (hr : 0 ≤ r) : metric.closed_ball x r = set_of fun (y : (b : β) → π b) => ∀ (b : β), y b ∈ metric.closed_ball (x b) r := sorry

/-- Any compact set in a metric space can be covered by finitely many balls of a given positive
radius -/
theorem finite_cover_balls_of_compact {α : Type u} [metric_space α] {s : set α} (hs : is_compact s) {e : ℝ} (he : 0 < e) : ∃ (t : set α), ∃ (H : t ⊆ s), set.finite t ∧ s ⊆ set.Union fun (x : α) => set.Union fun (H : x ∈ t) => metric.ball x e := sorry

theorem is_compact.finite_cover_balls {α : Type u} [metric_space α] {s : set α} (hs : is_compact s) {e : ℝ} (he : 0 < e) : ∃ (t : set α), ∃ (H : t ⊆ s), set.finite t ∧ s ⊆ set.Union fun (x : α) => set.Union fun (H : x ∈ t) => metric.ball x e :=
  finite_cover_balls_of_compact

/-- A metric space is proper if all closed balls are compact. -/
class proper_space (α : Type u) [metric_space α] 
where
  compact_ball : ∀ (x : α) (r : ℝ), is_compact (metric.closed_ball x r)

theorem tendsto_dist_right_cocompact_at_top {α : Type u} [metric_space α] [proper_space α] (x : α) : filter.tendsto (fun (y : α) => dist y x) (filter.cocompact α) filter.at_top := sorry

theorem tendsto_dist_left_cocompact_at_top {α : Type u} [metric_space α] [proper_space α] (x : α) : filter.tendsto (dist x) (filter.cocompact α) filter.at_top := sorry

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
theorem proper_space_of_compact_closed_ball_of_le {α : Type u} [metric_space α] (R : ℝ) (h : ∀ (x : α) (r : ℝ), R ≤ r → is_compact (metric.closed_ball x r)) : proper_space α := sorry

/- A compact metric space is proper -/

protected instance proper_of_compact {α : Type u} [metric_space α] [compact_space α] : proper_space α :=
  proper_space.mk fun (x : α) (r : ℝ) => is_closed.compact metric.is_closed_ball

/-- A proper space is locally compact -/
protected instance locally_compact_of_proper {α : Type u} [metric_space α] [proper_space α] : locally_compact_space α :=
  locally_compact_of_compact_nhds
    fun (x : α) =>
      Exists.intro (metric.closed_ball x 1)
        { left :=
            iff.mpr metric.mem_nhds_iff
              (Exists.intro 1
                (eq.mpr
                  (id
                    (Eq.trans (propext exists_prop)
                      ((fun (a a_1 : Prop) (e_1 : a = a_1) (b b_1 : Prop) (e_2 : b = b_1) =>
                          congr (congr_arg And e_1) e_2)
                        (1 > 0) (0 < 1) (propext gt_iff_lt) (metric.ball x 1 ⊆ metric.closed_ball x 1)
                        (metric.ball x 1 ⊆ metric.closed_ball x 1) (Eq.refl (metric.ball x 1 ⊆ metric.closed_ball x 1)))))
                  { left := zero_lt_one, right := metric.ball_subset_closed_ball })),
          right := proper_space.compact_ball x 1 }

/-- A proper space is complete -/
protected instance complete_of_proper {α : Type u} [metric_space α] [proper_space α] : complete_space α := sorry

/-- A proper metric space is separable, and therefore second countable. Indeed, any ball is
compact, and therefore admits a countable dense subset. Taking a countable union over the balls
centered at a fixed point and with integer radius, one obtains a countable set which is
dense in the whole space. -/
protected instance second_countable_of_proper {α : Type u} [metric_space α] [proper_space α] : topological_space.second_countable_topology α :=
  emetric.second_countable_of_separable α

/-- A finite product of proper spaces is proper. -/
protected instance pi_proper_space {β : Type v} {π : β → Type u_1} [fintype β] [(b : β) → metric_space (π b)] [h : ∀ (b : β), proper_space (π b)] : proper_space ((b : β) → π b) :=
  proper_space_of_compact_closed_ball_of_le 0
    fun (x : (b : β) → π b) (r : ℝ) (hr : 0 ≤ r) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (is_compact (metric.closed_ball x r))) (closed_ball_pi x hr)))
        (compact_pi_infinite fun (b : β) => proper_space.compact_ball (x b) r)

namespace metric


/-- A metric space is second countable if, for every `ε > 0`, there is a countable set which is
`ε`-dense. -/
theorem second_countable_of_almost_dense_set {α : Type u} [metric_space α] (H : ∀ (ε : ℝ) (H : ε > 0), ∃ (s : set α), set.countable s ∧ ∀ (x : α), ∃ (y : α), ∃ (H : y ∈ s), dist x y ≤ ε) : topological_space.second_countable_topology α := sorry

/-- A metric space space is second countable if one can reconstruct up to any `ε>0` any element of
the space from countably many data. -/
theorem second_countable_of_countable_discretization {α : Type u} [metric_space α] (H : ∀ (ε : ℝ), ε > 0 → ∃ (β : Type u_1), Exists (∃ (F : α → β), ∀ (x y : α), F x = F y → dist x y ≤ ε)) : topological_space.second_countable_topology α := sorry

end metric


theorem lebesgue_number_lemma_of_metric {α : Type u} [metric_space α] {s : set α} {ι : Sort u_1} {c : ι → set α} (hs : is_compact s) (hc₁ : ∀ (i : ι), is_open (c i)) (hc₂ : s ⊆ set.Union fun (i : ι) => c i) : ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (x : α), x ∈ s → ∃ (i : ι), metric.ball x δ ⊆ c i := sorry

theorem lebesgue_number_lemma_of_metric_sUnion {α : Type u} [metric_space α] {s : set α} {c : set (set α)} (hs : is_compact s) (hc₁ : ∀ (t : set α), t ∈ c → is_open t) (hc₂ : s ⊆ ⋃₀c) : ∃ (δ : ℝ), ∃ (H : δ > 0), ∀ (x : α) (H : x ∈ s), ∃ (t : set α), ∃ (H : t ∈ c), metric.ball x δ ⊆ t := sorry

namespace metric


/-- Boundedness of a subset of a metric space. We formulate the definition to work
even in the empty space. -/
def bounded {α : Type u} [metric_space α] (s : set α)  :=
  ∃ (C : ℝ), ∀ (x y : α), x ∈ s → y ∈ s → dist x y ≤ C

@[simp] theorem bounded_empty {α : Type u} [metric_space α] : bounded ∅ := sorry

theorem bounded_iff_mem_bounded {α : Type u} [metric_space α] {s : set α} : bounded s ↔ ∀ (x : α), x ∈ s → bounded s := sorry

/-- Subsets of a bounded set are also bounded -/
theorem bounded.subset {α : Type u} [metric_space α] {s : set α} {t : set α} (incl : s ⊆ t) : bounded t → bounded s :=
  Exists.imp
    fun (C : ℝ) (hC : ∀ (x y : α), x ∈ t → y ∈ t → dist x y ≤ C) (x y : α) (hx : x ∈ s) (hy : y ∈ s) =>
      hC x y (incl hx) (incl hy)

/-- Closed balls are bounded -/
theorem bounded_closed_ball {α : Type u} [metric_space α] {x : α} {r : ℝ} : bounded (closed_ball x r) := sorry

/-- Open balls are bounded -/
theorem bounded_ball {α : Type u} [metric_space α] {x : α} {r : ℝ} : bounded (ball x r) :=
  bounded.subset ball_subset_closed_ball bounded_closed_ball

/-- Given a point, a bounded subset is included in some ball around this point -/
theorem bounded_iff_subset_ball {α : Type u} [metric_space α] {s : set α} (c : α) : bounded s ↔ ∃ (r : ℝ), s ⊆ closed_ball c r := sorry

theorem bounded_closure_of_bounded {α : Type u} [metric_space α] {s : set α} (h : bounded s) : bounded (closure s) := sorry

theorem Mathlib.bounded.closure {α : Type u} [metric_space α] {s : set α} (h : bounded s) : bounded (closure s) :=
  bounded_closure_of_bounded

/-- The union of two bounded sets is bounded iff each of the sets is bounded -/
@[simp] theorem bounded_union {α : Type u} [metric_space α] {s : set α} {t : set α} : bounded (s ∪ t) ↔ bounded s ∧ bounded t := sorry

/-- A finite union of bounded sets is bounded -/
theorem bounded_bUnion {α : Type u} {β : Type v} [metric_space α] {I : set β} {s : β → set α} (H : set.finite I) : bounded (set.Union fun (i : β) => set.Union fun (H : i ∈ I) => s i) ↔ ∀ (i : β), i ∈ I → bounded (s i) := sorry

/-- A compact set is bounded -/
-- We cover the compact set by finitely many balls of radius 1,

theorem bounded_of_compact {α : Type u} [metric_space α] {s : set α} (h : is_compact s) : bounded s := sorry

-- and then argue that a finite union of bounded sets is bounded

theorem Mathlib.is_compact.bounded {α : Type u} [metric_space α] {s : set α} (h : is_compact s) : bounded s :=
  bounded_of_compact

/-- A finite set is bounded -/
theorem bounded_of_finite {α : Type u} [metric_space α] {s : set α} (h : set.finite s) : bounded s :=
  is_compact.bounded (set.finite.is_compact h)

/-- A singleton is bounded -/
theorem bounded_singleton {α : Type u} [metric_space α] {x : α} : bounded (singleton x) :=
  bounded_of_finite (set.finite_singleton x)

/-- Characterization of the boundedness of the range of a function -/
theorem bounded_range_iff {α : Type u} {β : Type v} [metric_space α] {f : β → α} : bounded (set.range f) ↔ ∃ (C : ℝ), ∀ (x y : β), dist (f x) (f y) ≤ C := sorry

/-- In a compact space, all sets are bounded -/
theorem bounded_of_compact_space {α : Type u} [metric_space α] {s : set α} [compact_space α] : bounded s :=
  bounded.subset (set.subset_univ s) (is_compact.bounded compact_univ)

/-- The Heine–Borel theorem:
In a proper space, a set is compact if and only if it is closed and bounded -/
theorem compact_iff_closed_bounded {α : Type u} [metric_space α] {s : set α} [proper_space α] : is_compact s ↔ is_closed s ∧ bounded s := sorry

/-- The image of a proper space under an expanding onto map is proper. -/
theorem proper_image_of_proper {α : Type u} {β : Type v} [metric_space α] [proper_space α] [metric_space β] (f : α → β) (f_cont : continuous f) (hf : set.range f = set.univ) (C : ℝ) (hC : ∀ (x y : α), dist x y ≤ C * dist (f x) (f y)) : proper_space β := sorry

/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the emetric.diameter -/
def diam {α : Type u} [metric_space α] (s : set α) : ℝ :=
  ennreal.to_real (emetric.diam s)

/-- The diameter of a set is always nonnegative -/
theorem diam_nonneg {α : Type u} [metric_space α] {s : set α} : 0 ≤ diam s :=
  ennreal.to_real_nonneg

theorem diam_subsingleton {α : Type u} [metric_space α] {s : set α} (hs : set.subsingleton s) : diam s = 0 := sorry

/-- The empty set has zero diameter -/
@[simp] theorem diam_empty {α : Type u} [metric_space α] : diam ∅ = 0 :=
  diam_subsingleton set.subsingleton_empty

/-- A singleton has zero diameter -/
@[simp] theorem diam_singleton {α : Type u} [metric_space α] {x : α} : diam (singleton x) = 0 :=
  diam_subsingleton set.subsingleton_singleton

-- Does not work as a simp-lemma, since {x, y} reduces to (insert y {x})

theorem diam_pair {α : Type u} [metric_space α] {x : α} {y : α} : diam (insert x (singleton y)) = dist x y := sorry

-- Does not work as a simp-lemma, since {x, y, z} reduces to (insert z (insert y {x}))

theorem diam_triple {α : Type u} [metric_space α] {x : α} {y : α} {z : α} : diam (insert x (insert y (singleton z))) = max (max (dist x y) (dist x z)) (dist y z) := sorry

/-- If the distance between any two points in a set is bounded by some constant `C`,
then `ennreal.of_real C`  bounds the emetric diameter of this set. -/
theorem ediam_le_of_forall_dist_le {α : Type u} [metric_space α] {s : set α} {C : ℝ} (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist x y ≤ C) : emetric.diam s ≤ ennreal.of_real C :=
  emetric.diam_le_of_forall_edist_le
    fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) => Eq.symm (edist_dist x y) ▸ ennreal.of_real_le_of_real (h x hx y hy)

/-- If the distance between any two points in a set is bounded by some non-negative constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le {α : Type u} [metric_space α] {s : set α} {C : ℝ} (h₀ : 0 ≤ C) (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist x y ≤ C) : diam s ≤ C :=
  ennreal.to_real_le_of_le_of_real h₀ (ediam_le_of_forall_dist_le h)

/-- If the distance between any two points in a nonempty set is bounded by some constant,
this constant bounds the diameter. -/
theorem diam_le_of_forall_dist_le_of_nonempty {α : Type u} [metric_space α] {s : set α} (hs : set.nonempty s) {C : ℝ} (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist x y ≤ C) : diam s ≤ C := sorry

/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem' {α : Type u} [metric_space α] {s : set α} {x : α} {y : α} (h : emetric.diam s ≠ ⊤) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s := sorry

/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
theorem bounded_iff_ediam_ne_top {α : Type u} [metric_space α] {s : set α} : bounded s ↔ emetric.diam s ≠ ⊤ := sorry

theorem bounded.ediam_ne_top {α : Type u} [metric_space α] {s : set α} (h : bounded s) : emetric.diam s ≠ ⊤ :=
  iff.mp bounded_iff_ediam_ne_top h

/-- The distance between two points in a set is controlled by the diameter of the set. -/
theorem dist_le_diam_of_mem {α : Type u} [metric_space α] {s : set α} {x : α} {y : α} (h : bounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
  dist_le_diam_of_mem' (bounded.ediam_ne_top h) hx hy

/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `emetric.diam`.
This lemma makes it possible to avoid side conditions in some situations -/
theorem diam_eq_zero_of_unbounded {α : Type u} [metric_space α] {s : set α} (h : ¬bounded s) : diam s = 0 := sorry

/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
theorem diam_mono {α : Type u} [metric_space α] {s : set α} {t : set α} (h : s ⊆ t) (ht : bounded t) : diam s ≤ diam t := sorry

/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
theorem diam_union {α : Type u} [metric_space α] {s : set α} {x : α} {y : α} {t : set α} (xs : x ∈ s) (yt : y ∈ t) : diam (s ∪ t) ≤ diam s + dist x y + diam t := sorry

/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
theorem diam_union' {α : Type u} [metric_space α] {s : set α} {t : set α} (h : set.nonempty (s ∩ t)) : diam (s ∪ t) ≤ diam s + diam t := sorry

/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
theorem diam_closed_ball {α : Type u} [metric_space α] {x : α} {r : ℝ} (h : 0 ≤ r) : diam (closed_ball x r) ≤ bit0 1 * r := sorry

/-- The diameter of a ball of radius `r` is at most `2 r`. -/
theorem diam_ball {α : Type u} [metric_space α] {x : α} {r : ℝ} (h : 0 ≤ r) : diam (ball x r) ≤ bit0 1 * r :=
  le_trans (diam_mono ball_subset_closed_ball bounded_closed_ball) (diam_closed_ball h)

