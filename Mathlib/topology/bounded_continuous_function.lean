/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.normed_space.basic
import Mathlib.PostPort

universes u v w u_1 

namespace Mathlib

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with
the uniform distance.

-/

/-- The type of bounded continuous functions from a topological space to a metric space -/
def bounded_continuous_function (α : Type u) (β : Type v) [topological_space α] [metric_space β] :=
  Subtype fun (f : α → β) => continuous f ∧ ∃ (C : ℝ), ∀ (x y : α), dist (f x) (f y) ≤ C

namespace bounded_continuous_function


protected instance has_coe_to_fun {α : Type u} {β : Type v} [topological_space α] [metric_space β] : has_coe_to_fun (bounded_continuous_function α β) :=
  has_coe_to_fun.mk (fun (x : bounded_continuous_function α β) => α → β) subtype.val

theorem bounded_range {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} : metric.bounded (set.range ⇑f) :=
  iff.mpr metric.bounded_range_iff (and.right (subtype.property f))

/-- If a function is continuous on a compact space, it is automatically bounded,
and therefore gives rise to an element of the type of bounded continuous functions -/
def mk_of_compact {α : Type u} {β : Type v} [topological_space α] [metric_space β] [compact_space α] (f : α → β) (hf : continuous f) : bounded_continuous_function α β :=
  { val := f, property := sorry }

/-- If a function is bounded on a discrete space, it is automatically continuous,
and therefore gives rise to an element of the type of bounded continuous functions -/
def mk_of_discrete {α : Type u} {β : Type v} [topological_space α] [metric_space β] [discrete_topology α] (f : α → β) (hf : ∃ (C : ℝ), ∀ (x y : α), dist (f x) (f y) ≤ C) : bounded_continuous_function α β :=
  { val := f, property := sorry }

/-- The uniform distance between two bounded continuous functions -/
protected instance has_dist {α : Type u} {β : Type v} [topological_space α] [metric_space β] : has_dist (bounded_continuous_function α β) :=
  has_dist.mk
    fun (f g : bounded_continuous_function α β) =>
      Inf (set_of fun (C : ℝ) => 0 ≤ C ∧ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C)

theorem dist_eq {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} : dist f g = Inf (set_of fun (C : ℝ) => 0 ≤ C ∧ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C) :=
  rfl

theorem dist_set_exists {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} : ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C := sorry

/-- The pointwise distance is controlled by the distance between functions, by definition. -/
theorem dist_coe_le_dist {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} (x : α) : dist (coe_fn f x) (coe_fn g x) ≤ dist f g :=
  le_cInf dist_set_exists
    fun (b : ℝ) (hb : b ∈ set_of fun (C : ℝ) => 0 ≤ C ∧ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C) => and.right hb x

theorem ext {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} (H : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g :=
  subtype.eq (funext H)

theorem ext_iff {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} : f = g ↔ ∀ (x : α), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : α) => h ▸ rfl, mpr := ext }

/- This lemma will be needed in the proof of the metric space instance, but it will become
useless afterwards as it will be superceded by the general result that the distance is nonnegative
is metric spaces. -/

/-- The distance between two functions is controlled by the supremum of the pointwise distances -/
theorem dist_le {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} {C : ℝ} (C0 : 0 ≤ C) : dist f g ≤ C ↔ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C := sorry

/-- On an empty space, bounded continuous functions are at distance 0 -/
theorem dist_zero_of_empty {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} {g : bounded_continuous_function α β} (e : ¬Nonempty α) : dist f g = 0 :=
  le_antisymm (iff.mpr (dist_le (le_refl 0)) fun (x : α) => not.elim e (Nonempty.intro x)) dist_nonneg'

/-- The type of bounded continuous functions, with the uniform distance, is a metric space. -/
protected instance metric_space {α : Type u} {β : Type v} [topological_space α] [metric_space β] : metric_space (bounded_continuous_function α β) :=
  metric_space.mk sorry sorry sorry sorry
    (fun (x y : bounded_continuous_function α β) =>
      ennreal.of_real
        ((fun (f g : bounded_continuous_function α β) =>
            Inf (set_of fun (C : ℝ) => 0 ≤ C ∧ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C))
          x y))
    (uniform_space_of_dist
      (fun (f g : bounded_continuous_function α β) =>
        Inf (set_of fun (C : ℝ) => 0 ≤ C ∧ ∀ (x : α), dist (coe_fn f x) (coe_fn g x) ≤ C))
      sorry sorry sorry)

/-- Constant as a continuous bounded function. -/
def const (α : Type u) {β : Type v} [topological_space α] [metric_space β] (b : β) : bounded_continuous_function α β :=
  { val := fun (x : α) => b, property := sorry }

@[simp] theorem coe_const {α : Type u} {β : Type v} [topological_space α] [metric_space β] (b : β) : ⇑(const α b) = function.const α b :=
  rfl

theorem const_apply {α : Type u} {β : Type v} [topological_space α] [metric_space β] (a : α) (b : β) : coe_fn (const α b) a = b :=
  rfl

/-- If the target space is inhabited, so is the space of bounded continuous functions -/
protected instance inhabited {α : Type u} {β : Type v} [topological_space α] [metric_space β] [Inhabited β] : Inhabited (bounded_continuous_function α β) :=
  { default := const α Inhabited.default }

/-- The evaluation map is continuous, as a joint function of `u` and `x` -/
theorem continuous_eval {α : Type u} {β : Type v} [topological_space α] [metric_space β] : continuous fun (p : bounded_continuous_function α β × α) => coe_fn (prod.fst p) (prod.snd p) := sorry

/- use the continuity of `f` to find a neighborhood of `x` where it varies at most by ε/2 -/

/-- In particular, when `x` is fixed, `f → f x` is continuous -/
theorem continuous_evalx {α : Type u} {β : Type v} [topological_space α] [metric_space β] {x : α} : continuous fun (f : bounded_continuous_function α β) => coe_fn f x :=
  continuous.comp continuous_eval (continuous.prod_mk continuous_id continuous_const)

/-- When `f` is fixed, `x → f x` is also continuous, by definition -/
theorem continuous_evalf {α : Type u} {β : Type v} [topological_space α] [metric_space β] {f : bounded_continuous_function α β} : continuous ⇑f :=
  and.left (subtype.property f)

/-- Bounded continuous functions taking values in a complete space form a complete space. -/
protected instance complete_space {α : Type u} {β : Type v} [topological_space α] [metric_space β] [complete_space β] : complete_space (bounded_continuous_function α β) := sorry

/-- Composition (in the target) of a bounded continuous function with a Lipschitz map again
gives a bounded continuous function -/
def comp {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [metric_space β] [metric_space γ] (G : β → γ) {C : nnreal} (H : lipschitz_with C G) (f : bounded_continuous_function α β) : bounded_continuous_function α γ :=
  { val := fun (x : α) => G (coe_fn f x), property := sorry }

/-- The composition operator (in the target) with a Lipschitz map is Lipschitz -/
theorem lipschitz_comp {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [metric_space β] [metric_space γ] {G : β → γ} {C : nnreal} (H : lipschitz_with C G) : lipschitz_with C (comp G H) := sorry

/-- The composition operator (in the target) with a Lipschitz map is uniformly continuous -/
theorem uniform_continuous_comp {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [metric_space β] [metric_space γ] {G : β → γ} {C : nnreal} (H : lipschitz_with C G) : uniform_continuous (comp G H) :=
  lipschitz_with.uniform_continuous (lipschitz_comp H)

/-- The composition operator (in the target) with a Lipschitz map is continuous -/
theorem continuous_comp {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [metric_space β] [metric_space γ] {G : β → γ} {C : nnreal} (H : lipschitz_with C G) : continuous (comp G H) :=
  lipschitz_with.continuous (lipschitz_comp H)

/-- Restriction (in the target) of a bounded continuous function taking values in a subset -/
def cod_restrict {α : Type u} {β : Type v} [topological_space α] [metric_space β] (s : set β) (f : bounded_continuous_function α β) (H : ∀ (x : α), coe_fn f x ∈ s) : bounded_continuous_function α ↥s :=
  { val := set.cod_restrict (⇑f) s H, property := sorry }

/- Arzela-Ascoli theorem asserts that, on a compact space, a set of functions sharing
a common modulus of continuity and taking values in a compact set forms a compact
subset for the topology of uniform convergence. In this section, we prove this theorem
and several useful variations around it. -/

/-- First version, with pointwise equicontinuity and range in a compact space -/
theorem arzela_ascoli₁ {α : Type u} {β : Type v} [topological_space α] [compact_space α] [metric_space β] [compact_space β] (A : set (bounded_continuous_function α β)) (closed : is_closed A) (H : ∀ (x : α) (ε : ℝ) (H : ε > 0),
  ∃ (U : set α),
    ∃ (H : U ∈ nhds x),
      ∀ (y z : α), y ∈ U → z ∈ U → ∀ (f : bounded_continuous_function α β), f ∈ A → dist (coe_fn f y) (coe_fn f z) < ε) : is_compact A := sorry

/-- Second version, with pointwise equicontinuity and range in a compact subset -/
theorem arzela_ascoli₂ {α : Type u} {β : Type v} [topological_space α] [compact_space α] [metric_space β] (s : set β) (hs : is_compact s) (A : set (bounded_continuous_function α β)) (closed : is_closed A) (in_s : ∀ (f : bounded_continuous_function α β) (x : α), f ∈ A → coe_fn f x ∈ s) (H : ∀ (x : α) (ε : ℝ) (H : ε > 0),
  ∃ (U : set α),
    ∃ (H : U ∈ nhds x),
      ∀ (y z : α), y ∈ U → z ∈ U → ∀ (f : bounded_continuous_function α β), f ∈ A → dist (coe_fn f y) (coe_fn f z) < ε) : is_compact A := sorry

/- This version is deduced from the previous one by restricting to the compact type in the target,
using compactness there and then lifting everything to the original space. -/

/-- Third (main) version, with pointwise equicontinuity and range in a compact subset, but
without closedness. The closure is then compact -/
theorem arzela_ascoli {α : Type u} {β : Type v} [topological_space α] [compact_space α] [metric_space β] (s : set β) (hs : is_compact s) (A : set (bounded_continuous_function α β)) (in_s : ∀ (f : bounded_continuous_function α β) (x : α), f ∈ A → coe_fn f x ∈ s) (H : ∀ (x : α) (ε : ℝ) (H : ε > 0),
  ∃ (U : set α),
    ∃ (H : U ∈ nhds x),
      ∀ (y z : α), y ∈ U → z ∈ U → ∀ (f : bounded_continuous_function α β), f ∈ A → dist (coe_fn f y) (coe_fn f z) < ε) : is_compact (closure A) := sorry

/- This version is deduced from the previous one by checking that the closure of A, in
addition to being closed, still satisfies the properties of compact range and equicontinuity -/

/- To apply the previous theorems, one needs to check the equicontinuity. An important
instance is when the source space is a metric space, and there is a fixed modulus of continuity
for all the functions in the set A -/

theorem equicontinuous_of_continuity_modulus {β : Type v} [metric_space β] {α : Type u} [metric_space α] (b : ℝ → ℝ) (b_lim : filter.tendsto b (nhds 0) (nhds 0)) (A : set (bounded_continuous_function α β)) (H : ∀ (x y : α) (f : bounded_continuous_function α β), f ∈ A → dist (coe_fn f x) (coe_fn f y) ≤ b (dist x y)) (x : α) (ε : ℝ) (ε0 : 0 < ε) : ∃ (U : set α),
  ∃ (H : U ∈ nhds x),
    ∀ (y z : α), y ∈ U → z ∈ U → ∀ (f : bounded_continuous_function α β), f ∈ A → dist (coe_fn f y) (coe_fn f z) < ε := sorry

/- In this section, if β is a normed group, then we show that the space of bounded
continuous functions from α to β inherits a normed group structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

protected instance has_zero {α : Type u} {β : Type v} [topological_space α] [normed_group β] : HasZero (bounded_continuous_function α β) :=
  { zero := const α 0 }

@[simp] theorem coe_zero {α : Type u} {β : Type v} [topological_space α] [normed_group β] {x : α} : coe_fn 0 x = 0 :=
  rfl

protected instance has_norm {α : Type u} {β : Type v} [topological_space α] [normed_group β] : has_norm (bounded_continuous_function α β) :=
  has_norm.mk fun (u : bounded_continuous_function α β) => dist u 0

theorem norm_def {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) : norm f = dist f 0 :=
  rfl

/-- The norm of a bounded continuous function is the supremum of `∥f x∥`.
We use `Inf` to ensure that the definition works if `α` has no elements. -/
theorem norm_eq {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) : norm f = Inf (set_of fun (C : ℝ) => 0 ≤ C ∧ ∀ (x : α), norm (coe_fn f x) ≤ C) := sorry

theorem norm_coe_le_norm {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (x : α) : norm (coe_fn f x) ≤ norm f := sorry

theorem dist_le_two_norm' {β : Type v} {γ : Type w} [normed_group β] {f : γ → β} {C : ℝ} (hC : ∀ (x : γ), norm (f x) ≤ C) (x : γ) (y : γ) : dist (f x) (f y) ≤ bit0 1 * C :=
  trans_rel_left LessEq (le_trans (dist_le_norm_add_norm (f x) (f y)) (add_le_add (hC x) (hC y))) (Eq.symm (two_mul C))

/-- Distance between the images of any two points is at most twice the norm of the function. -/
theorem dist_le_two_norm {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (x : α) (y : α) : dist (coe_fn f x) (coe_fn f y) ≤ bit0 1 * norm f :=
  dist_le_two_norm' (norm_coe_le_norm f) x y

/-- The norm of a function is controlled by the supremum of the pointwise norms -/
theorem norm_le {α : Type u} {β : Type v} [topological_space α] [normed_group β] {f : bounded_continuous_function α β} {C : ℝ} (C0 : 0 ≤ C) : norm f ≤ C ↔ ∀ (x : α), norm (coe_fn f x) ≤ C := sorry

/-- Norm of `const α b` is less than or equal to `∥b∥`. If `α` is nonempty,
then it is equal to `∥b∥`. -/
theorem norm_const_le {α : Type u} {β : Type v} [topological_space α] [normed_group β] (b : β) : norm (const α b) ≤ norm b :=
  iff.mpr (norm_le (norm_nonneg b)) fun (x : α) => le_refl (norm (coe_fn (const α b) x))

@[simp] theorem norm_const_eq {α : Type u} {β : Type v} [topological_space α] [normed_group β] [h : Nonempty α] (b : β) : norm (const α b) = norm b :=
  le_antisymm (norm_const_le b) (nonempty.elim h fun (x : α) => norm_coe_le_norm (const α b) x)

/-- Constructing a bounded continuous function from a uniformly bounded continuous
function taking values in a normed group. -/
def of_normed_group {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : α → β) (Hf : continuous f) (C : ℝ) (H : ∀ (x : α), norm (f x) ≤ C) : bounded_continuous_function α β :=
  { val := fun (n : α) => f n, property := sorry }

theorem norm_of_normed_group_le {α : Type u} {β : Type v} [topological_space α] [normed_group β] {f : α → β} (hfc : continuous f) {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ (x : α), norm (f x) ≤ C) : norm (of_normed_group f hfc C hfC) ≤ C :=
  iff.mpr (norm_le hC) hfC

/-- Constructing a bounded continuous function from a uniformly bounded
function on a discrete space, taking values in a normed group -/
def of_normed_group_discrete {α : Type u} {β : Type v} [topological_space α] [discrete_topology α] [normed_group β] (f : α → β) (C : ℝ) (H : ∀ (x : α), norm (f x) ≤ C) : bounded_continuous_function α β :=
  of_normed_group f sorry C H

/-- The pointwise sum of two bounded continuous functions is again bounded continuous. -/
protected instance has_add {α : Type u} {β : Type v} [topological_space α] [normed_group β] : Add (bounded_continuous_function α β) :=
  { add := fun (f g : bounded_continuous_function α β) => of_normed_group (⇑f + ⇑g) sorry (norm f + norm g) sorry }

/-- The pointwise opposite of a bounded continuous function is again bounded continuous. -/
protected instance has_neg {α : Type u} {β : Type v} [topological_space α] [normed_group β] : Neg (bounded_continuous_function α β) :=
  { neg := fun (f : bounded_continuous_function α β) => of_normed_group (-⇑f) sorry (norm f) sorry }

/-- The pointwise difference of two bounded continuous functions is again bounded continuous. -/
protected instance has_sub {α : Type u} {β : Type v} [topological_space α] [normed_group β] : Sub (bounded_continuous_function α β) :=
  { sub := fun (f g : bounded_continuous_function α β) => of_normed_group (⇑f - ⇑g) sorry (norm f + norm g) sorry }

@[simp] theorem coe_add {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (g : bounded_continuous_function α β) : ⇑(f + g) = fun (x : α) => coe_fn f x + coe_fn g x :=
  rfl

theorem add_apply {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (g : bounded_continuous_function α β) {x : α} : coe_fn (f + g) x = coe_fn f x + coe_fn g x :=
  rfl

@[simp] theorem coe_neg {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) : ⇑(-f) = fun (x : α) => -coe_fn f x :=
  rfl

theorem neg_apply {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) {x : α} : coe_fn (-f) x = -coe_fn f x :=
  rfl

theorem forall_coe_zero_iff_zero {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) : (∀ (x : α), coe_fn f x = 0) ↔ f = 0 :=
  iff.symm ext_iff

protected instance add_comm_group {α : Type u} {β : Type v} [topological_space α] [normed_group β] : add_comm_group (bounded_continuous_function α β) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry

@[simp] theorem coe_sub {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (g : bounded_continuous_function α β) : ⇑(f - g) = fun (x : α) => coe_fn f x - coe_fn g x :=
  rfl

theorem sub_apply {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (g : bounded_continuous_function α β) {x : α} : coe_fn (f - g) x = coe_fn f x - coe_fn g x :=
  rfl

protected instance normed_group {α : Type u} {β : Type v} [topological_space α] [normed_group β] : normed_group (bounded_continuous_function α β) :=
  normed_group.mk sorry

theorem abs_diff_coe_le_dist {α : Type u} {β : Type v} [topological_space α] [normed_group β] (f : bounded_continuous_function α β) (g : bounded_continuous_function α β) {x : α} : norm (coe_fn f x - coe_fn g x) ≤ dist f g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (norm (coe_fn f x - coe_fn g x) ≤ dist f g)) (dist_eq_norm f g)))
    (norm_coe_le_norm (f - g) x)

theorem coe_le_coe_add_dist {α : Type u} [topological_space α] {x : α} {f : bounded_continuous_function α ℝ} {g : bounded_continuous_function α ℝ} : coe_fn f x ≤ coe_fn g x + dist f g :=
  iff.mp sub_le_iff_le_add' (and.right (iff.mp abs_le (dist_coe_le_dist x)))

/-!
### Normed space structure

In this section, if `β` is a normed space, then we show that the space of bounded
continuous functions from `α` to `β` inherits a normed space structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

protected instance has_scalar {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] : has_scalar 𝕜 (bounded_continuous_function α β) :=
  has_scalar.mk
    fun (c : 𝕜) (f : bounded_continuous_function α β) => of_normed_group (c • ⇑f) sorry (norm c * norm f) sorry

@[simp] theorem coe_smul {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] (c : 𝕜) (f : bounded_continuous_function α β) : ⇑(c • f) = fun (x : α) => c • coe_fn f x :=
  rfl

theorem smul_apply {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] (c : 𝕜) (f : bounded_continuous_function α β) (x : α) : coe_fn (c • f) x = c • coe_fn f x :=
  rfl

protected instance semimodule {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] : semimodule 𝕜 (bounded_continuous_function α β) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

protected instance normed_space {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] : normed_space 𝕜 (bounded_continuous_function α β) :=
  normed_space.mk sorry

/-!
### Normed ring structure

In this section, if `R` is a normed ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

protected instance ring {α : Type u} [topological_space α] {R : Type u_1} [normed_ring R] : ring (bounded_continuous_function α R) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    (fun (f g : bounded_continuous_function α R) => of_normed_group (⇑f * ⇑g) sorry (norm f * norm g) sorry) sorry
    (const α 1) sorry sorry sorry sorry

protected instance normed_ring {α : Type u} [topological_space α] {R : Type u_1} [normed_ring R] : normed_ring (bounded_continuous_function α R) :=
  normed_ring.mk sorry sorry

/-!
### Normed commutative ring structure

In this section, if `R` is a normed commutative ring, then we show that the space of bounded
continuous functions from `α` to `R` inherits a normed commutative ring structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

protected instance comm_ring {α : Type u} [topological_space α] {R : Type u_1} [normed_comm_ring R] : comm_ring (bounded_continuous_function α R) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

protected instance normed_comm_ring {α : Type u} [topological_space α] {R : Type u_1} [normed_comm_ring R] : normed_comm_ring (bounded_continuous_function α R) :=
  normed_comm_ring.mk sorry

/-!
### Normed algebra structure

In this section, if `γ` is a normed algebra, then we show that the space of bounded
continuous functions from `α` to `γ` inherits a normed algebra structure, by using
pointwise operations and checking that they are compatible with the uniform distance. -/

/-- `bounded_continuous_function.const` as a `ring_hom`. -/
def C {α : Type u} {γ : Type w} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_ring γ] [normed_algebra 𝕜 γ] : 𝕜 →+* bounded_continuous_function α γ :=
  ring_hom.mk (fun (c : 𝕜) => const α (coe_fn (algebra_map 𝕜 γ) c)) sorry sorry sorry sorry

protected instance algebra {α : Type u} {γ : Type w} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_ring γ] [normed_algebra 𝕜 γ] : algebra 𝕜 (bounded_continuous_function α γ) :=
  algebra.mk C sorry sorry

protected instance normed_algebra {α : Type u} {γ : Type w} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_ring γ] [normed_algebra 𝕜 γ] [Nonempty α] : normed_algebra 𝕜 (bounded_continuous_function α γ) :=
  normed_algebra.mk sorry

/-!
### Structure as normed module over scalar functions

If `β` is a normed `𝕜`-space, then we show that the space of bounded continuous
functions from `α` to `β` is naturally a module over the algebra of bounded continuous
functions from `α` to `𝕜`. -/

protected instance has_scalar' {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] : has_scalar (bounded_continuous_function α 𝕜) (bounded_continuous_function α β) :=
  has_scalar.mk
    fun (f : bounded_continuous_function α 𝕜) (g : bounded_continuous_function α β) =>
      of_normed_group (fun (x : α) => coe_fn f x • coe_fn g x) sorry (norm f * norm g) sorry

protected instance module' {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] : module (bounded_continuous_function α 𝕜) (bounded_continuous_function α β) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

theorem norm_smul_le {α : Type u} {β : Type v} {𝕜 : Type u_1} [normed_field 𝕜] [topological_space α] [normed_group β] [normed_space 𝕜 β] (f : bounded_continuous_function α 𝕜) (g : bounded_continuous_function α β) : norm (f • g) ≤ norm f * norm g :=
  norm_of_normed_group_le (has_scalar'._proof_1 f g) (mul_nonneg (norm_nonneg f) (norm_nonneg g))
    (has_scalar'._proof_2 f g)

