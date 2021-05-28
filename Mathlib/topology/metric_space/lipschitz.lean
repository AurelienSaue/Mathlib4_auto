/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.function.iterate
import Mathlib.topology.metric_space.basic
import Mathlib.category_theory.endomorphism
import Mathlib.category_theory.types
import Mathlib.PostPort

universes u v w x 

namespace Mathlib

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous.

## Main definitions and lemmas

* `lipschitz_with K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `lipschitz_on_with K f`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `lipschitz_with.uniform_continuous`: a Lipschitz function is uniformly continuous
* `lipschitz_on_with.uniform_continuous_on`: a function which is Lipschitz on a set is uniformly
  continuous on that set.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjuction in the definition and have
coercions both to `ℝ` and `ennreal`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `lipschitz_with (nnreal.of_real K) f`.
-/

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def lipschitz_with {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (K : nnreal) (f : α → β)  :=
  ∀ (x y : α), edist (f x) (f y) ≤ ↑K * edist x y

theorem lipschitz_with_iff_dist_le_mul {α : Type u} {β : Type v} [metric_space α] [metric_space β] {K : nnreal} {f : α → β} : lipschitz_with K f ↔ ∀ (x y : α), dist (f x) (f y) ≤ ↑K * dist x y := sorry

theorem lipschitz_with.dist_le_mul {α : Type u} {β : Type v} [metric_space α] [metric_space β] {K : nnreal} {f : α → β} : lipschitz_with K f → ∀ (x y : α), dist (f x) (f y) ≤ ↑K * dist x y :=
  iff.mp lipschitz_with_iff_dist_le_mul

/-- A function `f` is Lipschitz continuous with constant `K ≥ 0` on `s` if for all `x, y` in `s`
we have `dist (f x) (f y) ≤ K * dist x y` -/
def lipschitz_on_with {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (K : nnreal) (f : α → β) (s : set α)  :=
  ∀ {x : α}, x ∈ s → ∀ {y : α}, y ∈ s → edist (f x) (f y) ≤ ↑K * edist x y

@[simp] theorem lipschitz_on_with_empty {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (K : nnreal) (f : α → β) : lipschitz_on_with K f ∅ :=
  fun (x : α) (x_in : x ∈ ∅) (y : α) (y_in : y ∈ ∅) => false.elim x_in

theorem lipschitz_on_with.mono {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {s : set α} {t : set α} {f : α → β} (hf : lipschitz_on_with K f t) (h : s ⊆ t) : lipschitz_on_with K f s :=
  fun (x : α) (x_in : x ∈ s) (y : α) (y_in : y ∈ s) => hf (h x_in) (h y_in)

theorem lipschitz_on_with_iff_dist_le_mul {α : Type u} {β : Type v} [metric_space α] [metric_space β] {K : nnreal} {s : set α} {f : α → β} : lipschitz_on_with K f s ↔ ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist (f x) (f y) ≤ ↑K * dist x y := sorry

theorem lipschitz_on_with.dist_le_mul {α : Type u} {β : Type v} [metric_space α] [metric_space β] {K : nnreal} {s : set α} {f : α → β} : lipschitz_on_with K f s → ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → dist (f x) (f y) ≤ ↑K * dist x y :=
  iff.mp lipschitz_on_with_iff_dist_le_mul

@[simp] theorem lipschitz_on_univ {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} : lipschitz_on_with K f set.univ ↔ lipschitz_with K f := sorry

theorem lipschitz_on_with_iff_restrict {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} {s : set α} : lipschitz_on_with K f s ↔ lipschitz_with K (set.restrict f s) := sorry

namespace lipschitz_with


theorem edist_le_mul {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (h : lipschitz_with K f) (x : α) (y : α) : edist (f x) (f y) ≤ ↑K * edist x y :=
  h x y

theorem edist_lt_top {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) {x : α} {y : α} (h : edist x y < ⊤) : edist (f x) (f y) < ⊤ :=
  lt_of_le_of_lt (hf x y) (ennreal.mul_lt_top ennreal.coe_lt_top h)

theorem mul_edist_le {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (h : lipschitz_with K f) (x : α) (y : α) : ↑K⁻¹ * edist (f x) (f y) ≤ edist x y := sorry

protected theorem of_edist_le {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {f : α → β} (h : ∀ (x y : α), edist (f x) (f y) ≤ edist x y) : lipschitz_with 1 f := sorry

protected theorem weaken {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) {K' : nnreal} (h : K ≤ K') : lipschitz_with K' f :=
  fun (x y : α) => le_trans (hf x y) (ennreal.mul_right_mono (iff.mpr ennreal.coe_le_coe h))

theorem ediam_image_le {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) (s : set α) : emetric.diam (f '' s) ≤ ↑K * emetric.diam s := sorry

/-- A Lipschitz function is uniformly continuous -/
protected theorem uniform_continuous {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) : uniform_continuous f := sorry

/-- A Lipschitz function is continuous -/
protected theorem continuous {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) : continuous f :=
  uniform_continuous.continuous (lipschitz_with.uniform_continuous hf)

protected theorem const {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] (b : β) : lipschitz_with 0 fun (a : α) => b := sorry

protected theorem id {α : Type u} [emetric_space α] : lipschitz_with 1 id :=
  lipschitz_with.of_edist_le fun (x y : α) => le_refl (edist (id x) (id y))

protected theorem subtype_val {α : Type u} [emetric_space α] (s : set α) : lipschitz_with 1 subtype.val :=
  lipschitz_with.of_edist_le fun (x y : Subtype fun (x : α) => x ∈ s) => le_refl (edist (subtype.val x) (subtype.val y))

protected theorem subtype_coe {α : Type u} [emetric_space α] (s : set α) : lipschitz_with 1 coe :=
  lipschitz_with.subtype_val s

protected theorem restrict {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) (s : set α) : lipschitz_with K (set.restrict f s) :=
  fun (x y : ↥s) => hf ↑x ↑y

protected theorem comp {α : Type u} {β : Type v} {γ : Type w} [emetric_space α] [emetric_space β] [emetric_space γ] {Kf : nnreal} {Kg : nnreal} {f : β → γ} {g : α → β} (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf * Kg) (f ∘ g) := sorry

protected theorem prod_fst {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] : lipschitz_with 1 prod.fst :=
  lipschitz_with.of_edist_le
    fun (x y : α × β) => le_max_left (edist (prod.fst x) (prod.fst y)) (edist (prod.snd x) (prod.snd y))

protected theorem prod_snd {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] : lipschitz_with 1 prod.snd :=
  lipschitz_with.of_edist_le
    fun (x y : α × β) => le_max_right (edist (prod.fst x) (prod.fst y)) (edist (prod.snd x) (prod.snd y))

protected theorem prod {α : Type u} {β : Type v} {γ : Type w} [emetric_space α] [emetric_space β] [emetric_space γ] {f : α → β} {Kf : nnreal} (hf : lipschitz_with Kf f) {g : α → γ} {Kg : nnreal} (hg : lipschitz_with Kg g) : lipschitz_with (max Kf Kg) fun (x : α) => (f x, g x) := sorry

protected theorem uncurry {α : Type u} {β : Type v} {γ : Type w} [emetric_space α] [emetric_space β] [emetric_space γ] {f : α → β → γ} {Kα : nnreal} {Kβ : nnreal} (hα : ∀ (b : β), lipschitz_with Kα fun (a : α) => f a b) (hβ : ∀ (a : α), lipschitz_with Kβ (f a)) : lipschitz_with (Kα + Kβ) (function.uncurry f) := sorry

protected theorem iterate {α : Type u} [emetric_space α] {K : nnreal} {f : α → α} (hf : lipschitz_with K f) (n : ℕ) : lipschitz_with (K ^ n) (nat.iterate f n) := sorry

theorem edist_iterate_succ_le_geometric {α : Type u} [emetric_space α] {K : nnreal} {f : α → α} (hf : lipschitz_with K f) (x : α) (n : ℕ) : edist (nat.iterate f n x) (nat.iterate f (n + 1) x) ≤ edist x (f x) * ↑K ^ n := sorry

protected theorem mul {α : Type u} [emetric_space α] {f : category_theory.End α} {g : category_theory.End α} {Kf : nnreal} {Kg : nnreal} (hf : lipschitz_with Kf f) (hg : lipschitz_with Kg g) : lipschitz_with (Kf * Kg) (f * g) :=
  lipschitz_with.comp hf hg

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
protected theorem list_prod {α : Type u} {ι : Type x} [emetric_space α] (f : ι → category_theory.End α) (K : ι → nnreal) (h : ∀ (i : ι), lipschitz_with (K i) (f i)) (l : List ι) : lipschitz_with (list.prod (list.map K l)) (list.prod (list.map f l)) := sorry

protected theorem pow {α : Type u} [emetric_space α] {f : category_theory.End α} {K : nnreal} (h : lipschitz_with K f) (n : ℕ) : lipschitz_with (K ^ n) (f ^ n) := sorry

protected theorem of_dist_le' {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {K : ℝ} (h : ∀ (x y : α), dist (f x) (f y) ≤ K * dist x y) : lipschitz_with (nnreal.of_real K) f :=
  of_dist_le_mul fun (x y : α) => le_trans (h x y) (mul_le_mul_of_nonneg_right (nnreal.le_coe_of_real K) dist_nonneg)

protected theorem mk_one {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} (h : ∀ (x y : α), dist (f x) (f y) ≤ dist x y) : lipschitz_with 1 f := sorry

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {α : Type u} [metric_space α] {f : α → ℝ} (K : ℝ) (h : ∀ (x y : α), f x ≤ f y + K * dist x y) : lipschitz_with (nnreal.of_real K) f := sorry

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {α : Type u} [metric_space α] {f : α → ℝ} (K : nnreal) (h : ∀ (x y : α), f x ≤ f y + ↑K * dist x y) : lipschitz_with K f := sorry

protected theorem of_le_add {α : Type u} [metric_space α] {f : α → ℝ} (h : ∀ (x y : α), f x ≤ f y + dist x y) : lipschitz_with 1 f := sorry

protected theorem le_add_mul {α : Type u} [metric_space α] {f : α → ℝ} {K : nnreal} (h : lipschitz_with K f) (x : α) (y : α) : f x ≤ f y + ↑K * dist x y :=
  iff.mp sub_le_iff_le_add' (le_trans (le_abs_self (f x - f y)) (dist_le_mul h x y))

protected theorem iff_le_add_mul {α : Type u} [metric_space α] {f : α → ℝ} {K : nnreal} : lipschitz_with K f ↔ ∀ (x y : α), f x ≤ f y + ↑K * dist x y :=
  { mp := lipschitz_with.le_add_mul, mpr := lipschitz_with.of_le_add_mul K }

theorem nndist_le {α : Type u} {β : Type v} [metric_space α] [metric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) (x : α) (y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
  dist_le_mul hf x y

theorem diam_image_le {α : Type u} {β : Type v} [metric_space α] [metric_space β] {K : nnreal} {f : α → β} (hf : lipschitz_with K f) (s : set α) (hs : metric.bounded s) : metric.diam (f '' s) ≤ ↑K * metric.diam s := sorry

protected theorem dist_left {α : Type u} [metric_space α] (y : α) : lipschitz_with 1 fun (x : α) => dist x y := sorry

protected theorem dist_right {α : Type u} [metric_space α] (x : α) : lipschitz_with 1 (dist x) :=
  lipschitz_with.of_le_add fun (y z : α) => dist_triangle_right x y z

protected theorem dist {α : Type u} [metric_space α] : lipschitz_with (bit0 1) (function.uncurry dist) :=
  lipschitz_with.uncurry lipschitz_with.dist_left lipschitz_with.dist_right

theorem dist_iterate_succ_le_geometric {α : Type u} [metric_space α] {K : nnreal} {f : α → α} (hf : lipschitz_with K f) (x : α) (n : ℕ) : dist (nat.iterate f n x) (nat.iterate f (n + 1) x) ≤ dist x (f x) * ↑K ^ n := sorry

end lipschitz_with


namespace lipschitz_on_with


protected theorem uniform_continuous_on {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {s : set α} {f : α → β} (hf : lipschitz_on_with K f s) : uniform_continuous_on f s :=
  iff.mpr uniform_continuous_on_iff_restrict
    (lipschitz_with.uniform_continuous (iff.mp lipschitz_on_with_iff_restrict hf))

protected theorem continuous_on {α : Type u} {β : Type v} [emetric_space α] [emetric_space β] {K : nnreal} {s : set α} {f : α → β} (hf : lipschitz_on_with K f s) : continuous_on f s :=
  uniform_continuous_on.continuous_on (lipschitz_on_with.uniform_continuous_on hf)

end lipschitz_on_with


/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
theorem continuous_at_of_locally_lipschitz {α : Type u} {β : Type v} [metric_space α] [metric_space β] {f : α → β} {x : α} {r : ℝ} (hr : 0 < r) (K : ℝ) (h : ∀ (y : α), dist y x < r → dist (f y) (f x) ≤ K * dist y x) : continuous_at f x := sorry

