/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Gluing metric spaces
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.metric_space.isometry
import Mathlib.topology.metric_space.premetric_space
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  γ ---> α
  |
  |Ψ
  v
  β
```
where `hΦ : isometry Φ` and `hΨ : isometry Ψ`.
We want to complete the square by a space `glue_space hΦ hΨ` and two isometries
`to_glue_l hΦ hΨ` and `to_glue_r hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `α ⊕ β`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are ε-close. If `ε > 0`, this yields a metric
space structure on `α ⊕ β`, without the need to take a quotient. In particular, when `α` and `β` are
inhabited, this gives a natural metric space structure on `α ⊕ β`, where the basepoints are at
distance 1, say, and the distances between other points are obtained by going through the two
basepoints.

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/

namespace metric


/-- Define a predistance on α ⊕ β, for which Φ p and Ψ p are at distance ε -/
def glue_dist {α : Type u} {β : Type v} {γ : Type w} [metric_space α] [metric_space β] (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) : α ⊕ β → α ⊕ β → ℝ :=
  sorry

theorem glue_dist_glued_points {α : Type u} {β : Type v} {γ : Type w} [metric_space α] [metric_space β] [Nonempty γ] (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) (p : γ) : glue_dist Φ Ψ ε (sum.inl (Φ p)) (sum.inr (Ψ p)) = ε := sorry

/-- Given two maps Φ and Ψ intro metric spaces α and β such that the distances between Φ p and Φ q,
and between Ψ p and Ψ q, coincide up to 2 ε where ε > 0, one can almost glue the two spaces α
and β along the images of Φ and Ψ, so that Φ p and Ψ p are at distance ε. -/
def glue_metric_approx {α : Type u} {β : Type v} {γ : Type w} [metric_space α] [metric_space β] [Nonempty γ] (Φ : γ → α) (Ψ : γ → β) (ε : ℝ) (ε0 : 0 < ε) (H : ∀ (p q : γ), abs (dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)) ≤ bit0 1 * ε) : metric_space (α ⊕ β) :=
  metric_space.mk (glue_dist_self Φ Ψ ε) (glue_eq_of_dist_eq_zero Φ Ψ ε ε0) (glue_dist_comm Φ Ψ ε)
    (glue_dist_triangle Φ Ψ ε H) (fun (x y : α ⊕ β) => ennreal.of_real (glue_dist Φ Ψ ε x y))
    (uniform_space_of_dist (glue_dist Φ Ψ ε) (glue_dist_self Φ Ψ ε) (glue_dist_comm Φ Ψ ε) (glue_dist_triangle Φ Ψ ε H))

/- A particular case of the previous construction is when one uses basepoints in α and β and one
glues only along the basepoints, putting them at distance 1. We give a direct definition of
the distance, without infi, as it is easier to use in applications, and show that it is equal to
the gluing distance defined above to take advantage of the lemmas we have already proved. -/

/- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam α + diam β + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/

def sum.dist {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] : α ⊕ β → α ⊕ β → ℝ :=
  sorry

theorem sum.dist_eq_glue_dist {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] {p : α ⊕ β} {q : α ⊕ β} : sum.dist p q = glue_dist (fun (_x : Unit) => Inhabited.default) (fun (_x : Unit) => Inhabited.default) 1 p q := sorry

theorem sum.one_dist_le {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] {x : α} {y : β} : 1 ≤ sum.dist (sum.inl x) (sum.inr y) :=
  le_trans (le_add_of_nonneg_right dist_nonneg)
    (add_le_add_right (le_add_of_nonneg_left dist_nonneg) (dist Inhabited.default y))

theorem sum.one_dist_le' {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] {x : α} {y : β} : 1 ≤ sum.dist (sum.inr y) (sum.inl x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ sum.dist (sum.inr y) (sum.inl x))) (sum.dist_comm (sum.inr y) (sum.inl x))))
    sum.one_dist_le

/-- The distance on the disjoint union indeed defines a metric space. All the distance properties
follow from our choice of the distance. The harder work is to show that the uniform structure
defined by the distance coincides with the disjoint union uniform structure. -/
def metric_space_sum {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] : metric_space (α ⊕ β) :=
  metric_space.mk sorry sorry sum.dist_comm sorry (fun (x y : α ⊕ β) => ennreal.of_real (sum.dist x y)) sum.uniform_space

theorem sum.dist_eq {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] {x : α ⊕ β} {y : α ⊕ β} : dist x y = sum.dist x y :=
  rfl

/-- The left injection of a space in a disjoint union in an isometry -/
theorem isometry_on_inl {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] : isometry sum.inl :=
  iff.mpr isometry_emetric_iff_metric fun (x y : α) => rfl

/-- The right injection of a space in a disjoint union in an isometry -/
theorem isometry_on_inr {α : Type u} {β : Type v} [metric_space α] [metric_space β] [Inhabited α] [Inhabited β] : isometry sum.inr :=
  iff.mpr isometry_emetric_iff_metric fun (x y : β) => rfl

/- Exact gluing of two metric spaces along isometric subsets. -/

def glue_premetric {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) : premetric_space (α ⊕ β) :=
  premetric_space.mk sorry sorry sorry

def glue_space {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ)  :=
  premetric.metric_quot (α ⊕ β)

protected instance metric_space_glue_space {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) : metric_space (glue_space hΦ hΨ) :=
  premetric.metric_space_quot

def to_glue_l {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) (x : α) : glue_space hΦ hΨ :=
  quotient.mk (sum.inl x)

def to_glue_r {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) (y : β) : glue_space hΦ hΨ :=
  quotient.mk (sum.inr y)

protected instance inhabited_left {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) [Inhabited α] : Inhabited (glue_space hΦ hΨ) :=
  { default := to_glue_l hΦ hΨ Inhabited.default }

protected instance inhabited_right {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) [Inhabited β] : Inhabited (glue_space hΦ hΨ) :=
  { default := to_glue_r hΦ hΨ Inhabited.default }

theorem to_glue_commute {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) : to_glue_l hΦ hΨ ∘ Φ = to_glue_r hΦ hΨ ∘ Ψ := sorry

theorem to_glue_l_isometry {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) : isometry (to_glue_l hΦ hΨ) :=
  iff.mpr isometry_emetric_iff_metric fun (_x _x_1 : α) => rfl

theorem to_glue_r_isometry {α : Type u} {β : Type v} {γ : Type w} [Nonempty γ] [metric_space γ] [metric_space α] [metric_space β] {Φ : γ → α} {Ψ : γ → β} (hΦ : isometry Φ) (hΨ : isometry Ψ) : isometry (to_glue_r hΦ hΨ) :=
  iff.mpr isometry_emetric_iff_metric fun (_x _x_1 : β) => rfl

/- In this section, we define the inductive limit of
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
where the X n are metric spaces and f n isometric embeddings. We do it by defining a premetric
space structure on Σn, X n, where the predistance dist x y is obtained by pushing x and y in a
common X k using composition by the f n, and taking the distance there. This does not depend on
the choice of k as the f n are isometries. The metric space associated to this premetric space
is the desired inductive limit.-/

/-- Predistance on the disjoint union Σn, X n. -/
def inductive_limit_dist {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] (f : (n : ℕ) → X n → X (n + 1)) (x : sigma fun (n : ℕ) => X n) (y : sigma fun (n : ℕ) => X n) : ℝ :=
  dist (nat.le_rec_on sorry f (sigma.snd x)) (nat.le_rec_on sorry f (sigma.snd y))

/-- The predistance on the disjoint union Σn, X n can be computed in any X k for large enough k.-/
theorem inductive_limit_dist_eq_dist {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) (x : sigma fun (n : ℕ) => X n) (y : sigma fun (n : ℕ) => X n) (m : ℕ) (hx : sigma.fst x ≤ m) (hy : sigma.fst y ≤ m) : inductive_limit_dist f x y = dist (nat.le_rec_on hx f (sigma.snd x)) (nat.le_rec_on hy f (sigma.snd y)) := sorry

/-- Premetric space structure on Σn, X n.-/
def inductive_premetric {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) : premetric_space (sigma fun (n : ℕ) => X n) :=
  premetric_space.mk sorry sorry sorry

/-- The type giving the inductive limit in a metric space context. -/
def inductive_limit {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n))  :=
  premetric.metric_quot (sigma fun (n : ℕ) => X n)

/-- Metric space structure on the inductive limit. -/
protected instance metric_space_inductive_limit {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) : metric_space (inductive_limit I) :=
  premetric.metric_space_quot

/-- Mapping each `X n` to the inductive limit. -/
def to_inductive_limit {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) (n : ℕ) (x : X n) : inductive_limit I :=
  quotient.mk (sigma.mk n x)

protected instance inductive_limit.inhabited {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) [Inhabited (X 0)] : Inhabited (inductive_limit I) :=
  { default := to_inductive_limit I 0 Inhabited.default }

/-- The map `to_inductive_limit n` mapping `X n` to the inductive limit is an isometry. -/
theorem to_inductive_limit_isometry {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) (n : ℕ) : isometry (to_inductive_limit I n) := sorry

/-- The maps `to_inductive_limit n` are compatible with the maps `f n`. -/
theorem to_inductive_limit_commute {X : ℕ → Type u} [(n : ℕ) → metric_space (X n)] {f : (n : ℕ) → X n → X (n + 1)} (I : ∀ (n : ℕ), isometry (f n)) (n : ℕ) : to_inductive_limit I (Nat.succ n) ∘ f n = to_inductive_limit I n := sorry

