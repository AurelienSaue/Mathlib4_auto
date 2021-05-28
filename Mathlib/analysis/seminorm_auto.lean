/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.pointwise
import Mathlib.analysis.normed_space.basic
import PostPort

universes u_1 u_2 l 

namespace Mathlib

/-!
# Seminorms and Local Convexity

This file introduces the following notions, defined for a vector space
over a normed field:

- the subset properties of being `absorbent` and `balanced`,

- a `seminorm`, a function to the reals that is positive-semidefinite,
  absolutely homogeneous, and subadditive.

We prove related properties.

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

## References
* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]
-/

/-!
### Subset Properties

Absorbent and balanced sets in a vector space over a
nondiscrete normed field.
-/

/-- A set `A` absorbs another set `B` if `B` is contained in scaling
`A` by elements of sufficiently large norms. -/
def absorbs (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (A : set E) (B : set E)  :=
  ∃ (r : ℝ), ∃ (H : r > 0), ∀ (a : 𝕜), r ≤ norm a → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (A : set E)  :=
  ∀ (x : E), ∃ (r : ℝ), ∃ (H : r > 0), ∀ (a : 𝕜), r ≤ norm a → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm no greater than one. -/
def balanced (𝕜 : Type u_1) [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (A : set E)  :=
  ∀ (a : 𝕜), norm a ≤ 1 → a • A ⊆ A

/-- A balanced set absorbs itself. -/
theorem balanced.absorbs_self {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] {A : set E} (hA : balanced 𝕜 A) : absorbs 𝕜 A A := sorry

/-!
Properties of balanced and absorbing sets in a topological vector space:
-/

/-- Every neighbourhood of the origin is absorbent. -/
theorem absorbent_nhds_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] {A : set E} [topological_space E] [topological_vector_space 𝕜 E] (hA : A ∈ nhds 0) : absorbent 𝕜 A := sorry

/-- The union of `{0}` with the interior of a balanced set
    is balanced. -/
theorem balanced_zero_union_interior {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] {A : set E} [topological_space E] [topological_vector_space 𝕜 E] (hA : balanced 𝕜 A) : balanced 𝕜 (singleton 0 ∪ interior A) := sorry

/-- The interior of a balanced set is balanced if it contains the origin. -/
theorem balanced.interior {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] {A : set E} [topological_space E] [topological_vector_space 𝕜 E] (hA : balanced 𝕜 A) (h : 0 ∈ interior A) : balanced 𝕜 (interior A) := sorry

/-- The closure of a balanced set is balanced. -/
theorem balanced.closure {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] {A : set E} [topological_space E] [topological_vector_space 𝕜 E] (hA : balanced 𝕜 A) : balanced 𝕜 (closure A) := sorry

/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (𝕜 : Type u_1) (E : Type u_2) [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E] 
where
  to_fun : E → ℝ
  smul' : ∀ (a : 𝕜) (x : E), to_fun (a • x) = norm a * to_fun x
  triangle' : ∀ (x y : E), to_fun (x + y) ≤ to_fun x + to_fun y

protected instance seminorm.inhabited {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] : Inhabited (seminorm 𝕜 E) :=
  { default := seminorm.mk (fun (_x : E) => 0) sorry sorry }

protected instance seminorm.has_coe_to_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] : has_coe_to_fun (seminorm 𝕜 E) :=
  has_coe_to_fun.mk (fun (p : seminorm 𝕜 E) => E → ℝ) fun (p : seminorm 𝕜 E) => seminorm.to_fun p

namespace seminorm


protected theorem smul {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (c : 𝕜) (x : E) : coe_fn p (c • x) = norm c * coe_fn p x :=
  smul' p c x

protected theorem triangle {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (x : E) (y : E) : coe_fn p (x + y) ≤ coe_fn p x + coe_fn p y :=
  triangle' p x y

@[simp] protected theorem zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) : coe_fn p 0 = 0 := sorry

@[simp] protected theorem neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (x : E) : coe_fn p (-x) = coe_fn p x := sorry

theorem nonneg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (x : E) : 0 ≤ coe_fn p x := sorry

theorem sub_rev {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (x : E) (y : E) : coe_fn p (x - y) = coe_fn p (y - x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn p (x - y) = coe_fn p (y - x))) (Eq.symm (neg_sub y x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn p (-(y - x)) = coe_fn p (y - x))) (seminorm.neg p (y - x))))
      (Eq.refl (coe_fn p (y - x))))

/-- The ball of radius `r` at `x` with respect to seminorm `p`
    is the set of elements `y` with `p (y - x) < `r`. -/
def ball {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (x : E) (r : ℝ) : set E :=
  set_of fun (y : E) => coe_fn p (y - x) < r

theorem mem_ball {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (x : E) (y : E) (r : ℝ) : y ∈ ball p x r ↔ coe_fn p (y - x) < r :=
  iff.rfl

theorem mem_ball_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (y : E) (r : ℝ) : y ∈ ball p 0 r ↔ coe_fn p y < r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (y ∈ ball p 0 r ↔ coe_fn p y < r)) (propext (mem_ball p 0 y r))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn p (y - 0) < r ↔ coe_fn p y < r)) (sub_zero y))) (iff.refl (coe_fn p y < r)))

theorem ball_zero_eq {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (r : ℝ) : ball p 0 r = set_of fun (y : E) => coe_fn p y < r := sorry

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [add_comm_group E] [vector_space 𝕜 E] (p : seminorm 𝕜 E) (r : ℝ) : balanced 𝕜 (ball p 0 r) := sorry

