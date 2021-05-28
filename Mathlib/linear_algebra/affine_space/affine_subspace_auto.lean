/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.affine_space.basic
import Mathlib.linear_algebra.tensor_product
import Mathlib.data.set.intervals.unordered_interval
import PostPort

universes u_1 u_2 u_3 l u_4 

namespace Mathlib

/-!
# Affine spaces

This file defines affine subspaces (over modules) and the affine span of a set of points.

## Main definitions

* `affine_subspace k P` is the type of affine subspaces.  Unlike
  affine spaces, affine subspaces are allowed to be empty, and lemmas
  that do not apply to empty affine subspaces have `nonempty`
  hypotheses.  There is a `complete_lattice` structure on affine
  subspaces.
* `affine_subspace.direction` gives the `submodule` spanned by the
  pairwise differences of points in an `affine_subspace`.  There are
  various lemmas relating to the set of vectors in the `direction`,
  and relating the lattice structure on affine subspaces to that on
  their directions.
* `affine_span` gives the affine subspace spanned by a set of points,
  with `vector_span` giving its direction.  `affine_span` is defined
  in terms of `span_points`, which gives an explicit description of
  the points contained in the affine span; `span_points` itself should
  generally only be used when that description is required, with
  `affine_span` being the main definition for other purposes.  Two
  other descriptions of the affine span are proved equivalent: it is
  the `Inf` of affine subspaces containing the points, and (if
  `[nontrivial k]`) it contains exactly those points that are affine
  combinations of points in the given set.

## Implementation notes

`out_param` is used in the definiton of `add_torsor V P` to make `V` an implicit argument (deduced
from `P`) in most cases; `include V` is needed in many cases for `V`, and type classes using it, to
be added as implicit arguments to individual lemmas.  As for modules, `k` is an explicit argument
rather than implied by `P` or `V`.

This file only provides purely algebraic definitions and results.
Those depending on analysis or topology are defined elsewhere; see
`analysis.normed_space.add_torsor` and `topology.algebra.affine`.

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space
-/

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vector_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : submodule k V :=
  submodule.span k (s -ᵥ s)

/-- The definition of `vector_span`, for rewriting. -/
theorem vector_span_def (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : vector_span k s = submodule.span k (s -ᵥ s) :=
  rfl

/-- `vector_span` is monotone. -/
theorem vector_span_mono (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s₁ : set P} {s₂ : set P} (h : s₁ ⊆ s₂) : vector_span k s₁ ≤ vector_span k s₂ :=
  submodule.span_mono (set.vsub_self_mono h)

/-- The `vector_span` of the empty set is `⊥`. -/
@[simp] theorem vector_span_empty (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P] : vector_span k ∅ = ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (vector_span k ∅ = ⊥)) (vector_span_def k ∅)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (submodule.span k (∅ -ᵥ ∅) = ⊥)) (set.vsub_empty ∅)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (submodule.span k ∅ = ⊥)) submodule.span_empty)) (Eq.refl ⊥)))

/-- The `vector_span` of a single point is `⊥`. -/
@[simp] theorem vector_span_singleton (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) : vector_span k (singleton p) = ⊥ := sorry

/-- The `s -ᵥ s` lies within the `vector_span k s`. -/
theorem vsub_set_subset_vector_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : s -ᵥ s ⊆ ↑(vector_span k s) :=
  submodule.subset_span

/-- Each pairwise difference is in the `vector_span`. -/
theorem vsub_mem_vector_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p1 : P} {p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) : p1 -ᵥ p2 ∈ vector_span k s :=
  vsub_set_subset_vector_span k s (set.vsub_mem_vsub hp1 hp2)

/-- The points in the affine span of a (possibly empty) set of
points. Use `affine_span` instead to get an `affine_subspace k P`. -/
def span_points (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : set P :=
  set_of fun (p : P) => ∃ (p1 : P), ∃ (H : p1 ∈ s), ∃ (v : V), ∃ (H : v ∈ vector_span k s), p = v +ᵥ p1

/-- A point in a set is in its affine span. -/
theorem mem_span_points (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (s : set P) : p ∈ s → p ∈ span_points k s := sorry

/-- A set is contained in its `span_points`. -/
theorem subset_span_points (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : s ⊆ span_points k s :=
  fun (p : P) => mem_span_points k p s

/-- The `span_points` of a set is nonempty if and only if that set
is. -/
@[simp] theorem span_points_nonempty (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : set.nonempty (span_points k s) ↔ set.nonempty s := sorry

/-- Adding a point in the affine span and a vector in the spanning
submodule produces a point in the affine span. -/
theorem vadd_mem_span_points_of_mem_span_points_of_mem_vector_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p : P} {v : V} (hp : p ∈ span_points k s) (hv : v ∈ vector_span k s) : v +ᵥ p ∈ span_points k s := sorry

/-- Subtracting two points in the affine span produces a vector in the
spanning submodule. -/
theorem vsub_mem_vector_span_of_mem_span_points_of_mem_span_points (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p1 : P} {p2 : P} (hp1 : p1 ∈ span_points k s) (hp2 : p2 ∈ span_points k s) : p1 -ᵥ p2 ∈ vector_span k s := sorry

/-- An `affine_subspace k P` is a subset of an `affine_space V P`
that, if not empty, has an affine space structure induced by a
corresponding subspace of the `module k V`. -/
structure affine_subspace (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P] 
where
  carrier : set P
  smul_vsub_vadd_mem : ∀ (c : k) {p1 p2 p3 : P}, p1 ∈ carrier → p2 ∈ carrier → p3 ∈ carrier → c • (p1 -ᵥ p2) +ᵥ p3 ∈ carrier

namespace submodule


/-- Reinterpret `p : submodule k V` as an `affine_subspace k V`. -/
def to_affine_subspace {k : Type u_1} {V : Type u_2} [ring k] [add_comm_group V] [module k V] (p : submodule k V) : affine_subspace k V :=
  affine_subspace.mk ↑p sorry

end submodule


namespace affine_subspace


protected instance set.has_coe (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P] : has_coe (affine_subspace k P) (set P) :=
  has_coe.mk carrier

protected instance has_mem (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P] : has_mem P (affine_subspace k P) :=
  has_mem.mk fun (p : P) (s : affine_subspace k P) => p ∈ ↑s

/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp] theorem mem_coe (k : Type u_1) {V : Type u_2} (P : Type u_3) [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (s : affine_subspace k P) : p ∈ ↑s ↔ p ∈ s :=
  iff.rfl

/-- The direction of an affine subspace is the submodule spanned by
the pairwise differences of points.  (Except in the case of an empty
affine subspace, where the direction is the zero submodule, every
vector in the direction is the difference of two points in the affine
subspace.) -/
def direction {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : affine_subspace k P) : submodule k V :=
  vector_span k ↑s

/-- The direction equals the `vector_span`. -/
theorem direction_eq_vector_span {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : affine_subspace k P) : direction s = vector_span k ↑s :=
  rfl

/-- Alternative definition of the direction when the affine subspace
is nonempty.  This is defined so that the order on submodules (as used
in the definition of `submodule.span`) can be used in the proof of
`coe_direction_eq_vsub_set`, and is not intended to be used beyond
that proof. -/
def direction_of_nonempty {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} (h : set.nonempty ↑s) : submodule k V :=
  submodule.mk (↑s -ᵥ ↑s) sorry sorry sorry

/-- `direction_of_nonempty` gives the same submodule as
`direction`. -/
theorem direction_of_nonempty_eq_direction {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} (h : set.nonempty ↑s) : direction_of_nonempty h = direction s :=
  le_antisymm (vsub_set_subset_vector_span k ↑s) (iff.mpr submodule.span_le set.subset.rfl)

/-- The set of vectors in the direction of a nonempty affine subspace
is given by `vsub_set`. -/
theorem coe_direction_eq_vsub_set {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} (h : set.nonempty ↑s) : ↑(direction s) = ↑s -ᵥ ↑s :=
  direction_of_nonempty_eq_direction h ▸ rfl

/-- A vector is in the direction of a nonempty affine subspace if and
only if it is the subtraction of two vectors in the subspace. -/
theorem mem_direction_iff_eq_vsub {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} (h : set.nonempty ↑s) (v : V) : v ∈ direction s ↔ ∃ (p1 : P), ∃ (H : p1 ∈ s), ∃ (p2 : P), ∃ (H : p2 ∈ s), v = p1 -ᵥ p2 := sorry

/-- Adding a vector in the direction to a point in the subspace
produces a point in the subspace. -/
theorem vadd_mem_of_mem_direction {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {v : V} (hv : v ∈ direction s) {p : P} (hp : p ∈ s) : v +ᵥ p ∈ s := sorry

/-- Subtracting two points in the subspace produces a vector in the
direction. -/
theorem vsub_mem_direction {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p1 : P} {p2 : P} (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) : p1 -ᵥ p2 ∈ direction s :=
  vsub_mem_vector_span k hp1 hp2

/-- Adding a vector to a point in a subspace produces a point in the
subspace if and only if the vector is in the direction. -/
theorem vadd_mem_iff_mem_direction {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} (v : V) {p : P} (hp : p ∈ s) : v +ᵥ p ∈ s ↔ v ∈ direction s := sorry

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
right. -/
theorem coe_direction_eq_vsub_set_right {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) : ↑(direction s) = (fun (_x : P) => _x -ᵥ p) '' ↑s := sorry

/-- Given a point in an affine subspace, the set of vectors in its
direction equals the set of vectors subtracting that point on the
left. -/
theorem coe_direction_eq_vsub_set_left {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) : ↑(direction s) = has_vsub.vsub p '' ↑s := sorry

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the right. -/
theorem mem_direction_iff_eq_vsub_right {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) (v : V) : v ∈ direction s ↔ ∃ (p2 : P), ∃ (H : p2 ∈ s), v = p2 -ᵥ p := sorry

/-- Given a point in an affine subspace, a vector is in its direction
if and only if it results from subtracting that point on the left. -/
theorem mem_direction_iff_eq_vsub_left {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) (v : V) : v ∈ direction s ↔ ∃ (p2 : P), ∃ (H : p2 ∈ s), v = p -ᵥ p2 := sorry

/-- Given a point in an affine subspace, a result of subtracting that
point on the right is in the direction if and only if the other point
is in the subspace. -/
theorem vsub_right_mem_direction_iff_mem {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) (p2 : P) : p2 -ᵥ p ∈ direction s ↔ p2 ∈ s := sorry

/-- Given a point in an affine subspace, a result of subtracting that
point on the left is in the direction if and only if the other point
is in the subspace. -/
theorem vsub_left_mem_direction_iff_mem {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) (p2 : P) : p -ᵥ p2 ∈ direction s ↔ p2 ∈ s := sorry

/-- Two affine subspaces are equal if they have the same points. -/
theorem ext {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h : ↑s1 = ↑s2) : s1 = s2 := sorry

/-- Two affine subspaces with the same direction and nonempty
intersection are equal. -/
theorem ext_of_direction_eq {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (hd : direction s1 = direction s2) (hn : set.nonempty (↑s1 ∩ ↑s2)) : s1 = s2 := sorry

protected instance to_add_torsor {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : affine_subspace k P) [Nonempty ↥s] : add_torsor ↥(direction s) ↥s :=
  add_torsor.mk (fun (a : ↥(direction s)) (b : ↥s) => { val := ↑a +ᵥ ↑b, property := sorry }) sorry sorry
    (fun (a b : ↥s) => { val := ↑a -ᵥ ↑b, property := sorry }) sorry sorry

@[simp] theorem coe_vsub {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : affine_subspace k P) [Nonempty ↥s] (a : ↥s) (b : ↥s) : ↑(a -ᵥ b) = ↑a -ᵥ ↑b :=
  rfl

@[simp] theorem coe_vadd {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : affine_subspace k P) [Nonempty ↥s] (a : ↥(direction s)) (b : ↥s) : ↑(a +ᵥ b) = ↑a +ᵥ ↑b :=
  rfl

/-- Two affine subspaces with nonempty intersection are equal if and
only if their directions are equal. -/
theorem eq_iff_direction_eq_of_mem {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s₁ : affine_subspace k P} {s₂ : affine_subspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) : s₁ = s₂ ↔ direction s₁ = direction s₂ :=
  { mp := fun (h : s₁ = s₂) => h ▸ rfl,
    mpr := fun (h : direction s₁ = direction s₂) => ext_of_direction_eq h (Exists.intro p { left := h₁, right := h₂ }) }

/-- Construct an affine subspace from a point and a direction. -/
def mk' {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (direction : submodule k V) : affine_subspace k P :=
  mk (set_of fun (q : P) => ∃ (v : V), ∃ (H : v ∈ direction), q = v +ᵥ p) sorry

/-- An affine subspace constructed from a point and a direction contains
that point. -/
theorem self_mem_mk' {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (direction : submodule k V) : p ∈ mk' p direction :=
  Exists.intro 0 (Exists.intro (submodule.zero_mem direction) (Eq.symm (zero_vadd V p)))

/-- An affine subspace constructed from a point and a direction contains
the result of adding a vector in that direction to that point. -/
theorem vadd_mem_mk' {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {v : V} (p : P) {direction : submodule k V} (hv : v ∈ direction) : v +ᵥ p ∈ mk' p direction :=
  Exists.intro v (Exists.intro hv rfl)

/-- An affine subspace constructed from a point and a direction is
nonempty. -/
theorem mk'_nonempty {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (direction : submodule k V) : set.nonempty ↑(mk' p direction) :=
  Exists.intro p (self_mem_mk' p direction)

/-- The direction of an affine subspace constructed from a point and a
direction. -/
@[simp] theorem direction_mk' {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (direction : submodule k V) : direction (mk' p direction) = direction := sorry

/-- Constructing an affine subspace from a point in a subspace and
that subspace's direction yields the original subspace. -/
@[simp] theorem mk'_eq {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p : P} (hp : p ∈ s) : mk' p (direction s) = s :=
  ext_of_direction_eq (direction_mk' p (direction s)) (Exists.intro p (set.mem_inter (self_mem_mk' p (direction s)) hp))

/-- If an affine subspace contains a set of points, it contains the
`span_points` of that set. -/
theorem span_points_subset_coe_of_subset_coe {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {s1 : affine_subspace k P} (h : s ⊆ ↑s1) : span_points k s ⊆ ↑s1 := sorry

end affine_subspace


/-- The affine span of a set of points is the smallest affine subspace
containing those points. (Actually defined here in terms of spans in
modules.) -/
def affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : affine_subspace k P :=
  affine_subspace.mk (span_points k s) sorry

/-- The affine span, converted to a set, is `span_points`. -/
@[simp] theorem coe_affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : ↑(affine_span k s) = span_points k s :=
  rfl

/-- A set is contained in its affine span. -/
theorem subset_affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : s ⊆ ↑(affine_span k s) :=
  subset_span_points k s

/-- The direction of the affine span is the `vector_span`. -/
theorem direction_affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : affine_subspace.direction (affine_span k s) = vector_span k s := sorry

/-- A point in a set is in its affine span. -/
theorem mem_affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {p : P} {s : set P} (hp : p ∈ s) : p ∈ affine_span k s :=
  mem_span_points k p s hp

namespace affine_subspace


protected instance complete_lattice {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : complete_lattice (affine_subspace k P) :=
  complete_lattice.mk (fun (s1 s2 : affine_subspace k P) => affine_span k (↑s1 ∪ ↑s2)) partial_order.le partial_order.lt
    sorry sorry sorry sorry sorry sorry (fun (s1 s2 : affine_subspace k P) => mk (↑s1 ∩ ↑s2) sorry) sorry sorry sorry
    (mk set.univ sorry) sorry (mk ∅ sorry) sorry
    (fun (s : set (affine_subspace k P)) =>
      affine_span k (set.Union fun (s' : affine_subspace k P) => set.Union fun (H : s' ∈ s) => ↑s'))
    (fun (s : set (affine_subspace k P)) =>
      mk (set.Inter fun (s' : affine_subspace k P) => set.Inter fun (H : s' ∈ s) => ↑s') sorry)
    sorry sorry sorry sorry

protected instance inhabited {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : Inhabited (affine_subspace k P) :=
  { default := ⊤ }

/-- The `≤` order on subspaces is the same as that on the corresponding
sets. -/
theorem le_def {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : s1 ≤ s2 ↔ ↑s1 ⊆ ↑s2 :=
  iff.rfl

/-- One subspace is less than or equal to another if and only if all
its points are in the second subspace. -/
theorem le_def' {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : s1 ≤ s2 ↔ ∀ (p : P), p ∈ s1 → p ∈ s2 :=
  iff.rfl

/-- The `<` order on subspaces is the same as that on the corresponding
sets. -/
theorem lt_def {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : s1 < s2 ↔ ↑s1 ⊂ ↑s2 :=
  iff.rfl

/-- One subspace is not less than or equal to another if and only if
it has a point not in the second subspace. -/
theorem not_le_iff_exists {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : ¬s1 ≤ s2 ↔ ∃ (p : P), ∃ (H : p ∈ s1), ¬p ∈ s2 :=
  set.not_subset

/-- If a subspace is less than another, there is a point only in the
second. -/
theorem exists_of_lt {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h : s1 < s2) : ∃ (p : P), ∃ (H : p ∈ s2), ¬p ∈ s1 :=
  set.exists_of_ssubset h

/-- A subspace is less than another if and only if it is less than or
equal to the second subspace and there is a point only in the
second. -/
theorem lt_iff_le_and_exists {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : s1 < s2 ↔ s1 ≤ s2 ∧ ∃ (p : P), ∃ (H : p ∈ s2), ¬p ∈ s1 := sorry

/-- If an affine subspace is nonempty and contained in another with
the same direction, they are equal. -/
theorem eq_of_direction_eq_of_nonempty_of_le {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s₁ : affine_subspace k P} {s₂ : affine_subspace k P} (hd : direction s₁ = direction s₂) (hn : set.nonempty ↑s₁) (hle : s₁ ≤ s₂) : s₁ = s₂ := sorry

/-- The affine span is the `Inf` of subspaces containing the given
points. -/
theorem affine_span_eq_Inf (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s : set P) : affine_span k s = Inf (set_of fun (s' : affine_subspace k P) => s ⊆ ↑s') := sorry

/-- The Galois insertion formed by `affine_span` and coercion back to
a set. -/
protected def gi (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : galois_insertion (affine_span k) coe :=
  galois_insertion.mk (fun (s : set P) (_x : ↑(affine_span k s) ≤ s) => affine_span k s) sorry sorry sorry

/-- The span of the empty set is `⊥`. -/
@[simp] theorem span_empty (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : affine_span k ∅ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (affine_subspace.gi k V P))

/-- The span of `univ` is `⊤`. -/
@[simp] theorem span_univ (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : affine_span k set.univ = ⊤ :=
  iff.mpr eq_top_iff (subset_span_points k ↑⊤)

/-- The affine span of a single point, coerced to a set, contains just
that point. -/
@[simp] theorem coe_affine_span_singleton (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (p : P) : ↑(affine_span k (singleton p)) = singleton p := sorry

/-- A point is in the affine span of a single point if and only if
they are equal. -/
@[simp] theorem mem_affine_span_singleton (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (p1 : P) (p2 : P) : p1 ∈ affine_span k (singleton p2) ↔ p1 = p2 := sorry

/-- The span of a union of sets is the sup of their spans. -/
theorem span_union (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s : set P) (t : set P) : affine_span k (s ∪ t) = affine_span k s ⊔ affine_span k t :=
  galois_connection.l_sup (galois_insertion.gc (affine_subspace.gi k V P))

/-- The span of a union of an indexed family of sets is the sup of
their spans. -/
theorem span_Union (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {ι : Type u_4} (s : ι → set P) : affine_span k (set.Union fun (i : ι) => s i) = supr fun (i : ι) => affine_span k (s i) :=
  galois_connection.l_supr (galois_insertion.gc (affine_subspace.gi k V P))

/-- `⊤`, coerced to a set, is the whole set of points. -/
@[simp] theorem top_coe (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : ↑⊤ = set.univ :=
  rfl

/-- All points are in `⊤`. -/
theorem mem_top (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (p : P) : p ∈ ⊤ :=
  set.mem_univ p

/-- The direction of `⊤` is the whole module as a submodule. -/
@[simp] theorem direction_top (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : direction ⊤ = ⊤ := sorry

/-- `⊥`, coerced to a set, is the empty set. -/
@[simp] theorem bot_coe (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : ↑⊥ = ∅ :=
  rfl

/-- No points are in `⊥`. -/
theorem not_mem_bot (k : Type u_1) (V : Type u_2) {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (p : P) : ¬p ∈ ⊥ :=
  set.not_mem_empty p

/-- The direction of `⊥` is the submodule `⊥`. -/
@[simp] theorem direction_bot (k : Type u_1) (V : Type u_2) (P : Type u_3) [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] : direction ⊥ = ⊥ := sorry

/-- A nonempty affine subspace is `⊤` if and only if its direction is
`⊤`. -/
@[simp] theorem direction_eq_top_iff_of_nonempty {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s : affine_subspace k P} (h : set.nonempty ↑s) : direction s = ⊤ ↔ s = ⊤ := sorry

/-- The inf of two affine subspaces, coerced to a set, is the
intersection of the two sets of points. -/
@[simp] theorem inf_coe {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : ↑s1 ⊓ ↑s2 = ↑s1 ∩ ↑s2 :=
  rfl

/-- A point is in the inf of two affine subspaces if and only if it is
in both of them. -/
theorem mem_inf_iff {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (p : P) (s1 : affine_subspace k P) (s2 : affine_subspace k P) : p ∈ s1 ⊓ s2 ↔ p ∈ s1 ∧ p ∈ s2 :=
  iff.rfl

/-- The direction of the inf of two affine subspaces is less than or
equal to the inf of their directions. -/
theorem direction_inf {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : direction (s1 ⊓ s2) ≤ direction s1 ⊓ direction s2 := sorry

/-- If two affine subspaces have a point in common, the direction of
their inf equals the inf of their directions. -/
theorem direction_inf_of_mem {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s₁ : affine_subspace k P} {s₂ : affine_subspace k P} {p : P} (h₁ : p ∈ s₁) (h₂ : p ∈ s₂) : direction (s₁ ⊓ s₂) = direction s₁ ⊓ direction s₂ := sorry

/-- If two affine subspaces have a point in their inf, the direction
of their inf equals the inf of their directions. -/
theorem direction_inf_of_mem_inf {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s₁ : affine_subspace k P} {s₂ : affine_subspace k P} {p : P} (h : p ∈ s₁ ⊓ s₂) : direction (s₁ ⊓ s₂) = direction s₁ ⊓ direction s₂ :=
  direction_inf_of_mem (and.left (iff.mp (mem_inf_iff p s₁ s₂) h)) (and.right (iff.mp (mem_inf_iff p s₁ s₂) h))

/-- If one affine subspace is less than or equal to another, the same
applies to their directions. -/
theorem direction_le {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h : s1 ≤ s2) : direction s1 ≤ direction s2 := sorry

/-- If one nonempty affine subspace is less than another, the same
applies to their directions -/
theorem direction_lt_of_nonempty {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h : s1 < s2) (hn : set.nonempty ↑s1) : direction s1 < direction s2 := sorry

/-- The sup of the directions of two affine subspaces is less than or
equal to the direction of their sup. -/
theorem sup_direction_le {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s1 : affine_subspace k P) (s2 : affine_subspace k P) : direction s1 ⊔ direction s2 ≤ direction (s1 ⊔ s2) := sorry

/-- The sup of the directions of two nonempty affine subspaces with
empty intersection is less than the direction of their sup. -/
theorem sup_direction_lt_of_nonempty_of_inter_empty {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h1 : set.nonempty ↑s1) (h2 : set.nonempty ↑s2) (he : ↑s1 ∩ ↑s2 = ∅) : direction s1 ⊔ direction s2 < direction (s1 ⊔ s2) := sorry

/-- If the directions of two nonempty affine subspaces span the whole
module, they have nonempty intersection. -/
theorem inter_nonempty_of_nonempty_of_sup_direction_eq_top {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h1 : set.nonempty ↑s1) (h2 : set.nonempty ↑s2) (hd : direction s1 ⊔ direction s2 = ⊤) : set.nonempty (↑s1 ∩ ↑s2) := sorry

/-- If the directions of two nonempty affine subspaces are complements
of each other, they intersect in exactly one point. -/
theorem inter_eq_singleton_of_nonempty_of_is_compl {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} (h1 : set.nonempty ↑s1) (h2 : set.nonempty ↑s2) (hd : is_compl (direction s1) (direction s2)) : ∃ (p : P), ↑s1 ∩ ↑s2 = singleton p := sorry

/-- Coercing a subspace to a set then taking the affine span produces
the original subspace. -/
@[simp] theorem affine_span_coe {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [S : add_torsor V P] (s : affine_subspace k P) : affine_span k ↑s = s := sorry

end affine_subspace


/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left. -/
theorem vector_span_eq_span_vsub_set_left (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p : P} (hp : p ∈ s) : vector_span k s = submodule.span k (has_vsub.vsub p '' s) := sorry

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right. -/
theorem vector_span_eq_span_vsub_set_right (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p : P} (hp : p ∈ s) : vector_span k s = submodule.span k ((fun (_x : P) => _x -ᵥ p) '' s) := sorry

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the left, excluding the subtraction of that point from
itself. -/
theorem vector_span_eq_span_vsub_set_left_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p : P} (hp : p ∈ s) : vector_span k s = submodule.span k (has_vsub.vsub p '' (s \ singleton p)) := sorry

/-- The `vector_span` is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from
itself. -/
theorem vector_span_eq_span_vsub_set_right_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} {p : P} (hp : p ∈ s) : vector_span k s = submodule.span k ((fun (_x : P) => _x -ᵥ p) '' (s \ singleton p)) := sorry

/-- The `vector_span` of the image of a function is the span of the
pairwise subtractions with a given point on the left, excluding the
subtraction of that point from itself. -/
theorem vector_span_image_eq_span_vsub_set_left_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) {s : set ι} {i : ι} (hi : i ∈ s) : vector_span k (p '' s) = submodule.span k (has_vsub.vsub (p i) '' (p '' (s \ singleton i))) := sorry

/-- The `vector_span` of the image of a function is the span of the
pairwise subtractions with a given point on the right, excluding the
subtraction of that point from itself. -/
theorem vector_span_image_eq_span_vsub_set_right_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) {s : set ι} {i : ι} (hi : i ∈ s) : vector_span k (p '' s) = submodule.span k ((fun (_x : P) => _x -ᵥ p i) '' (p '' (s \ singleton i))) := sorry

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left. -/
theorem vector_span_range_eq_span_range_vsub_left (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (i0 : ι) : vector_span k (set.range p) = submodule.span k (set.range fun (i : ι) => p i0 -ᵥ p i) := sorry

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right. -/
theorem vector_span_range_eq_span_range_vsub_right (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (i0 : ι) : vector_span k (set.range p) = submodule.span k (set.range fun (i : ι) => p i -ᵥ p i0) := sorry

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the left, excluding the subtraction
of that point from itself. -/
theorem vector_span_range_eq_span_range_vsub_left_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (i₀ : ι) : vector_span k (set.range p) = submodule.span k (set.range fun (i : Subtype fun (x : ι) => x ≠ i₀) => p i₀ -ᵥ p ↑i) := sorry

/-- The `vector_span` of an indexed family is the span of the pairwise
subtractions with a given point on the right, excluding the subtraction
of that point from itself. -/
theorem vector_span_range_eq_span_range_vsub_right_ne (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {ι : Type u_4} (p : ι → P) (i₀ : ι) : vector_span k (set.range p) = submodule.span k (set.range fun (i : Subtype fun (x : ι) => x ≠ i₀) => p ↑i -ᵥ p i₀) := sorry

/-- The affine span of a set is nonempty if and only if that set
is. -/
theorem affine_span_nonempty (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (s : set P) : set.nonempty ↑(affine_span k s) ↔ set.nonempty s :=
  span_points_nonempty k s

/-- The affine span of a nonempty set is nonempty. -/
protected instance affine_span.nonempty (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set P} [Nonempty ↥s] : Nonempty ↥(affine_span k s) :=
  set.nonempty.to_subtype (iff.mpr (affine_span_nonempty k s) (iff.mp nonempty_subtype _inst_5))

/-- Suppose a set of vectors spans `V`.  Then a point `p`, together
with those vectors added to `p`, spans `P`. -/
theorem affine_span_singleton_union_vadd_eq_top_of_span_eq_top {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : set V} (p : P) (h : submodule.span k (set.range coe) = ⊤) : affine_span k (singleton p ∪ (fun (v : V) => v +ᵥ p) '' s) = ⊤ := sorry

/-- `affine_span` is monotone. -/
theorem affine_span_mono (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s₁ : set P} {s₂ : set P} (h : s₁ ⊆ s₂) : affine_span k s₁ ≤ affine_span k s₂ :=
  affine_subspace.span_points_subset_coe_of_subset_coe (set.subset.trans h (subset_affine_span k s₂))

/-- Taking the affine span of a set, adding a point and taking the
span again produces the same results as adding the point to the set
and taking the span. -/
theorem affine_span_insert_affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] (p : P) (ps : set P) : affine_span k (insert p ↑(affine_span k ps)) = affine_span k (insert p ps) := sorry

/-- If a point is in the affine span of a set, adding it to that set
does not change the affine span. -/
theorem affine_span_insert_eq_affine_span (k : Type u_1) {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {p : P} {ps : set P} (h : p ∈ affine_span k ps) : affine_span k (insert p ps) = affine_span k ps := sorry

namespace affine_subspace


/-- The direction of the sup of two nonempty affine subspaces is the
sup of the two directions and of any one difference between points in
the two subspaces. -/
theorem direction_sup {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s1 : affine_subspace k P} {s2 : affine_subspace k P} {p1 : P} {p2 : P} (hp1 : p1 ∈ s1) (hp2 : p2 ∈ s2) : direction (s1 ⊔ s2) = direction s1 ⊔ direction s2 ⊔ submodule.span k (singleton (p2 -ᵥ p1)) := sorry

/-- The direction of the span of the result of adding a point to a
nonempty affine subspace is the sup of the direction of that subspace
and of any one difference between that point and a point in the
subspace. -/
theorem direction_affine_span_insert {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p1 : P} {p2 : P} (hp1 : p1 ∈ s) : direction (affine_span k (insert p2 ↑s)) = submodule.span k (singleton (p2 -ᵥ p1)) ⊔ direction s := sorry

/-- Given a point `p1` in an affine subspace `s`, and a point `p2`, a
point `p` is in the span of `s` with `p2` added if and only if it is a
multiple of `p2 -ᵥ p1` added to a point in `s`. -/
theorem mem_affine_span_insert_iff {k : Type u_1} {V : Type u_2} {P : Type u_3} [ring k] [add_comm_group V] [module k V] [add_torsor V P] {s : affine_subspace k P} {p1 : P} (hp1 : p1 ∈ s) (p2 : P) (p : P) : p ∈ affine_span k (insert p2 ↑s) ↔ ∃ (r : k), ∃ (p0 : P), ∃ (hp0 : p0 ∈ s), p = r • (p2 -ᵥ p1) +ᵥ p0 := sorry

