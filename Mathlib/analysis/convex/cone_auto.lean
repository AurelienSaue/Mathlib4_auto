/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.linear_pmap
import Mathlib.analysis.convex.basic
import Mathlib.order.zorn
import Mathlib.PostPort

universes u_1 l u_2 u_3 u_4 

namespace Mathlib

/-!
# Convex cones

In a vector space `E` over `ℝ`, we define a convex cone as a subset `s` such that
`a • x + b • y ∈ s` whenever `x, y ∈ s` and `a, b > 0`. We prove that convex cones form
a `complete_lattice`, and define their images (`convex_cone.map`) and preimages
(`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered semimodules.

We also define `convex.to_cone` to be the minimal cone that includes a given convex set.

## Main statements

We prove two extension theorems:

* `riesz_extension`:
  [M. Riesz extension theorem](https://en.wikipedia.org/wiki/M._Riesz_extension_theorem) says that
  if `s` is a convex cone in a real vector space `E`, `p` is a submodule of `E`
  such that `p + s = E`, and `f` is a linear function `p → ℝ` which is
  nonnegative on `p ∩ s`, then there exists a globally defined linear function
  `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.

* `exists_extension_of_le_sublinear`:
  Hahn-Banach theorem: if `N : E → ℝ` is a sublinear map, `f` is a linear map
  defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
  then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
  for all `x`

## Implementation notes

While `convex` is a predicate on sets, `convex_cone` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone

## TODO

* Define the dual cone.
-/

/-!
### Definition of `convex_cone` and basic properties
-/

/-- A convex cone is a subset `s` of a vector space over `ℝ` such that `a • x + b • y ∈ s`
whenever `a, b > 0` and `x, y ∈ s`. -/
structure convex_cone (E : Type u_1) [add_comm_group E] [vector_space ℝ E] where
  carrier : set E
  smul_mem' : ∀ {c : ℝ}, 0 < c → ∀ {x : E}, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ {x : E}, x ∈ carrier → ∀ {y : E}, y ∈ carrier → x + y ∈ carrier

namespace convex_cone


protected instance set.has_coe {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    has_coe (convex_cone E) (set E) :=
  has_coe.mk carrier

protected instance has_mem {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    has_mem E (convex_cone E) :=
  has_mem.mk fun (m : E) (S : convex_cone E) => m ∈ carrier S

protected instance has_le {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    HasLessEq (convex_cone E) :=
  { LessEq := fun (S T : convex_cone E) => carrier S ⊆ carrier T }

protected instance has_lt {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    HasLess (convex_cone E) :=
  { Less := fun (S T : convex_cone E) => carrier S ⊂ carrier T }

@[simp] theorem mem_coe {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E)
    {x : E} : x ∈ ↑S ↔ x ∈ S :=
  iff.rfl

@[simp] theorem mem_mk {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {s : set E}
    {h₁ : ∀ {c : ℝ}, 0 < c → ∀ {x : E}, x ∈ s → c • x ∈ s}
    {h₂ : ∀ {x : E}, x ∈ s → ∀ {y : E}, y ∈ s → x + y ∈ s} {x : E} : x ∈ mk s h₁ h₂ ↔ x ∈ s :=
  iff.rfl

/-- Two `convex_cone`s are equal if the underlying subsets are equal. -/
theorem ext' {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {S : convex_cone E}
    {T : convex_cone E} (h : ↑S = ↑T) : S = T :=
  sorry

/-- Two `convex_cone`s are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {S : convex_cone E}
    {T : convex_cone E} : ↑S = ↑T ↔ S = T :=
  { mp := ext', mpr := fun (h : S = T) => h ▸ rfl }

/-- Two `convex_cone`s are equal if they have the same elements. -/
theorem ext {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {S : convex_cone E}
    {T : convex_cone E} (h : ∀ (x : E), x ∈ S ↔ x ∈ T) : S = T :=
  ext' (set.ext h)

theorem smul_mem {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) {c : ℝ}
    {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S :=
  smul_mem' S hc hx

theorem add_mem {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) {x : E}
    (hx : x ∈ S) {y : E} (hy : y ∈ S) : x + y ∈ S :=
  add_mem' S hx hy

theorem smul_mem_iff {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E)
    {c : ℝ} (hc : 0 < c) {x : E} : c • x ∈ S ↔ x ∈ S :=
  sorry

theorem convex {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) :
    convex ↑S :=
  iff.mpr convex_iff_forall_pos
    fun (x y : E) (hx : x ∈ ↑S) (hy : y ∈ ↑S) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
      (hab : a + b = 1) => add_mem S (smul_mem S ha hx) (smul_mem S hb hy)

protected instance has_inf {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    has_inf (convex_cone E) :=
  has_inf.mk fun (S T : convex_cone E) => mk (↑S ∩ ↑T) sorry sorry

theorem coe_inf {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E)
    (T : convex_cone E) : ↑(S ⊓ T) = ↑S ∩ ↑T :=
  rfl

theorem mem_inf {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E)
    (T : convex_cone E) {x : E} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  iff.rfl

protected instance has_Inf {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    has_Inf (convex_cone E) :=
  has_Inf.mk
    fun (S : set (convex_cone E)) =>
      mk (set.Inter fun (s : convex_cone E) => set.Inter fun (H : s ∈ S) => ↑s) sorry sorry

theorem mem_Inf {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {x : E}
    {S : set (convex_cone E)} : x ∈ Inf S ↔ ∀ (s : convex_cone E), s ∈ S → x ∈ s :=
  set.mem_bInter_iff

protected instance has_bot {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    has_bot (convex_cone E) :=
  has_bot.mk (mk ∅ sorry sorry)

theorem mem_bot {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (x : E) : x ∈ ⊥ = False := rfl

protected instance has_top {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    has_top (convex_cone E) :=
  has_top.mk (mk set.univ sorry sorry)

theorem mem_top {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (x : E) : x ∈ ⊤ :=
  set.mem_univ x

protected instance complete_lattice {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    complete_lattice (convex_cone E) :=
  complete_lattice.mk
    (fun (a b : convex_cone E) => Inf (set_of fun (x : convex_cone E) => a ≤ x ∧ b ≤ x)) LessEq Less
    sorry sorry sorry sorry sorry sorry has_inf.inf sorry sorry sorry ⊤ sorry ⊥ sorry
    (fun (s : set (convex_cone E)) =>
      Inf (set_of fun (T : convex_cone E) => ∀ (S : convex_cone E), S ∈ s → S ≤ T))
    Inf sorry sorry sorry sorry

protected instance inhabited {E : Type u_1} [add_comm_group E] [vector_space ℝ E] :
    Inhabited (convex_cone E) :=
  { default := ⊥ }

/-- The image of a convex cone under an `ℝ`-linear map is a convex cone. -/
def map {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {F : Type u_2} [add_comm_group F]
    [vector_space ℝ F] (f : linear_map ℝ E F) (S : convex_cone E) : convex_cone F :=
  mk (⇑f '' ↑S) sorry sorry

theorem map_map {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {F : Type u_2}
    [add_comm_group F] [vector_space ℝ F] {G : Type u_3} [add_comm_group G] [vector_space ℝ G]
    (g : linear_map ℝ F G) (f : linear_map ℝ E F) (S : convex_cone E) :
    map g (map f S) = map (linear_map.comp g f) S :=
  ext' (set.image_image ⇑g ⇑f ↑S)

@[simp] theorem map_id {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) :
    map linear_map.id S = S :=
  ext' (set.image_id ↑S)

/-- The preimage of a convex cone under an `ℝ`-linear map is a convex cone. -/
def comap {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {F : Type u_2} [add_comm_group F]
    [vector_space ℝ F] (f : linear_map ℝ E F) (S : convex_cone F) : convex_cone E :=
  mk (⇑f ⁻¹' ↑S) sorry sorry

@[simp] theorem comap_id {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) :
    comap linear_map.id S = S :=
  ext' set.preimage_id

theorem comap_comap {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {F : Type u_2}
    [add_comm_group F] [vector_space ℝ F] {G : Type u_3} [add_comm_group G] [vector_space ℝ G]
    (g : linear_map ℝ F G) (f : linear_map ℝ E F) (S : convex_cone G) :
    comap f (comap g S) = comap (linear_map.comp g f) S :=
  ext' (Eq.symm set.preimage_comp)

@[simp] theorem mem_comap {E : Type u_1} [add_comm_group E] [vector_space ℝ E] {F : Type u_2}
    [add_comm_group F] [vector_space ℝ F] {f : linear_map ℝ E F} {S : convex_cone F} {x : E} :
    x ∈ comap f S ↔ coe_fn f x ∈ S :=
  iff.rfl

/--
Constructs an ordered semimodule given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_ordered_semimodule {M : Type u_1} [ordered_add_comm_group M] [semimodule ℝ M]
    (S : convex_cone M) (h : ∀ (x y : M), x ≤ y ↔ y - x ∈ S) : ordered_semimodule ℝ M :=
  sorry

/-! ### Convex cones with extra properties -/

/-- A convex cone is pointed if it includes 0. -/
def pointed {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) := 0 ∈ S

/-- A convex cone is blunt if it doesn't include 0. -/
def blunt {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) := ¬0 ∈ S

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def flat {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) :=
  ∃ (x : E), ∃ (H : x ∈ S), x ≠ 0 ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def salient {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) :=
  ∀ (x : E), x ∈ S → x ≠ 0 → ¬-x ∈ S

theorem pointed_iff_not_blunt {E : Type u_1} [add_comm_group E] [vector_space ℝ E]
    (S : convex_cone E) : pointed S ↔ ¬blunt S :=
  { mp := fun (h₁ : pointed S) (h₂ : blunt S) => h₂ h₁,
    mpr := fun (h : ¬blunt S) => iff.mp not_not h }

theorem salient_iff_not_flat {E : Type u_1} [add_comm_group E] [vector_space ℝ E]
    (S : convex_cone E) : salient S ↔ ¬flat S :=
  sorry

/-- A blunt cone (one not containing 0) is always salient. -/
theorem salient_of_blunt {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E) :
    blunt S → salient S :=
  sorry

/-- A pointed convex cone defines a preorder. -/
def to_preorder {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E)
    (h₁ : pointed S) : preorder E :=
  preorder.mk (fun (x y : E) => y - x ∈ S) (fun (a b : E) => b - a ∈ S ∧ ¬a - b ∈ S) sorry sorry

/-- A pointed and salient cone defines a partial order. -/
def to_partial_order {E : Type u_1} [add_comm_group E] [vector_space ℝ E] (S : convex_cone E)
    (h₁ : pointed S) (h₂ : salient S) : partial_order E :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def to_ordered_add_comm_group {E : Type u_1} [add_comm_group E] [vector_space ℝ E]
    (S : convex_cone E) (h₁ : pointed S) (h₂ : salient S) : ordered_add_comm_group E :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry
    add_comm_group.neg add_comm_group.sub sorry sorry partial_order.le partial_order.lt sorry sorry
    sorry sorry

/-! ### Positive cone of an ordered semimodule -/

/--
The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
semimodule.
-/
def positive_cone (M : Type u_4) [ordered_add_comm_group M] [semimodule ℝ M]
    [ordered_semimodule ℝ M