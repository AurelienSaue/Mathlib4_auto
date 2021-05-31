/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.ord_connected
import Mathlib.data.set.intervals.image_preimage
import Mathlib.data.complex.module
import Mathlib.linear_algebra.affine_space.affine_map
import Mathlib.algebra.module.ordered
import Mathlib.PostPort

universes u u_1 v v' w x u' 

namespace Mathlib

/-!
# Convex sets and functions on real vector spaces

In a real vector space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
* A set `s` is `convex` if for any two points `x y ∈ s` it includes `segment x y`;
* A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
  points `x y ∈ s` the segment joining `(x, f x)` to `(y, f y)` is (non-strictly) above the graph
  of `f`; equivalently, `convex_on f s` means that the epigraph
  `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is a convex set;
* Center mass of a finite set of points with prescribed weights.
* Convex hull of a set `s` is the minimal convex set that includes `s`.
* Standard simplex `std_simplex ι [fintype ι]` is the intersection of the positive quadrant with
  the hyperplane `s.sum = 1` in the space `ι → ℝ`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex, and prove Jensen's inequality.

Note: To define convexity for functions `f : E → β`, we need `β` to be an ordered vector space,
defined using the instance `ordered_semimodule ℝ β`.

## Notations

We use the following local notations:

* `I = Icc (0:ℝ) 1`;
* `[x, y] = segment x y`.

They are defined using `local notation`, so they are not available outside of this file.
-/

/-! ### Segment -/

/-- Segments in a vector space. -/
def segment {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : set E :=
  set_of fun (z : E) => ∃ (a : ℝ), ∃ (b : ℝ), ∃ (ha : 0 ≤ a), ∃ (hb : 0 ≤ b), ∃ (hab : a + b = 1), a • x + b • y = z

theorem segment_symm {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : segment x y = segment y x := sorry

theorem left_mem_segment {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : x ∈ segment x y := sorry

theorem right_mem_segment {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : y ∈ segment x y :=
  segment_symm y x ▸ left_mem_segment y x

theorem segment_same {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) : segment x x = singleton x := sorry

theorem segment_eq_image {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : segment x y = (fun (θ : ℝ) => (1 - θ) • x + θ • y) '' set.Icc 0 1 := sorry

theorem segment_eq_image' {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : segment x y = (fun (θ : ℝ) => x + θ • (y - x)) '' set.Icc 0 1 := sorry

theorem segment_eq_image₂ {E : Type u} [add_comm_group E] [vector_space ℝ E] (x : E) (y : E) : segment x y =
  (fun (p : ℝ × ℝ) => prod.fst p • x + prod.snd p • y) ''
    set_of fun (p : ℝ × ℝ) => 0 ≤ prod.fst p ∧ 0 ≤ prod.snd p ∧ prod.fst p + prod.snd p = 1 := sorry

theorem segment_eq_Icc {a : ℝ} {b : ℝ} (h : a ≤ b) : segment a b = set.Icc a b := sorry

theorem segment_eq_Icc' (a : ℝ) (b : ℝ) : segment a b = set.Icc (min a b) (max a b) := sorry

theorem segment_eq_interval (a : ℝ) (b : ℝ) : segment a b = set.interval a b :=
  segment_eq_Icc' a b

theorem mem_segment_translate {E : Type u} [add_comm_group E] [vector_space ℝ E] (a : E) {x : E} {b : E} {c : E} : a + x ∈ segment (a + b) (a + c) ↔ x ∈ segment b c := sorry

theorem segment_translate_preimage {E : Type u} [add_comm_group E] [vector_space ℝ E] (a : E) (b : E) (c : E) : (fun (x : E) => a + x) ⁻¹' segment (a + b) (a + c) = segment b c :=
  set.ext fun (x : E) => mem_segment_translate a

theorem segment_translate_image {E : Type u} [add_comm_group E] [vector_space ℝ E] (a : E) (b : E) (c : E) : (fun (x : E) => a + x) '' segment b c = segment (a + b) (a + c) :=
  Eq.subst (segment_translate_preimage a b c) (set.image_preimage_eq (segment (a + b) (a + c))) (add_left_surjective a)

/-! ### Convexity of sets -/

/-- Convexity of sets. -/
def convex {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : set E) :=
  ∀ {x y : E}, x ∈ s → y ∈ s → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

theorem convex_iff_forall_pos {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} : convex s ↔ ∀ {x y : E}, x ∈ s → y ∈ s → ∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := sorry

theorem convex_iff_segment_subset {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} : convex s ↔ ∀ {x y : E}, x ∈ s → y ∈ s → segment x y ⊆ s := sorry

theorem convex.segment_subset {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (h : convex s) {x : E} {y : E} (hx : x ∈ s) (hy : y ∈ s) : segment x y ⊆ s :=
  iff.mp convex_iff_segment_subset h x y hx hy

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
theorem convex_iff_pointwise_add_subset {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} : convex s ↔ ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s := sorry

/-- Alternative definition of set convexity, using division. -/
theorem convex_iff_div {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} : convex s ↔
  ∀ {x y : E}, x ∈ s → y ∈ s → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s := sorry

/-! ### Examples of convex sets -/

theorem convex_empty {E : Type u} [add_comm_group E] [vector_space ℝ E] : convex ∅ := sorry

theorem convex_singleton {E : Type u} [add_comm_group E] [vector_space ℝ E] (c : E) : convex (singleton c) := sorry

theorem convex_univ {E : Type u} [add_comm_group E] [vector_space ℝ E] : convex set.univ :=
  fun (_x _x_1 : E) (_x : _x ∈ set.univ) (_x : _x_1 ∈ set.univ) (_x _x_2 : ℝ) (_x_3 : 0 ≤ _x) (_x_4 : 0 ≤ _x_2)
    (_x : _x + _x_2 = 1) => trivial

theorem convex.inter {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : set E} (hs : convex s) (ht : convex t) : convex (s ∩ t) :=
  fun (x y : E) (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) =>
    { left := hs (and.left hx) (and.left hy) ha hb hab, right := ht (and.right hx) (and.right hy) ha hb hab }

theorem convex_sInter {E : Type u} [add_comm_group E] [vector_space ℝ E] {S : set (set E)} (h : ∀ (s : set E), s ∈ S → convex s) : convex (⋂₀S) :=
  fun (x y : E) (hx : x ∈ ⋂₀S) (hy : y ∈ ⋂₀S) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (s : set E)
    (hs : s ∈ S) => h s hs (hx s hs) (hy s hs) ha hb hab

theorem convex_Inter {E : Type u} [add_comm_group E] [vector_space ℝ E] {ι : Sort u_1} {s : ι → set E} (h : ∀ (i : ι), convex (s i)) : convex (set.Inter fun (i : ι) => s i) :=
  Eq.subst (set.sInter_range s) convex_sInter (iff.mpr set.forall_range_iff h)

theorem convex.prod {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set E} {t : set F} (hs : convex s) (ht : convex t) : convex (set.prod s t) := sorry

theorem convex.combo_to_vadd {E : Type u} [add_comm_group E] [vector_space ℝ E] {a : ℝ} {b : ℝ} {x : E} {y : E} (h : a + b = 1) : a • x + b • y = b • (y - x) + x := sorry

/--
Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
theorem convex.combo_affine_apply {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {a : ℝ} {b : ℝ} {x : E} {y : E} {f : affine_map ℝ E F} (h : a + b = 1) : coe_fn f (a • x + b • y) = a • coe_fn f x + b • coe_fn f y := sorry

/-- The preimage of a convex set under an affine map is convex. -/
theorem convex.affine_preimage {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] (f : affine_map ℝ E F) {s : set F} (hs : convex s) : convex (⇑f ⁻¹' s) := sorry

/-- The image of a convex set under an affine map is convex. -/
theorem convex.affine_image {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] (f : affine_map ℝ E F) {s : set E} (hs : convex s) : convex (⇑f '' s) := sorry

theorem convex.linear_image {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set E} (hs : convex s) (f : linear_map ℝ E F) : convex (⇑f '' s) :=
  convex.affine_image (linear_map.to_affine_map f) hs

theorem convex.is_linear_image {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set E} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) : convex (f '' s) :=
  convex.linear_image hs (is_linear_map.mk' f hf)

theorem convex.linear_preimage {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set F} (hs : convex s) (f : linear_map ℝ E F) : convex (⇑f ⁻¹' s) :=
  convex.affine_preimage (linear_map.to_affine_map f) hs

theorem convex.is_linear_preimage {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set F} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) : convex (f ⁻¹' s) :=
  convex.linear_preimage hs (is_linear_map.mk' f hf)

theorem convex.neg {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) : convex ((fun (z : E) => -z) '' s) :=
  convex.is_linear_image hs is_linear_map.is_linear_map_neg

theorem convex.neg_preimage {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) : convex ((fun (z : E) => -z) ⁻¹' s) :=
  convex.is_linear_preimage hs is_linear_map.is_linear_map_neg

theorem convex.smul {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (c : ℝ) (hs : convex s) : convex (c • s) :=
  convex.linear_image hs (coe_fn (linear_map.lsmul ℝ E) c)

theorem convex.smul_preimage {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (c : ℝ) (hs : convex s) : convex ((fun (z : E) => c • z) ⁻¹' s) :=
  convex.linear_preimage hs (coe_fn (linear_map.lsmul ℝ E) c)

theorem convex.add {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : set E} (hs : convex s) (ht : convex t) : convex (s + t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (convex (s + t))) (Eq.symm set.add_image_prod)))
    (convex.is_linear_image (convex.prod hs ht) is_linear_map.is_linear_map_add)

theorem convex.sub {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : set E} (hs : convex s) (ht : convex t) : convex ((fun (x : E × E) => prod.fst x - prod.snd x) '' set.prod s t) :=
  convex.is_linear_image (convex.prod hs ht) is_linear_map.is_linear_map_sub

theorem convex.translate {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) (z : E) : convex ((fun (x : E) => z + x) '' s) :=
  convex.affine_image (affine_map.const ℝ E z +ᵥ affine_map.id ℝ E) hs

/-- The translation of a convex set is also convex. -/
theorem convex.translate_preimage_right {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) (a : E) : convex ((fun (z : E) => a + z) ⁻¹' s) :=
  convex.affine_preimage (affine_map.const ℝ E a +ᵥ affine_map.id ℝ E) hs

/-- The translation of a convex set is also convex. -/
theorem convex.translate_preimage_left {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) (a : E) : convex ((fun (z : E) => z + a) ⁻¹' s) := sorry

theorem convex.affinity {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) (z : E) (c : ℝ) : convex ((fun (x : E) => z + c • x) '' s) :=
  convex.affine_image (affine_map.const ℝ E z +ᵥ c • affine_map.id ℝ E) hs

theorem real.convex_iff_ord_connected {s : set ℝ} : convex s ↔ set.ord_connected s := sorry

theorem convex.ord_connected {s : set ℝ} : convex s → set.ord_connected s :=
  iff.mp real.convex_iff_ord_connected

theorem convex_Iio (r : ℝ) : convex (set.Iio r) :=
  set.ord_connected.convex set.ord_connected_Iio

theorem convex_Ioi (r : ℝ) : convex (set.Ioi r) :=
  set.ord_connected.convex set.ord_connected_Ioi

theorem convex_Iic (r : ℝ) : convex (set.Iic r) :=
  set.ord_connected.convex set.ord_connected_Iic

theorem convex_Ici (r : ℝ) : convex (set.Ici r) :=
  set.ord_connected.convex set.ord_connected_Ici

theorem convex_Ioo (r : ℝ) (s : ℝ) : convex (set.Ioo r s) :=
  set.ord_connected.convex set.ord_connected_Ioo

theorem convex_Ico (r : ℝ) (s : ℝ) : convex (set.Ico r s) :=
  set.ord_connected.convex set.ord_connected_Ico

theorem convex_Ioc (r : ℝ) (s : ℝ) : convex (set.Ioc r s) :=
  set.ord_connected.convex set.ord_connected_Ioc

theorem convex_Icc (r : ℝ) (s : ℝ) : convex (set.Icc r s) :=
  set.ord_connected.convex set.ord_connected_Icc

theorem convex_interval (r : ℝ) (s : ℝ) : convex (set.interval r s) :=
  set.ord_connected.convex set.ord_connected_interval

theorem convex_segment {E : Type u} [add_comm_group E] [vector_space ℝ E] (a : E) (b : E) : convex (segment a b) := sorry

theorem convex_halfspace_lt {E : Type u} [add_comm_group E] [vector_space ℝ E] {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) : convex (set_of fun (w : E) => f w < r) :=
  convex.is_linear_preimage (convex_Iio r) h

theorem convex_halfspace_le {E : Type u} [add_comm_group E] [vector_space ℝ E] {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) : convex (set_of fun (w : E) => f w ≤ r) :=
  convex.is_linear_preimage (convex_Iic r) h

theorem convex_halfspace_gt {E : Type u} [add_comm_group E] [vector_space ℝ E] {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) : convex (set_of fun (w : E) => r < f w) :=
  convex.is_linear_preimage (convex_Ioi r) h

theorem convex_halfspace_ge {E : Type u} [add_comm_group E] [vector_space ℝ E] {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) : convex (set_of fun (w : E) => r ≤ f w) :=
  convex.is_linear_preimage (convex_Ici r) h

theorem convex_hyperplane {E : Type u} [add_comm_group E] [vector_space ℝ E] {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) : convex (set_of fun (w : E) => f w = r) :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (convex (f ⁻¹' set_of fun (p : ℝ) => p = r))) set.set_of_eq_eq_singleton))
      (convex.is_linear_preimage (convex_singleton r) h))

theorem convex_halfspace_re_lt (r : ℝ) : convex (set_of fun (c : ℂ) => complex.re c < r) :=
  convex_halfspace_lt (is_linear_map.mk complex.add_re complex.smul_re) r

theorem convex_halfspace_re_le (r : ℝ) : convex (set_of fun (c : ℂ) => complex.re c ≤ r) :=
  convex_halfspace_le (is_linear_map.mk complex.add_re complex.smul_re) r

theorem convex_halfspace_re_gt (r : ℝ) : convex (set_of fun (c : ℂ) => r < complex.re c) :=
  convex_halfspace_gt (is_linear_map.mk complex.add_re complex.smul_re) r

theorem convex_halfspace_re_lge (r : ℝ) : convex (set_of fun (c : ℂ) => r ≤ complex.re c) :=
  convex_halfspace_ge (is_linear_map.mk complex.add_re complex.smul_re) r

theorem convex_halfspace_im_lt (r : ℝ) : convex (set_of fun (c : ℂ) => complex.im c < r) :=
  convex_halfspace_lt (is_linear_map.mk complex.add_im complex.smul_im) r

theorem convex_halfspace_im_le (r : ℝ) : convex (set_of fun (c : ℂ) => complex.im c ≤ r) :=
  convex_halfspace_le (is_linear_map.mk complex.add_im complex.smul_im) r

theorem convex_halfspace_im_gt (r : ℝ) : convex (set_of fun (c : ℂ) => r < complex.im c) :=
  convex_halfspace_gt (is_linear_map.mk complex.add_im complex.smul_im) r

theorem convex_halfspace_im_lge (r : ℝ) : convex (set_of fun (c : ℂ) => r ≤ complex.im c) :=
  convex_halfspace_ge (is_linear_map.mk complex.add_im complex.smul_im) r

/-! ### Convex combinations in intervals -/

theorem convex.combo_self {α : Type v'} [linear_ordered_field α] (a : α) {x : α} {y : α} (h : x + y = 1) : a = x * a + y * a := sorry

/--
If `x` is in an `Ioo`, it can be expressed as a convex combination of the endpoints.
-/
theorem convex.mem_Ioo {α : Type v'} [linear_ordered_field α] {a : α} {b : α} {x : α} (h : a < b) : x ∈ set.Ioo a b ↔ ∃ (x_a : α), ∃ (x_b : α), 0 < x_a ∧ 0 < x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x := sorry

/-- If `x` is in an `Ioc`, it can be expressed as a convex combination of the endpoints. -/
theorem convex.mem_Ioc {α : Type v'} [linear_ordered_field α] {a : α} {b : α} {x : α} (h : a < b) : x ∈ set.Ioc a b ↔ ∃ (x_a : α), ∃ (x_b : α), 0 ≤ x_a ∧ 0 < x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x := sorry

/-- If `x` is in an `Ico`, it can be expressed as a convex combination of the endpoints. -/
theorem convex.mem_Ico {α : Type v'} [linear_ordered_field α] {a : α} {b : α} {x : α} (h : a < b) : x ∈ set.Ico a b ↔ ∃ (x_a : α), ∃ (x_b : α), 0 < x_a ∧ 0 ≤ x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x := sorry

/-- If `x` is in an `Icc`, it can be expressed as a convex combination of the endpoints. -/
theorem convex.mem_Icc {α : Type v'} [linear_ordered_field α] {a : α} {b : α} {x : α} (h : a ≤ b) : x ∈ set.Icc a b ↔ ∃ (x_a : α), ∃ (x_b : α), 0 ≤ x_a ∧ 0 ≤ x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x := sorry

theorem submodule.convex {E : Type u} [add_comm_group E] [vector_space ℝ E] (K : submodule ℝ E) : convex ↑K :=
  id
    fun (x y : E) (ᾰ : x ∈ ↑K) (ᾰ_1 : y ∈ ↑K) (a b : ℝ) (ᾰ_2 : 0 ≤ a) (ᾰ_3 : 0 ≤ b) (ᾰ_4 : a + b = 1) =>
      submodule.add_mem K (submodule.smul_mem K a ᾰ) (submodule.smul_mem K b ᾰ_1)

theorem subspace.convex {E : Type u} [add_comm_group E] [vector_space ℝ E] (K : subspace ℝ E) : convex ↑K :=
  submodule.convex K

/-! ### Convex and concave functions -/

/-- Convexity of functions -/
def convex_on {E : Type u} [add_comm_group E] [vector_space ℝ E] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] (s : set E) (f : E → β) :=
  convex s ∧ ∀ {x y : E}, x ∈ s → y ∈ s → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def concave_on {E : Type u} [add_comm_group E] [vector_space ℝ E] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] (s : set E) (f : E → β) :=
  convex s ∧ ∀ {x y : E}, x ∈ s → y ∈ s → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y)

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] theorem neg_convex_on_iff {E : Type u} [add_comm_group E] [vector_space ℝ E] {γ : Type u_1} [ordered_add_comm_group γ] [semimodule ℝ γ] (s : set E) (f : E → γ) : convex_on s (-f) ↔ concave_on s f := sorry

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] theorem neg_concave_on_iff {E : Type u} [add_comm_group E] [vector_space ℝ E] {γ : Type u_1} [ordered_add_comm_group γ] [semimodule ℝ γ] (s : set E) (f : E → γ) : concave_on s (-f) ↔ convex_on s f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (concave_on s (-f) ↔ convex_on s f)) (Eq.symm (propext (neg_convex_on_iff s (-f))))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (convex_on s ( --f) ↔ convex_on s f)) (neg_neg f))) (iff.refl (convex_on s f)))

theorem convex_on_id {s : set ℝ} (hs : convex s) : convex_on s id := sorry

theorem concave_on_id {s : set ℝ} (hs : convex s) : concave_on s id := sorry

theorem convex_on_const {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] (c : β) (hs : convex s) : convex_on s fun (x : E) => c := sorry

theorem concave_on_const {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] (c : β) (hs : convex s) : concave_on s fun (x : E) => c :=
  convex_on_const c hs

theorem convex_on_iff_div {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} : convex_on s f ↔
  convex s ∧
    ∀ {x y : E},
      x ∈ s →
        y ∈ s →
          ∀ {a b : ℝ},
            0 ≤ a →
              0 ≤ b → 0 < a + b → f ((a / (a + b)) • x + (b / (a + b)) • y) ≤ (a / (a + b)) • f x + (b / (a + b)) • f y := sorry

theorem concave_on_iff_div {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} : concave_on s f ↔
  convex s ∧
    ∀ {x y : E},
      x ∈ s →
        y ∈ s →
          ∀ {a b : ℝ},
            0 ≤ a →
              0 ≤ b → 0 < a + b → (a / (a + b)) • f x + (b / (a + b)) • f y ≤ f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  convex_on_iff_div

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
theorem linear_order.convex_on_of_lt {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} [linear_order E] (hs : convex s) (hf : ∀ {x y : E}, x ∈ s → y ∈ s → x < y → ∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y) : convex_on s f := sorry

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
theorem linear_order.concave_on_of_lt {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} [linear_order E] (hs : convex s) (hf : ∀ {x y : E}, x ∈ s → y ∈ s → x < y → ∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y)) : concave_on s f :=
  linear_order.convex_on_of_lt hs hf

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
theorem convex_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) : convex_on s f := sorry

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is convex on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
theorem convex_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : convex_on s f) {x : ℝ} {y : ℝ} {z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) := sorry

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is convex on `D` iff for any three
points `x<y<z` the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
theorem convex_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} : convex_on s f ↔ ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z → (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
  { mp := convex_on.slope_mono_adjacent, mpr := convex_on_real_of_slope_mono_adjacent hs }

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is greater than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
theorem concave_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on s f := sorry

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is concave on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is greater than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
theorem concave_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : concave_on s f) {x : ℝ} {y : ℝ} {z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) := sorry

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is concave on `D` iff for any
three points `x<y<z` the slope of the secant line of `f` on `[x, y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
theorem concave_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} : concave_on s f ↔ ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z → (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
  { mp := concave_on.slope_mono_adjacent, mpr := concave_on_real_of_slope_mono_adjacent hs }

theorem convex_on.subset {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {t : set E} {f : E → β} (h_convex_on : convex_on t f) (h_subset : s ⊆ t) (h_convex : convex s) : convex_on s f :=
  { left := h_convex,
    right := fun (x y : E) (hx : x ∈ s) (hy : y ∈ s) => and.right h_convex_on x y (h_subset hx) (h_subset hy) }

theorem concave_on.subset {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {t : set E} {f : E → β} (h_concave_on : concave_on t f) (h_subset : s ⊆ t) (h_convex : convex s) : concave_on s f :=
  convex_on.subset h_concave_on h_subset h_convex

theorem convex_on.add {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} {g : E → β} (hf : convex_on s f) (hg : convex_on s g) : convex_on s fun (x : E) => f x + g x := sorry

theorem concave_on.add {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} {g : E → β} (hf : concave_on s f) (hg : concave_on s g) : concave_on s fun (x : E) => f x + g x :=
  convex_on.add hf hg

theorem convex_on.smul {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : E → β} {c : ℝ} (hc : 0 ≤ c) (hf : convex_on s f) : convex_on s fun (x : E) => c • f x := sorry

theorem concave_on.smul {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : E → β} {c : ℝ} (hc : 0 ≤ c) (hf : concave_on s f) : concave_on s fun (x : E) => c • f x :=
  convex_on.smul hc hf

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem convex_on.le_on_segment' {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [linear_ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} {x : E} {y : E} {a : ℝ} {b : ℝ} (hf : convex_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : f (a • x + b • y) ≤ max (f x) (f y) := sorry

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem concave_on.le_on_segment' {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [linear_ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} {x : E} {y : E} {a : ℝ} {b : ℝ} (hf : concave_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) :=
  convex_on.le_on_segment' hf hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem convex_on.le_on_segment {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [linear_ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} (hf : convex_on s f) {x : E} {y : E} {z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ segment x y) : f z ≤ max (f x) (f y) := sorry

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem concave_on.le_on_segment {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [linear_ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} (hf : concave_on s f) {x : E} {y : E} {z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ segment x y) : min (f x) (f y) ≤ f z :=
  convex_on.le_on_segment hf hx hy hz

theorem convex_on.convex_le {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : E → β} (hf : convex_on s f) (r : β) : convex (has_sep.sep (fun (x : E) => f x ≤ r) s) := sorry

theorem concave_on.concave_le {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] [ordered_semimodule ℝ β] {f : E → β} (hf : concave_on s f) (r : β) : convex (has_sep.sep (fun (x : E) => r ≤ f x) s) :=
  convex_on.convex_le hf r

theorem convex_on.convex_lt {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [ordered_cancel_add_comm_monoid γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} (hf : convex_on s f) (r : γ) : convex (has_sep.sep (fun (x : E) => f x < r) s) := sorry

theorem concave_on.convex_lt {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [ordered_cancel_add_comm_monoid γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} (hf : concave_on s f) (r : γ) : convex (has_sep.sep (fun (x : E) => r < f x) s) :=
  convex_on.convex_lt hf r

theorem convex_on.convex_epigraph {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} (hf : convex_on s f) : convex (set_of fun (p : E × γ) => prod.fst p ∈ s ∧ f (prod.fst p) ≤ prod.snd p) := sorry

theorem concave_on.convex_hypograph {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} (hf : concave_on s f) : convex (set_of fun (p : E × γ) => prod.fst p ∈ s ∧ prod.snd p ≤ f (prod.fst p)) :=
  convex_on.convex_epigraph hf

theorem convex_on_iff_convex_epigraph {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} : convex_on s f ↔ convex (set_of fun (p : E × γ) => prod.fst p ∈ s ∧ f (prod.fst p) ≤ prod.snd p) := sorry

theorem concave_on_iff_convex_hypograph {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {γ : Type u_1} [ordered_add_comm_group γ] [semimodule ℝ γ] [ordered_semimodule ℝ γ] {f : E → γ} : concave_on s f ↔ convex (set_of fun (p : E × γ) => prod.fst p ∈ s ∧ prod.snd p ≤ f (prod.fst p)) :=
  convex_on_iff_convex_epigraph

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
theorem convex_on.comp_affine_map {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : F → β} (g : affine_map ℝ E F) {s : set F} (hf : convex_on s f) : convex_on (⇑g ⁻¹' s) (f ∘ ⇑g) := sorry

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
theorem concave_on.comp_affine_map {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : F → β} (g : affine_map ℝ E F) {s : set F} (hf : concave_on s f) : concave_on (⇑g ⁻¹' s) (f ∘ ⇑g) :=
  convex_on.comp_affine_map g hf

/-- If `g` is convex on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
theorem convex_on.comp_linear_map {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {g : F → β} {s : set F} (hg : convex_on s g) (f : linear_map ℝ E F) : convex_on (⇑f ⁻¹' s) (g ∘ ⇑f) :=
  convex_on.comp_affine_map (linear_map.to_affine_map f) hg

/-- If `g` is concave on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
theorem concave_on.comp_linear_map {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {g : F → β} {s : set F} (hg : concave_on s g) (f : linear_map ℝ E F) : concave_on (⇑f ⁻¹' s) (g ∘ ⇑f) :=
  concave_on.comp_affine_map (linear_map.to_affine_map f) hg

/-- If a function is convex on `s`, it remains convex after a translation. -/
theorem convex_on.translate_right {E : Type u} [add_comm_group E] [vector_space ℝ E] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} {s : set E} {a : E} (hf : convex_on s f) : convex_on ((fun (z : E) => a + z) ⁻¹' s) (f ∘ fun (z : E) => a + z) :=
  convex_on.comp_affine_map (affine_map.const ℝ E a +ᵥ affine_map.id ℝ E) hf

/-- If a function is concave on `s`, it remains concave after a translation. -/
theorem concave_on.translate_right {E : Type u} [add_comm_group E] [vector_space ℝ E] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} {s : set E} {a : E} (hf : concave_on s f) : concave_on ((fun (z : E) => a + z) ⁻¹' s) (f ∘ fun (z : E) => a + z) :=
  concave_on.comp_affine_map (affine_map.const ℝ E a +ᵥ affine_map.id ℝ E) hf

/-- If a function is convex on `s`, it remains convex after a translation. -/
theorem convex_on.translate_left {E : Type u} [add_comm_group E] [vector_space ℝ E] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} {s : set E} {a : E} (hf : convex_on s f) : convex_on ((fun (z : E) => a + z) ⁻¹' s) (f ∘ fun (z : E) => z + a) := sorry

/-- If a function is concave on `s`, it remains concave after a translation. -/
theorem concave_on.translate_left {E : Type u} [add_comm_group E] [vector_space ℝ E] {β : Type u_1} [ordered_add_comm_monoid β] [semimodule ℝ β] {f : E → β} {s : set E} {a : E} (hf : concave_on s f) : concave_on ((fun (z : E) => a + z) ⁻¹' s) (f ∘ fun (z : E) => z + a) := sorry

/-! ### Center of mass -/

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def finset.center_mass {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (t : finset ι) (w : ι → ℝ) (z : ι → E) : E :=
  (finset.sum t fun (i : ι) => w i)⁻¹ • finset.sum t fun (i : ι) => w i • z i

theorem finset.center_mass_empty {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (w : ι → ℝ) (z : ι → E) : finset.center_mass ∅ w z = 0 := sorry

theorem finset.center_mass_pair {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (i : ι) (j : ι) (w : ι → ℝ) (z : ι → E) (hne : i ≠ j) : finset.center_mass (insert i (singleton j)) w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j := sorry

theorem finset.center_mass_insert {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (i : ι) (t : finset ι) {w : ι → ℝ} (z : ι → E) (ha : ¬i ∈ t) (hw : (finset.sum t fun (j : ι) => w j) ≠ 0) : finset.center_mass (insert i t) w z =
  (w i / (w i + finset.sum t fun (j : ι) => w j)) • z i +
    ((finset.sum t fun (j : ι) => w j) / (w i + finset.sum t fun (j : ι) => w j)) • finset.center_mass t w z := sorry

theorem finset.center_mass_singleton {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (i : ι) {w : ι → ℝ} (z : ι → E) (hw : w i ≠ 0) : finset.center_mass (singleton i) w z = z i := sorry

theorem finset.center_mass_eq_of_sum_1 {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (t : finset ι) {w : ι → ℝ} (z : ι → E) (hw : (finset.sum t fun (i : ι) => w i) = 1) : finset.center_mass t w z = finset.sum t fun (i : ι) => w i • z i := sorry

theorem finset.center_mass_smul {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (c : ℝ) (t : finset ι) {w : ι → ℝ} (z : ι → E) : (finset.center_mass t w fun (i : ι) => c • z i) = c • finset.center_mass t w z := sorry

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem finset.center_mass_segment' {E : Type u} {ι : Type w} {ι' : Type x} [add_comm_group E] [vector_space ℝ E] (s : finset ι) (t : finset ι') (ws : ι → ℝ) (zs : ι → E) (wt : ι' → ℝ) (zt : ι' → E) (hws : (finset.sum s fun (i : ι) => ws i) = 1) (hwt : (finset.sum t fun (i : ι') => wt i) = 1) (a : ℝ) (b : ℝ) (hab : a + b = 1) : a • finset.center_mass s ws zs + b • finset.center_mass t wt zt =
  finset.center_mass (finset.map function.embedding.inl s ∪ finset.map function.embedding.inr t)
    (sum.elim (fun (i : ι) => a * ws i) fun (j : ι') => b * wt j) (sum.elim zs zt) := sorry

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem finset.center_mass_segment {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (s : finset ι) (w₁ : ι → ℝ) (w₂ : ι → ℝ) (z : ι → E) (hw₁ : (finset.sum s fun (i : ι) => w₁ i) = 1) (hw₂ : (finset.sum s fun (i : ι) => w₂ i) = 1) (a : ℝ) (b : ℝ) (hab : a + b = 1) : a • finset.center_mass s w₁ z + b • finset.center_mass s w₂ z =
  finset.center_mass s (fun (i : ι) => a * w₁ i + b * w₂ i) z := sorry

theorem finset.center_mass_ite_eq {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] (i : ι) (t : finset ι) (z : ι → E) (hi : i ∈ t) : finset.center_mass t (fun (j : ι) => ite (i = j) 1 0) z = z i := sorry

theorem finset.center_mass_subset {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {t : finset ι} {w : ι → ℝ} (z : ι → E) {t' : finset ι} (ht : t ⊆ t') (h : ∀ (i : ι), i ∈ t' → ¬i ∈ t → w i = 0) : finset.center_mass t w z = finset.center_mass t' w z := sorry

theorem finset.center_mass_filter_ne_zero {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {t : finset ι} {w : ι → ℝ} (z : ι → E) : finset.center_mass (finset.filter (fun (i : ι) => w i ≠ 0) t) w z = finset.center_mass t w z := sorry

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem convex.center_mass_mem {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : finset ι} {w : ι → ℝ} {z : ι → E} (hs : convex s) : (∀ (i : ι), i ∈ t → 0 ≤ w i) →
  (0 < finset.sum t fun (i : ι) => w i) → (∀ (i : ι), i ∈ t → z i ∈ s) → finset.center_mass t w z ∈ s := sorry

theorem convex.sum_mem {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : finset ι} {w : ι → ℝ} {z : ι → E} (hs : convex s) (h₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i) (h₁ : (finset.sum t fun (i : ι) => w i) = 1) (hz : ∀ (i : ι), i ∈ t → z i ∈ s) : (finset.sum t fun (i : ι) => w i • z i) ∈ s := sorry

theorem convex_iff_sum_mem {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} : convex s ↔
  ∀ (t : finset E) (w : E → ℝ),
    (∀ (i : E), i ∈ t → 0 ≤ w i) →
      (finset.sum t fun (i : E) => w i) = 1 → (∀ (x : E), x ∈ t → x ∈ s) → (finset.sum t fun (x : E) => w x • x) ∈ s := sorry

/-- Jensen's inequality, `finset.center_mass` version. -/
theorem convex_on.map_center_mass_le {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : finset ι} {w : ι → ℝ} {z : ι → E} {f : E → ℝ} (hf : convex_on s f) (h₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i) (hpos : 0 < finset.sum t fun (i : ι) => w i) (hmem : ∀ (i : ι), i ∈ t → z i ∈ s) : f (finset.center_mass t w z) ≤ finset.center_mass t w (f ∘ z) := sorry

/-- Jensen's inequality, `finset.sum` version. -/
theorem convex_on.map_sum_le {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : finset ι} {w : ι → ℝ} {z : ι → E} {f : E → ℝ} (hf : convex_on s f) (h₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i) (h₁ : (finset.sum t fun (i : ι) => w i) = 1) (hmem : ∀ (i : ι), i ∈ t → z i ∈ s) : f (finset.sum t fun (i : ι) => w i • z i) ≤ finset.sum t fun (i : ι) => w i * f (z i) := sorry

/-- If a function `f` is convex on `s` takes value `y` at the center of mass of some points
`z i ∈ s`, then for some `i` we have `y ≤ f (z i)`. -/
theorem convex_on.exists_ge_of_center_mass {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : finset ι} {w : ι → ℝ} {z : ι → E} {f : E → ℝ} (h : convex_on s f) (hw₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i) (hws : 0 < finset.sum t fun (i : ι) => w i) (hz : ∀ (i : ι), i ∈ t → z i ∈ s) : ∃ (i : ι), ∃ (H : i ∈ t), f (finset.center_mass t w z) ≤ f (z i) := sorry

/-! ### Convex hull -/

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convex_hull {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : set E) : set E :=
  set.Inter fun (t : set E) => set.Inter fun (hst : s ⊆ t) => set.Inter fun (ht : convex t) => t

theorem subset_convex_hull {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : set E) : s ⊆ convex_hull s :=
  set.subset_Inter fun (t : set E) => set.subset_Inter fun (hst : s ⊆ t) => set.subset_Inter fun (ht : convex t) => hst

theorem convex_convex_hull {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : set E) : convex (convex_hull s) :=
  convex_Inter fun (t : set E) => convex_Inter fun (ht : s ⊆ t) => convex_Inter id

theorem convex_hull_min {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : set E} (hst : s ⊆ t) (ht : convex t) : convex_hull s ⊆ t :=
  set.Inter_subset_of_subset t (set.Inter_subset_of_subset hst (set.Inter_subset (fun (ht : convex t) => t) ht))

theorem convex_hull_mono {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {t : set E} (hst : s ⊆ t) : convex_hull s ⊆ convex_hull t :=
  convex_hull_min (set.subset.trans hst (subset_convex_hull t)) (convex_convex_hull t)

theorem convex.convex_hull_eq {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : convex s) : convex_hull s = s :=
  set.subset.antisymm (convex_hull_min (set.subset.refl s) hs) (subset_convex_hull s)

@[simp] theorem convex_hull_singleton {E : Type u} [add_comm_group E] [vector_space ℝ E] {x : E} : convex_hull (singleton x) = singleton x :=
  convex.convex_hull_eq (convex_singleton x)

theorem is_linear_map.image_convex_hull {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set E} {f : E → F} (hf : is_linear_map ℝ f) : f '' convex_hull s = convex_hull (f '' s) := sorry

theorem linear_map.image_convex_hull {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {s : set E} (f : linear_map ℝ E F) : ⇑f '' convex_hull s = convex_hull (⇑f '' s) :=
  is_linear_map.image_convex_hull (linear_map.is_linear f)

theorem finset.center_mass_mem_convex_hull {E : Type u} {ι : Type w} [add_comm_group E] [vector_space ℝ E] {s : set E} (t : finset ι) {w : ι → ℝ} (hw₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i) (hws : 0 < finset.sum t fun (i : ι) => w i) {z : ι → E} (hz : ∀ (i : ι), i ∈ t → z i ∈ s) : finset.center_mass t w z ∈ convex_hull s :=
  convex.center_mass_mem (convex_convex_hull s) hw₀ hws fun (i : ι) (hi : i ∈ t) => subset_convex_hull s (hz i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
theorem convex_hull_eq {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : set E) : convex_hull s =
  set_of
    fun (x : E) =>
      ∃ (ι : Type u'),
        ∃ (t : finset ι),
          ∃ (w : ι → ℝ),
            ∃ (z : ι → E),
              ∃ (hw₀ : ∀ (i : ι), i ∈ t → 0 ≤ w i),
                ∃ (hw₁ : (finset.sum t fun (i : ι) => w i) = 1),
                  ∃ (hz : ∀ (i : ι), i ∈ t → z i ∈ s), finset.center_mass t w z = x := sorry

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then `f` can't have a maximum on `convex_hull s` outside of `s`. -/
theorem convex_on.exists_ge_of_mem_convex_hull {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} {f : E → ℝ} (hf : convex_on (convex_hull s) f) {x : E} (hx : x ∈ convex_hull s) : ∃ (y : E), ∃ (H : y ∈ s), f x ≤ f y := sorry

theorem finset.convex_hull_eq {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : finset E) : convex_hull ↑s =
  set_of
    fun (x : E) =>
      ∃ (w : E → ℝ),
        ∃ (hw₀ : ∀ (y : E), y ∈ s → 0 ≤ w y),
          ∃ (hw₁ : (finset.sum s fun (y : E) => w y) = 1), finset.center_mass s w id = x := sorry

theorem set.finite.convex_hull_eq {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : set.finite s) : convex_hull s =
  set_of
    fun (x : E) =>
      ∃ (w : E → ℝ),
        ∃ (hw₀ : ∀ (y : E), y ∈ s → 0 ≤ w y),
          ∃ (hw₁ : (finset.sum (set.finite.to_finset hs) fun (y : E) => w y) = 1),
            finset.center_mass (set.finite.to_finset hs) w id = x := sorry

theorem convex_hull_eq_union_convex_hull_finite_subsets {E : Type u} [add_comm_group E] [vector_space ℝ E] (s : set E) : convex_hull s = set.Union fun (t : finset E) => set.Union fun (w : ↑t ⊆ s) => convex_hull ↑t := sorry

theorem is_linear_map.convex_hull_image {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] {f : E → F} (hf : is_linear_map ℝ f) (s : set E) : convex_hull (f '' s) = f '' convex_hull s := sorry

theorem linear_map.convex_hull_image {E : Type u} {F : Type v} [add_comm_group E] [vector_space ℝ E] [add_comm_group F] [vector_space ℝ F] (f : linear_map ℝ E F) (s : set E) : convex_hull (⇑f '' s) = ⇑f '' convex_hull s :=
  is_linear_map.convex_hull_image (linear_map.is_linear f) s

/-! ### Simplex -/

/-- The standard simplex in the space of functions `ι → ℝ` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type u_1) [fintype ι] : set (ι → ℝ) :=
  set_of fun (f : ι → ℝ) => (∀ (x : ι), 0 ≤ f x) ∧ (finset.sum finset.univ fun (x : ι) => f x) = 1

theorem std_simplex_eq_inter (ι : Type w) [fintype ι] : std_simplex ι =
  (set.Inter fun (x : ι) => set_of fun (f : ι → ℝ) => 0 ≤ f x) ∩
    set_of fun (f : ι → ℝ) => (finset.sum finset.univ fun (x : ι) => f x) = 1 := sorry

theorem convex_std_simplex (ι : Type w) [fintype ι] : convex (std_simplex ι) := sorry

theorem ite_eq_mem_std_simplex {ι : Type w} [fintype ι] (i : ι) : (fun (j : ι) => ite (i = j) 1 0) ∈ std_simplex ι := sorry

/-- `std_simplex ι` is the convex hull of the canonical basis in `ι → ℝ`. -/
theorem convex_hull_basis_eq_std_simplex {ι : Type w} [fintype ι] : convex_hull (set.range fun (i j : ι) => ite (i = j) 1 0) = std_simplex ι := sorry

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
theorem set.finite.convex_hull_eq_image {E : Type u} [add_comm_group E] [vector_space ℝ E] {s : set E} (hs : set.finite s) : convex_hull s =
  ⇑(finset.sum finset.univ fun (x : ↥s) => linear_map.smul_right (linear_map.proj x) (subtype.val x)) '' std_simplex ↥s := sorry

/-- All values of a function `f ∈ std_simplex ι` belong to `[0, 1]`. -/
theorem mem_Icc_of_mem_std_simplex {ι : Type w} [fintype ι] {f : ι → ℝ} (hf : f ∈ std_simplex ι) (x : ι) : f x ∈ set.Icc 0 1 :=
  { left := and.left hf x,
    right :=
      and.right hf ▸ finset.single_le_sum (fun (y : ι) (hy : y ∈ finset.univ) => and.left hf y) (finset.mem_univ x) }

