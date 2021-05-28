/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.PostPort

universes u l u_1 v w 

namespace Mathlib

/-!
# Subfields

Let `K` be a field. This file defines the "bundled" subfield type `subfield K`, a type
whose terms correspond to subfields of `K`. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : set K` and `is_subfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `set R` to `subfield R`, sending a subset of `R`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [field K] (L : Type u) [field L] (f g : K →+* L)`
`(A : subfield K) (B : subfield L) (s : set K)`

* `subfield R` : the type of subfields of a ring `R`.

* `instance : complete_lattice (subfield R)` : the complete lattice structure on the subfields.

* `subfield.closure` : subfield closure of a set, i.e., the smallest subfield that includes the set.

* `subfield.gi` : `closure : set M → subfield M` and coercion `coe : subfield M → set M`
  form a `galois_insertion`.

* `comap f B : subfield K` : the preimage of a subfield `B` along the ring homomorphism `f`

* `map f A : subfield L` : the image of a subfield `A` along the ring homomorphism `f`.

* `prod A B : subfield (K × L)` : the product of subfields

* `f.field_range : subfield B` : the range of the ring homomorphism `f`.

* `eq_locus_field f g : subfield K` : given ring homomorphisms `f g : K →+* R`,
     the subfield of `K` where `f x = g x`

## Implementation notes

A subfield is implemented as a subring which is is closed under `⁻¹`.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

/-- `subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
structure subfield (K : Type u) [field K] 
extends subring K
where
  inv_mem' : ∀ (x : K), x ∈ carrier → x⁻¹ ∈ carrier

/-- Reinterpret a `subfield` as a `subring`. -/
namespace subfield


/-- The underlying `add_subgroup` of a subfield. -/
def to_add_subgroup {K : Type u} [field K] (s : subfield K) : add_subgroup K :=
  add_subgroup.mk (add_subgroup.carrier (subring.to_add_subgroup (to_subring s))) sorry sorry sorry

/-- The underlying submonoid of a subfield. -/
def to_submonoid {K : Type u} [field K] (s : subfield K) : submonoid K :=
  submonoid.mk (submonoid.carrier (subring.to_submonoid (to_subring s))) sorry sorry

protected instance set.has_coe {K : Type u} [field K] : has_coe (subfield K) (set K) :=
  has_coe.mk carrier

@[simp] theorem coe_to_subring {K : Type u} [field K] (s : subfield K) : ↑(to_subring s) = ↑s :=
  rfl

protected instance has_coe_to_sort {K : Type u} [field K] : has_coe_to_sort (subfield K) :=
  has_coe_to_sort.mk (Type u) fun (S : subfield K) => ↥(carrier S)

protected instance has_mem {K : Type u} [field K] : has_mem K (subfield K) :=
  has_mem.mk fun (m : K) (S : subfield K) => m ∈ ↑S

@[simp] theorem mem_mk {K : Type u} [field K] (s : set K) (ho : 1 ∈ s) (hm : ∀ {a b : K}, a ∈ s → b ∈ s → a * b ∈ s) (hz : 0 ∈ s) (ha : ∀ {a b : K}, a ∈ s → b ∈ s → a + b ∈ s) (hn : ∀ {x : K}, x ∈ s → -x ∈ s) (hi : ∀ (x : K), x ∈ s → x⁻¹ ∈ s) (x : K) : x ∈ mk s ho hm hz ha hn hi ↔ x ∈ s :=
  iff.rfl

@[simp] theorem mem_to_subring {K : Type u} [field K] (s : subfield K) (x : K) : x ∈ to_subring s ↔ x ∈ s :=
  iff.rfl

end subfield


protected theorem subfield.exists {K : Type u} [field K] {s : subfield K} {p : ↥s → Prop} : (∃ (x : ↥s), p x) ↔ ∃ (x : K), ∃ (H : x ∈ s), p { val := x, property := H } :=
  set_coe.exists

protected theorem subfield.forall {K : Type u} [field K] {s : subfield K} {p : ↥s → Prop} : (∀ (x : ↥s), p x) ↔ ∀ (x : K) (H : x ∈ s), p { val := x, property := H } :=
  set_coe.forall

/-- A `subring` containing inverses is a `subfield`. -/
def subring.to_subfield {K : Type u} [field K] (s : subring K) (hinv : ∀ (x : K), x ∈ s → x⁻¹ ∈ s) : subfield K :=
  subfield.mk (subring.carrier s) sorry sorry sorry sorry sorry hinv

namespace subfield


/-- Two subfields are equal if the underlying subsets are equal. -/
theorem ext' {K : Type u} [field K] {s : subfield K} {t : subfield K} (h : ↑s = ↑t) : s = t := sorry

/-- Two subfields are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {K : Type u} [field K] {s : subfield K} {t : subfield K} : s = t ↔ ↑s = ↑t :=
  { mp := fun (h : s = t) => h ▸ rfl, mpr := fun (h : ↑s = ↑t) => ext' h }

/-- Two subfields are equal if they have the same elements. -/
theorem ext {K : Type u} [field K] {S : subfield K} {T : subfield K} (h : ∀ (x : K), x ∈ S ↔ x ∈ T) : S = T :=
  ext' (set.ext h)

/-- A subfield contains the ring's 1. -/
theorem one_mem {K : Type u} [field K] (s : subfield K) : 1 ∈ s :=
  one_mem' s

/-- A subfield contains the ring's 0. -/
theorem zero_mem {K : Type u} [field K] (s : subfield K) : 0 ∈ s :=
  zero_mem' s

/-- A subfield is closed under multiplication. -/
theorem mul_mem {K : Type u} [field K] (s : subfield K) {x : K} {y : K} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem' s

/-- A subfield is closed under addition. -/
theorem add_mem {K : Type u} [field K] (s : subfield K) {x : K} {y : K} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem' s

/-- A subfield is closed under negation. -/
theorem neg_mem {K : Type u} [field K] (s : subfield K) {x : K} : x ∈ s → -x ∈ s :=
  neg_mem' s

/-- A subfield is closed under subtraction. -/
theorem sub_mem {K : Type u} [field K] (s : subfield K) {x : K} {y : K} : x ∈ s → y ∈ s → x - y ∈ s :=
  subring.sub_mem (to_subring s)

/-- A subfield is closed under inverses. -/
theorem inv_mem {K : Type u} [field K] (s : subfield K) {x : K} : x ∈ s → x⁻¹ ∈ s :=
  inv_mem' s

/-- A subfield is closed under division. -/
theorem div_mem {K : Type u} [field K] (s : subfield K) {x : K} {y : K} (hx : x ∈ s) (hy : y ∈ s) : x / y ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x / y ∈ s)) (div_eq_mul_inv x y))) (mul_mem s hx (inv_mem s hy))

/-- Product of a list of elements in a subfield is in the subfield. -/
theorem list_prod_mem {K : Type u} [field K] (s : subfield K) {l : List K} : (∀ (x : K), x ∈ l → x ∈ s) → list.prod l ∈ s :=
  submonoid.list_prod_mem (to_submonoid s)

/-- Sum of a list of elements in a subfield is in the subfield. -/
theorem list_sum_mem {K : Type u} [field K] (s : subfield K) {l : List K} : (∀ (x : K), x ∈ l → x ∈ s) → list.sum l ∈ s :=
  add_subgroup.list_sum_mem (to_add_subgroup s)

/-- Product of a multiset of elements in a subfield is in the subfield. -/
theorem multiset_prod_mem {K : Type u} [field K] (s : subfield K) (m : multiset K) : (∀ (a : K), a ∈ m → a ∈ s) → multiset.prod m ∈ s :=
  submonoid.multiset_prod_mem (to_submonoid s) m

/-- Sum of a multiset of elements in a `subfield` is in the `subfield`. -/
theorem multiset_sum_mem {K : Type u} [field K] (s : subfield K) (m : multiset K) : (∀ (a : K), a ∈ m → a ∈ s) → multiset.sum m ∈ s :=
  add_subgroup.multiset_sum_mem (to_add_subgroup s) m

/-- Product of elements of a subfield indexed by a `finset` is in the subfield. -/
theorem prod_mem {K : Type u} [field K] (s : subfield K) {ι : Type u_1} {t : finset ι} {f : ι → K} (h : ∀ (c : ι), c ∈ t → f c ∈ s) : (finset.prod t fun (i : ι) => f i) ∈ s :=
  submonoid.prod_mem (to_submonoid s) h

/-- Sum of elements in a `subfield` indexed by a `finset` is in the `subfield`. -/
theorem sum_mem {K : Type u} [field K] (s : subfield K) {ι : Type u_1} {t : finset ι} {f : ι → K} (h : ∀ (c : ι), c ∈ t → f c ∈ s) : (finset.sum t fun (i : ι) => f i) ∈ s :=
  add_subgroup.sum_mem (to_add_subgroup s) h

theorem pow_mem {K : Type u} [field K] (s : subfield K) {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  submonoid.pow_mem (to_submonoid s) hx n

theorem gsmul_mem {K : Type u} [field K] (s : subfield K) {x : K} (hx : x ∈ s) (n : ℤ) : n •ℤ x ∈ s :=
  add_subgroup.gsmul_mem (to_add_subgroup s) hx n

theorem coe_int_mem {K : Type u} [field K] (s : subfield K) (n : ℤ) : ↑n ∈ s := sorry

/-- A subfield inherits a field structure -/
protected instance to_field {K : Type u} [field K] (s : subfield K) : field ↥s :=
  field.mk integral_domain.add sorry integral_domain.zero sorry sorry integral_domain.neg integral_domain.sub sorry sorry
    integral_domain.mul sorry integral_domain.one sorry sorry sorry sorry sorry
    (fun (x : ↥s) => { val := ↑x⁻¹, property := sorry }) sorry sorry sorry

@[simp] theorem coe_add {K : Type u} [field K] (s : subfield K) (x : ↥s) (y : ↥s) : ↑(x + y) = ↑x + ↑y :=
  rfl

@[simp] theorem coe_neg {K : Type u} [field K] (s : subfield K) (x : ↥s) : ↑(-x) = -↑x :=
  rfl

@[simp] theorem coe_mul {K : Type u} [field K] (s : subfield K) (x : ↥s) (y : ↥s) : ↑(x * y) = ↑x * ↑y :=
  rfl

@[simp] theorem coe_inv {K : Type u} [field K] (s : subfield K) (x : ↥s) : ↑(x⁻¹) = (↑x⁻¹) :=
  rfl

@[simp] theorem coe_zero {K : Type u} [field K] (s : subfield K) : ↑0 = 0 :=
  rfl

@[simp] theorem coe_one {K : Type u} [field K] (s : subfield K) : ↑1 = 1 :=
  rfl

/-- The embedding from a subfield of the field `K` to `K`. -/
def subtype {K : Type u} [field K] (s : subfield K) : ↥s →+* K :=
  ring_hom.mk coe sorry sorry sorry sorry

protected instance to_algebra {K : Type u} [field K] (s : subfield K) : algebra (↥s) K :=
  ring_hom.to_algebra (subtype s)

@[simp] theorem coe_subtype {K : Type u} [field K] (s : subfield K) : ⇑(subtype s) = coe :=
  rfl

/-! # Partial order -/

protected instance partial_order {K : Type u} [field K] : partial_order (subfield K) :=
  partial_order.mk (fun (s t : subfield K) => ∀ {x : K}, x ∈ s → x ∈ t) partial_order.lt sorry sorry sorry

theorem le_def {K : Type u} [field K] {s : subfield K} {t : subfield K} : s ≤ t ↔ ∀ {x : K}, x ∈ s → x ∈ t :=
  iff.rfl

@[simp] theorem coe_subset_coe {K : Type u} [field K] {s : subfield K} {t : subfield K} : ↑s ⊆ ↑t ↔ s ≤ t :=
  iff.rfl

@[simp] theorem coe_ssubset_coe {K : Type u} [field K] {s : subfield K} {t : subfield K} : ↑s ⊂ ↑t ↔ s < t :=
  iff.rfl

@[simp] theorem mem_coe {K : Type u} [field K] {s : subfield K} {m : K} : m ∈ ↑s ↔ m ∈ s :=
  iff.rfl

@[simp] theorem coe_coe {K : Type u} [field K] (s : subfield K) : ↥↑s = ↥s :=
  rfl

@[simp] theorem mem_to_submonoid {K : Type u} [field K] {s : subfield K} {x : K} : x ∈ to_submonoid s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem coe_to_submonoid {K : Type u} [field K] (s : subfield K) : ↑(to_submonoid s) = ↑s :=
  rfl

@[simp] theorem mem_to_add_subgroup {K : Type u} [field K] {s : subfield K} {x : K} : x ∈ to_add_subgroup s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem coe_to_add_subgroup {K : Type u} [field K] (s : subfield K) : ↑(to_add_subgroup s) = ↑s :=
  rfl

/-! # top -/

/-- The subfield of `K` containing all elements of `K`. -/
protected instance has_top {K : Type u} [field K] : has_top (subfield K) :=
  has_top.mk (mk (subring.carrier ⊤) sorry sorry sorry sorry sorry sorry)

protected instance inhabited {K : Type u} [field K] : Inhabited (subfield K) :=
  { default := ⊤ }

@[simp] theorem mem_top {K : Type u} [field K] (x : K) : x ∈ ⊤ :=
  set.mem_univ x

@[simp] theorem coe_top {K : Type u} [field K] : ↑⊤ = set.univ :=
  rfl

/-! # comap -/

/-- The preimage of a subfield along a ring homomorphism is a subfield. -/
def comap {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : subfield L) : subfield K :=
  mk (subring.carrier (subring.comap f (to_subring s))) sorry sorry sorry sorry sorry sorry

@[simp] theorem coe_comap {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : subfield L) : ↑(comap f s) = ⇑f ⁻¹' ↑s :=
  rfl

@[simp] theorem mem_comap {K : Type u} {L : Type v} [field K] [field L] {s : subfield L} {f : K →+* L} {x : K} : x ∈ comap f s ↔ coe_fn f x ∈ s :=
  iff.rfl

theorem comap_comap {K : Type u} {L : Type v} {M : Type w} [field K] [field L] [field M] (s : subfield M) (g : L →+* M) (f : K →+* L) : comap f (comap g s) = comap (ring_hom.comp g f) s :=
  rfl

/-! # map -/

/-- The image of a subfield along a ring homomorphism is a subfield. -/
def map {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : subfield K) : subfield L :=
  mk (subring.carrier (subring.map f (to_subring s))) sorry sorry sorry sorry sorry sorry

@[simp] theorem coe_map {K : Type u} {L : Type v} [field K] [field L] (s : subfield K) (f : K →+* L) : ↑(map f s) = ⇑f '' ↑s :=
  rfl

@[simp] theorem mem_map {K : Type u} {L : Type v} [field K] [field L] {f : K →+* L} {s : subfield K} {y : L} : y ∈ map f s ↔ ∃ (x : K), ∃ (H : x ∈ s), coe_fn f x = y :=
  set.mem_image_iff_bex

theorem map_map {K : Type u} {L : Type v} {M : Type w} [field K] [field L] [field M] (s : subfield K) (g : L →+* M) (f : K →+* L) : map g (map f s) = map (ring_hom.comp g f) s :=
  ext' (set.image_image (fun (a : L) => coe_fn g a) (fun (a : K) => coe_fn f a) (subring.carrier (to_subring s)))

theorem map_le_iff_le_comap {K : Type u} {L : Type v} [field K] [field L] {f : K →+* L} {s : subfield K} {t : subfield L} : map f s ≤ t ↔ s ≤ comap f t :=
  set.image_subset_iff

theorem gc_map_comap {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) : galois_connection (map f) (comap f) :=
  fun (S : subfield K) (T : subfield L) => map_le_iff_le_comap

end subfield


namespace ring_hom


/-! # range -/

/-- The range of a ring homomorphism, as a subfield of the target. -/
def field_range {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) : subfield L :=
  subfield.map f ⊤

@[simp] theorem coe_field_range {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) : ↑(field_range f) = set.range ⇑f :=
  set.image_univ

@[simp] theorem mem_field_range {K : Type u} {L : Type v} [field K] [field L] {f : K →+* L} {y : L} : y ∈ range f ↔ ∃ (x : K), coe_fn f x = y := sorry

theorem map_field_range {K : Type u} {L : Type v} {M : Type w} [field K] [field L] [field M] (g : L →+* M) (f : K →+* L) : subfield.map g (field_range f) = field_range (comp g f) :=
  subfield.map_map ⊤ g f

end ring_hom


namespace subfield


/-! # inf -/

/-- The inf of two subfields is their intersection. -/
protected instance has_inf {K : Type u} [field K] : has_inf (subfield K) :=
  has_inf.mk
    fun (s t : subfield K) => mk (subring.carrier (to_subring s ⊓ to_subring t)) sorry sorry sorry sorry sorry sorry

@[simp] theorem coe_inf {K : Type u} [field K] (p : subfield K) (p' : subfield K) : ↑(p ⊓ p') = ↑p ∩ ↑p' :=
  rfl

@[simp] theorem mem_inf {K : Type u} [field K] {p : subfield K} {p' : subfield K} {x : K} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  iff.rfl

protected instance has_Inf {K : Type u} [field K] : has_Inf (subfield K) :=
  has_Inf.mk
    fun (S : set (subfield K)) => mk (subring.carrier (Inf (to_subring '' S))) sorry sorry sorry sorry sorry sorry

@[simp] theorem coe_Inf {K : Type u} [field K] (S : set (subfield K)) : ↑(Inf S) = set.Inter fun (s : subfield K) => set.Inter fun (H : s ∈ S) => ↑s := sorry

theorem mem_Inf {K : Type u} [field K] {S : set (subfield K)} {x : K} : x ∈ Inf S ↔ ∀ (p : subfield K), p ∈ S → x ∈ p := sorry

@[simp] theorem Inf_to_subring {K : Type u} [field K] (s : set (subfield K)) : to_subring (Inf s) = infi fun (t : subfield K) => infi fun (H : t ∈ s) => to_subring t := sorry

theorem is_glb_Inf {K : Type u} [field K] (S : set (subfield K)) : is_glb S (Inf S) := sorry

/-- Subfields of a ring form a complete lattice. -/
protected instance complete_lattice {K : Type u} [field K] : complete_lattice (subfield K) :=
  complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry sorry
    has_inf.inf sorry sorry sorry ⊤ sorry complete_lattice.bot sorry complete_lattice.Sup complete_lattice.Inf sorry sorry
    sorry sorry

/-! # subfield closure of a subset -/

/-- The `subfield` generated by a set. -/
def closure {K : Type u} [field K] (s : set K) : subfield K :=
  mk
    (set_of
      fun (_x : K) => ∃ (x : K), ∃ (H : x ∈ subring.closure s), ∃ (y : K), ∃ (H : y ∈ subring.closure s), x / y = _x)
    sorry sorry sorry sorry sorry sorry

theorem mem_closure_iff {K : Type u} [field K] {s : set K} {x : K} : x ∈ closure s ↔ ∃ (y : K), ∃ (H : y ∈ subring.closure s), ∃ (z : K), ∃ (H : z ∈ subring.closure s), y / z = x :=
  iff.rfl

theorem subring_closure_le {K : Type u} [field K] (s : set K) : subring.closure s ≤ to_subring (closure s) :=
  fun (x : K) (hx : x ∈ subring.closure s) =>
    Exists.intro x (Exists.intro hx (Exists.intro 1 (Exists.intro (subring.one_mem (subring.closure s)) (div_one x))))

/-- The subfield generated by a set includes the set. -/
@[simp] theorem subset_closure {K : Type u} [field K] {s : set K} : s ⊆ ↑(closure s) :=
  set.subset.trans subring.subset_closure (subring_closure_le s)

theorem mem_closure {K : Type u} [field K] {x : K} {s : set K} : x ∈ closure s ↔ ∀ (S : subfield K), s ⊆ ↑S → x ∈ S := sorry

/-- A subfield `t` includes `closure s` if and only if it includes `s`. -/
@[simp] theorem closure_le {K : Type u} [field K] {s : set K} {t : subfield K} : closure s ≤ t ↔ s ⊆ ↑t :=
  { mp := set.subset.trans subset_closure,
    mpr := fun (h : s ⊆ ↑t) (x : K) (hx : x ∈ closure s) => iff.mp mem_closure hx t h }

/-- Subfield closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
theorem closure_mono {K : Type u} [field K] {s : set K} {t : set K} (h : s ⊆ t) : closure s ≤ closure t :=
  iff.mpr closure_le (set.subset.trans h subset_closure)

theorem closure_eq_of_le {K : Type u} [field K] {s : set K} {t : subfield K} (h₁ : s ⊆ ↑t) (h₂ : t ≤ closure s) : closure s = t :=
  le_antisymm (iff.mpr closure_le h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1`, and all elements
of `s`, and is preserved under addition, negation, and multiplication, then `p` holds for all elements
of the closure of `s`. -/
theorem closure_induction {K : Type u} [field K] {s : set K} {p : K → Prop} {x : K} (h : x ∈ closure s) (Hs : ∀ (x : K), x ∈ s → p x) (H1 : p 1) (Hadd : ∀ (x y : K), p x → p y → p (x + y)) (Hneg : ∀ (x : K), p x → p (-x)) (Hinv : ∀ (x : K), p x → p (x⁻¹)) (Hmul : ∀ (x y : K), p x → p y → p (x * y)) : p x :=
  iff.mpr closure_le Hs x h

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi (K : Type u) [field K] : galois_insertion closure coe :=
  galois_insertion.mk (fun (s : set K) (_x : ↑(closure s) ≤ s) => closure s) sorry sorry sorry

/-- Closure of a subfield `S` equals `S`. -/
theorem closure_eq {K : Type u} [field K] (s : subfield K) : closure ↑s = s :=
  galois_insertion.l_u_eq (subfield.gi K) s

@[simp] theorem closure_empty {K : Type u} [field K] : closure ∅ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (subfield.gi K))

@[simp] theorem closure_univ {K : Type u} [field K] : closure set.univ = ⊤ :=
  coe_top ▸ closure_eq ⊤

theorem closure_union {K : Type u} [field K] (s : set K) (t : set K) : closure (s ∪ t) = closure s ⊔ closure t :=
  galois_connection.l_sup (galois_insertion.gc (subfield.gi K))

theorem closure_Union {K : Type u} [field K] {ι : Sort u_1} (s : ι → set K) : closure (set.Union fun (i : ι) => s i) = supr fun (i : ι) => closure (s i) :=
  galois_connection.l_supr (galois_insertion.gc (subfield.gi K))

theorem closure_sUnion {K : Type u} [field K] (s : set (set K)) : closure (⋃₀s) = supr fun (t : set K) => supr fun (H : t ∈ s) => closure t :=
  galois_connection.l_Sup (galois_insertion.gc (subfield.gi K))

theorem map_sup {K : Type u} {L : Type v} [field K] [field L] (s : subfield K) (t : subfield K) (f : K →+* L) : map f (s ⊔ t) = map f s ⊔ map f t :=
  galois_connection.l_sup (gc_map_comap f)

theorem map_supr {K : Type u} {L : Type v} [field K] [field L] {ι : Sort u_1} (f : K →+* L) (s : ι → subfield K) : map f (supr s) = supr fun (i : ι) => map f (s i) :=
  galois_connection.l_supr (gc_map_comap f)

theorem comap_inf {K : Type u} {L : Type v} [field K] [field L] (s : subfield L) (t : subfield L) (f : K →+* L) : comap f (s ⊓ t) = comap f s ⊓ comap f t :=
  galois_connection.u_inf (gc_map_comap f)

theorem comap_infi {K : Type u} {L : Type v} [field K] [field L] {ι : Sort u_1} (f : K →+* L) (s : ι → subfield L) : comap f (infi s) = infi fun (i : ι) => comap f (s i) :=
  galois_connection.u_infi (gc_map_comap f)

@[simp] theorem map_bot {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) : map f ⊥ = ⊥ :=
  galois_connection.l_bot (gc_map_comap f)

@[simp] theorem comap_top {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) : comap f ⊤ = ⊤ :=
  galois_connection.u_top (gc_map_comap f)

/-- The underlying set of a non-empty directed Sup of subfields is just a union of the subfields.
  Note that this fails without the directedness assumption (the union of two subfields is
  typically not a subfield) -/
theorem mem_supr_of_directed {K : Type u} [field K] {ι : Sort u_1} [hι : Nonempty ι] {S : ι → subfield K} (hS : directed LessEq S) {x : K} : (x ∈ supr fun (i : ι) => S i) ↔ ∃ (i : ι), x ∈ S i := sorry

theorem coe_supr_of_directed {K : Type u} [field K] {ι : Sort u_1} [hι : Nonempty ι] {S : ι → subfield K} (hS : directed LessEq S) : ↑(supr fun (i : ι) => S i) = set.Union fun (i : ι) => ↑(S i) := sorry

theorem mem_Sup_of_directed_on {K : Type u} [field K] {S : set (subfield K)} (Sne : set.nonempty S) (hS : directed_on LessEq S) {x : K} : x ∈ Sup S ↔ ∃ (s : subfield K), ∃ (H : s ∈ S), x ∈ s := sorry

theorem coe_Sup_of_directed_on {K : Type u} [field K] {S : set (subfield K)} (Sne : set.nonempty S) (hS : directed_on LessEq S) : ↑(Sup S) = set.Union fun (s : subfield K) => set.Union fun (H : s ∈ S) => ↑s := sorry

end subfield


namespace ring_hom


/-- Restrict the codomain of a ring homomorphism to a subfield that includes the range. -/
def cod_restrict_field {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : subfield L) (h : ∀ (x : K), coe_fn f x ∈ s) : K →+* ↥s :=
  mk (fun (x : K) => { val := coe_fn f x, property := h x }) sorry sorry sorry sorry

/-- Restriction of a ring homomorphism to a subfield of the domain. -/
def restrict_field {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : subfield K) : ↥s →+* L :=
  comp f (subfield.subtype s)

@[simp] theorem restrict_field_apply {K : Type u} {L : Type v} [field K] [field L] {s : subfield K} (f : K →+* L) (x : ↥s) : coe_fn (restrict_field f s) x = coe_fn f ↑x :=
  rfl

/-- Restriction of a ring homomorphism to its range interpreted as a subfield. -/
def range_restrict_field {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) : K →+* ↥(range f) :=
  cod_restrict' f (range f) sorry

@[simp] theorem coe_range_restrict_field {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (x : K) : ↑(coe_fn (range_restrict_field f) x) = coe_fn f x :=
  rfl

/-- The subfield of elements `x : R` such that `f x = g x`, i.e.,
the equalizer of f and g as a subfield of R -/
def eq_locus_field {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (g : K →+* L) : subfield K :=
  subfield.mk (set_of fun (x : K) => coe_fn f x = coe_fn g x) sorry sorry sorry sorry sorry sorry

/-- If two ring homomorphisms are equal on a set, then they are equal on its subfield closure. -/
theorem eq_on_field_closure {K : Type u} {L : Type v} [field K] [field L] {f : K →+* L} {g : K →+* L} {s : set K} (h : set.eq_on (⇑f) (⇑g) s) : set.eq_on ⇑f ⇑g ↑(subfield.closure s) :=
  (fun (this : subfield.closure s ≤ eq_locus_field f g) => this) (iff.mpr subfield.closure_le h)

theorem eq_of_eq_on_subfield_top {K : Type u} {L : Type v} [field K] [field L] {f : K →+* L} {g : K →+* L} (h : set.eq_on ⇑f ⇑g ↑⊤) : f = g :=
  ext fun (x : K) => h trivial

theorem eq_of_eq_on_of_field_closure_eq_top {K : Type u} {L : Type v} [field K] [field L] {s : set K} (hs : subfield.closure s = ⊤) {f : K →+* L} {g : K →+* L} (h : set.eq_on (⇑f) (⇑g) s) : f = g :=
  eq_of_eq_on_subfield_top (hs ▸ eq_on_field_closure h)

theorem field_closure_preimage_le {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : set L) : subfield.closure (⇑f ⁻¹' s) ≤ subfield.comap f (subfield.closure s) :=
  iff.mpr subfield.closure_le
    fun (x : K) (hx : x ∈ ⇑f ⁻¹' s) => iff.mpr subfield.mem_coe (iff.mpr subfield.mem_comap (subfield.subset_closure hx))

/-- The image under a ring homomorphism of the subfield generated by a set equals
the subfield generated by the image of the set. -/
theorem map_field_closure {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : set K) : subfield.map f (subfield.closure s) = subfield.closure (⇑f '' s) := sorry

end ring_hom


namespace subfield


/-- The ring homomorphism associated to an inclusion of subfields. -/
def inclusion {K : Type u} [field K] {S : subfield K} {T : subfield K} (h : S ≤ T) : ↥S →+* ↥T :=
  ring_hom.cod_restrict_field (subtype S) T sorry

@[simp] theorem field_range_subtype {K : Type u} [field K] (s : subfield K) : ring_hom.field_range (subtype s) = s :=
  ext' (Eq.trans (ring_hom.coe_srange (subtype s)) subtype.range_coe)

end subfield


namespace ring_equiv


/-- Makes the identity isomorphism from a proof two subfields of a multiplicative
    monoid are equal. -/
def subfield_congr {K : Type u} [field K] {s : subfield K} {t : subfield K} (h : s = t) : ↥s ≃+* ↥t :=
  mk (equiv.to_fun (equiv.set_congr sorry)) (equiv.inv_fun (equiv.set_congr sorry)) sorry sorry sorry sorry

end ring_equiv


namespace subfield


theorem closure_preimage_le {K : Type u} {L : Type v} [field K] [field L] (f : K →+* L) (s : set L) : closure (⇑f ⁻¹' s) ≤ comap f (closure s) :=
  iff.mpr closure_le fun (x : K) (hx : x ∈ ⇑f ⁻¹' s) => iff.mpr mem_coe (iff.mpr mem_comap (subset_closure hx))

