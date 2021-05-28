/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.field_theory.subfield
import Mathlib.field_theory.tower
import Mathlib.ring_theory.algebraic
import PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-!
# Intermediate fields

Let `L / K` be a field extension, given as an instance `algebra K L`.
This file defines the type of fields in between `K` and `L`, `intermediate_field K L`.
An `intermediate_field K L` is a subfield of `L` which contains (the image of) `K`,
i.e. it is a `subfield L` and a `subalgebra K L`.

## Main definitions

 * `intermediate_field K L` : the type of intermediate fields between `K` and `L`.

 * `subalgebra.to_intermediate_field`: turns a subalgebra closed under `⁻¹`
   into an intermediate field

 * `subfield.to_intermediate_field`: turns a subfield containing the image of `K`
   into an intermediate field

* `intermediate_field.map`: map an intermediate field along an `alg_hom`

## Implementation notes

Intermediate fields are defined with a structure extending `subfield` and `subalgebra`.
A `subalgebra` is closed under all operations except `⁻¹`,

## Tags
intermediate field, field extension
-/

/-- `S : intermediate_field K L` is a subset of `L` such that there is a field
tower `L / S / K`. -/
structure intermediate_field (K : Type u_1) (L : Type u_2) [field K] [field L] [algebra K L] 
extends subalgebra K L, subfield L
where

/-- Reinterpret an `intermediate_field` as a `subalgebra`. -/
/-- Reinterpret an `intermediate_field` as a `subfield`. -/
namespace intermediate_field


protected instance set.has_coe {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] : has_coe (intermediate_field K L) (set L) :=
  has_coe.mk carrier

@[simp] theorem coe_to_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : ↑(to_subalgebra S) = ↑S :=
  rfl

@[simp] theorem coe_to_subfield {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : ↑(to_subfield S) = ↑S :=
  rfl

protected instance has_coe_to_sort {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] : has_coe_to_sort (intermediate_field K L) :=
  has_coe_to_sort.mk (Type u_2) fun (S : intermediate_field K L) => ↥(carrier S)

protected instance has_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] : has_mem L (intermediate_field K L) :=
  has_mem.mk fun (m : L) (S : intermediate_field K L) => m ∈ ↑S

@[simp] theorem mem_mk {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (s : set L) (hK : ∀ (x : K), coe_fn (algebra_map K L) x ∈ s) (ho : 1 ∈ s) (hm : ∀ {a b : L}, a ∈ s → b ∈ s → a * b ∈ s) (hz : 0 ∈ s) (ha : ∀ {a b : L}, a ∈ s → b ∈ s → a + b ∈ s) (hn : ∀ {x : L}, x ∈ s → -x ∈ s) (hi : ∀ (x : L), x ∈ s → x⁻¹ ∈ s) (x : L) : x ∈ mk s ho hm hz ha hK hn hi ↔ x ∈ s :=
  iff.rfl

@[simp] theorem mem_coe {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (x : L) : x ∈ ↑S ↔ x ∈ S :=
  iff.rfl

@[simp] theorem mem_to_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (s : intermediate_field K L) (x : L) : x ∈ to_subalgebra s ↔ x ∈ s :=
  iff.rfl

@[simp] theorem mem_to_subfield {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (s : intermediate_field K L) (x : L) : x ∈ to_subfield s ↔ x ∈ s :=
  iff.rfl

/-- Two intermediate fields are equal if the underlying subsets are equal. -/
theorem ext' {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {s : intermediate_field K L} {t : intermediate_field K L} (h : ↑s = ↑t) : s = t := sorry

/-- Two intermediate fields are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {s : intermediate_field K L} {t : intermediate_field K L} : s = t ↔ ↑s = ↑t :=
  { mp := fun (h : s = t) => h ▸ rfl, mpr := fun (h : ↑s = ↑t) => ext' h }

/-- Two intermediate fields are equal if they have the same elements. -/
theorem ext {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {S : intermediate_field K L} {T : intermediate_field K L} (h : ∀ (x : L), x ∈ S ↔ x ∈ T) : S = T :=
  ext' (set.ext h)

/-- An intermediate field contains the image of the smaller field. -/
theorem algebra_map_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (x : K) : coe_fn (algebra_map K L) x ∈ S :=
  algebra_map_mem' S x

/-- An intermediate field contains the ring's 1. -/
theorem one_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : 1 ∈ S :=
  one_mem' S

/-- An intermediate field contains the ring's 0. -/
theorem zero_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : 0 ∈ S :=
  zero_mem' S

/-- An intermediate field is closed under multiplication. -/
theorem mul_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} {y : L} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem' S

/-- An intermediate field is closed under scalar multiplication. -/
theorem smul_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {y : L} : y ∈ S → ∀ {x : K}, x • y ∈ S :=
  subalgebra.smul_mem (to_subalgebra S)

/-- An intermediate field is closed under addition. -/
theorem add_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} {y : L} : x ∈ S → y ∈ S → x + y ∈ S :=
  add_mem' S

/-- An intermediate field is closed under subtraction -/
theorem sub_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} {y : L} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
  subfield.sub_mem (to_subfield S) hx hy

/-- An intermediate field is closed under negation. -/
theorem neg_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} : x ∈ S → -x ∈ S :=
  neg_mem' S

/-- An intermediate field is closed under inverses. -/
theorem inv_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} : x ∈ S → x⁻¹ ∈ S :=
  inv_mem' S

/-- An intermediate field is closed under division. -/
theorem div_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} {y : L} (hx : x ∈ S) (hy : y ∈ S) : x / y ∈ S :=
  subfield.div_mem (to_subfield S) hx hy

/-- Product of a list of elements in an intermediate_field is in the intermediate_field. -/
theorem list_prod_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {l : List L} : (∀ (x : L), x ∈ l → x ∈ S) → list.prod l ∈ S :=
  subfield.list_prod_mem (to_subfield S)

/-- Sum of a list of elements in an intermediate field is in the intermediate_field. -/
theorem list_sum_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {l : List L} : (∀ (x : L), x ∈ l → x ∈ S) → list.sum l ∈ S :=
  subfield.list_sum_mem (to_subfield S)

/-- Product of a multiset of elements in an intermediate field is in the intermediate_field. -/
theorem multiset_prod_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (m : multiset L) : (∀ (a : L), a ∈ m → a ∈ S) → multiset.prod m ∈ S :=
  subfield.multiset_prod_mem (to_subfield S) m

/-- Sum of a multiset of elements in a `intermediate_field` is in the `intermediate_field`. -/
theorem multiset_sum_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (m : multiset L) : (∀ (a : L), a ∈ m → a ∈ S) → multiset.sum m ∈ S :=
  subfield.multiset_sum_mem (to_subfield S) m

/-- Product of elements of an intermediate field indexed by a `finset` is in the intermediate_field. -/
theorem prod_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {ι : Type u_3} {t : finset ι} {f : ι → L} (h : ∀ (c : ι), c ∈ t → f c ∈ S) : (finset.prod t fun (i : ι) => f i) ∈ S :=
  subfield.prod_mem (to_subfield S) h

/-- Sum of elements in a `intermediate_field` indexed by a `finset` is in the `intermediate_field`. -/
theorem sum_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {ι : Type u_3} {t : finset ι} {f : ι → L} (h : ∀ (c : ι), c ∈ t → f c ∈ S) : (finset.sum t fun (i : ι) => f i) ∈ S :=
  subfield.sum_mem (to_subfield S) h

theorem pow_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} (hx : x ∈ S) (n : ℤ) : x ^ n ∈ S :=
  int.cases_on n (fun (n : ℕ) => is_submonoid.pow_mem hx)
    fun (n : ℕ) => subfield.inv_mem (to_subfield S) (is_submonoid.pow_mem hx)

theorem gsmul_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} (hx : x ∈ S) (n : ℤ) : n •ℤ x ∈ S :=
  subfield.gsmul_mem (to_subfield S) hx n

theorem coe_int_mem {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (n : ℤ) : ↑n ∈ S := sorry

end intermediate_field


/-- Turn a subalgebra closed under inverses into an intermediate field -/
def subalgebra.to_intermediate_field {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : subalgebra K L) (inv_mem : ∀ (x : L), x ∈ S → x⁻¹ ∈ S) : intermediate_field K L :=
  intermediate_field.mk (subalgebra.carrier S) sorry sorry sorry sorry sorry sorry inv_mem

@[simp] theorem to_subalgebra_to_intermediate_field {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : subalgebra K L) (inv_mem : ∀ (x : L), x ∈ S → x⁻¹ ∈ S) : intermediate_field.to_subalgebra (subalgebra.to_intermediate_field S inv_mem) = S :=
  subalgebra.ext
    fun (x : L) => iff.refl (x ∈ intermediate_field.to_subalgebra (subalgebra.to_intermediate_field S inv_mem))

@[simp] theorem to_intermediate_field_to_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (inv_mem : ∀ (x : L), x ∈ intermediate_field.to_subalgebra S → x⁻¹ ∈ S) : subalgebra.to_intermediate_field (intermediate_field.to_subalgebra S) inv_mem = S :=
  intermediate_field.ext
    fun (x : L) => iff.refl (x ∈ subalgebra.to_intermediate_field (intermediate_field.to_subalgebra S) inv_mem)

/-- Turn a subfield of `L` containing the image of `K` into an intermediate field -/
def subfield.to_intermediate_field {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : subfield L) (algebra_map_mem : ∀ (x : K), coe_fn (algebra_map K L) x ∈ S) : intermediate_field K L :=
  intermediate_field.mk (subfield.carrier S) (subfield.one_mem' S) (subfield.mul_mem' S) (subfield.zero_mem' S)
    (subfield.add_mem' S) algebra_map_mem (subfield.neg_mem' S) (subfield.inv_mem' S)

namespace intermediate_field


/-- An intermediate field inherits a field structure -/
protected instance to_field {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : field ↥S :=
  subfield.to_field (to_subfield S)

@[simp] theorem coe_add {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (x : ↥S) (y : ↥S) : ↑(x + y) = ↑x + ↑y :=
  rfl

@[simp] theorem coe_neg {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (x : ↥S) : ↑(-x) = -↑x :=
  rfl

@[simp] theorem coe_mul {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (x : ↥S) (y : ↥S) : ↑(x * y) = ↑x * ↑y :=
  rfl

@[simp] theorem coe_inv {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) (x : ↥S) : ↑(x⁻¹) = (↑x⁻¹) :=
  rfl

@[simp] theorem coe_zero {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : ↑0 = 0 :=
  rfl

@[simp] theorem coe_one {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : ↑1 = 1 :=
  rfl

protected instance algebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : algebra K ↥S :=
  subalgebra.algebra (to_subalgebra S)

protected instance to_algebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : algebra (↥S) L :=
  subalgebra.to_algebra (to_subalgebra S)

protected instance is_scalar_tower {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : is_scalar_tower K (↥S) L :=
  is_scalar_tower.subalgebra' K L L (to_subalgebra S)

/-- If `f : L →+* L'` fixes `K`, `S.map f` is the intermediate field between `L'` and `K`
such that `x ∈ S ↔ f x ∈ S.map f`. -/
def map {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {L' : Type u_3} [field L'] [algebra K L'] (f : alg_hom K L L') : intermediate_field K L' :=
  mk (subalgebra.carrier (subalgebra.map (to_subalgebra S) f)) sorry sorry sorry sorry sorry sorry sorry

/-- The embedding from an intermediate field of `L / K` to `L`. -/
def val {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : alg_hom K (↥S) L :=
  subalgebra.val (to_subalgebra S)

@[simp] theorem coe_val {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : ⇑(val S) = coe :=
  rfl

@[simp] theorem val_mk {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) {x : L} (hx : x ∈ S) : coe_fn (val S) { val := x, property := hx } = x :=
  rfl

theorem to_subalgebra_injective {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {S : intermediate_field K L} {S' : intermediate_field K L} (h : to_subalgebra S = to_subalgebra S') : S = S' := sorry

protected instance partial_order {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] : partial_order (intermediate_field K L) :=
  partial_order.mk (fun (S T : intermediate_field K L) => ↑S ⊆ ↑T)
    (preorder.lt._default fun (S T : intermediate_field K L) => ↑S ⊆ ↑T) sorry sorry sorry

theorem set_range_subset {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : set.range ⇑(algebra_map K L) ⊆ ↑S :=
  subalgebra.range_subset (to_subalgebra S)

theorem field_range_le {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (S : intermediate_field K L) : ring_hom.field_range (algebra_map K L) ≤ to_subfield S := sorry

@[simp] theorem to_subalgebra_le_to_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {S : intermediate_field K L} {S' : intermediate_field K L} : to_subalgebra S ≤ to_subalgebra S' ↔ S ≤ S' :=
  iff.rfl

@[simp] theorem to_subalgebra_lt_to_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {S : intermediate_field K L} {S' : intermediate_field K L} : to_subalgebra S < to_subalgebra S' ↔ S < S' :=
  iff.rfl

/-- Lift an intermediate_field of an intermediate_field -/
def lift1 {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} (E : intermediate_field K ↥F) : intermediate_field K L :=
  map E (val F)

/-- Lift an intermediate_field of an intermediate_field -/
def lift2 {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} (E : intermediate_field (↥F) L) : intermediate_field K L :=
  mk (carrier E) sorry sorry sorry sorry sorry sorry sorry

protected instance has_lift1 {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} : has_lift_t (intermediate_field K ↥F) (intermediate_field K L) :=
  has_lift_t.mk lift1

protected instance has_lift2 {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} : has_lift_t (intermediate_field (↥F) L) (intermediate_field K L) :=
  has_lift_t.mk lift2

@[simp] theorem mem_lift2 {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field (↥F) L} {x : L} : x ∈ ↑E ↔ x ∈ E :=
  iff.rfl

protected instance lift2_alg {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field (↥F) L} : algebra K ↥E :=
  algebra.mk (ring_hom.mk ⇑(ring_hom.comp (algebra_map ↥F ↥E) (algebra_map K ↥F)) sorry sorry sorry sorry) sorry sorry

protected instance lift2_tower {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field (↥F) L} : is_scalar_tower K ↥F ↥E := sorry

/-- `lift2` is isomorphic to the original `intermediate_field`. -/
def lift2_alg_equiv {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} (E : intermediate_field (↥F) L) : alg_equiv K ↥↑E ↥E :=
  alg_equiv.mk (fun (x : ↥↑E) => x) (fun (x : ↥E) => x) sorry sorry sorry sorry sorry

protected instance finite_dimensional_left {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (F : intermediate_field K L) [finite_dimensional K L] : finite_dimensional K ↥F :=
  finite_dimensional.finite_dimensional_submodule (subalgebra.to_submodule (to_subalgebra F))

protected instance finite_dimensional_right {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (F : intermediate_field K L) [finite_dimensional K L] : finite_dimensional (↥F) L :=
  finite_dimensional.right K (↥F) L

@[simp] theorem dim_eq_dim_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (F : intermediate_field K L) : vector_space.dim K ↥(to_subalgebra F) = vector_space.dim K ↥F :=
  rfl

@[simp] theorem findim_eq_findim_subalgebra {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (F : intermediate_field K L) : finite_dimensional.findim K ↥(to_subalgebra F) = finite_dimensional.findim K ↥F :=
  rfl

@[simp] theorem to_subalgebra_eq_iff {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field K L} : to_subalgebra F = to_subalgebra E ↔ F = E := sorry

theorem eq_of_le_of_findim_le {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field K L} [finite_dimensional K L] (h_le : F ≤ E) (h_findim : finite_dimensional.findim K ↥E ≤ finite_dimensional.findim K ↥F) : F = E := sorry

theorem eq_of_le_of_findim_eq {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field K L} [finite_dimensional K L] (h_le : F ≤ E) (h_findim : finite_dimensional.findim K ↥F = finite_dimensional.findim K ↥E) : F = E :=
  eq_of_le_of_findim_le h_le (eq.ge h_findim)

theorem eq_of_le_of_findim_le' {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field K L} [finite_dimensional K L] (h_le : F ≤ E) (h_findim : finite_dimensional.findim (↥F) L ≤ finite_dimensional.findim (↥E) L) : F = E := sorry

theorem eq_of_le_of_findim_eq' {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] {F : intermediate_field K L} {E : intermediate_field K L} [finite_dimensional K L] (h_le : F ≤ E) (h_findim : finite_dimensional.findim (↥F) L = finite_dimensional.findim (↥E) L) : F = E :=
  eq_of_le_of_findim_le' h_le (eq.le h_findim)

end intermediate_field


/-- If `L/K` is algebraic, the `K`-subalgebras of `L` are all fields.  -/
def subalgebra_equiv_intermediate_field {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (alg : algebra.is_algebraic K L) : subalgebra K L ≃o intermediate_field K L :=
  rel_iso.mk
    (equiv.mk (fun (S : subalgebra K L) => subalgebra.to_intermediate_field S sorry)
      (fun (S : intermediate_field K L) => intermediate_field.to_subalgebra S) sorry sorry)
    sorry

@[simp] theorem mem_subalgebra_equiv_intermediate_field {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (alg : algebra.is_algebraic K L) {S : subalgebra K L} {x : L} : x ∈ coe_fn (subalgebra_equiv_intermediate_field alg) S ↔ x ∈ S :=
  iff.rfl

@[simp] theorem mem_subalgebra_equiv_intermediate_field_symm {K : Type u_1} {L : Type u_2} [field K] [field L] [algebra K L] (alg : algebra.is_algebraic K L) {S : intermediate_field K L} {x : L} : x ∈ coe_fn (order_iso.symm (subalgebra_equiv_intermediate_field alg)) S ↔ x ∈ S :=
  iff.rfl

