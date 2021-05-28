/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.ring.basic
import Mathlib.algebra.group_with_zero.default
import PostPort

universes u l u_1 u_2 

namespace Mathlib

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements -/
class division_ring (K : Type u) 
extends div_inv_monoid K, ring K, nontrivial K
where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * (a⁻¹) = 1
  inv_zero : 0⁻¹ = 0

/-- Every division ring is a `group_with_zero`. -/
protected instance division_ring.to_group_with_zero {K : Type u} [division_ring K] : group_with_zero K :=
  group_with_zero.mk division_ring.mul division_ring.mul_assoc division_ring.one division_ring.one_mul
    division_ring.mul_one division_ring.zero sorry sorry division_ring.inv division_ring.div division_ring.exists_pair_ne
    division_ring.inv_zero division_ring.mul_inv_cancel

theorem inverse_eq_has_inv {K : Type u} [division_ring K] : ring.inverse = has_inv.inv := sorry

theorem one_div_neg_one_eq_neg_one {K : Type u} [division_ring K] : 1 / -1 = -1 :=
  (fun (this : -1 * -1 = 1) => Eq.symm (eq_one_div_of_mul_eq_one this))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-1 * -1 = 1)) (neg_mul_neg 1 1)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 * 1 = 1)) (one_mul 1))) (Eq.refl 1)))

theorem one_div_neg_eq_neg_one_div {K : Type u} [division_ring K] (a : K) : 1 / -a = -(1 / a) := sorry

theorem div_neg_eq_neg_div {K : Type u} [division_ring K] (a : K) (b : K) : b / -a = -(b / a) := sorry

theorem neg_div {K : Type u} [division_ring K] (a : K) (b : K) : -b / a = -(b / a) := sorry

theorem neg_div' {K : Type u_1} [division_ring K] (a : K) (b : K) : -(b / a) = -b / a := sorry

theorem neg_div_neg_eq {K : Type u} [division_ring K] (a : K) (b : K) : -a / -b = a / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a / -b = a / b)) (div_neg_eq_neg_div b (-a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-(-a / b) = a / b)) (neg_div b a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ( --(a / b) = a / b)) (neg_neg (a / b)))) (Eq.refl (a / b))))

theorem div_add_div_same {K : Type u} [division_ring K] (a : K) (b : K) (c : K) : a / c + b / c = (a + b) / c := sorry

theorem same_add_div {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : (b + a) / b = 1 + a / b := sorry

theorem one_add_div {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  Eq.symm (same_add_div h)

theorem div_add_same {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : (a + b) / b = a / b + 1 := sorry

theorem div_add_one {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  Eq.symm (div_add_same h)

theorem div_sub_div_same {K : Type u} [division_ring K] (a : K) (b : K) (c : K) : a / c - b / c = (a - b) / c := sorry

theorem same_sub_div {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := sorry

theorem one_sub_div {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  Eq.symm (same_sub_div h)

theorem div_sub_same {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := sorry

theorem div_sub_one {K : Type u} [division_ring K] {a : K} {b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  Eq.symm (div_sub_same h)

theorem neg_inv {K : Type u} [division_ring K] {a : K} : -(a⁻¹) = (-a⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-(a⁻¹) = (-a⁻¹))) (inv_eq_one_div a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-(1 / a) = (-a⁻¹))) (inv_eq_one_div (-a))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-(1 / a) = 1 / -a)) (div_neg_eq_neg_div a 1))) (Eq.refl (-(1 / a)))))

theorem add_div {K : Type u} [division_ring K] (a : K) (b : K) (c : K) : (a + b) / c = a / c + b / c :=
  Eq.symm (div_add_div_same a b c)

theorem sub_div {K : Type u} [division_ring K] (a : K) (b : K) (c : K) : (a - b) / c = a / c - b / c :=
  Eq.symm (div_sub_div_same a b c)

theorem div_neg {K : Type u} [division_ring K] {b : K} (a : K) : a / -b = -(a / b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / -b = -(a / b))) (Eq.symm (div_neg_eq_neg_div b a)))) (Eq.refl (a / -b))

theorem inv_neg {K : Type u} [division_ring K] {a : K} : -a⁻¹ = -(a⁻¹) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a⁻¹ = -(a⁻¹))) neg_inv)) (Eq.refl (-a⁻¹))

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div {K : Type u} [division_ring K] {a : K} {b : K} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := sorry

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div {K : Type u} [division_ring K] {a : K} {b : K} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := sorry

theorem add_div_eq_mul_add_div {K : Type u} [division_ring K] (a : K) (b : K) {c : K} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  iff.mpr (eq_div_iff_mul_eq hc)
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + b / c) * c = a * c + b)) (right_distrib a (b / c) c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * c + b / c * c = a * c + b)) (div_mul_cancel b hc))) (Eq.refl (a * c + b))))

protected instance division_ring.to_domain {K : Type u} [division_ring K] : domain K :=
  domain.mk division_ring.add division_ring.add_assoc division_ring.zero division_ring.zero_add division_ring.add_zero
    division_ring.neg division_ring.sub division_ring.add_left_neg division_ring.add_comm division_ring.mul
    division_ring.mul_assoc division_ring.one division_ring.one_mul division_ring.mul_one division_ring.left_distrib
    division_ring.right_distrib division_ring.exists_pair_ne sorry

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements -/
class field (K : Type u) 
extends has_inv K, comm_ring K, nontrivial K
where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * (a⁻¹) = 1
  inv_zero : 0⁻¹ = 0

protected instance field.to_division_ring {K : Type u} [field K] : division_ring K :=
  division_ring.mk field.add sorry field.zero sorry sorry field.neg field.sub sorry sorry field.mul sorry field.one sorry
    sorry sorry sorry field.inv (div_inv_monoid.div._default field.mul sorry field.one sorry sorry field.inv) sorry sorry
    sorry

/-- Every field is a `comm_group_with_zero`. -/
protected instance field.to_comm_group_with_zero {K : Type u} [field K] : comm_group_with_zero K :=
  comm_group_with_zero.mk group_with_zero.mul sorry group_with_zero.one sorry sorry field.mul_comm group_with_zero.zero
    sorry sorry group_with_zero.inv group_with_zero.div sorry sorry sorry

theorem one_div_add_one_div {K : Type u} [field K] {a : K} {b : K} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := sorry

theorem div_add_div {K : Type u} [field K] (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) := sorry

theorem div_sub_div {K : Type u} [field K] (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d) := sorry

theorem inv_add_inv {K : Type u} [field K] {a : K} {b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + (b⁻¹) = (a + b) / (a * b) := sorry

theorem inv_sub_inv {K : Type u} [field K] {a : K} {b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - (b⁻¹) = (b - a) / (a * b) := sorry

theorem add_div' {K : Type u} [field K] (a : K) (b : K) (c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := sorry

theorem sub_div' {K : Type u} [field K] (a : K) (b : K) (c : K) (hc : c ≠ 0) : b - a / c = (b * c - a) / c := sorry

theorem div_add' {K : Type u} [field K] (a : K) (b : K) (c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := sorry

theorem div_sub' {K : Type u} [field K] (a : K) (b : K) (c : K) (hc : c ≠ 0) : a / c - b = (a - c * b) / c := sorry

protected instance field.to_integral_domain {K : Type u} [field K] : integral_domain K :=
  integral_domain.mk field.add field.add_assoc field.zero field.zero_add field.add_zero field.neg field.sub
    field.add_left_neg field.add_comm field.mul field.mul_assoc field.one field.one_mul field.mul_one field.left_distrib
    field.right_distrib field.mul_comm field.exists_pair_ne sorry

/-- A predicate to express that a ring is a field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a field. -/
structure is_field (R : Type u) [ring R] 
where
  exists_pair_ne : ∃ (x : R), ∃ (y : R), x ≠ y
  mul_comm : ∀ (x y : R), x * y = y * x
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ (b : R), a * b = 1

/-- Transferring from field to is_field -/
theorem field.to_is_field (R : Type u) [field R] : is_field R :=
  is_field.mk field.exists_pair_ne field.mul_comm fun (a : R) (ha : a ≠ 0) => Exists.intro (a⁻¹) (field.mul_inv_cancel ha)

/-- Transferring from is_field to field -/
def is_field.to_field (R : Type u) [ring R] (h : is_field R) : field R :=
  field.mk ring.add ring.add_assoc ring.zero ring.zero_add ring.add_zero ring.neg ring.sub ring.add_left_neg ring.add_comm
    ring.mul ring.mul_assoc ring.one ring.one_mul ring.mul_one ring.left_distrib ring.right_distrib (is_field.mul_comm h)
    (fun (a : R) =>
      dite (a = 0) (fun (ha : a = 0) => 0) fun (ha : ¬a = 0) => classical.some (is_field.mul_inv_cancel h ha))
    (is_field.exists_pair_ne h) sorry sorry

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_is_field (R : Type u) [ring R] (hf : is_field R) (x : R) : x ≠ 0 → exists_unique fun (y : R) => x * y = 1 := sorry

namespace ring_hom


@[simp] theorem map_units_inv {K : Type u} {R : Type u_1} [semiring R] [division_ring K] (f : R →+* K) (u : units R) : coe_fn f ↑(u⁻¹) = (coe_fn f ↑u⁻¹) :=
  monoid_hom.map_units_inv (↑f) u

theorem map_ne_zero {K : Type u} {R : Type u_1} [division_ring K] [semiring R] [nontrivial R] (f : K →+* R) {x : K} : coe_fn f x ≠ 0 ↔ x ≠ 0 :=
  monoid_with_zero_hom.map_ne_zero (to_monoid_with_zero_hom f)

@[simp] theorem map_eq_zero {K : Type u} {R : Type u_1} [division_ring K] [semiring R] [nontrivial R] (f : K →+* R) {x : K} : coe_fn f x = 0 ↔ x = 0 :=
  monoid_with_zero_hom.map_eq_zero (to_monoid_with_zero_hom f)

theorem map_inv {K : Type u} {K' : Type u_2} [division_ring K] [division_ring K'] (g : K →+* K') (x : K) : coe_fn g (x⁻¹) = (coe_fn g x⁻¹) :=
  monoid_with_zero_hom.map_inv' (to_monoid_with_zero_hom g) x

theorem map_div {K : Type u} {K' : Type u_2} [division_ring K] [division_ring K'] (g : K →+* K') (x : K) (y : K) : coe_fn g (x / y) = coe_fn g x / coe_fn g y :=
  monoid_with_zero_hom.map_div (to_monoid_with_zero_hom g) x y

protected theorem injective {K : Type u} {R : Type u_1} [division_ring K] [semiring R] [nontrivial R] (f : K →+* R) : function.injective ⇑f :=
  iff.mpr (injective_iff f) fun (x : K) => iff.mp (map_eq_zero f)

end ring_hom


/-- Constructs a `division_ring` structure on a `ring` consisting only of units and 0. -/
def division_ring_of_is_unit_or_eq_zero {R : Type u_1} [nontrivial R] [hR : ring R] (h : ∀ (a : R), is_unit a ∨ a = 0) : division_ring R :=
  division_ring.mk ring.add ring.add_assoc group_with_zero.zero ring.zero_add ring.add_zero ring.neg ring.sub
    ring.add_left_neg ring.add_comm group_with_zero.mul sorry group_with_zero.one sorry sorry ring.left_distrib
    ring.right_distrib group_with_zero.inv group_with_zero.div sorry sorry sorry

/-- Constructs a `field` structure on a `comm_ring` consisting only of units and 0. -/
def field_of_is_unit_or_eq_zero {R : Type u_1} [nontrivial R] [hR : comm_ring R] (h : ∀ (a : R), is_unit a ∨ a = 0) : field R :=
  field.mk comm_ring.add comm_ring.add_assoc group_with_zero.zero comm_ring.zero_add comm_ring.add_zero comm_ring.neg
    comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm group_with_zero.mul sorry group_with_zero.one sorry sorry
    comm_ring.left_distrib comm_ring.right_distrib comm_ring.mul_comm group_with_zero.inv sorry sorry sorry

