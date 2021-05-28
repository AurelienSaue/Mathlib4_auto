/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.basic
import Mathlib.logic.nontrivial
import PostPort

universes u l u_1 

namespace Mathlib

/-!
# Units (i.e., invertible elements) of a multiplicative monoid
-/

/-- Units of a monoid, bundled version. An element of a `monoid` is a unit if it has a two-sided
inverse. This version bundles the inverse element so that it can be computed. For a predicate
see `is_unit`. -/
structure units (α : Type u) [monoid α] 
where
  val : α
  inv : α
  val_inv : val * inv = 1
  inv_val : inv * val = 1

/-- Units of an add_monoid, bundled version. An element of an add_monoid is a unit if it has a
    two-sided additive inverse. This version bundles the inverse element so that it can be
    computed. For a predicate see `is_add_unit`. -/
structure add_units (α : Type u) [add_monoid α] 
where
  val : α
  neg : α
  val_neg : val + neg = 0
  neg_val : neg + val = 0

namespace units


protected instance Mathlib.add_units.has_coe {α : Type u} [add_monoid α] : has_coe (add_units α) α :=
  has_coe.mk add_units.val

@[simp] theorem Mathlib.add_units.coe_mk {α : Type u} [add_monoid α] (a : α) (b : α) (h₁ : a + b = 0) (h₂ : b + a = 0) : ↑(add_units.mk a b h₁ h₂) = a :=
  rfl

theorem ext {α : Type u} [monoid α] : function.injective coe := sorry

theorem Mathlib.add_units.eq_iff {α : Type u} [add_monoid α] {a : add_units α} {b : add_units α} : ↑a = ↑b ↔ a = b :=
  function.injective.eq_iff add_units.ext

theorem Mathlib.add_units.ext_iff {α : Type u} [add_monoid α] {a : add_units α} {b : add_units α} : a = b ↔ ↑a = ↑b :=
  iff.symm add_units.eq_iff

protected instance Mathlib.add_units.decidable_eq {α : Type u} [add_monoid α] [DecidableEq α] : DecidableEq (add_units α) :=
  fun (a b : add_units α) => decidable_of_iff' (↑a = ↑b) add_units.ext_iff

@[simp] theorem mk_coe {α : Type u} [monoid α] (u : units α) (y : α) (h₁ : ↑u * y = 1) (h₂ : y * ↑u = 1) : mk (↑u) y h₁ h₂ = u :=
  ext rfl

/-- Units of a monoid form a group. -/
protected instance group {α : Type u} [monoid α] : group (units α) :=
  group.mk (fun (u₁ u₂ : units α) => mk (val u₁ * val u₂) (inv u₂ * inv u₁) sorry sorry) sorry (mk 1 1 sorry sorry) sorry
    sorry (fun (u : units α) => mk (inv u) (val u) (inv_val u) (val_inv u))
    (div_inv_monoid.div._default (fun (u₁ u₂ : units α) => mk (val u₁ * val u₂) (inv u₂ * inv u₁) sorry sorry) sorry
      (mk 1 1 sorry sorry) sorry sorry fun (u : units α) => mk (inv u) (val u) (inv_val u) (val_inv u))
    sorry

@[simp] theorem Mathlib.add_units.coe_add {α : Type u} [add_monoid α] (a : add_units α) (b : add_units α) : ↑(a + b) = ↑a + ↑b :=
  rfl

@[simp] theorem coe_one {α : Type u} [monoid α] : ↑1 = 1 :=
  rfl

@[simp] theorem Mathlib.add_units.coe_eq_zero {α : Type u} [add_monoid α] {a : add_units α} : ↑a = 0 ↔ a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑a = 0 ↔ a = 0)) (Eq.symm add_units.coe_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑a = ↑0 ↔ a = 0)) (propext add_units.eq_iff))) (iff.refl (a = 0)))

@[simp] theorem inv_mk {α : Type u} [monoid α] (x : α) (y : α) (h₁ : x * y = 1) (h₂ : y * x = 1) : mk x y h₁ h₂⁻¹ = mk y x h₂ h₁ :=
  rfl

theorem val_coe {α : Type u} [monoid α] (a : units α) : ↑a = val a :=
  rfl

theorem coe_inv {α : Type u} [monoid α] (a : units α) : ↑(a⁻¹) = inv a :=
  rfl

@[simp] theorem inv_mul {α : Type u} [monoid α] (a : units α) : ↑(a⁻¹) * ↑a = 1 :=
  inv_val a

@[simp] theorem Mathlib.add_units.add_neg {α : Type u} [add_monoid α] (a : add_units α) : ↑a + ↑(-a) = 0 :=
  add_units.val_neg a

theorem inv_mul_of_eq {α : Type u} [monoid α] {u : units α} {a : α} (h : ↑u = a) : ↑(u⁻¹) * a = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(u⁻¹) * a = 1)) (Eq.symm h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(u⁻¹) * ↑u = 1)) (inv_mul u))) (Eq.refl 1))

theorem Mathlib.add_units.add_neg_of_eq {α : Type u} [add_monoid α] {u : add_units α} {a : α} (h : ↑u = a) : a + ↑(-u) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + ↑(-u) = 0)) (Eq.symm h)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑u + ↑(-u) = 0)) (add_units.add_neg u))) (Eq.refl 0))

@[simp] theorem mul_inv_cancel_left {α : Type u} [monoid α] (a : units α) (b : α) : ↑a * (↑(a⁻¹) * b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑a * (↑(a⁻¹) * b) = b)) (Eq.symm (mul_assoc (↑a) (↑(a⁻¹)) b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑a * ↑(a⁻¹) * b = b)) (mul_inv a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 * b = b)) (one_mul b))) (Eq.refl b)))

@[simp] theorem Mathlib.add_units.neg_add_cancel_left {α : Type u} [add_monoid α] (a : add_units α) (b : α) : ↑(-a) + (↑a + b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(-a) + (↑a + b) = b)) (Eq.symm (add_assoc (↑(-a)) (↑a) b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(-a) + ↑a + b = b)) (add_units.neg_add a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + b = b)) (zero_add b))) (Eq.refl b)))

@[simp] theorem mul_inv_cancel_right {α : Type u} [monoid α] (a : α) (b : units α) : a * ↑b * ↑(b⁻¹) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * ↑b * ↑(b⁻¹) = a)) (mul_assoc a ↑b ↑(b⁻¹))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (↑b * ↑(b⁻¹)) = a)) (mul_inv b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = a)) (mul_one a))) (Eq.refl a)))

@[simp] theorem Mathlib.add_units.neg_add_cancel_right {α : Type u} [add_monoid α] (a : α) (b : add_units α) : a + ↑(-b) + ↑b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + ↑(-b) + ↑b = a)) (add_assoc a ↑(-b) ↑b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + (↑(-b) + ↑b) = a)) (add_units.neg_add b)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 = a)) (add_zero a))) (Eq.refl a)))

protected instance Mathlib.add_units.inhabited {α : Type u} [add_monoid α] : Inhabited (add_units α) :=
  { default := 0 }

protected instance comm_group {α : Type u_1} [comm_monoid α] : comm_group (units α) :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

protected instance Mathlib.add_units.has_repr {α : Type u} [add_monoid α] [has_repr α] : has_repr (add_units α) :=
  has_repr.mk (repr ∘ add_units.val)

@[simp] theorem Mathlib.add_units.add_right_inj {α : Type u} [add_monoid α] (a : add_units α) {b : α} {c : α} : ↑a + b = ↑a + c ↔ b = c := sorry

@[simp] theorem Mathlib.add_units.add_left_inj {α : Type u} [add_monoid α] (a : add_units α) {b : α} {c : α} : b + ↑a = c + ↑a ↔ b = c := sorry

theorem Mathlib.add_units.eq_add_neg_iff_add_eq {α : Type u} [add_monoid α] {c : add_units α} {a : α} {b : α} : a = b + ↑(-c) ↔ a + ↑c = b := sorry

theorem eq_inv_mul_iff_mul_eq {α : Type u} [monoid α] (b : units α) {a : α} {c : α} : a = ↑(b⁻¹) * c ↔ ↑b * a = c := sorry

theorem inv_mul_eq_iff_eq_mul {α : Type u} [monoid α] (a : units α) {b : α} {c : α} : ↑(a⁻¹) * b = c ↔ b = ↑a * c := sorry

theorem mul_inv_eq_iff_eq_mul {α : Type u} [monoid α] (b : units α) {a : α} {c : α} : a * ↑(b⁻¹) = c ↔ a = c * ↑b := sorry

theorem inv_eq_of_mul_eq_one {α : Type u} [monoid α] {u : units α} {a : α} (h : ↑u * a = 1) : ↑(u⁻¹) = a := sorry

theorem inv_unique {α : Type u} [monoid α] {u₁ : units α} {u₂ : units α} (h : ↑u₁ = ↑u₂) : ↑(u₁⁻¹) = ↑(u₂⁻¹) :=
  (fun (this : ↑u₁ * ↑(u₂⁻¹) = 1) => inv_eq_of_mul_eq_one this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑u₁ * ↑(u₂⁻¹) = 1)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑u₂ * ↑(u₂⁻¹) = 1)) (mul_inv u₂))) (Eq.refl 1)))

end units


/-- For `a, b` in a `comm_monoid` such that `a * b = 1`, makes a unit out of `a`. -/
def add_units.mk_of_add_eq_zero {α : Type u} [add_comm_monoid α] (a : α) (b : α) (hab : a + b = 0) : add_units α :=
  add_units.mk a b hab sorry

@[simp] theorem units.coe_mk_of_mul_eq_one {α : Type u} [comm_monoid α] {a : α} {b : α} (h : a * b = 1) : ↑(units.mk_of_mul_eq_one a b h) = a :=
  rfl

/-- Partial division. It is defined when the
  second argument is invertible, and unlike the division operator
  in `division_ring` it is not totalized at zero. -/
def divp {α : Type u} [monoid α] (a : α) (u : units α) : α :=
  a * ↑(u⁻¹)

infixl:70 " /ₚ " => Mathlib.divp

@[simp] theorem divp_self {α : Type u} [monoid α] (u : units α) : ↑u /ₚ u = 1 :=
  units.mul_inv u

@[simp] theorem divp_one {α : Type u} [monoid α] (a : α) : a /ₚ 1 = a :=
  mul_one a

theorem divp_assoc {α : Type u} [monoid α] (a : α) (b : α) (u : units α) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc a b ↑(u⁻¹)

@[simp] theorem divp_inv {α : Type u} [monoid α] {a : α} (u : units α) : a /ₚ (u⁻¹) = a * ↑u :=
  rfl

@[simp] theorem divp_mul_cancel {α : Type u} [monoid α] (a : α) (u : units α) : a /ₚ u * ↑u = a :=
  Eq.trans (mul_assoc a ↑(u⁻¹) ↑u)
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (↑(u⁻¹) * ↑u) = a)) (units.inv_mul u)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = a)) (mul_one a))) (Eq.refl a)))

@[simp] theorem mul_divp_cancel {α : Type u} [monoid α] (a : α) (u : units α) : a * ↑u /ₚ u = a :=
  Eq.trans (mul_assoc a ↑u ↑(u⁻¹))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (↑u * ↑(u⁻¹)) = a)) (units.mul_inv u)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a * 1 = a)) (mul_one a))) (Eq.refl a)))

@[simp] theorem divp_left_inj {α : Type u} [monoid α] (u : units α) {a : α} {b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  units.mul_left_inj (u⁻¹)

theorem divp_divp_eq_divp_mul {α : Type u} [monoid α] (x : α) (u₁ : units α) (u₂ : units α) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := sorry

theorem divp_eq_iff_mul_eq {α : Type u} [monoid α] {x : α} {u : units α} {y : α} : x /ₚ u = y ↔ y * ↑u = x :=
  iff.trans (iff.symm (units.mul_left_inj u))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x /ₚ u * ↑u = y * ↑u ↔ y * ↑u = x)) (divp_mul_cancel x u)))
      { mp := Eq.symm, mpr := Eq.symm })

theorem divp_eq_one_iff_eq {α : Type u} [monoid α] {a : α} {u : units α} : a /ₚ u = 1 ↔ a = ↑u :=
  iff.trans (iff.symm (units.mul_left_inj u))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a /ₚ u * ↑u = 1 * ↑u ↔ a = ↑u)) (divp_mul_cancel a u)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a = 1 * ↑u ↔ a = ↑u)) (one_mul ↑u))) (iff.refl (a = ↑u))))

@[simp] theorem one_divp {α : Type u} [monoid α] (u : units α) : 1 /ₚ u = ↑(u⁻¹) :=
  one_mul ↑(u⁻¹)

theorem divp_eq_divp_iff {α : Type u} [comm_monoid α] {x : α} {y : α} {ux : units α} {uy : units α} : x /ₚ ux = y /ₚ uy ↔ x * ↑uy = y * ↑ux := sorry

theorem divp_mul_divp {α : Type u} [comm_monoid α] (x : α) (y : α) (ux : units α) (uy : units α) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := sorry

/-!
# `is_unit` predicate

In this file we define the `is_unit` predicate on a `monoid`, and
prove a few basic properties. For the bundled version see `units`. See
also `prime`, `associated`, and `irreducible` in `algebra/associated`.

-/

/-- An element `a : M` of a monoid is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : units M`, where
`units M` is a bundled version of `is_unit`. -/
def is_unit {M : Type u_1} [monoid M] (a : M)  :=
  ∃ (u : units M), ↑u = a

theorem is_unit_of_subsingleton {M : Type u_1} [monoid M] [subsingleton M] (a : M) : is_unit a :=
  Exists.intro (units.mk a a (subsingleton.elim (a * a) 1) (subsingleton.elim (a * a) 1)) rfl

@[simp] theorem is_unit_unit {M : Type u_1} [monoid M] (u : units M) : is_unit ↑u :=
  Exists.intro u rfl

@[simp] theorem is_add_unit_zero {M : Type u_1} [add_monoid M] : is_add_unit 0 :=
  Exists.intro 0 rfl

theorem is_add_unit_of_add_eq_zero {M : Type u_1} [add_comm_monoid M] (a : M) (b : M) (h : a + b = 0) : is_add_unit a :=
  Exists.intro (add_units.mk_of_add_eq_zero a b h) rfl

theorem is_add_unit_iff_exists_neg {M : Type u_1} [add_comm_monoid M] {a : M} : is_add_unit a ↔ ∃ (b : M), a + b = 0 := sorry

theorem is_add_unit_iff_exists_neg' {M : Type u_1} [add_comm_monoid M] {a : M} : is_add_unit a ↔ ∃ (b : M), b + a = 0 := sorry

/-- Multiplication by a `u : units M` doesn't affect `is_unit`. -/
@[simp] theorem units.is_unit_mul_units {M : Type u_1} [monoid M] (a : M) (u : units M) : is_unit (a * ↑u) ↔ is_unit a := sorry

theorem is_unit.mul {M : Type u_1} [monoid M] {x : M} {y : M} : is_unit x → is_unit y → is_unit (x * y) := sorry

theorem is_add_unit_of_add_is_add_unit_left {M : Type u_1} [add_comm_monoid M] {x : M} {y : M} (hu : is_add_unit (x + y)) : is_add_unit x := sorry

theorem is_unit_of_mul_is_unit_right {M : Type u_1} [comm_monoid M] {x : M} {y : M} (hu : is_unit (x * y)) : is_unit y :=
  is_unit_of_mul_is_unit_left (eq.mpr (id (Eq._oldrec (Eq.refl (is_unit (y * x))) (mul_comm y x))) hu)

theorem is_unit.mul_right_inj {M : Type u_1} [monoid M] {a : M} {b : M} {c : M} (ha : is_unit a) : a * b = a * c ↔ b = c := sorry

theorem is_unit.mul_left_inj {M : Type u_1} [monoid M] {a : M} {b : M} {c : M} (ha : is_unit a) : b * a = c * a ↔ b = c := sorry

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. -/
def is_unit.unit {M : Type u_1} [monoid M] {a : M} (h : is_unit a) : units M :=
  classical.some h

theorem is_unit.unit_spec {M : Type u_1} [monoid M] {a : M} (h : is_unit a) : ↑(is_unit.unit h) = a :=
  classical.some_spec h

/-- Constructs a `group` structure on a `monoid` consisting only of units. -/
def group_of_is_unit {M : Type u_1} [hM : monoid M] (h : ∀ (a : M), is_unit a) : group M :=
  group.mk monoid.mul monoid.mul_assoc monoid.one monoid.one_mul monoid.mul_one (fun (a : M) => ↑(is_unit.unit (h a)⁻¹))
    (div_inv_monoid.div._default monoid.mul monoid.mul_assoc monoid.one monoid.one_mul monoid.mul_one
      fun (a : M) => ↑(is_unit.unit (h a)⁻¹))
    sorry

/-- Constructs a `comm_group` structure on a `comm_monoid` consisting only of units. -/
def comm_group_of_is_unit {M : Type u_1} [hM : comm_monoid M] (h : ∀ (a : M), is_unit a) : comm_group M :=
  comm_group.mk comm_monoid.mul comm_monoid.mul_assoc comm_monoid.one comm_monoid.one_mul comm_monoid.mul_one
    (fun (a : M) => ↑(is_unit.unit (h a)⁻¹))
    (group.div._default comm_monoid.mul comm_monoid.mul_assoc comm_monoid.one comm_monoid.one_mul comm_monoid.mul_one
      fun (a : M) => ↑(is_unit.unit (h a)⁻¹))
    sorry comm_monoid.mul_comm

