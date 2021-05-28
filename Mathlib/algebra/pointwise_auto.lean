/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.module.basic
import Mathlib.data.set.finite
import Mathlib.group_theory.submonoid.basic
import PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Pointwise addition, multiplication, and scalar multiplication of sets.

This file defines pointwise algebraic operations on sets.
* For a type `α` with multiplication, multiplication is defined on `set α` by taking
  `s * t` to be the set of all `x * y` where `x ∈ s` and `y ∈ t`. Similarly for addition.
* For `α` a semigroup, `set α` is a semigroup.
* If `α` is a (commutative) monoid, we define an alias `set_semiring α` for `set α`, which then
  becomes a (commutative) semiring with union as addition and pointwise multiplication as
  multiplication.
* For a type `β` with scalar multiplication by another type `α`, this
  file defines a scalar multiplication of `set β` by `set α` and a separate scalar
  multiplication of `set β` by `α`.
* We also define pointwise multiplication on `finset`.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes
* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication

-/

namespace set


/-! ### Properties about 1 -/

protected instance has_one {α : Type u_1} [HasOne α] : HasOne (set α) :=
  { one := singleton 1 }

theorem singleton_one {α : Type u_1} [HasOne α] : singleton 1 = 1 :=
  rfl

@[simp] theorem mem_zero {α : Type u_1} {a : α} [HasZero α] : a ∈ 0 ↔ a = 0 :=
  iff.rfl

theorem one_mem_one {α : Type u_1} [HasOne α] : 1 ∈ 1 :=
  Eq.refl 1

@[simp] theorem zero_subset {α : Type u_1} {s : set α} [HasZero α] : 0 ⊆ s ↔ 0 ∈ s :=
  singleton_subset_iff

theorem zero_nonempty {α : Type u_1} [HasZero α] : set.nonempty 0 :=
  Exists.intro 0 rfl

@[simp] theorem image_zero {α : Type u_1} {β : Type u_2} [HasZero α] {f : α → β} : f '' 0 = singleton (f 0) :=
  image_singleton

/-! ### Properties about multiplication -/

protected instance has_add {α : Type u_1} [Add α] : Add (set α) :=
  { add := image2 Add.add }

@[simp] theorem image2_mul {α : Type u_1} {s : set α} {t : set α} [Mul α] : image2 Mul.mul s t = s * t :=
  rfl

theorem mem_add {α : Type u_1} {s : set α} {t : set α} {a : α} [Add α] : a ∈ s + t ↔ ∃ (x : α), ∃ (y : α), x ∈ s ∧ y ∈ t ∧ x + y = a :=
  iff.rfl

theorem mul_mem_mul {α : Type u_1} {s : set α} {t : set α} {a : α} {b : α} [Mul α] (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t :=
  mem_image2_of_mem ha hb

theorem add_image_prod {α : Type u_1} {s : set α} {t : set α} [Add α] : (fun (x : α × α) => prod.fst x + prod.snd x) '' set.prod s t = s + t :=
  image_prod Add.add

@[simp] theorem image_mul_left {α : Type u_1} {t : set α} {a : α} [group α] : (fun (b : α) => a * b) '' t = (fun (b : α) => a⁻¹ * b) ⁻¹' t := sorry

@[simp] theorem image_add_right {α : Type u_1} {t : set α} {b : α} [add_group α] : (fun (a : α) => a + b) '' t = (fun (a : α) => a + -b) ⁻¹' t := sorry

theorem image_add_left' {α : Type u_1} {t : set α} {a : α} [add_group α] : (fun (b : α) => -a + b) '' t = (fun (b : α) => a + b) ⁻¹' t := sorry

theorem image_mul_right' {α : Type u_1} {t : set α} {b : α} [group α] : (fun (a : α) => a * (b⁻¹)) '' t = (fun (a : α) => a * b) ⁻¹' t := sorry

@[simp] theorem preimage_add_left_singleton {α : Type u_1} {a : α} {b : α} [add_group α] : Add.add a ⁻¹' singleton b = singleton (-a + b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Add.add a ⁻¹' singleton b = singleton (-a + b))) (Eq.symm image_add_left')))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((fun (b : α) => -a + b) '' singleton b = singleton (-a + b))) image_singleton))
      (Eq.refl (singleton (-a + b))))

@[simp] theorem preimage_mul_right_singleton {α : Type u_1} {a : α} {b : α} [group α] : (fun (_x : α) => _x * a) ⁻¹' singleton b = singleton (b * (a⁻¹)) := sorry

@[simp] theorem preimage_add_left_zero {α : Type u_1} {a : α} [add_group α] : (fun (b : α) => a + b) ⁻¹' 0 = singleton (-a) := sorry

@[simp] theorem preimage_mul_right_one {α : Type u_1} {b : α} [group α] : (fun (a : α) => a * b) ⁻¹' 1 = singleton (b⁻¹) := sorry

theorem preimage_add_left_zero' {α : Type u_1} {a : α} [add_group α] : (fun (b : α) => -a + b) ⁻¹' 0 = singleton a := sorry

theorem preimage_add_right_zero' {α : Type u_1} {b : α} [add_group α] : (fun (a : α) => a + -b) ⁻¹' 0 = singleton b := sorry

@[simp] theorem mul_singleton {α : Type u_1} {s : set α} {b : α} [Mul α] : s * singleton b = (fun (a : α) => a * b) '' s :=
  image2_singleton_right

@[simp] theorem singleton_add {α : Type u_1} {t : set α} {a : α} [Add α] : singleton a + t = (fun (b : α) => a + b) '' t :=
  image2_singleton_left

@[simp] theorem singleton_add_singleton {α : Type u_1} {a : α} {b : α} [Add α] : singleton a + singleton b = singleton (a + b) :=
  image2_singleton

protected instance semigroup {α : Type u_1} [semigroup α] : semigroup (set α) :=
  semigroup.mk Mul.mul sorry

protected instance monoid {α : Type u_1} [monoid α] : monoid (set α) :=
  monoid.mk semigroup.mul sorry 1 sorry sorry

protected theorem mul_comm {α : Type u_1} {s : set α} {t : set α} [comm_semigroup α] : s * t = t * s := sorry

protected instance add_comm_monoid {α : Type u_1} [add_comm_monoid α] : add_comm_monoid (set α) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

theorem singleton.is_mul_hom {α : Type u_1} [Mul α] : is_mul_hom singleton :=
  is_mul_hom.mk fun (a b : α) => Eq.symm singleton_mul_singleton

@[simp] theorem empty_add {α : Type u_1} {s : set α} [Add α] : ∅ + s = ∅ :=
  image2_empty_left

@[simp] theorem mul_empty {α : Type u_1} {s : set α} [Mul α] : s * ∅ = ∅ :=
  image2_empty_right

theorem add_subset_add {α : Type u_1} {s₁ : set α} {s₂ : set α} {t₁ : set α} {t₂ : set α} [Add α] (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ + s₂ ⊆ t₁ + t₂ :=
  image2_subset h₁ h₂

theorem union_add {α : Type u_1} {s : set α} {t : set α} {u : set α} [Add α] : s ∪ t + u = s + u ∪ (t + u) :=
  image2_union_left

theorem mul_union {α : Type u_1} {s : set α} {t : set α} {u : set α} [Mul α] : s * (t ∪ u) = s * t ∪ s * u :=
  image2_union_right

theorem Union_mul_left_image {α : Type u_1} {s : set α} {t : set α} [Mul α] : (Union fun (a : α) => Union fun (H : a ∈ s) => (fun (x : α) => a * x) '' t) = s * t :=
  Union_image_left fun (a x : α) => a * x

theorem Union_mul_right_image {α : Type u_1} {s : set α} {t : set α} [Mul α] : (Union fun (a : α) => Union fun (H : a ∈ t) => (fun (x : α) => x * a) '' s) = s * t :=
  Union_image_right fun (x a : α) => x * a

@[simp] theorem univ_mul_univ {α : Type u_1} [monoid α] : univ * univ = univ := sorry

/-- `singleton` is a monoid hom. -/
def singleton_add_hom {α : Type u_1} [add_monoid α] : α →+ set α :=
  add_monoid_hom.mk singleton sorry sorry

theorem nonempty.add {α : Type u_1} {s : set α} {t : set α} [Add α] : set.nonempty s → set.nonempty t → set.nonempty (s + t) :=
  nonempty.image2

theorem finite.mul {α : Type u_1} {s : set α} {t : set α} [Mul α] (hs : finite s) (ht : finite t) : finite (s * t) :=
  finite.image2 (fun (a b : α) => a * b) hs ht

/-- multiplication preserves finiteness -/
def fintype_mul {α : Type u_1} [Mul α] [DecidableEq α] (s : set α) (t : set α) [hs : fintype ↥s] [ht : fintype ↥t] : fintype ↥(s * t) :=
  set.fintype_image2 (fun (a b : α) => a * b) s t

theorem bdd_above_add {α : Type u_1} [ordered_add_comm_monoid α] {A : set α} {B : set α} : bdd_above A → bdd_above B → bdd_above (A + B) := sorry

/-! ### Properties about inversion -/

protected instance has_inv {α : Type u_1} [has_inv α] : has_inv (set α) :=
  has_inv.mk (preimage has_inv.inv)

@[simp] theorem mem_inv {α : Type u_1} {s : set α} {a : α} [has_inv α] : a ∈ (s⁻¹) ↔ a⁻¹ ∈ s :=
  iff.rfl

theorem inv_mem_inv {α : Type u_1} {s : set α} {a : α} [group α] : a⁻¹ ∈ (s⁻¹) ↔ a ∈ s := sorry

@[simp] theorem inv_preimage {α : Type u_1} {s : set α} [has_inv α] : has_inv.inv ⁻¹' s = (s⁻¹) :=
  rfl

@[simp] theorem image_inv {α : Type u_1} {s : set α} [group α] : has_inv.inv '' s = (s⁻¹) := sorry

@[simp] theorem inter_neg {α : Type u_1} {s : set α} {t : set α} [Neg α] : -(s ∩ t) = -s ∩ -t :=
  preimage_inter

@[simp] theorem union_neg {α : Type u_1} {s : set α} {t : set α} [Neg α] : -(s ∪ t) = -s ∪ -t :=
  preimage_union

@[simp] theorem compl_inv {α : Type u_1} {s : set α} [has_inv α] : sᶜ⁻¹ = (s⁻¹ᶜ) :=
  preimage_compl

@[simp] protected theorem inv_inv {α : Type u_1} {s : set α} [group α] : s⁻¹⁻¹ = s := sorry

@[simp] protected theorem univ_inv {α : Type u_1} [group α] : univ⁻¹ = univ :=
  preimage_univ

@[simp] theorem neg_subset_neg {α : Type u_1} [add_group α] {s : set α} {t : set α} : -s ⊆ -t ↔ s ⊆ t :=
  function.surjective.preimage_subset_preimage_iff (equiv.surjective (equiv.neg α))

theorem neg_subset {α : Type u_1} [add_group α] {s : set α} {t : set α} : -s ⊆ t ↔ s ⊆ -t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-s ⊆ t ↔ s ⊆ -t)) (Eq.symm (propext neg_subset_neg))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ( --s ⊆ -t ↔ s ⊆ -t)) set.neg_neg)) (iff.refl (s ⊆ -t)))

/-! ### Properties about scalar multiplication -/

/-- Scaling a set: multiplying every element by a scalar. -/
protected instance has_scalar_set {α : Type u_1} {β : Type u_2} [has_scalar α β] : has_scalar α (set β) :=
  has_scalar.mk fun (a : α) => image (has_scalar.smul a)

@[simp] theorem image_smul {α : Type u_1} {β : Type u_2} {a : α} [has_scalar α β] {t : set β} : (fun (x : β) => a • x) '' t = a • t :=
  rfl

theorem mem_smul_set {α : Type u_1} {β : Type u_2} {a : α} {x : β} [has_scalar α β] {t : set β} : x ∈ a • t ↔ ∃ (y : β), y ∈ t ∧ a • y = x :=
  iff.rfl

theorem smul_mem_smul_set {α : Type u_1} {β : Type u_2} {a : α} {y : β} [has_scalar α β] {t : set β} (hy : y ∈ t) : a • y ∈ a • t :=
  Exists.intro y { left := hy, right := rfl }

theorem smul_set_union {α : Type u_1} {β : Type u_2} {a : α} [has_scalar α β] {s : set β} {t : set β} : a • (s ∪ t) = a • s ∪ a • t := sorry

@[simp] theorem smul_set_empty {α : Type u_1} {β : Type u_2} [has_scalar α β] (a : α) : a • ∅ = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a • ∅ = ∅)) (Eq.symm image_smul)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((fun (x : β) => a • x) '' ∅ = ∅)) (image_empty fun (x : β) => a • x))) (Eq.refl ∅))

theorem smul_set_mono {α : Type u_1} {β : Type u_2} {a : α} [has_scalar α β] {s : set β} {t : set β} (h : s ⊆ t) : a • s ⊆ a • t := sorry

/-- Pointwise scalar multiplication by a set of scalars. -/
protected instance has_scalar {α : Type u_1} {β : Type u_2} [has_scalar α β] : has_scalar (set α) (set β) :=
  has_scalar.mk (image2 has_scalar.smul)

@[simp] theorem image2_smul {α : Type u_1} {β : Type u_2} {s : set α} [has_scalar α β] {t : set β} : image2 has_scalar.smul s t = s • t :=
  rfl

theorem mem_smul {α : Type u_1} {β : Type u_2} {s : set α} {x : β} [has_scalar α β] {t : set β} : x ∈ s • t ↔ ∃ (a : α), ∃ (y : β), a ∈ s ∧ y ∈ t ∧ a • y = x :=
  iff.rfl

theorem image_smul_prod {α : Type u_1} {β : Type u_2} {s : set α} [has_scalar α β] {t : set β} : (fun (x : α × β) => prod.fst x • prod.snd x) '' set.prod s t = s • t :=
  image_prod has_scalar.smul

theorem range_smul_range {α : Type u_1} {β : Type u_2} [has_scalar α β] {ι : Type u_3} {κ : Type u_4} (b : ι → α) (c : κ → β) : range b • range c = range fun (p : ι × κ) => b (prod.fst p) • c (prod.snd p) := sorry

theorem singleton_smul {α : Type u_1} {β : Type u_2} {a : α} [has_scalar α β] {t : set β} : singleton a • t = a • t :=
  image2_singleton_left

/-! ### `set α` as a `(∪,*)`-semiring -/

/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
def set_semiring (α : Type u_1)  :=
  set α

/-- The identitiy function `set α → set_semiring α`. -/
/-- The identitiy function `set_semiring α → set α`. -/
protected def up {α : Type u_1} (s : set α) : set_semiring α :=
  s

protected def set_semiring.down {α : Type u_1} (s : set_semiring α) : set α :=
  s

@[simp] protected theorem down_up {α : Type u_1} {s : set α} : set_semiring.down (set.up s) = s :=
  rfl

@[simp] protected theorem up_down {α : Type u_1} {s : set_semiring α} : set.up (set_semiring.down s) = s :=
  rfl

protected instance set_semiring.semiring {α : Type u_1} [monoid α] : semiring (set_semiring α) :=
  semiring.mk (fun (s t : set_semiring α) => s ∪ t) union_assoc ∅ empty_union union_empty union_comm monoid.mul sorry
    monoid.one sorry sorry sorry sorry sorry sorry

protected instance set_semiring.comm_semiring {α : Type u_1} [comm_monoid α] : comm_semiring (set_semiring α) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry comm_monoid.mul sorry comm_monoid.one sorry sorry
    sorry sorry sorry sorry sorry

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
protected instance mul_action_set {α : Type u_1} {β : Type u_2} [monoid α] [mul_action α β] : mul_action α (set β) :=
  mul_action.mk sorry sorry

theorem image_add {α : Type u_1} {β : Type u_2} {s : set α} {t : set α} [Add α] [Add β] (m : α → β) [is_add_hom m] : m '' (s + t) = m '' s + m '' t := sorry

theorem preimage_mul_preimage_subset {α : Type u_1} {β : Type u_2} [Mul α] [Mul β] (m : α → β) [is_mul_hom m] {s : set β} {t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) := sorry

/-- The image of a set under function is a ring homomorphism
with respect to the pointwise operations on sets. -/
def image_hom {α : Type u_1} {β : Type u_2} [monoid α] [monoid β] (f : α →* β) : set_semiring α →+* set_semiring β :=
  ring_hom.mk (image ⇑f) sorry sorry sorry sorry

end set


/-- A nonempty set in a semimodule is scaled by zero to the singleton
containing 0 in the semimodule. -/
theorem zero_smul_set {α : Type u_1} {β : Type u_2} [semiring α] [add_comm_monoid β] [semimodule α β] {s : set β} (h : set.nonempty s) : 0 • s = 0 := sorry

theorem mem_inv_smul_set_iff {α : Type u_1} {β : Type u_2} [field α] [mul_action α β] {a : α} (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A := sorry

theorem mem_smul_set_iff_inv_smul_mem {α : Type u_1} {β : Type u_2} [field α] [mul_action α β] {a : α} (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (x ∈ a • A ↔ a⁻¹ • x ∈ A)) (Eq.symm (propext (mem_inv_smul_set_iff (inv_ne_zero ha) A x)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ a • A ↔ x ∈ a⁻¹⁻¹ • A)) (inv_inv' a))) (iff.refl (x ∈ a • A)))

namespace finset


/-- The pointwise product of two finite sets `s` and `t`:
  `st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
protected instance has_add {α : Type u_1} [DecidableEq α] [Add α] : Add (finset α) :=
  { add := fun (s t : finset α) => image (fun (p : α × α) => prod.fst p + prod.snd p) (finset.product s t) }

theorem mul_def {α : Type u_1} [DecidableEq α] [Mul α] {s : finset α} {t : finset α} : s * t = image (fun (p : α × α) => prod.fst p * prod.snd p) (finset.product s t) :=
  rfl

theorem mem_add {α : Type u_1} [DecidableEq α] [Add α] {s : finset α} {t : finset α} {x : α} : x ∈ s + t ↔ ∃ (y : α), ∃ (z : α), y ∈ s ∧ z ∈ t ∧ y + z = x := sorry

@[simp] theorem coe_add {α : Type u_1} [DecidableEq α] [Add α] {s : finset α} {t : finset α} : ↑(s + t) = ↑s + ↑t := sorry

theorem mul_mem_mul {α : Type u_1} [DecidableEq α] [Mul α] {s : finset α} {t : finset α} {x : α} {y : α} (hx : x ∈ s) (hy : y ∈ t) : x * y ∈ s * t :=
  eq.mpr (id (propext mem_mul)) (Exists.intro x (Exists.intro y { left := hx, right := { left := hy, right := rfl } }))

theorem add_card_le {α : Type u_1} [DecidableEq α] [Add α] {s : finset α} {t : finset α} : card (s + t) ≤ card s * card t := sorry

theorem mul_card_le {α : Type u_1} [DecidableEq α] [Mul α] {s : finset α} {t : finset α} : card (s * t) ≤ card s * card t := sorry

/-- A finite set `U` contained in the product of two sets `S * S'` is also contained in the product
of two finite sets `T * T' ⊆ S * S'`. -/
theorem subset_add {M : Type u_1} [add_monoid M] {S : set M} {S' : set M} {U : finset M} (f : ↑U ⊆ S + S') : ∃ (T : finset M), ∃ (T' : finset M), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ U ⊆ T + T' := sorry

end finset


/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/

namespace submonoid


theorem mul_subset {M : Type u_1} [monoid M] {s : set M} {t : set M} {S : submonoid M} (hs : s ⊆ ↑S) (ht : t ⊆ ↑S) : s * t ⊆ ↑S := sorry

theorem mul_subset_closure {M : Type u_1} [monoid M] {s : set M} {t : set M} {u : set M} (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ ↑(closure u) :=
  mul_subset (set.subset.trans hs subset_closure) (set.subset.trans ht subset_closure)

theorem Mathlib.add_submonoid.coe_add_self_eq {M : Type u_1} [add_monoid M] (s : add_submonoid M) : ↑s + ↑s = ↑s := sorry

