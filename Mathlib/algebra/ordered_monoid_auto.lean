/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.with_one
import Mathlib.algebra.group.type_tags
import Mathlib.algebra.group.prod
import Mathlib.algebra.order_functions
import Mathlib.order.bounded_lattice
import PostPort

universes u_1 l u u_2 

namespace Mathlib

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

-/

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that
  * `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
  * `a * b < a * c → b < c`.
-/
class ordered_comm_monoid (α : Type u_1) 
extends partial_order α, comm_monoid α
where
  mul_le_mul_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c * a ≤ c * b
  lt_of_mul_lt_mul_left : ∀ (a b c : α), a * b < a * c → b < c

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that
  * `a ≤ b → c + a ≤ c + b` (addition is monotone)
  * `a + b < a + c → b < c`.
-/
class ordered_add_comm_monoid (α : Type u_1) 
extends partial_order α, add_comm_monoid α
where
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c + a ≤ c + b
  lt_of_add_lt_add_left : ∀ (a b c : α), a + b < a + c → b < c

/-- A linearly ordered commutative monoid with a zero element. -/
class linear_ordered_comm_monoid_with_zero (α : Type u_1) 
extends ordered_comm_monoid α, comm_monoid_with_zero α, linear_order α
where
  zero_le_one : 0 ≤ 1

theorem mul_le_mul_left' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (h : a ≤ b) (c : α) : c * a ≤ c * b :=
  ordered_comm_monoid.mul_le_mul_left a b h c

theorem add_le_add_right {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} (h : a ≤ b) (c : α) : a + c ≤ b + c := sorry

theorem lt_of_add_lt_add_left {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} : a + b < a + c → b < c :=
  ordered_add_comm_monoid.lt_of_add_lt_add_left a b c

theorem mul_le_mul' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} {d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  has_le.le.trans (mul_le_mul_right' h₁ c) (mul_le_mul_left' h₂ b)

theorem mul_le_mul_three {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} {d : α} {e : α} {f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃

theorem le_mul_of_one_le_right' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (h : 1 ≤ b) : a ≤ a * b :=
  (fun (this : a * 1 ≤ a * b) => eq.mp (Eq._oldrec (Eq.refl (a * 1 ≤ a * b)) (mul_one a)) this) (mul_le_mul_left' h a)

theorem le_mul_of_one_le_left' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (h : 1 ≤ b) : a ≤ b * a :=
  (fun (this : 1 * a ≤ b * a) => eq.mp (Eq._oldrec (Eq.refl (1 * a ≤ b * a)) (one_mul a)) this) (mul_le_mul_right' h a)

theorem lt_of_mul_lt_mul_right' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (h : a * b < c * b) : a < c := sorry

-- here we start using properties of one.

theorem le_add_of_nonneg_of_le {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} (ha : 0 ≤ a) (hbc : b ≤ c) : b ≤ a + c :=
  zero_add b ▸ add_le_add ha hbc

theorem le_add_of_le_of_nonneg {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b ≤ c) (ha : 0 ≤ a) : b ≤ c + a :=
  add_zero b ▸ add_le_add hbc ha

theorem add_nonneg {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
  le_add_of_nonneg_of_le ha hb

theorem one_lt_mul_of_lt_of_le' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  lt_of_lt_of_le ha (le_mul_of_one_le_right' hb)

theorem add_pos_of_nonneg_of_pos {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b :=
  lt_of_lt_of_le hb (le_add_of_nonneg_left ha)

theorem one_lt_mul' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  one_lt_mul_of_lt_of_le' ha (has_lt.lt.le hb)

theorem mul_le_one' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  one_mul 1 ▸ mul_le_mul' ha hb

theorem mul_le_of_le_one_of_le' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
  one_mul c ▸ mul_le_mul' ha hbc

theorem mul_le_of_le_of_le_one' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
  mul_one c ▸ mul_le_mul' hbc ha

theorem mul_lt_one_of_lt_one_of_le_one' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  has_le.le.trans_lt (mul_le_of_le_of_le_one' le_rfl hb) ha

theorem mul_lt_one_of_le_one_of_lt_one' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  has_le.le.trans_lt (mul_le_of_le_one_of_le' ha le_rfl) hb

theorem mul_lt_one' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_one_of_le_one_of_lt_one' (has_lt.lt.le ha) hb

theorem lt_add_of_nonneg_of_lt' {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} (ha : 0 ≤ a) (hbc : b < c) : b < a + c :=
  has_lt.lt.trans_le hbc (le_add_of_nonneg_left ha)

theorem lt_mul_of_lt_of_one_le' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
  has_lt.lt.trans_le hbc (le_mul_of_one_le_right' ha)

theorem lt_add_of_pos_of_lt' {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} (ha : 0 < a) (hbc : b < c) : b < a + c :=
  lt_add_of_nonneg_of_lt' (has_lt.lt.le ha) hbc

theorem lt_add_of_lt_of_pos' {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : 0 < a) : b < c + a :=
  lt_add_of_lt_of_nonneg' hbc (has_lt.lt.le ha)

theorem mul_lt_of_le_one_of_lt' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
  lt_of_le_of_lt (mul_le_of_le_one_of_le' ha le_rfl) hbc

theorem mul_lt_of_lt_of_le_one' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : a ≤ 1) : b * a < c :=
  lt_of_le_of_lt (mul_le_of_le_of_le_one' le_rfl ha) hbc

theorem mul_lt_of_lt_one_of_lt' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} {c : α} (ha : a < 1) (hbc : b < c) : a * b < c :=
  mul_lt_of_le_one_of_lt' (has_lt.lt.le ha) hbc

theorem add_lt_of_lt_of_neg' {α : Type u} [ordered_add_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : a < 0) : b + a < c :=
  add_lt_of_lt_of_nonpos' hbc (has_lt.lt.le ha)

theorem mul_eq_one_iff' {α : Type u} [ordered_comm_monoid α] {a : α} {b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 := sorry

theorem monotone.mul' {α : Type u} [ordered_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} {g : β → α} (hf : monotone f) (hg : monotone g) : monotone fun (x : β) => f x * g x :=
  fun (x y : β) (h : x ≤ y) => mul_le_mul' (hf h) (hg h)

theorem monotone.mul_const' {α : Type u} [ordered_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} (hf : monotone f) (a : α) : monotone fun (x : β) => f x * a :=
  monotone.mul' hf monotone_const

theorem monotone.const_mul' {α : Type u} [ordered_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} (hf : monotone f) (a : α) : monotone fun (x : β) => a * f x :=
  monotone.mul' monotone_const hf

theorem bit0_pos {α : Type u} [ordered_add_comm_monoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos h h

namespace units


protected instance Mathlib.add_units.preorder {α : Type u} [add_monoid α] [preorder α] : preorder (add_units α) :=
  preorder.lift coe

@[simp] theorem Mathlib.add_units.coe_le_coe {α : Type u} [add_monoid α] [preorder α] {a : add_units α} {b : add_units α} : ↑a ≤ ↑b ↔ a ≤ b :=
  iff.rfl

-- should `to_additive` do this?

@[simp] theorem Mathlib.add_units.coe_lt_coe {α : Type u} [add_monoid α] [preorder α] {a : add_units α} {b : add_units α} : ↑a < ↑b ↔ a < b :=
  iff.rfl

protected instance partial_order {α : Type u} [monoid α] [partial_order α] : partial_order (units α) :=
  partial_order.lift coe ext

protected instance linear_order {α : Type u} [monoid α] [linear_order α] : linear_order (units α) :=
  linear_order.lift coe ext

@[simp] theorem Mathlib.add_units.max_coe {α : Type u} [add_monoid α] [linear_order α] {a : add_units α} {b : add_units α} : ↑(max a b) = max ↑a ↑b := sorry

@[simp] theorem Mathlib.add_units.min_coe {α : Type u} [add_monoid α] [linear_order α] {a : add_units α} {b : add_units α} : ↑(min a b) = min ↑a ↑b := sorry

end units


namespace with_zero


protected instance preorder {α : Type u} [preorder α] : preorder (with_zero α) :=
  with_bot.preorder

protected instance partial_order {α : Type u} [partial_order α] : partial_order (with_zero α) :=
  with_bot.partial_order

protected instance order_bot {α : Type u} [partial_order α] : order_bot (with_zero α) :=
  with_bot.order_bot

theorem zero_le {α : Type u} [partial_order α] (a : with_zero α) : 0 ≤ a :=
  order_bot.bot_le a

theorem zero_lt_coe {α : Type u} [partial_order α] (a : α) : 0 < ↑a :=
  with_bot.bot_lt_coe a

@[simp] theorem coe_lt_coe {α : Type u} [partial_order α] {a : α} {b : α} : ↑a < ↑b ↔ a < b :=
  with_bot.coe_lt_coe

@[simp] theorem coe_le_coe {α : Type u} [partial_order α] {a : α} {b : α} : ↑a ≤ ↑b ↔ a ≤ b :=
  with_bot.coe_le_coe

protected instance lattice {α : Type u} [lattice α] : lattice (with_zero α) :=
  with_bot.lattice

protected instance linear_order {α : Type u} [linear_order α] : linear_order (with_zero α) :=
  with_bot.linear_order

theorem mul_le_mul_left {α : Type u} [ordered_comm_monoid α] (a : with_zero α) (b : with_zero α) : a ≤ b → ∀ (c : with_zero α), c * a ≤ c * b := sorry

theorem lt_of_mul_lt_mul_left {α : Type u} [ordered_comm_monoid α] (a : with_zero α) (b : with_zero α) (c : with_zero α) : a * b < a * c → b < c := sorry

protected instance ordered_comm_monoid {α : Type u} [ordered_comm_monoid α] : ordered_comm_monoid (with_zero α) :=
  ordered_comm_monoid.mk comm_monoid_with_zero.mul sorry comm_monoid_with_zero.one sorry sorry sorry partial_order.le
    partial_order.lt sorry sorry sorry mul_le_mul_left lt_of_mul_lt_mul_left

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.

Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
-/
def ordered_add_comm_monoid {α : Type u} [ordered_add_comm_monoid α] (zero_le : ∀ (a : α), 0 ≤ a) : ordered_add_comm_monoid (with_zero α) :=
  ordered_add_comm_monoid.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry partial_order.le
    partial_order.lt sorry sorry sorry sorry sorry

end with_zero


namespace with_top


protected instance has_zero {α : Type u} [HasZero α] : HasZero (with_top α) :=
  { zero := ↑0 }

@[simp] theorem coe_one {α : Type u} [HasOne α] : ↑1 = 1 :=
  rfl

@[simp] theorem coe_eq_one {α : Type u} [HasOne α] {a : α} : ↑a = 1 ↔ a = 1 :=
  coe_eq_coe

@[simp] theorem one_eq_coe {α : Type u} [HasOne α] {a : α} : 1 = ↑a ↔ a = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 = ↑a ↔ a = 1)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑a = 1 ↔ a = 1)) (propext coe_eq_one))) (iff.refl (a = 1)))

@[simp] theorem top_ne_one {α : Type u} [HasOne α] : ⊤ ≠ 1 :=
  fun (ᾰ : ⊤ = 1) => eq.dcases_on ᾰ (fun (a : some 1 = none) => option.no_confusion a) (Eq.refl 1) (HEq.refl ᾰ)

@[simp] theorem one_ne_top {α : Type u} [HasOne α] : 1 ≠ ⊤ :=
  fun (ᾰ : 1 = ⊤) => eq.dcases_on ᾰ (fun (a : none = some 1) => option.no_confusion a) (Eq.refl ⊤) (HEq.refl ᾰ)

protected instance has_add {α : Type u} [Add α] : Add (with_top α) :=
  { add := fun (o₁ o₂ : with_top α) => option.bind o₁ fun (a : α) => option.map (fun (b : α) => a + b) o₂ }

protected instance add_semigroup {α : Type u} [add_semigroup α] : add_semigroup (with_top α) :=
  add_semigroup.mk Add.add sorry

theorem coe_add {α : Type u} [Add α] {a : α} {b : α} : ↑(a + b) = ↑a + ↑b :=
  rfl

theorem coe_bit0 {α : Type u} [Add α] {a : α} : ↑(bit0 a) = bit0 ↑a :=
  rfl

theorem coe_bit1 {α : Type u} [Add α] [HasOne α] {a : α} : ↑(bit1 a) = bit1 ↑a :=
  rfl

@[simp] theorem add_top {α : Type u} [Add α] {a : with_top α} : a + ⊤ = ⊤ :=
  option.cases_on a (idRhs (none + ⊤ = none + ⊤) rfl) fun (a : α) => idRhs (some a + ⊤ = some a + ⊤) rfl

@[simp] theorem top_add {α : Type u} [Add α] {a : with_top α} : ⊤ + a = ⊤ :=
  rfl

theorem add_eq_top {α : Type u} [Add α] {a : with_top α} {b : with_top α} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := sorry

theorem add_lt_top {α : Type u} [Add α] [partial_order α] {a : with_top α} {b : with_top α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := sorry

theorem add_eq_coe {α : Type u} [Add α] {a : with_top α} {b : with_top α} {c : α} : a + b = ↑c ↔ ∃ (a' : α), ∃ (b' : α), ↑a' = a ∧ ↑b' = b ∧ a' + b' = c := sorry

protected instance add_comm_semigroup {α : Type u} [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
  add_comm_semigroup.mk add_comm_semigroup.add sorry sorry

protected instance add_monoid {α : Type u} [add_monoid α] : add_monoid (with_top α) :=
  add_monoid.mk Add.add sorry (some 0) sorry sorry

protected instance add_comm_monoid {α : Type u} [add_comm_monoid α] : add_comm_monoid (with_top α) :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance ordered_add_comm_monoid {α : Type u} [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
  ordered_add_comm_monoid.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry partial_order.le
    partial_order.lt sorry sorry sorry sorry sorry

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coe_add_hom {α : Type u} [add_monoid α] : α →+ with_top α :=
  add_monoid_hom.mk coe sorry sorry

@[simp] theorem coe_coe_add_hom {α : Type u} [add_monoid α] : ⇑coe_add_hom = coe :=
  rfl

@[simp] theorem zero_lt_top {α : Type u} [ordered_add_comm_monoid α] : 0 < ⊤ :=
  coe_lt_top 0

@[simp] theorem zero_lt_coe {α : Type u} [ordered_add_comm_monoid α] (a : α) : 0 < ↑a ↔ 0 < a :=
  coe_lt_coe

end with_top


namespace with_bot


protected instance has_zero {α : Type u} [HasZero α] : HasZero (with_bot α) :=
  with_top.has_zero

protected instance has_one {α : Type u} [HasOne α] : HasOne (with_bot α) :=
  with_top.has_one

protected instance add_semigroup {α : Type u} [add_semigroup α] : add_semigroup (with_bot α) :=
  with_top.add_semigroup

protected instance add_comm_semigroup {α : Type u} [add_comm_semigroup α] : add_comm_semigroup (with_bot α) :=
  with_top.add_comm_semigroup

protected instance add_monoid {α : Type u} [add_monoid α] : add_monoid (with_bot α) :=
  with_top.add_monoid

protected instance add_comm_monoid {α : Type u} [add_comm_monoid α] : add_comm_monoid (with_bot α) :=
  with_top.add_comm_monoid

protected instance ordered_add_comm_monoid {α : Type u} [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_bot α) :=
  ordered_add_comm_monoid.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry partial_order.le
    partial_order.lt sorry sorry sorry sorry sorry

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`

theorem coe_zero {α : Type u} [HasZero α] : ↑0 = 0 :=
  rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`

theorem coe_one {α : Type u} [HasOne α] : ↑1 = 1 :=
  rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`

theorem coe_eq_zero {α : Type u_1} [add_monoid α] {a : α} : ↑a = 0 ↔ a = 0 := sorry

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`

theorem coe_add {α : Type u} [add_semigroup α] (a : α) (b : α) : ↑(a + b) = ↑a + ↑b := sorry

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`

theorem coe_bit0 {α : Type u} [add_semigroup α] {a : α} : ↑(bit0 a) = bit0 ↑a := sorry

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`

theorem coe_bit1 {α : Type u} [add_semigroup α] [HasOne α] {a : α} : ↑(bit1 a) = bit1 ↑a := sorry

@[simp] theorem bot_add {α : Type u} [ordered_add_comm_monoid α] (a : with_bot α) : ⊥ + a = ⊥ :=
  rfl

@[simp] theorem add_bot {α : Type u} [ordered_add_comm_monoid α] (a : with_bot α) : a + ⊥ = ⊥ :=
  option.cases_on a (Eq.refl (none + ⊥)) fun (a : α) => Eq.refl (some a + ⊥)

end with_bot


/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
class canonically_ordered_add_monoid (α : Type u_1) 
extends ordered_add_comm_monoid α, order_bot α
where
  le_iff_exists_add : ∀ (a b : α), a ≤ b ↔ ∃ (c : α), b = a + c

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Example seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
class canonically_ordered_monoid (α : Type u_1) 
extends ordered_comm_monoid α, order_bot α
where
  le_iff_exists_mul : ∀ (a b : α), a ≤ b ↔ ∃ (c : α), b = a * c

theorem le_iff_exists_mul {α : Type u} [canonically_ordered_monoid α] {a : α} {b : α} : a ≤ b ↔ ∃ (c : α), b = a * c :=
  canonically_ordered_monoid.le_iff_exists_mul a b

theorem self_le_mul_right {α : Type u} [canonically_ordered_monoid α] (a : α) (b : α) : a ≤ a * b :=
  iff.mpr le_iff_exists_mul (Exists.intro b rfl)

theorem self_le_add_left {α : Type u} [canonically_ordered_add_monoid α] (a : α) (b : α) : a ≤ b + a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b + a)) (add_comm b a))) (self_le_add_right a b)

@[simp] theorem one_le {α : Type u} [canonically_ordered_monoid α] (a : α) : 1 ≤ a := sorry

@[simp] theorem bot_eq_one {α : Type u} [canonically_ordered_monoid α] : ⊥ = 1 :=
  le_antisymm bot_le (one_le ⊥)

@[simp] theorem add_eq_zero_iff {α : Type u} [canonically_ordered_add_monoid α] {a : α} {b : α} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  add_eq_zero_iff' (zero_le a) (zero_le b)

@[simp] theorem le_one_iff_eq_one {α : Type u} [canonically_ordered_monoid α] {a : α} : a ≤ 1 ↔ a = 1 :=
  { mp := fun (h : a ≤ 1) => le_antisymm h (one_le a), mpr := fun (h : a = 1) => h ▸ le_refl a }

theorem pos_iff_ne_zero {α : Type u} [canonically_ordered_add_monoid α] {a : α} : 0 < a ↔ a ≠ 0 :=
  { mp := ne_of_gt, mpr := fun (hne : a ≠ 0) => lt_of_le_of_ne (zero_le a) (ne.symm hne) }

theorem exists_pos_mul_of_lt {α : Type u} [canonically_ordered_monoid α] {a : α} {b : α} (h : a < b) : ∃ (c : α), ∃ (H : c > 1), a * c = b := sorry

theorem le_mul_left {α : Type u} [canonically_ordered_monoid α] {a : α} {b : α} {c : α} (h : a ≤ c) : a ≤ b * c := sorry

theorem le_mul_right {α : Type u} [canonically_ordered_monoid α] {a : α} {b : α} {c : α} (h : a ≤ b) : a ≤ b * c := sorry

-- This instance looks absurd: a monoid already has a zero

/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
protected instance with_zero.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] : canonically_ordered_add_monoid (with_zero α) :=
  canonically_ordered_add_monoid.mk ordered_add_comm_monoid.add sorry ordered_add_comm_monoid.zero sorry sorry sorry
    ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry sorry sorry sorry 0 sorry sorry

protected instance with_top.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] : canonically_ordered_add_monoid (with_top α) :=
  canonically_ordered_add_monoid.mk ordered_add_comm_monoid.add sorry ordered_add_comm_monoid.zero sorry sorry sorry
    order_bot.le order_bot.lt sorry sorry sorry sorry sorry order_bot.bot sorry sorry

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
class canonically_linear_ordered_add_monoid (α : Type u_1) 
extends canonically_ordered_add_monoid α, linear_order α
where

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
class canonically_linear_ordered_monoid (α : Type u_1) 
extends canonically_ordered_monoid α, linear_order α
where

protected instance canonically_linear_ordered_add_monoid.semilattice_sup_bot {α : Type u} [canonically_linear_ordered_add_monoid α] : semilattice_sup_bot α :=
  semilattice_sup_bot.mk order_bot.bot lattice.le lattice.lt sorry sorry sorry sorry lattice.sup sorry sorry sorry

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
class ordered_cancel_add_comm_monoid (α : Type u) 
extends add_cancel_comm_monoid α, partial_order α
where
  add_le_add_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c + a ≤ c + b
  le_of_add_le_add_left : ∀ (a b c : α), a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
class ordered_cancel_comm_monoid (α : Type u) 
extends partial_order α, cancel_comm_monoid α
where
  mul_le_mul_left : ∀ (a b : α), a ≤ b → ∀ (c : α), c * a ≤ c * b
  le_of_mul_le_mul_left : ∀ (a b c : α), a * b ≤ a * c → b ≤ c

theorem le_of_mul_le_mul_left' {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} : a * b ≤ a * c → b ≤ c :=
  ordered_cancel_comm_monoid.le_of_mul_le_mul_left

protected instance ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid {α : Type u} [ordered_cancel_add_comm_monoid α] : ordered_add_comm_monoid α :=
  ordered_add_comm_monoid.mk ordered_cancel_add_comm_monoid.add ordered_cancel_add_comm_monoid.add_assoc
    ordered_cancel_add_comm_monoid.zero ordered_cancel_add_comm_monoid.zero_add ordered_cancel_add_comm_monoid.add_zero
    ordered_cancel_add_comm_monoid.add_comm ordered_cancel_add_comm_monoid.le ordered_cancel_add_comm_monoid.lt
    ordered_cancel_add_comm_monoid.le_refl ordered_cancel_add_comm_monoid.le_trans
    ordered_cancel_add_comm_monoid.le_antisymm ordered_cancel_add_comm_monoid.add_le_add_left sorry

theorem mul_lt_mul_left' {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} (h : a < b) (c : α) : c * a < c * b :=
  lt_of_le_not_le (mul_le_mul_left' (has_lt.lt.le h) c) (mt le_of_mul_le_mul_left' (not_le_of_gt h))

theorem add_lt_add_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} (h : a < b) (c : α) : a + c < b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + c < b + c)) (add_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (c + a < b + c)) (add_comm b c))) (add_lt_add_left h c))

theorem mul_lt_mul''' {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} {d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  lt_trans (mul_lt_mul_right' h₁ c) (mul_lt_mul_left' h₂ b)

theorem mul_lt_mul_of_le_of_lt {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} {d : α} (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
  lt_of_le_of_lt (mul_le_mul_right' h₁ c) (mul_lt_mul_left' h₂ b)

theorem mul_lt_mul_of_lt_of_le {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} {d : α} (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
  lt_of_lt_of_le (mul_lt_mul_right' h₁ c) (mul_le_mul_left' h₂ b)

theorem lt_add_of_pos_right {α : Type u} [ordered_cancel_add_comm_monoid α] (a : α) {b : α} (h : 0 < b) : a < a + b :=
  (fun (this : a + 0 < a + b) => eq.mp (Eq._oldrec (Eq.refl (a + 0 < a + b)) (add_zero a)) this) (add_lt_add_left h a)

theorem lt_mul_of_one_lt_left' {α : Type u} [ordered_cancel_comm_monoid α] (a : α) {b : α} (h : 1 < b) : a < b * a :=
  (fun (this : 1 * a < b * a) => eq.mp (Eq._oldrec (Eq.refl (1 * a < b * a)) (one_mul a)) this) (mul_lt_mul_right' h a)

theorem le_of_add_le_add_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (h : a + b ≤ c + b) : a ≤ c := sorry

theorem mul_lt_one {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
  one_mul 1 ▸ mul_lt_mul''' ha hb

theorem add_neg_of_neg_of_nonpos {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} (ha : a < 0) (hb : b ≤ 0) : a + b < 0 :=
  zero_add 0 ▸ add_lt_add_of_lt_of_le ha hb

theorem add_neg_of_nonpos_of_neg {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} (ha : a ≤ 0) (hb : b < 0) : a + b < 0 :=
  zero_add 0 ▸ add_lt_add_of_le_of_lt ha hb

theorem lt_add_of_pos_of_le {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (ha : 0 < a) (hbc : b ≤ c) : b < a + c :=
  zero_add b ▸ add_lt_add_of_lt_of_le ha hbc

theorem lt_add_of_le_of_pos {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b ≤ c) (ha : 0 < a) : b < c + a :=
  add_zero b ▸ add_lt_add_of_le_of_lt hbc ha

theorem mul_le_of_le_one_of_le {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
  one_mul c ▸ mul_le_mul' ha hbc

theorem mul_le_of_le_of_le_one {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
  mul_one c ▸ mul_le_mul' hbc ha

theorem add_lt_of_neg_of_le {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (ha : a < 0) (hbc : b ≤ c) : a + b < c :=
  zero_add c ▸ add_lt_add_of_lt_of_le ha hbc

theorem mul_lt_of_le_of_lt_one {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
  mul_one c ▸ mul_lt_mul_of_le_of_lt hbc ha

theorem lt_mul_of_one_le_of_lt {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
  one_mul b ▸ mul_lt_mul_of_le_of_lt ha hbc

theorem lt_mul_of_lt_of_one_le {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
  mul_one b ▸ mul_lt_mul_of_lt_of_le hbc ha

theorem lt_add_of_pos_of_lt {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (ha : 0 < a) (hbc : b < c) : b < a + c :=
  zero_add b ▸ add_lt_add ha hbc

theorem lt_mul_of_lt_of_one_lt {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : 1 < a) : b < c * a :=
  mul_one b ▸ mul_lt_mul''' hbc ha

theorem mul_lt_of_le_one_of_lt {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
  one_mul c ▸ mul_lt_mul_of_le_of_lt ha hbc

theorem add_lt_of_lt_of_nonpos {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : a ≤ 0) : b + a < c :=
  add_zero c ▸ add_lt_add_of_lt_of_le hbc ha

theorem mul_lt_of_lt_one_of_lt {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} {c : α} (ha : a < 1) (hbc : b < c) : a * b < c :=
  one_mul c ▸ mul_lt_mul''' ha hbc

theorem add_lt_of_lt_of_neg {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} {c : α} (hbc : b < c) (ha : a < 0) : b + a < c :=
  add_zero c ▸ add_lt_add hbc ha

@[simp] theorem add_le_add_iff_left {α : Type u} [ordered_cancel_add_comm_monoid α] (a : α) {b : α} {c : α} : a + b ≤ a + c ↔ b ≤ c :=
  { mp := le_of_add_le_add_left, mpr := fun (h : b ≤ c) => add_le_add_left h a }

@[simp] theorem add_le_add_iff_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} (c : α) : a + c ≤ b + c ↔ a ≤ b :=
  add_comm c a ▸ add_comm c b ▸ add_le_add_iff_left c

@[simp] theorem mul_lt_mul_iff_left {α : Type u} [ordered_cancel_comm_monoid α] (a : α) {b : α} {c : α} : a * b < a * c ↔ b < c :=
  { mp := lt_of_mul_lt_mul_left', mpr := fun (h : b < c) => mul_lt_mul_left' h a }

@[simp] theorem mul_lt_mul_iff_right {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} (c : α) : a * c < b * c ↔ a < b :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_iff_left c

@[simp] theorem le_add_iff_nonneg_right {α : Type u} [ordered_cancel_add_comm_monoid α] (a : α) {b : α} : a ≤ a + b ↔ 0 ≤ b :=
  (fun (this : a + 0 ≤ a + b ↔ 0 ≤ b) => eq.mp (Eq._oldrec (Eq.refl (a + 0 ≤ a + b ↔ 0 ≤ b)) (add_zero a)) this)
    (add_le_add_iff_left a)

@[simp] theorem le_add_iff_nonneg_left {α : Type u} [ordered_cancel_add_comm_monoid α] (a : α) {b : α} : a ≤ b + a ↔ 0 ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b + a ↔ 0 ≤ b)) (add_comm b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ a + b ↔ 0 ≤ b)) (propext (le_add_iff_nonneg_right a)))) (iff.refl (0 ≤ b)))

@[simp] theorem lt_mul_iff_one_lt_right' {α : Type u} [ordered_cancel_comm_monoid α] (a : α) {b : α} : a < a * b ↔ 1 < b :=
  (fun (this : a * 1 < a * b ↔ 1 < b) => eq.mp (Eq._oldrec (Eq.refl (a * 1 < a * b ↔ 1 < b)) (mul_one a)) this)
    (mul_lt_mul_iff_left a)

@[simp] theorem lt_mul_iff_one_lt_left' {α : Type u} [ordered_cancel_comm_monoid α] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < b * a ↔ 1 < b)) (mul_comm b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a < a * b ↔ 1 < b)) (propext (lt_mul_iff_one_lt_right' a)))) (iff.refl (1 < b)))

@[simp] theorem mul_le_iff_le_one_left' {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} : a * b ≤ b ↔ a ≤ 1 := sorry

@[simp] theorem add_le_iff_nonpos_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} : a + b ≤ a ↔ b ≤ 0 := sorry

@[simp] theorem add_lt_iff_neg_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : α} {b : α} : a + b < b ↔ a < 0 := sorry

@[simp] theorem mul_lt_iff_lt_one_left' {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} : a * b < a ↔ b < 1 := sorry

theorem mul_eq_one_iff_eq_one_of_one_le {α : Type u} [ordered_cancel_comm_monoid α] {a : α} {b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 := sorry

theorem monotone.add_strict_mono {α : Type u} [ordered_cancel_add_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} {g : β → α} (hf : monotone f) (hg : strict_mono g) : strict_mono fun (x : β) => f x + g x :=
  fun (x y : β) (h : x < y) => add_lt_add_of_le_of_lt (hf (le_of_lt h)) (hg h)

theorem strict_mono.mul_monotone' {α : Type u} [ordered_cancel_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} {g : β → α} (hf : strict_mono f) (hg : monotone g) : strict_mono fun (x : β) => f x * g x :=
  fun (x y : β) (h : x < y) => mul_lt_mul_of_lt_of_le (hf h) (hg (le_of_lt h))

theorem strict_mono.add_const {α : Type u} [ordered_cancel_add_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} (hf : strict_mono f) (c : α) : strict_mono fun (x : β) => f x + c :=
  strict_mono.add_monotone hf monotone_const

theorem strict_mono.const_add {α : Type u} [ordered_cancel_add_comm_monoid α] {β : Type u_1} [preorder β] {f : β → α} (hf : strict_mono f) (c : α) : strict_mono fun (x : β) => c + f x :=
  monotone.add_strict_mono monotone_const hf

theorem with_top.add_lt_add_iff_left {α : Type u} [ordered_cancel_add_comm_monoid α] {a : with_top α} {b : with_top α} {c : with_top α} : a < ⊤ → (a + c < a + b ↔ c < b) := sorry

theorem with_bot.add_lt_add_iff_left {α : Type u} [ordered_cancel_add_comm_monoid α] {a : with_bot α} {b : with_bot α} {c : with_bot α} : ⊥ < a → (a + c < a + b ↔ c < b) := sorry

theorem with_top.add_lt_add_iff_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : with_top α} {b : with_top α} {c : with_top α} : a < ⊤ → (c + a < b + a ↔ c < b) := sorry

theorem with_bot.add_lt_add_iff_right {α : Type u} [ordered_cancel_add_comm_monoid α] {a : with_bot α} {b : with_bot α} {c : with_bot α} : ⊥ < a → (c + a < b + a ↔ c < b) := sorry

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/

theorem fn_min_add_fn_max {α : Type u} {β : Type u_1} [linear_order α] [add_comm_semigroup β] (f : α → β) (n : α) (m : α) : f (min n m) + f (max n m) = f n + f m := sorry

theorem min_mul_max {α : Type u} [linear_order α] [comm_semigroup α] (n : α) (m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
class linear_ordered_cancel_add_comm_monoid (α : Type u) 
extends ordered_cancel_add_comm_monoid α, linear_order α
where

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
class linear_ordered_cancel_comm_monoid (α : Type u) 
extends linear_order α, ordered_cancel_comm_monoid α
where

theorem min_add_add_left {α : Type u} [linear_ordered_cancel_add_comm_monoid α] (a : α) (b : α) (c : α) : min (a + b) (a + c) = a + min b c :=
  Eq.symm (monotone.map_min (monotone.const_add monotone_id a))

theorem min_mul_mul_right {α : Type u} [linear_ordered_cancel_comm_monoid α] (a : α) (b : α) (c : α) : min (a * c) (b * c) = min a b * c :=
  Eq.symm (monotone.map_min (monotone.mul_const' monotone_id c))

theorem max_add_add_left {α : Type u} [linear_ordered_cancel_add_comm_monoid α] (a : α) (b : α) (c : α) : max (a + b) (a + c) = a + max b c :=
  Eq.symm (monotone.map_max (monotone.const_add monotone_id a))

theorem max_mul_mul_right {α : Type u} [linear_ordered_cancel_comm_monoid α] (a : α) (b : α) (c : α) : max (a * c) (b * c) = max a b * c :=
  Eq.symm (monotone.map_max (monotone.mul_const' monotone_id c))

theorem min_le_add_of_nonneg_right {α : Type u} [linear_ordered_cancel_add_comm_monoid α] {a : α} {b : α} (hb : 0 ≤ b) : min a b ≤ a + b :=
  iff.mpr min_le_iff (Or.inl (le_add_of_nonneg_right hb))

theorem min_le_add_of_nonneg_left {α : Type u} [linear_ordered_cancel_add_comm_monoid α] {a : α} {b : α} (ha : 0 ≤ a) : min a b ≤ a + b :=
  iff.mpr min_le_iff (Or.inr (le_add_of_nonneg_left ha))

theorem max_le_mul_of_one_le {α : Type u} [linear_ordered_cancel_comm_monoid α] {a : α} {b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : max a b ≤ a * b :=
  iff.mpr max_le_iff { left := le_mul_of_one_le_right' hb, right := le_mul_of_one_le_left' ha }

namespace order_dual


protected instance ordered_comm_monoid {α : Type u} [ordered_comm_monoid α] : ordered_comm_monoid (order_dual α) :=
  ordered_comm_monoid.mk comm_monoid.mul sorry comm_monoid.one sorry sorry sorry partial_order.le partial_order.lt sorry
    sorry sorry sorry sorry

protected instance ordered_cancel_add_comm_monoid {α : Type u} [ordered_cancel_add_comm_monoid α] : ordered_cancel_add_comm_monoid (order_dual α) :=
  ordered_cancel_add_comm_monoid.mk ordered_add_comm_monoid.add sorry sorry ordered_add_comm_monoid.zero sorry sorry sorry
    sorry ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry sorry sorry sorry

protected instance linear_ordered_cancel_add_comm_monoid {α : Type u} [linear_ordered_cancel_add_comm_monoid α] : linear_ordered_cancel_add_comm_monoid (order_dual α) :=
  linear_ordered_cancel_add_comm_monoid.mk ordered_cancel_add_comm_monoid.add sorry sorry
    ordered_cancel_add_comm_monoid.zero sorry sorry sorry sorry linear_order.le linear_order.lt sorry sorry sorry sorry
    sorry sorry linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt

end order_dual


namespace prod


protected instance ordered_cancel_comm_monoid {M : Type u_1} {N : Type u_2} [ordered_cancel_comm_monoid M] [ordered_cancel_comm_monoid N] : ordered_cancel_comm_monoid (M × N) :=
  ordered_cancel_comm_monoid.mk comm_monoid.mul sorry sorry comm_monoid.one sorry sorry sorry sorry partial_order.le
    partial_order.lt sorry sorry sorry sorry sorry

end prod


protected instance multiplicative.preorder {α : Type u} [preorder α] : preorder (multiplicative α) :=
  id

protected instance additive.preorder {α : Type u} [preorder α] : preorder (additive α) :=
  id

protected instance multiplicative.partial_order {α : Type u} [partial_order α] : partial_order (multiplicative α) :=
  id

protected instance additive.partial_order {α : Type u} [partial_order α] : partial_order (additive α) :=
  id

protected instance multiplicative.linear_order {α : Type u} [linear_order α] : linear_order (multiplicative α) :=
  id

protected instance additive.linear_order {α : Type u} [linear_order α] : linear_order (additive α) :=
  id

protected instance multiplicative.ordered_comm_monoid {α : Type u} [ordered_add_comm_monoid α] : ordered_comm_monoid (multiplicative α) :=
  ordered_comm_monoid.mk comm_monoid.mul sorry comm_monoid.one sorry sorry sorry partial_order.le partial_order.lt sorry
    sorry sorry ordered_add_comm_monoid.add_le_add_left ordered_add_comm_monoid.lt_of_add_lt_add_left

protected instance additive.ordered_add_comm_monoid {α : Type u} [ordered_comm_monoid α] : ordered_add_comm_monoid (additive α) :=
  ordered_add_comm_monoid.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry partial_order.le
    partial_order.lt sorry sorry sorry ordered_comm_monoid.mul_le_mul_left ordered_comm_monoid.lt_of_mul_lt_mul_left

protected instance multiplicative.ordered_cancel_comm_monoid {α : Type u} [ordered_cancel_add_comm_monoid α] : ordered_cancel_comm_monoid (multiplicative α) :=
  ordered_cancel_comm_monoid.mk right_cancel_semigroup.mul sorry sorry ordered_comm_monoid.one sorry sorry sorry sorry
    ordered_comm_monoid.le ordered_comm_monoid.lt sorry sorry sorry sorry
    ordered_cancel_add_comm_monoid.le_of_add_le_add_left

protected instance additive.ordered_cancel_add_comm_monoid {α : Type u} [ordered_cancel_comm_monoid α] : ordered_cancel_add_comm_monoid (additive α) :=
  ordered_cancel_add_comm_monoid.mk add_right_cancel_semigroup.add sorry sorry ordered_add_comm_monoid.zero sorry sorry
    sorry sorry ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry sorry sorry
    ordered_cancel_comm_monoid.le_of_mul_le_mul_left

