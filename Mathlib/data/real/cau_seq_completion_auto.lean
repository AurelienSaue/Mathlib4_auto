/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis

Generalizes the Cauchy completion of (ℚ, abs) to the completion of a
commutative ring with absolute value.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.real.cau_seq
import PostPort

universes u_1 u_2 l 

namespace Mathlib

namespace cau_seq.completion


def Cauchy {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv]  :=
  quotient cau_seq.equiv

def mk {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : cau_seq β abv → Cauchy :=
  quotient.mk

@[simp] theorem mk_eq_mk {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) : quotient.mk f = mk f :=
  rfl

theorem mk_eq {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} {g : cau_seq β abv} : mk f = mk g ↔ f ≈ g :=
  quotient.eq

def of_rat {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (x : β) : Cauchy :=
  mk (const abv x)

protected instance Cauchy.has_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : HasZero Cauchy :=
  { zero := of_rat 0 }

protected instance Cauchy.has_one {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : HasOne Cauchy :=
  { one := of_rat 1 }

protected instance Cauchy.inhabited {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : Inhabited Cauchy :=
  { default := 0 }

theorem of_rat_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : of_rat 0 = 0 :=
  rfl

theorem of_rat_one {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : of_rat 1 = 1 :=
  rfl

@[simp] theorem mk_eq_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} : mk f = 0 ↔ lim_zero f :=
  eq.mp (Eq._oldrec (Eq.refl (mk f = 0 ↔ lim_zero (f - 0))) (sub_zero f)) quotient.eq

protected instance Cauchy.has_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : Add Cauchy :=
  { add := fun (x y : Cauchy) => quotient.lift_on₂ x y (fun (f g : cau_seq β abv) => mk (f + g)) sorry }

@[simp] theorem mk_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (g : cau_seq β abv) : mk f + mk g = mk (f + g) :=
  rfl

protected instance Cauchy.has_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : Neg Cauchy :=
  { neg := fun (x : Cauchy) => quotient.lift_on x (fun (f : cau_seq β abv) => mk (-f)) sorry }

@[simp] theorem mk_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) : -mk f = mk (-f) :=
  rfl

protected instance Cauchy.has_mul {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : Mul Cauchy :=
  { mul := fun (x y : Cauchy) => quotient.lift_on₂ x y (fun (f g : cau_seq β abv) => mk (f * g)) sorry }

@[simp] theorem mk_mul {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (g : cau_seq β abv) : mk f * mk g = mk (f * g) :=
  rfl

protected instance Cauchy.has_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : Sub Cauchy :=
  { sub := fun (x y : Cauchy) => quotient.lift_on₂ x y (fun (f g : cau_seq β abv) => mk (f - g)) sorry }

@[simp] theorem mk_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (f : cau_seq β abv) (g : cau_seq β abv) : mk f - mk g = mk (f - g) :=
  rfl

theorem of_rat_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : of_rat (x + y) = of_rat x + of_rat y :=
  congr_arg mk (const_add x y)

theorem of_rat_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (x : β) : of_rat (-x) = -of_rat x :=
  congr_arg mk (const_neg x)

theorem of_rat_mul {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : of_rat (x * y) = of_rat x * of_rat y :=
  congr_arg mk (const_mul x y)

protected instance Cauchy.comm_ring {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] : comm_ring Cauchy :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry

theorem of_rat_sub {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [comm_ring β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : of_rat (x - y) = of_rat x - of_rat y :=
  congr_arg mk (const_sub x y)

protected instance Cauchy.has_inv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] : has_inv Cauchy :=
  has_inv.mk
    fun (x : Cauchy) =>
      quotient.lift_on x
        (fun (f : cau_seq β abv) => mk (dite (lim_zero f) (fun (h : lim_zero f) => 0) fun (h : ¬lim_zero f) => inv f h))
        sorry

@[simp] theorem inv_zero {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] : 0⁻¹ = 0 := sorry

@[simp] theorem inv_mk {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] {f : cau_seq β abv} (hf : ¬lim_zero f) : mk f⁻¹ = mk (inv f hf) := sorry

theorem cau_seq_zero_ne_one {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] : ¬0 ≈ 1 := sorry

theorem zero_ne_one {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] : 0 ≠ 1 :=
  fun (h : 0 = 1) => cau_seq_zero_ne_one (iff.mp mk_eq h)

protected theorem inv_mul_cancel {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] {x : Cauchy} : x ≠ 0 → x⁻¹ * x = 1 := sorry

def field {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] : field Cauchy :=
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul sorry
    comm_ring.one sorry sorry sorry sorry sorry has_inv.inv sorry sorry inv_zero

theorem of_rat_inv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] (x : β) : of_rat (x⁻¹) = (of_rat x⁻¹) := sorry

theorem of_rat_div {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] (x : β) (y : β) : of_rat (x / y) = of_rat x / of_rat y := sorry

end cau_seq.completion


namespace cau_seq


class is_complete {α : Type u_1} [linear_ordered_field α] (β : Type u_2) [ring β] (abv : β → α) [is_absolute_value abv] 
where
  is_complete : ∀ (s : cau_seq β abv), ∃ (b : β), s ≈ const abv b

theorem complete {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (s : cau_seq β abv) : ∃ (b : β), s ≈ const abv b :=
  is_complete.is_complete

def lim {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (s : cau_seq β abv) : β :=
  classical.some (complete s)

theorem equiv_lim {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (s : cau_seq β abv) : s ≈ const abv (lim s) :=
  classical.some_spec (complete s)

theorem eq_lim_of_const_equiv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] {f : cau_seq β abv} {x : β} (h : const abv x ≈ f) : x = lim f :=
  iff.mp const_equiv (setoid.trans h (equiv_lim f))

theorem lim_eq_of_equiv_const {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] {f : cau_seq β abv} {x : β} (h : f ≈ const abv x) : lim f = x :=
  Eq.symm (eq_lim_of_const_equiv (setoid.symm h))

theorem lim_eq_lim_of_equiv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] {f : cau_seq β abv} {g : cau_seq β abv} (h : f ≈ g) : lim f = lim g :=
  lim_eq_of_equiv_const (setoid.trans h (equiv_lim g))

@[simp] theorem lim_const {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (x : β) : lim (const abv x) = x :=
  lim_eq_of_equiv_const (setoid.refl (const abv x))

theorem lim_add {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (f : cau_seq β abv) (g : cau_seq β abv) : lim f + lim g = lim (f + g) := sorry

theorem lim_mul_lim {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (f : cau_seq β abv) (g : cau_seq β abv) : lim f * lim g = lim (f * g) := sorry

theorem lim_mul {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (f : cau_seq β abv) (x : β) : lim f * x = lim (f * const abv x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lim f * x = lim (f * const abv x))) (Eq.symm (lim_mul_lim f (const abv x)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (lim f * x = lim f * lim (const abv x))) (lim_const x))) (Eq.refl (lim f * x)))

theorem lim_neg {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (f : cau_seq β abv) : lim (-f) = -lim f := sorry

theorem lim_eq_zero_iff {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [ring β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] (f : cau_seq β abv) : lim f = 0 ↔ lim_zero f := sorry

theorem lim_inv {α : Type u_1} [linear_ordered_field α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] [is_complete β abv] {f : cau_seq β abv} (hf : ¬lim_zero f) : lim (inv f hf) = (lim f⁻¹) := sorry

theorem lim_le {α : Type u_1} [linear_ordered_field α] [is_complete α abs] {f : cau_seq α abs} {x : α} (h : f ≤ const abs x) : lim f ≤ x :=
  iff.mp const_le (le_of_eq_of_le (setoid.symm (equiv_lim f)) h)

theorem le_lim {α : Type u_1} [linear_ordered_field α] [is_complete α abs] {f : cau_seq α abs} {x : α} (h : const abs x ≤ f) : x ≤ lim f :=
  iff.mp const_le (le_of_le_of_eq h (equiv_lim f))

theorem lt_lim {α : Type u_1} [linear_ordered_field α] [is_complete α abs] {f : cau_seq α abs} {x : α} (h : const abs x < f) : x < lim f :=
  iff.mp const_lt (lt_of_lt_of_eq h (equiv_lim f))

theorem lim_lt {α : Type u_1} [linear_ordered_field α] [is_complete α abs] {f : cau_seq α abs} {x : α} (h : f < const abs x) : lim f < x :=
  iff.mp const_lt (lt_of_eq_of_lt (setoid.symm (equiv_lim f)) h)

