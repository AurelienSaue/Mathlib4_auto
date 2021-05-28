/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.defs
import Mathlib.logic.function.basic
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/--
Composing two associative operations of `f : α → α → α` on the left
is equal to an associative operation on the left.
-/
theorem comp_assoc_left {α : Type u} (f : α → α → α) [is_associative α f] (x : α) (y : α) : f x ∘ f y = f (f x y) := sorry

/--
Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
theorem comp_assoc_right {α : Type u} (f : α → α → α) [is_associative α f] (x : α) (y : α) : ((fun (z : α) => f z x) ∘ fun (z : α) => f z y) = fun (z : α) => f z (f y x) := sorry

/--
Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp] theorem comp_mul_left {α : Type u_1} [semigroup α] (x : α) (y : α) : Mul.mul x ∘ Mul.mul y = Mul.mul (x * y) :=
  comp_assoc_left Mul.mul x y

/--
Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp] theorem comp_add_right {α : Type u_1} [add_semigroup α] (x : α) (y : α) : ((fun (_x : α) => _x + x) ∘ fun (_x : α) => _x + y) = fun (_x : α) => _x + (y + x) :=
  comp_assoc_right Add.add x y

theorem ite_add_zero {M : Type u} [add_monoid M] {P : Prop} [Decidable P] {a : M} {b : M} : ite P (a + b) 0 = ite P a 0 + ite P b 0 := sorry

theorem eq_one_iff_eq_one_of_mul_eq_one {M : Type u} [monoid M] {a : M} {b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := sorry

theorem add_left_comm {G : Type u} [add_comm_semigroup G] (a : G) (b : G) (c : G) : a + (b + c) = b + (a + c) :=
  left_comm Add.add add_comm add_assoc

theorem mul_right_comm {G : Type u} [comm_semigroup G] (a : G) (b : G) (c : G) : a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc

theorem add_add_add_comm {G : Type u} [add_comm_semigroup G] (a : G) (b : G) (c : G) (d : G) : a + b + (c + d) = a + c + (b + d) := sorry

@[simp] theorem bit0_zero {M : Type u} [add_monoid M] : bit0 0 = 0 :=
  add_zero 0

@[simp] theorem bit1_zero {M : Type u} [add_monoid M] [HasOne M] : bit1 0 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (bit1 0 = 1)) (bit1.equations._eqn_1 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (bit0 0 + 1 = 1)) bit0_zero))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + 1 = 1)) (zero_add 1))) (Eq.refl 1)))

theorem neg_unique {M : Type u} [add_comm_monoid M] {x : M} {y : M} {z : M} (hy : x + y = 0) (hz : x + z = 0) : y = z :=
  left_neg_eq_right_neg (trans (add_comm y x) hy) hz

@[simp] theorem mul_eq_left_iff {M : Type u} [left_cancel_monoid M] {a : M} {b : M} : a * b = a ↔ b = 1 :=
  iff.trans (eq.mpr (id (Eq._oldrec (Eq.refl (a * b = a ↔ a * b = a * 1)) (mul_one a))) (iff.refl (a * b = a)))
    mul_left_cancel_iff

@[simp] theorem left_eq_add_iff {M : Type u} [add_left_cancel_monoid M] {a : M} {b : M} : a = a + b ↔ b = 0 :=
  iff.trans eq_comm add_eq_left_iff

@[simp] theorem mul_eq_right_iff {M : Type u} [right_cancel_monoid M] {a : M} {b : M} : a * b = b ↔ a = 1 :=
  iff.trans (eq.mpr (id (Eq._oldrec (Eq.refl (a * b = b ↔ a * b = 1 * b)) (one_mul b))) (iff.refl (a * b = b)))
    mul_right_cancel_iff

@[simp] theorem right_eq_mul_iff {M : Type u} [right_cancel_monoid M] {a : M} {b : M} : b = a * b ↔ a = 1 :=
  iff.trans eq_comm mul_eq_right_iff

theorem neg_eq_zero_sub {G : Type u} [sub_neg_monoid G] (x : G) : -x = 0 - x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-x = 0 - x)) (sub_eq_add_neg 0 x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-x = 0 + -x)) (zero_add (-x)))) (Eq.refl (-x)))

theorem mul_one_div {G : Type u} [div_inv_monoid G] (x : G) (y : G) : x * (1 / y) = x / y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x * (1 / y) = x / y)) (div_eq_mul_inv 1 y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x * (1 * (y⁻¹)) = x / y)) (one_mul (y⁻¹))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (x * (y⁻¹) = x / y)) (div_eq_mul_inv x y))) (Eq.refl (x * (y⁻¹)))))

theorem mul_div_assoc {G : Type u} [div_inv_monoid G] {a : G} {b : G} {c : G} : a * b / c = a * (b / c) := sorry

theorem mul_div_assoc' {G : Type u} [div_inv_monoid G] (a : G) (b : G) (c : G) : a * (b / c) = a * b / c :=
  Eq.symm mul_div_assoc

@[simp] theorem one_div {G : Type u} [div_inv_monoid G] (a : G) : 1 / a = (a⁻¹) :=
  Eq.symm (inv_eq_one_div a)

@[simp] theorem neg_add_cancel_right {G : Type u} [add_group G] (a : G) (b : G) : a + -b + b = a := sorry

@[simp] theorem neg_zero {G : Type u} [add_group G] : -0 = 0 :=
  neg_eq_of_add_eq_zero (zero_add 0)

theorem left_inverse_inv (G : Type u_1) [group G] : function.left_inverse (fun (a : G) => a⁻¹) fun (a : G) => a⁻¹ :=
  inv_inv

@[simp] theorem inv_involutive {G : Type u} [group G] : function.involutive has_inv.inv :=
  inv_inv

theorem neg_injective {G : Type u} [add_group G] : function.injective Neg.neg :=
  function.involutive.injective neg_involutive

@[simp] theorem neg_inj {G : Type u} [add_group G] {a : G} {b : G} : -a = -b ↔ a = b :=
  function.injective.eq_iff neg_injective

@[simp] theorem add_neg_cancel_left {G : Type u} [add_group G] (a : G) (b : G) : a + (-a + b) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + (-a + b) = b)) (Eq.symm (add_assoc a (-a) b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a + b = b)) (add_right_neg a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 + b = b)) (zero_add b))) (Eq.refl b)))

theorem add_left_surjective {G : Type u} [add_group G] (a : G) : function.surjective (Add.add a) :=
  fun (x : G) => Exists.intro (-a + x) (add_neg_cancel_left a x)

theorem add_right_surjective {G : Type u} [add_group G] (a : G) : function.surjective fun (x : G) => x + a :=
  fun (x : G) => Exists.intro (x + -a) (neg_add_cancel_right x a)

@[simp] theorem mul_inv_rev {G : Type u} [group G] (a : G) (b : G) : a * b⁻¹ = b⁻¹ * (a⁻¹) := sorry

theorem eq_neg_of_eq_neg {G : Type u} [add_group G] {a : G} {b : G} (h : a = -b) : b = -a := sorry

theorem eq_neg_of_add_eq_zero {G : Type u} [add_group G] {a : G} {b : G} (h : a + b = 0) : a = -b := sorry

theorem eq_add_neg_of_add_eq {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : a + c = b) : a = b + -c := sorry

theorem eq_neg_add_of_add_eq {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : b + a = c) : a = -b + c := sorry

theorem neg_add_eq_of_eq_add {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : b = a + c) : -a + b = c := sorry

theorem mul_inv_eq_of_eq_mul {G : Type u} [group G] {a : G} {b : G} {c : G} (h : a = c * b) : a * (b⁻¹) = c := sorry

theorem eq_add_of_add_neg_eq {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : a + -c = b) : a = b + c := sorry

theorem eq_mul_of_inv_mul_eq {G : Type u} [group G] {a : G} {b : G} {c : G} (h : b⁻¹ * a = c) : a = b * c := sorry

theorem mul_eq_of_eq_inv_mul {G : Type u} [group G] {a : G} {b : G} {c : G} (h : b = a⁻¹ * c) : a * b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b = c)) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a⁻¹ * c) = c)) (mul_inv_cancel_left a c))) (Eq.refl c))

theorem mul_eq_of_eq_mul_inv {G : Type u} [group G] {a : G} {b : G} {c : G} (h : a = c * (b⁻¹)) : a * b = c := sorry

theorem add_self_iff_eq_zero {G : Type u} [add_group G] {a : G} : a + a = a ↔ a = 0 :=
  eq.mp (Eq._oldrec (Eq.refl (a + a = a + 0 ↔ a = 0)) (add_zero a)) (add_right_inj a)

@[simp] theorem neg_eq_zero {G : Type u} [add_group G] {a : G} : -a = 0 ↔ a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a = 0 ↔ a = 0)) (Eq.symm (propext neg_inj))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a = 0 ↔ -a = -0)) neg_zero)) (iff.refl (-a = 0)))

@[simp] theorem zero_eq_neg {G : Type u} [add_group G] {a : G} : 0 = -a ↔ a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 = -a ↔ a = 0)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a = 0 ↔ a = 0)) (propext neg_eq_zero))) (iff.refl (a = 0)))

theorem neg_ne_zero {G : Type u} [add_group G] {a : G} : -a ≠ 0 ↔ a ≠ 0 :=
  not_congr neg_eq_zero

theorem eq_neg_iff_eq_neg {G : Type u} [add_group G] {a : G} {b : G} : a = -b ↔ b = -a :=
  { mp := eq_neg_of_eq_neg, mpr := eq_neg_of_eq_neg }

theorem neg_eq_iff_neg_eq {G : Type u} [add_group G] {a : G} {b : G} : -a = b ↔ -b = a :=
  iff.trans eq_comm (iff.trans eq_neg_iff_eq_neg eq_comm)

theorem mul_eq_one_iff_eq_inv {G : Type u} [group G] {a : G} {b : G} : a * b = 1 ↔ a = (b⁻¹) := sorry

theorem mul_eq_one_iff_inv_eq {G : Type u} [group G] {a : G} {b : G} : a * b = 1 ↔ a⁻¹ = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b = 1 ↔ a⁻¹ = b)) (propext mul_eq_one_iff_eq_inv)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = (b⁻¹) ↔ a⁻¹ = b)) (propext eq_inv_iff_eq_inv)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b = (a⁻¹) ↔ a⁻¹ = b)) (propext eq_comm))) (iff.refl (a⁻¹ = b))))

theorem eq_neg_iff_add_eq_zero {G : Type u} [add_group G] {a : G} {b : G} : a = -b ↔ a + b = 0 :=
  iff.symm add_eq_zero_iff_eq_neg

theorem neg_eq_iff_add_eq_zero {G : Type u} [add_group G] {a : G} {b : G} : -a = b ↔ a + b = 0 :=
  iff.symm add_eq_zero_iff_neg_eq

theorem eq_mul_inv_iff_mul_eq {G : Type u} [group G] {a : G} {b : G} {c : G} : a = b * (c⁻¹) ↔ a * c = b := sorry

theorem eq_inv_mul_iff_mul_eq {G : Type u} [group G] {a : G} {b : G} {c : G} : a = b⁻¹ * c ↔ b * a = c := sorry

theorem inv_mul_eq_iff_eq_mul {G : Type u} [group G] {a : G} {b : G} {c : G} : a⁻¹ * b = c ↔ b = a * c := sorry

theorem add_neg_eq_iff_eq_add {G : Type u} [add_group G] {a : G} {b : G} {c : G} : a + -b = c ↔ a = c + b := sorry

theorem mul_inv_eq_one {G : Type u} [group G] {a : G} {b : G} : a * (b⁻¹) = 1 ↔ a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) = 1 ↔ a = b)) (propext mul_eq_one_iff_eq_inv)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = (b⁻¹⁻¹) ↔ a = b)) (inv_inv b))) (iff.refl (a = b)))

theorem inv_mul_eq_one {G : Type u} [group G] {a : G} {b : G} : a⁻¹ * b = 1 ↔ a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * b = 1 ↔ a = b)) (propext mul_eq_one_iff_eq_inv)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ = (b⁻¹) ↔ a = b)) (propext inv_inj))) (iff.refl (a = b)))

@[simp] theorem mul_left_eq_self {G : Type u} [group G] {a : G} {b : G} : a * b = b ↔ a = 1 := sorry

@[simp] theorem add_right_eq_self {G : Type u} [add_group G] {a : G} {b : G} : a + b = a ↔ b = 0 := sorry

theorem sub_left_injective {G : Type u} [add_group G] {b : G} : function.injective fun (a : G) => a - b := sorry

theorem div_right_injective {G : Type u} [group G] {b : G} : function.injective fun (a : G) => b / a := sorry

@[simp] theorem sub_self {G : Type u} [add_group G] (a : G) : a - a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - a = 0)) (sub_eq_add_neg a a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a = 0)) (add_right_neg a))) (Eq.refl 0))

@[simp] theorem sub_add_cancel {G : Type u} [add_group G] (a : G) (b : G) : a - b + b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b + b = a)) (sub_eq_add_neg a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -b + b = a)) (neg_add_cancel_right a b))) (Eq.refl a))

@[simp] theorem add_sub_cancel {G : Type u} [add_group G] (a : G) (b : G) : a + b - b = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b - b = a)) (sub_eq_add_neg (a + b) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b + -b = a)) (add_neg_cancel_right a b))) (Eq.refl a))

theorem add_sub_assoc {G : Type u} [add_group G] (a : G) (b : G) (c : G) : a + b - c = a + (b - c) := sorry

theorem eq_of_sub_eq_zero {G : Type u} [add_group G] {a : G} {b : G} (h : a - b = 0) : a = b := sorry

theorem sub_eq_zero_of_eq {G : Type u} [add_group G] {a : G} {b : G} (h : a = b) : a - b = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = 0)) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b - b = 0)) (sub_self b))) (Eq.refl 0))

theorem sub_eq_zero_iff_eq {G : Type u} [add_group G] {a : G} {b : G} : a - b = 0 ↔ a = b :=
  { mp := eq_of_sub_eq_zero, mpr := sub_eq_zero_of_eq }

@[simp] theorem sub_zero {G : Type u} [add_group G] (a : G) : a - 0 = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - 0 = a)) (sub_eq_add_neg a 0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -0 = a)) neg_zero))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a + 0 = a)) (add_zero a))) (Eq.refl a)))

theorem sub_ne_zero_of_ne {G : Type u} [add_group G] {a : G} {b : G} (h : a ≠ b) : a - b ≠ 0 :=
  id fun (hab : a - b = 0) => h (eq_of_sub_eq_zero hab)

@[simp] theorem sub_neg_eq_add {G : Type u} [add_group G] (a : G) (b : G) : a - -b = a + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - -b = a + b)) (sub_eq_add_neg a (-b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + --b = a + b)) (neg_neg b))) (Eq.refl (a + b)))

@[simp] theorem neg_sub {G : Type u} [add_group G] (a : G) (b : G) : -(a - b) = b - a := sorry

theorem add_sub {G : Type u} [add_group G] (a : G) (b : G) (c : G) : a + (b - c) = a + b - c := sorry

theorem sub_add_eq_sub_sub_swap {G : Type u} [add_group G] (a : G) (b : G) (c : G) : a - (b + c) = a - c - b := sorry

@[simp] theorem add_sub_add_right_eq_sub {G : Type u} [add_group G] (a : G) (b : G) (c : G) : a + c - (b + c) = a - b := sorry

theorem eq_sub_of_add_eq {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : a + c = b) : a = b - c := sorry

theorem sub_eq_of_eq_add {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : a = c + b) : a - b = c := sorry

theorem eq_add_of_sub_eq {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : a - c = b) : a = b + c := sorry

theorem add_eq_of_eq_sub {G : Type u} [add_group G] {a : G} {b : G} {c : G} (h : a = c - b) : a + b = c := sorry

@[simp] theorem sub_right_inj {G : Type u} [add_group G] {a : G} {b : G} {c : G} : a - b = a - c ↔ b = c :=
  function.injective.eq_iff sub_right_injective

@[simp] theorem sub_left_inj {G : Type u} [add_group G] {a : G} {b : G} {c : G} : b - a = c - a ↔ b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b - a = c - a ↔ b = c)) (sub_eq_add_neg b a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + -a = c - a ↔ b = c)) (sub_eq_add_neg c a))) (add_left_inj (-a)))

theorem sub_add_sub_cancel {G : Type u} [add_group G] (a : G) (b : G) (c : G) : a - b + (b - c) = a - c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b + (b - c) = a - c)) (Eq.symm (add_sub_assoc (a - b) b c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b + b - c = a - c)) (sub_add_cancel a b))) (Eq.refl (a - c)))

theorem sub_sub_sub_cancel_right {G : Type u} [add_group G] (a : G) (b : G) (c : G) : a - c - (b - c) = a - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - c - (b - c) = a - b)) (Eq.symm (neg_sub c b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - c - -(c - b) = a - b)) (sub_neg_eq_add (a - c) (c - b))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a - c + (c - b) = a - b)) (sub_add_sub_cancel a c b))) (Eq.refl (a - b))))

theorem sub_sub_assoc_swap {G : Type u} [add_group G] {a : G} {b : G} {c : G} : a - (b - c) = a + c - b := sorry

theorem sub_eq_zero {G : Type u} [add_group G] {a : G} {b : G} : a - b = 0 ↔ a = b := sorry

theorem sub_ne_zero {G : Type u} [add_group G] {a : G} {b : G} : a - b ≠ 0 ↔ a ≠ b :=
  not_congr sub_eq_zero

theorem eq_sub_iff_add_eq {G : Type u} [add_group G] {a : G} {b : G} {c : G} : a = b - c ↔ a + c = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b - c ↔ a + c = b)) (sub_eq_add_neg b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b + -c ↔ a + c = b)) (propext eq_add_neg_iff_add_eq))) (iff.refl (a + c = b)))

theorem sub_eq_iff_eq_add {G : Type u} [add_group G] {a : G} {b : G} {c : G} : a - b = c ↔ a = c + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = c ↔ a = c + b)) (sub_eq_add_neg a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -b = c ↔ a = c + b)) (propext add_neg_eq_iff_eq_add))) (iff.refl (a = c + b)))

theorem eq_iff_eq_of_sub_eq_sub {G : Type u} [add_group G] {a : G} {b : G} {c : G} {d : G} (H : a - b = c - d) : a = b ↔ c = d :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b ↔ c = d)) (Eq.symm (propext sub_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b = 0 ↔ c = d)) H))
      (eq.mpr (id (Eq._oldrec (Eq.refl (c - d = 0 ↔ c = d)) (propext sub_eq_zero))) (iff.refl (c = d))))

theorem left_inverse_sub_add_left {G : Type u} [add_group G] (c : G) : function.left_inverse (fun (x : G) => x - c) fun (x : G) => x + c :=
  fun (x : G) => add_sub_cancel x c

theorem left_inverse_add_left_sub {G : Type u} [add_group G] (c : G) : function.left_inverse (fun (x : G) => x + c) fun (x : G) => x - c :=
  fun (x : G) => sub_add_cancel x c

theorem left_inverse_add_right_neg_add {G : Type u} [add_group G] (c : G) : function.left_inverse (fun (x : G) => c + x) fun (x : G) => -c + x :=
  fun (x : G) => add_neg_cancel_left c x

theorem left_inverse_neg_add_add_right {G : Type u} [add_group G] (c : G) : function.left_inverse (fun (x : G) => -c + x) fun (x : G) => c + x :=
  fun (x : G) => neg_add_cancel_left c x

theorem neg_add {G : Type u} [add_comm_group G] (a : G) (b : G) : -(a + b) = -a + -b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-(a + b) = -a + -b)) (neg_add_rev a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-b + -a = -a + -b)) (add_comm (-b) (-a)))) (Eq.refl (-a + -b)))

theorem sub_add_eq_sub_sub {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - (b + c) = a - b - c := sorry

theorem neg_add_eq_sub {G : Type u} [add_comm_group G] (a : G) (b : G) : -a + b = b - a := sorry

theorem sub_add_eq_add_sub {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - b + c = a + c - b := sorry

theorem sub_sub {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - b - c = a - (b + c) := sorry

theorem sub_add {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - b + c = a - (b - c) := sorry

@[simp] theorem add_sub_add_left_eq_sub {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : c + a - (c + b) = a - b := sorry

theorem eq_sub_of_add_eq' {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} (h : c + a = b) : a = b - c := sorry

theorem sub_eq_of_eq_add' {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} (h : a = b + c) : a - b = c := sorry

theorem eq_add_of_sub_eq' {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} (h : a - b = c) : a = b + c := sorry

theorem add_eq_of_eq_sub' {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} (h : b = c - a) : a + b = c := sorry

theorem sub_sub_self {G : Type u} [add_comm_group G] (a : G) (b : G) : a - (a - b) = b := sorry

theorem add_sub_comm {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) (d : G) : a + b - (c + d) = a - c + (b - d) := sorry

theorem sub_eq_sub_add_sub {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - b = c - b + (a - c) := sorry

theorem neg_neg_sub_neg {G : Type u} [add_comm_group G] (a : G) (b : G) : -(-a - -b) = a - b := sorry

@[simp] theorem sub_sub_cancel {G : Type u} [add_comm_group G] (a : G) (b : G) : a - (a - b) = b :=
  sub_sub_self a b

theorem sub_eq_neg_add {G : Type u} [add_comm_group G] (a : G) (b : G) : a - b = -b + a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = -b + a)) (sub_eq_add_neg a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -b = -b + a)) (add_comm a (-b)))) (Eq.refl (-b + a)))

theorem neg_add' {G : Type u} [add_comm_group G] (a : G) (b : G) : -(a + b) = -a - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-(a + b) = -a - b)) (sub_eq_add_neg (-a) b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-(a + b) = -a + -b)) (neg_add a b))) (Eq.refl (-a + -b)))

@[simp] theorem neg_sub_neg {G : Type u} [add_comm_group G] (a : G) (b : G) : -a - -b = b - a := sorry

theorem eq_sub_iff_add_eq' {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} : a = b - c ↔ c + a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b - c ↔ c + a = b)) (propext eq_sub_iff_add_eq)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + c = b ↔ c + a = b)) (add_comm a c))) (iff.refl (c + a = b)))

theorem sub_eq_iff_eq_add' {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} : a - b = c ↔ a = b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = c ↔ a = b + c)) (propext sub_eq_iff_eq_add)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = c + b ↔ a = b + c)) (add_comm c b))) (iff.refl (a = b + c)))

@[simp] theorem add_sub_cancel' {G : Type u} [add_comm_group G] (a : G) (b : G) : a + b - a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b - a = b)) (sub_eq_neg_add (a + b) a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-a + (a + b) = b)) (neg_add_cancel_left a b))) (Eq.refl b))

@[simp] theorem add_sub_cancel'_right {G : Type u} [add_comm_group G] (a : G) (b : G) : a + (b - a) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + (b - a) = b)) (Eq.symm (add_sub_assoc a b a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b - a = b)) (add_sub_cancel' a b))) (Eq.refl b))

-- This lemma is in the `simp` set under the name `add_neg_cancel_comm_assoc`,

-- defined  in `algebra/group/commute`

theorem add_add_neg_cancel'_right {G : Type u} [add_comm_group G] (a : G) (b : G) : a + (b + -a) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + (b + -a) = b)) (Eq.symm (sub_eq_add_neg b a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + (b - a) = b)) (add_sub_cancel'_right a b))) (Eq.refl b))

theorem sub_right_comm {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - b - c = a - c - b := sorry

@[simp] theorem add_add_sub_cancel {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a + c + (b - c) = a + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + c + (b - c) = a + b)) (add_assoc a c (b - c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + (c + (b - c)) = a + b)) (add_sub_cancel'_right c b))) (Eq.refl (a + b)))

@[simp] theorem sub_add_add_cancel {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - c + (b + c) = a + b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - c + (b + c) = a + b)) (add_left_comm (a - c) b c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b + (a - c + c) = a + b)) (sub_add_cancel a c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b + a = a + b)) (add_comm b a))) (Eq.refl (a + b))))

@[simp] theorem sub_add_sub_cancel' {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a - b + (c - a) = c - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b + (c - a) = c - b)) (add_comm (a - b) (c - a)))) (sub_add_sub_cancel c a b)

@[simp] theorem add_sub_sub_cancel {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : a + b - (a - c) = b + c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b - (a - c) = b + c)) (Eq.symm (sub_add (a + b) a c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b - a + c = b + c)) (add_sub_cancel' a b))) (Eq.refl (b + c)))

@[simp] theorem sub_sub_sub_cancel_left {G : Type u} [add_comm_group G] (a : G) (b : G) (c : G) : c - a - (c - b) = b - a := sorry

theorem sub_eq_sub_iff_add_eq_add {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} {d : G} : a - b = c - d ↔ a + d = c + b := sorry

theorem sub_eq_sub_iff_sub_eq_sub {G : Type u} [add_comm_group G] {a : G} {b : G} {c : G} {d : G} : a - b = c - d ↔ a - c = b - d := sorry

