/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.opposite
import Mathlib.algebra.field
import Mathlib.group_theory.group_action.defs
import Mathlib.data.equiv.mul_add
import PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
# Algebraic operations on `αᵒᵖ`
-/

namespace opposite


protected instance has_add (α : Type u) [Add α] : Add (αᵒᵖ) :=
  { add := fun (x y : αᵒᵖ) => op (unop x + unop y) }

protected instance has_sub (α : Type u) [Sub α] : Sub (αᵒᵖ) :=
  { sub := fun (x y : αᵒᵖ) => op (unop x - unop y) }

protected instance add_semigroup (α : Type u) [add_semigroup α] : add_semigroup (αᵒᵖ) :=
  add_semigroup.mk Add.add sorry

protected instance add_left_cancel_semigroup (α : Type u) [add_left_cancel_semigroup α] : add_left_cancel_semigroup (αᵒᵖ) :=
  add_left_cancel_semigroup.mk add_semigroup.add sorry sorry

protected instance add_right_cancel_semigroup (α : Type u) [add_right_cancel_semigroup α] : add_right_cancel_semigroup (αᵒᵖ) :=
  add_right_cancel_semigroup.mk add_semigroup.add sorry sorry

protected instance add_comm_semigroup (α : Type u) [add_comm_semigroup α] : add_comm_semigroup (αᵒᵖ) :=
  add_comm_semigroup.mk add_semigroup.add sorry sorry

protected instance has_zero (α : Type u) [HasZero α] : HasZero (αᵒᵖ) :=
  { zero := op 0 }

protected instance nontrivial (α : Type u) [nontrivial α] : nontrivial (αᵒᵖ) :=
  sorry

@[simp] theorem unop_eq_zero_iff (α : Type u) [HasZero α] (a : αᵒᵖ) : unop a = 0 ↔ a = 0 :=
  iff.refl (unop a = 0)

@[simp] theorem op_eq_zero_iff (α : Type u) [HasZero α] (a : α) : op a = 0 ↔ a = 0 :=
  iff.refl (op a = 0)

protected instance add_monoid (α : Type u) [add_monoid α] : add_monoid (αᵒᵖ) :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

protected instance add_comm_monoid (α : Type u) [add_comm_monoid α] : add_comm_monoid (αᵒᵖ) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

protected instance has_neg (α : Type u) [Neg α] : Neg (αᵒᵖ) :=
  { neg := fun (x : αᵒᵖ) => op (-unop x) }

protected instance add_group (α : Type u) [add_group α] : add_group (αᵒᵖ) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg Sub.sub sorry

protected instance add_comm_group (α : Type u) [add_comm_group α] : add_comm_group (αᵒᵖ) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry sorry

protected instance has_mul (α : Type u) [Mul α] : Mul (αᵒᵖ) :=
  { mul := fun (x y : αᵒᵖ) => op (unop y * unop x) }

protected instance semigroup (α : Type u) [semigroup α] : semigroup (αᵒᵖ) :=
  semigroup.mk Mul.mul sorry

protected instance left_cancel_semigroup (α : Type u) [right_cancel_semigroup α] : left_cancel_semigroup (αᵒᵖ) :=
  left_cancel_semigroup.mk semigroup.mul sorry sorry

protected instance right_cancel_semigroup (α : Type u) [left_cancel_semigroup α] : right_cancel_semigroup (αᵒᵖ) :=
  right_cancel_semigroup.mk semigroup.mul sorry sorry

protected instance comm_semigroup (α : Type u) [comm_semigroup α] : comm_semigroup (αᵒᵖ) :=
  comm_semigroup.mk semigroup.mul sorry sorry

protected instance has_one (α : Type u) [HasOne α] : HasOne (αᵒᵖ) :=
  { one := op 1 }

@[simp] theorem unop_eq_one_iff (α : Type u) [HasOne α] (a : αᵒᵖ) : unop a = 1 ↔ a = 1 :=
  iff.refl (unop a = 1)

@[simp] theorem op_eq_one_iff (α : Type u) [HasOne α] (a : α) : op a = 1 ↔ a = 1 :=
  iff.refl (op a = 1)

protected instance monoid (α : Type u) [monoid α] : monoid (αᵒᵖ) :=
  monoid.mk semigroup.mul sorry 1 sorry sorry

protected instance comm_monoid (α : Type u) [comm_monoid α] : comm_monoid (αᵒᵖ) :=
  comm_monoid.mk monoid.mul sorry monoid.one sorry sorry sorry

protected instance has_inv (α : Type u) [has_inv α] : has_inv (αᵒᵖ) :=
  has_inv.mk fun (x : αᵒᵖ) => op (unop x⁻¹)

protected instance group (α : Type u) [group α] : group (αᵒᵖ) :=
  group.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv
    (div_inv_monoid.div._default monoid.mul sorry monoid.one sorry sorry has_inv.inv) sorry

protected instance comm_group (α : Type u) [comm_group α] : comm_group (αᵒᵖ) :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

protected instance distrib (α : Type u) [distrib α] : distrib (αᵒᵖ) :=
  distrib.mk Mul.mul Add.add sorry sorry

protected instance semiring (α : Type u) [semiring α] : semiring (αᵒᵖ) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry monoid.one sorry sorry
    sorry sorry sorry sorry

protected instance ring (α : Type u) [ring α] : ring (αᵒᵖ) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    monoid.mul sorry monoid.one sorry sorry sorry sorry

protected instance comm_ring (α : Type u) [comm_ring α] : comm_ring (αᵒᵖ) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

protected instance no_zero_divisors (α : Type u) [HasZero α] [Mul α] [no_zero_divisors α] : no_zero_divisors (αᵒᵖ) :=
  no_zero_divisors.mk
    fun (x y : αᵒᵖ) (H : op (unop y * unop x) = op 0) =>
      or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero (op_injective H))
        (fun (hy : unop y = 0) => Or.inr (unop_injective hy)) fun (hx : unop x = 0) => Or.inl (unop_injective hx)

protected instance integral_domain (α : Type u) [integral_domain α] : integral_domain (αᵒᵖ) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

protected instance field (α : Type u) [field α] : field (αᵒᵖ) :=
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul sorry
    comm_ring.one sorry sorry sorry sorry sorry has_inv.inv sorry sorry sorry

protected instance has_scalar (α : Type u) (R : Type u_1) [has_scalar R α] : has_scalar R (αᵒᵖ) :=
  has_scalar.mk fun (c : R) (x : αᵒᵖ) => op (c • unop x)

protected instance mul_action (α : Type u) (R : Type u_1) [monoid R] [mul_action R α] : mul_action R (αᵒᵖ) :=
  mul_action.mk sorry sorry

protected instance distrib_mul_action (α : Type u) (R : Type u_1) [monoid R] [add_monoid α] [distrib_mul_action R α] : distrib_mul_action R (αᵒᵖ) :=
  distrib_mul_action.mk sorry sorry

@[simp] theorem op_zero (α : Type u) [HasZero α] : op 0 = 0 :=
  rfl

@[simp] theorem unop_zero (α : Type u) [HasZero α] : unop 0 = 0 :=
  rfl

@[simp] theorem op_one (α : Type u) [HasOne α] : op 1 = 1 :=
  rfl

@[simp] theorem unop_one (α : Type u) [HasOne α] : unop 1 = 1 :=
  rfl

@[simp] theorem op_add {α : Type u} [Add α] (x : α) (y : α) : op (x + y) = op x + op y :=
  rfl

@[simp] theorem unop_add {α : Type u} [Add α] (x : αᵒᵖ) (y : αᵒᵖ) : unop (x + y) = unop x + unop y :=
  rfl

@[simp] theorem op_neg {α : Type u} [Neg α] (x : α) : op (-x) = -op x :=
  rfl

@[simp] theorem unop_neg {α : Type u} [Neg α] (x : αᵒᵖ) : unop (-x) = -unop x :=
  rfl

@[simp] theorem op_mul {α : Type u} [Mul α] (x : α) (y : α) : op (x * y) = op y * op x :=
  rfl

@[simp] theorem unop_mul {α : Type u} [Mul α] (x : αᵒᵖ) (y : αᵒᵖ) : unop (x * y) = unop y * unop x :=
  rfl

@[simp] theorem op_inv {α : Type u} [has_inv α] (x : α) : op (x⁻¹) = (op x⁻¹) :=
  rfl

@[simp] theorem unop_inv {α : Type u} [has_inv α] (x : αᵒᵖ) : unop (x⁻¹) = (unop x⁻¹) :=
  rfl

@[simp] theorem op_sub {α : Type u} [add_group α] (x : α) (y : α) : op (x - y) = op x - op y :=
  rfl

@[simp] theorem unop_sub {α : Type u} [add_group α] (x : αᵒᵖ) (y : αᵒᵖ) : unop (x - y) = unop x - unop y :=
  rfl

@[simp] theorem op_smul {α : Type u} {R : Type u_1} [has_scalar R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl

@[simp] theorem unop_smul {α : Type u} {R : Type u_1} [has_scalar R α] (c : R) (a : αᵒᵖ) : unop (c • a) = c • unop a :=
  rfl

/-- The function `op` is an additive equivalence. -/
def op_add_equiv {α : Type u} [Add α] : α ≃+ (αᵒᵖ) :=
  add_equiv.mk (equiv.to_fun equiv_to_opposite) (equiv.inv_fun equiv_to_opposite) sorry sorry sorry

@[simp] theorem coe_op_add_equiv {α : Type u} [Add α] : ⇑op_add_equiv = op :=
  rfl

@[simp] theorem coe_op_add_equiv_symm {α : Type u} [Add α] : ⇑(add_equiv.symm op_add_equiv) = unop :=
  rfl

@[simp] theorem op_add_equiv_to_equiv {α : Type u} [Add α] : add_equiv.to_equiv op_add_equiv = equiv_to_opposite :=
  rfl

end opposite


/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵒᵖ`. -/
def ring_hom.to_opposite {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R →+* S) (hf : ∀ (x y : R), commute (coe_fn f x) (coe_fn f y)) : R →+* (Sᵒᵖ) :=
  ring_hom.mk (add_monoid_hom.to_fun (add_monoid_hom.comp (add_equiv.to_add_monoid_hom opposite.op_add_equiv) ↑f)) sorry
    sorry sorry sorry

@[simp] theorem ring_hom.coe_to_opposite {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] (f : R →+* S) (hf : ∀ (x y : R), commute (coe_fn f x) (coe_fn f y)) : ⇑(ring_hom.to_opposite f hf) = opposite.op ∘ ⇑f :=
  rfl

