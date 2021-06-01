/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.algebra.field
import Mathlib.algebra.module.default
import Mathlib.algebra.algebra.basic
import Mathlib.algebra.group.type_tags
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u v u_1 u_2 

namespace Mathlib

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, group, ring, field, module, algebra
-/

namespace equiv


/-- Transfer `has_one` across an `equiv` -/
protected def has_zero {α : Type u} {β : Type v} (e : α ≃ β) [HasZero β] : HasZero α :=
  { zero := coe_fn (equiv.symm e) 0 }

theorem zero_def {α : Type u} {β : Type v} (e : α ≃ β) [HasZero β] : 0 = coe_fn (equiv.symm e) 0 :=
  rfl

/-- Transfer `has_mul` across an `equiv` -/
protected def has_add {α : Type u} {β : Type v} (e : α ≃ β) [Add β] : Add α :=
  { add := fun (x y : α) => coe_fn (equiv.symm e) (coe_fn e x + coe_fn e y) }

theorem add_def {α : Type u} {β : Type v} (e : α ≃ β) [Add β] (x : α) (y : α) :
    x + y = coe_fn (equiv.symm e) (coe_fn e x + coe_fn e y) :=
  rfl

/-- Transfer `has_div` across an `equiv` -/
protected def has_sub {α : Type u} {β : Type v} (e : α ≃ β) [Sub β] : Sub α :=
  { sub := fun (x y : α) => coe_fn (equiv.symm e) (coe_fn e x - coe_fn e y) }

theorem div_def {α : Type u} {β : Type v} (e : α ≃ β) [Div β] (x : α) (y : α) :
    x / y = coe_fn (equiv.symm e) (coe_fn e x / coe_fn e y) :=
  rfl

/-- Transfer `has_inv` across an `equiv` -/
protected def has_inv {α : Type u} {β : Type v} (e : α ≃ β) [has_inv β] : has_inv α :=
  has_inv.mk fun (x : α) => coe_fn (equiv.symm e) (coe_fn e x⁻¹)

theorem neg_def {α : Type u} {β : Type v} (e : α ≃ β) [Neg β] (x : α) :
    -x = coe_fn (equiv.symm e) (-coe_fn e x) :=
  rfl

/-- Transfer `has_scalar` across an `equiv` -/
protected def has_scalar {α : Type u} {β : Type v} (e : α ≃ β) {R : Type u_1} [has_scalar R β] :
    has_scalar R α :=
  has_scalar.mk fun (r : R) (x : α) => coe_fn (equiv.symm e) (r • coe_fn e x)

theorem smul_def {α : Type u} {β : Type v} (e : α ≃ β) {R : Type u_1} [has_scalar R β] (r : R)
    (x : α) : r • x = coe_fn (equiv.symm e) (r • coe_fn e x) :=
  rfl

/--
An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
def mul_equiv {α : Type u} {β : Type v} (e : α ≃ β) [Mul β] :
    let _inst : Mul α := equiv.has_mul e;
      α ≃* β :=
  let _inst : Mul α := equiv.has_mul e;
  mul_equiv.mk (to_fun e) (inv_fun e) (left_inv e) (right_inv e) sorry

@[simp] theorem mul_equiv_apply {α : Type u} {β : Type v} (e : α ≃ β) [Mul β] (a : α) :
    coe_fn (mul_equiv e) a = coe_fn e a :=
  rfl

theorem mul_equiv_symm_apply {α : Type u} {β : Type v} (e : α ≃ β) [Mul β] (b : β) :
    coe_fn (mul_equiv.symm (mul_equiv e)) b = coe_fn (equiv.symm e) b :=
  Eq.refl (coe_fn (mul_equiv.symm (mul_equiv e)) b)

/--
An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ring_equiv {α : Type u} {β : Type v} (e : α ≃ β) [Add β] [Mul β] :
    let _inst : Add α := equiv.has_add e;
      let _inst_3 : Mul α := equiv.has_mul e;
      α ≃+* β :=
  let _inst : Add α := equiv.has_add e;
  let _inst_3 : Mul α := equiv.has_mul e;
  ring_equiv.mk (to_fun e) (inv_fun e) (left_inv e) (right_inv e) sorry sorry

@[simp] theorem ring_equiv_apply {α : Type u} {β : Type v} (e : α ≃ β) [Add β] [Mul β] (a : α) :
    coe_fn (ring_equiv e) a = coe_fn e a :=
  rfl

theorem ring_equiv_symm_apply {α : Type u} {β : Type v} (e : α ≃ β) [Add β] [Mul β] (b : β) :
    coe_fn (ring_equiv.symm (ring_equiv e)) b = coe_fn (equiv.symm e) b :=
  Eq.refl (coe_fn (ring_equiv.symm (ring_equiv e)) b)

/-- Transfer `semigroup` across an `equiv` -/
protected def semigroup {α : Type u} {β : Type v} (e : α ≃ β) [semigroup β] : semigroup α :=
  semigroup.mk Mul.mul sorry

/-- Transfer `comm_semigroup` across an `equiv` -/
protected def comm_semigroup {α : Type u} {β : Type v} (e : α ≃ β) [comm_semigroup β] :
    comm_semigroup α :=
  comm_semigroup.mk semigroup.mul sorry sorry

/-- Transfer `monoid` across an `equiv` -/
protected def monoid {α : Type u} {β : Type v} (e : α ≃ β) [monoid β] : monoid α :=
  monoid.mk semigroup.mul sorry 1 sorry sorry

/-- Transfer `comm_monoid` across an `equiv` -/
protected def add_comm_monoid {α : Type u} {β : Type v} (e : α ≃ β) [add_comm_monoid β] :
    add_comm_monoid α :=
  add_comm_monoid.mk add_comm_semigroup.add sorry add_monoid.zero sorry sorry sorry

/-- Transfer `group` across an `equiv` -/
protected def group {α : Type u} {β : Type v} (e : α ≃ β) [group β] : group α :=
  group.mk monoid.mul sorry monoid.one sorry sorry has_inv.inv Div.div sorry

/-- Transfer `comm_group` across an `equiv` -/
protected def comm_group {α : Type u} {β : Type v} (e : α ≃ β) [comm_group β] : comm_group α :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

/-- Transfer `semiring` across an `equiv` -/
protected def semiring {α : Type u} {β : Type v} (e : α ≃ β) [semiring β] : semiring α :=
  semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry monoid.one sorry sorry sorry sorry
    sorry sorry

/-- Transfer `comm_semiring` across an `equiv` -/
protected def comm_semiring {α : Type u} {β : Type v} (e : α ≃ β) [comm_semiring β] :
    comm_semiring α :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry
    semiring.one sorry sorry sorry sorry sorry sorry sorry

/-- Transfer `ring` across an `equiv` -/
protected def ring {α : Type u} {β : Type v} (e : α ≃ β) [ring β] : ring α :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry
    sorry semiring.mul sorry semiring.one sorry sorry sorry sorry

/-- Transfer `comm_ring` across an `equiv` -/
protected def comm_ring {α : Type u} {β : Type v} (e : α ≃ β) [comm_ring β] : comm_ring α :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry comm_monoid.mul
    sorry comm_monoid.one sorry sorry sorry sorry sorry

/-- Transfer `nonzero` across an `equiv` -/
protected theorem nontrivial {α : Type u} {β : Type v} (e : α ≃ β) [nontrivial β] : nontrivial α :=
  sorry

/-- Transfer `domain` across an `equiv` -/
protected def domain {α : Type u} {β : Type v} (e : α ≃ β) [domain β] : domain α :=
  domain.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry sorry

/-- Transfer `integral_domain` across an `equiv` -/
protected def integral_domain {α : Type u} {β : Type v} (e : α ≃ β) [integral_domain β] :
    integral_domain α :=
  integral_domain.mk domain.add sorry domain.zero sorry sorry domain.neg domain.sub sorry sorry
    domain.mul sorry domain.one sorry sorry sorry sorry sorry sorry sorry

/-- Transfer `division_ring` across an `equiv` -/
protected def division_ring {α : Type u} {β : Type v} (e : α ≃ β) [division_ring β] :
    division_ring α :=
  division_ring.mk domain.add sorry 0 sorry sorry domain.neg domain.sub sorry sorry domain.mul sorry
    1 sorry sorry sorry sorry has_inv.inv Div.div sorry sorry sorry

/-- Transfer `field` across an `equiv` -/
protected def field {α : Type u} {β : Type v} (e : α ≃ β) [field β] : field α :=
  field.mk integral_domain.add sorry integral_domain.zero sorry sorry integral_domain.neg
    integral_domain.sub sorry sorry integral_domain.mul sorry integral_domain.one sorry sorry sorry
    sorry sorry division_ring.inv sorry sorry sorry

/-- Transfer `mul_action` across an `equiv` -/
protected def mul_action {α : Type u} {β : Type v} (R : Type u_1) [monoid R] (e : α ≃ β)
    [mul_action R β] : mul_action R α :=
  mul_action.mk sorry sorry

/-- Transfer `distrib_mul_action` across an `equiv` -/
protected def distrib_mul_action {α : Type u} {β : Type v} (R : Type u_1) [monoid R] (e : α ≃ β)
    [add_comm_monoid β] :
    let _inst : add_comm_monoid α := equiv.add_comm_monoid e;
      [_inst_3 : distrib_mul_action R β] → distrib_mul_action R α :=
  fun (_inst_3 : distrib_mul_action R β) =>
    let _inst_4 : add_comm_monoid α := equiv.add_comm_monoid e;
    distrib_mul_action.mk sorry sorry

/-- Transfer `semimodule` across an `equiv` -/
protected def semimodule {α : Type u} {β : Type v} (R : Type u_1) [semiring R] (e : α ≃ β)
    [add_comm_monoid β] :
    let _inst : add_comm_monoid α := equiv.add_comm_monoid e;
      [_inst_3 : semimodule R β] → semimodule R α :=
  let _inst : add_comm_monoid α := equiv.add_comm_monoid e;
  fun (_inst_3 : semimodule R β) => semimodule.mk sorry sorry

/--
An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linear_equiv {α : Type u} {β : Type v} (R : Type u_1) [semiring R] (e : α ≃ β)
    [add_comm_monoid β] [semimodule R β] :
    let _inst : add_comm_monoid α := equiv.add_comm_monoid e;
      let _inst_4 : semimodule R α := equiv.semimodule R e;
      linear_equiv R α β :=
  let _inst : add_comm_monoid α := equiv.add_comm_monoid e;
  let _inst_4 : semimodule R α := equiv.semimodule R e;
  linear_equiv.mk (add_equiv.to_fun (add_equiv e)) sorry sorry (add_equiv.inv_fun (add_equiv e))
    sorry sorry

/-- Transfer `algebra` across an `equiv` -/
protected def algebra {α : Type u} {β : Type v} (R : Type u_1) [comm_semiring R] (e : α ≃ β)
    [semiring β] :
    let _inst : semiring α := equiv.semiring e;
      [_inst_3 : algebra R β] → algebra R α :=
  let _inst : semiring α := equiv.semiring e;
  fun (_inst_3 : algebra R β) =>
    ring_hom.to_algebra' (ring_hom.comp (↑(ring_equiv.symm (ring_equiv e))) (algebra_map R β)) sorry

/--
An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def alg_equiv {α : Type u} {β : Type v} (R : Type u_1) [comm_semiring R] (e : α ≃ β) [semiring β]
    [algebra R β] :
    let _inst : semiring α := equiv.semiring e;
      let _inst_4 : algebra R α := equiv.algebra R e;
      alg_equiv R α β :=
  let _inst : semiring α := equiv.semiring e;
  let _inst_4 : algebra R α := equiv.algebra R e;
  alg_equiv.mk (ring_equiv.to_fun (ring_equiv e)) (ring_equiv.inv_fun (ring_equiv e)) sorry sorry
    sorry sorry sorry

end equiv


namespace ring_equiv


protected theorem local_ring {A : Type u_1} {B : Type u_2} [comm_ring A] [local_ring A]
    [comm_ring B] (e : A ≃+* B) : local_ring B :=
  local_of_surjective (↑e) (equiv.surjective (to_equiv e))

end Mathlib