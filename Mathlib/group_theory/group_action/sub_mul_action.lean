/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.group_action.basic
import Mathlib.algebra.group_action_hom
import Mathlib.algebra.module.basic
import Mathlib.PostPort

universes u v l 

namespace Mathlib

/-!

# Sets invariant to a `mul_action`

In this file we define `sub_mul_action R M`; a subset of a `mul_action M` which is closed with
respect to scalar multiplication.

For most uses, typically `submodule R M` is more powerful.

## Tags

submodule, mul_action
-/

/-- A sub_mul_action is a set which is closed under scalar multiplication.  -/
structure sub_mul_action (R : Type u) (M : Type v) [has_scalar R M] 
where
  carrier : set M
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

namespace sub_mul_action


protected instance set.has_coe_t {R : Type u} {M : Type v} [has_scalar R M] : has_coe_t (sub_mul_action R M) (set M) :=
  has_coe_t.mk fun (s : sub_mul_action R M) => carrier s

protected instance has_mem {R : Type u} {M : Type v} [has_scalar R M] : has_mem M (sub_mul_action R M) :=
  has_mem.mk fun (x : M) (p : sub_mul_action R M) => x ∈ ↑p

protected instance has_coe_to_sort {R : Type u} {M : Type v} [has_scalar R M] : has_coe_to_sort (sub_mul_action R M) :=
  has_coe_to_sort.mk (Type (max 0 v)) fun (p : sub_mul_action R M) => Subtype fun (x : M) => x ∈ p

protected instance has_top {R : Type u} {M : Type v} [has_scalar R M] : has_top (sub_mul_action R M) :=
  has_top.mk (mk set.univ sorry)

protected instance has_bot {R : Type u} {M : Type v} [has_scalar R M] : has_bot (sub_mul_action R M) :=
  has_bot.mk (mk ∅ sorry)

protected instance inhabited {R : Type u} {M : Type v} [has_scalar R M] : Inhabited (sub_mul_action R M) :=
  { default := ⊥ }

@[simp] theorem coe_sort_coe {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) : ↥↑p = ↥p :=
  rfl

protected theorem exists {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} {q : ↥p → Prop} : (∃ (x : ↥p), q x) ↔ ∃ (x : M), ∃ (H : x ∈ p), q { val := x, property := H } :=
  set_coe.exists

protected theorem forall {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} {q : ↥p → Prop} : (∀ (x : ↥p), q x) ↔ ∀ (x : M) (H : x ∈ p), q { val := x, property := H } :=
  set_coe.forall

theorem coe_injective {R : Type u} {M : Type v} [has_scalar R M] : function.injective coe := sorry

@[simp] theorem coe_set_eq {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} {q : sub_mul_action R M} : ↑p = ↑q ↔ p = q :=
  function.injective.eq_iff coe_injective

theorem ext'_iff {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} {q : sub_mul_action R M} : p = q ↔ ↑p = ↑q :=
  iff.symm coe_set_eq

theorem ext {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} {q : sub_mul_action R M} (h : ∀ (x : M), x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective (set.ext h)

end sub_mul_action


namespace sub_mul_action


@[simp] theorem mem_coe {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) {x : M} : x ∈ ↑p ↔ x ∈ p :=
  iff.rfl

theorem smul_mem {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) {x : M} (r : R) (h : x ∈ p) : r • x ∈ p :=
  smul_mem' p r h

protected instance has_scalar {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) : has_scalar R ↥p :=
  has_scalar.mk fun (c : R) (x : ↥p) => { val := c • subtype.val x, property := sorry }

@[simp] theorem coe_eq_coe {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} {x : ↥p} {y : ↥p} : ↑x = ↑y ↔ x = y :=
  iff.symm subtype.ext_iff_val

@[simp] theorem coe_smul {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} (r : R) (x : ↥p) : ↑(r • x) = r • ↑x :=
  rfl

@[simp] theorem coe_mk {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} (x : M) (hx : x ∈ p) : ↑{ val := x, property := hx } = x :=
  rfl

@[simp] theorem coe_mem {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} (x : ↥p) : ↑x ∈ p :=
  subtype.property x

@[simp] protected theorem eta {R : Type u} {M : Type v} [has_scalar R M] {p : sub_mul_action R M} (x : ↥p) (hx : ↑x ∈ p) : { val := ↑x, property := hx } = x :=
  subtype.eta x hx

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) : mul_action_hom R (↥p) M :=
  mul_action_hom.mk coe sorry

@[simp] theorem subtype_apply {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) (x : ↥p) : coe_fn (sub_mul_action.subtype p) x = ↑x :=
  rfl

theorem subtype_eq_val {R : Type u} {M : Type v} [has_scalar R M] (p : sub_mul_action R M) : ⇑(sub_mul_action.subtype p) = subtype.val :=
  rfl

@[simp] theorem smul_mem_iff' {R : Type u} {M : Type v} [monoid R] [mul_action R M] (p : sub_mul_action R M) {x : M} (u : units R) : ↑u • x ∈ p ↔ x ∈ p := sorry

/-- If the scalar product forms a `mul_action`, then the subset inherits this action -/
protected instance mul_action {R : Type u} {M : Type v} [monoid R] [mul_action R M] (p : sub_mul_action R M) : mul_action R ↥p :=
  mul_action.mk sorry sorry

theorem zero_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : sub_mul_action R M) (h : set.nonempty ↑p) : 0 ∈ p := sorry

/-- If the scalar product forms a `semimodule`, and the `sub_mul_action` is not `⊥`, then the
subset inherits the zero. -/
protected instance has_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (p : sub_mul_action R M) [n_empty : Nonempty ↥p] : HasZero ↥p :=
  { zero := { val := 0, property := sorry } }

theorem neg_mem {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : sub_mul_action R M) {x : M} (hx : x ∈ p) : -x ∈ p :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-x ∈ p)) (Eq.symm (neg_one_smul R x)))) (smul_mem p (-1) hx)

@[simp] theorem neg_mem_iff {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : sub_mul_action R M) {x : M} : -x ∈ p ↔ x ∈ p :=
  { mp := fun (h : -x ∈ p) => eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ p)) (Eq.symm (neg_neg x)))) (neg_mem p h),
    mpr := neg_mem p }

protected instance has_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : sub_mul_action R M) : Neg ↥p :=
  { neg := fun (x : ↥p) => { val := -subtype.val x, property := sorry } }

@[simp] theorem coe_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M] [semimodule R M] (p : sub_mul_action R M) (x : ↥p) : ↑(-x) = -↑x :=
  rfl

end sub_mul_action


namespace sub_mul_action


theorem smul_mem_iff {R : Type u} {M : Type v} [division_ring R] [add_comm_group M] [module R M] (p : sub_mul_action R M) {r : R} {x : M} (r0 : r ≠ 0) : r • x ∈ p ↔ x ∈ p :=
  smul_mem_iff' p (units.mk0 r r0)

