/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.linear_map
import Mathlib.group_theory.group_action.sub_mul_action
import Mathlib.PostPort

universes u v l w 

namespace Mathlib

/-!

# Submodules of a module

In this file we define

* `submodule R M` : a subset of a `module` `M` that contains zero and is closed with respect to addition and
  scalar multiplication.

* `subspace k M` : an abbreviation for `submodule` assuming that `k` is a `field`.

## Tags

submodule, subspace, linear map
-/

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure submodule (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M]
    extends add_submonoid M, sub_mul_action R M where

/-- Reinterpret a `submodule` as an `add_submonoid`. -/
/-- Reinterpret a `submodule` as an `sub_mul_action`. -/
namespace submodule


protected instance set.has_coe_t {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] : has_coe_t (submodule R M) (set M) :=
  has_coe_t.mk fun (s : submodule R M) => carrier s

protected instance has_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] : has_mem M (submodule R M) :=
  has_mem.mk fun (x : M) (p : submodule R M) => x ∈ ↑p

protected instance has_coe_to_sort {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] : has_coe_to_sort (submodule R M) :=
  has_coe_to_sort.mk (Type (max 0 v)) fun (p : submodule R M) => Subtype fun (x : M) => x ∈ p

@[simp] theorem coe_sort_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] (p : submodule R M) : ↥↑p = ↥p :=
  rfl

protected theorem exists {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]
    {p : submodule R M} {q : ↥p → Prop} :
    (∃ (x : ↥p), q x) ↔ ∃ (x : M), ∃ (H : x ∈ p), q { val := x, property := H } :=
  set_coe.exists

protected theorem forall {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]
    {p : submodule R M} {q : ↥p → Prop} :
    (∀ (x : ↥p), q x) ↔ ∀ (x : M) (H : x ∈ p), q { val := x, property := H } :=
  set_coe.forall

theorem coe_injective {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] :
    function.injective coe :=
  sorry

@[simp] theorem coe_set_eq {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] {p : submodule R M} {q : submodule R M} : ↑p = ↑q ↔ p = q :=
  function.injective.eq_iff coe_injective

@[simp] theorem mk_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]
    (S : set M) (h₁ : 0 ∈ S) (h₂ : ∀ {a b : M}, a ∈ S → b ∈ S → a + b ∈ S)
    (h₃ : ∀ (c : R) {x : M}, x ∈ S → c • x ∈ S) : ↑(mk S h₁ h₂ h₃) = S :=
  rfl

theorem ext'_iff {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]
    {p : submodule R M} {q : submodule R M} : p = q ↔ ↑p = ↑q :=
  iff.symm coe_set_eq

theorem ext {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M]
    {p : submodule R M} {q : submodule R M} (h : ∀ (x : M), x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective (set.ext h)

theorem to_add_submonoid_injective {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] : function.injective to_add_submonoid :=
  fun (p q : submodule R M) (h : to_add_submonoid p = to_add_submonoid q) =>
    iff.mpr ext'_iff (iff.mp add_submonoid.ext'_iff h)

@[simp] theorem to_add_submonoid_eq {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] {p : submodule R M} {q : submodule R M} :
    to_add_submonoid p = to_add_submonoid q ↔ p = q :=
  function.injective.eq_iff to_add_submonoid_injective

theorem to_sub_mul_action_injective {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] : function.injective to_sub_mul_action :=
  fun (p q : submodule R M) (h : to_sub_mul_action p = to_sub_mul_action q) =>
    iff.mpr ext'_iff (iff.mp sub_mul_action.ext'_iff h)

@[simp] theorem to_sub_mul_action_eq {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    [semimodule R M] {p : submodule R M} {q : submodule R M} :
    to_sub_mul_action p = to_sub_mul_action q ↔ p = q :=
  function.injective.eq_iff to_sub_mul_action_injective

end submodule


namespace submodule


-- We can infer the module structure implicitly from the bundled submodule,

-- rather than via typeclass resolution.

@[simp] theorem mem_carrier {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} : x ∈ carrier p ↔ x ∈ ↑p :=
  iff.rfl

@[simp] theorem mem_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} : x ∈ ↑p ↔ x ∈ p :=
  iff.rfl

@[simp] theorem zero_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : 0 ∈ p :=
  zero_mem' p

theorem add_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} {y : M} (h₁ : x ∈ p) (h₂ : y ∈ p) :
    x + y ∈ p :=
  add_mem' p h₁ h₂

theorem smul_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} (r : R) (h : x ∈ p) : r • x ∈ p :=
  smul_mem' p r h

theorem sum_mem {R : Type u} {M : Type v} {ι : Type w} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {t : finset ι} {f : ι → M} :
    (∀ (c : ι), c ∈ t → f c ∈ p) → (finset.sum t fun (i : ι) => f i) ∈ p :=
  add_submonoid.sum_mem (to_add_submonoid p)

theorem sum_smul_mem {R : Type u} {M : Type v} {ι : Type w} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {t : finset ι} {f : ι → M} (r : ι → R)
    (hyp : ∀ (c : ι), c ∈ t → f c ∈ p) : (finset.sum t fun (i : ι) => r i • f i) ∈ p :=
  sum_mem p fun (i : ι) (hi : i ∈ t) => smul_mem p (r i) (hyp i hi)

@[simp] theorem smul_mem_iff' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} (u : units R) :
    ↑u • x ∈ p ↔ x ∈ p :=
  sub_mul_action.smul_mem_iff' (to_sub_mul_action p) u

protected instance has_add {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : Add ↥p :=
  { add := fun (x y : ↥p) => { val := subtype.val x + subtype.val y, property := sorry } }

protected instance has_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : HasZero ↥p :=
  { zero := { val := 0, property := zero_mem p } }

protected instance inhabited {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : Inhabited ↥p :=
  { default := 0 }

protected instance has_scalar {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : has_scalar R ↥p :=
  has_scalar.mk fun (c : R) (x : ↥p) => { val := c • subtype.val x, property := sorry }

protected theorem nonempty {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : set.nonempty ↑p :=
  Exists.intro 0 (zero_mem p)

@[simp] theorem mk_eq_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} (h : x ∈ p) :
    { val := x, property := h } = 0 ↔ x = 0 :=
  subtype.ext_iff_val

@[simp] theorem coe_eq_coe {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} {x : ↥p} {y : ↥p} : ↑x = ↑y ↔ x = y :=
  iff.symm subtype.ext_iff_val

@[simp] theorem coe_eq_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} {x : ↥p} : ↑x = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp] theorem coe_add {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} (x : ↥p) (y : ↥p) : ↑(x + y) = ↑x + ↑y :=
  rfl

@[simp] theorem coe_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} : ↑0 = 0 :=
  rfl

@[simp] theorem coe_smul {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} (r : R) (x : ↥p) : ↑(r • x) = r • ↑x :=
  rfl

@[simp] theorem coe_mk {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} (x : M) (hx : x ∈ p) :
    ↑{ val := x, property := hx } = x :=
  rfl

@[simp] theorem coe_mem {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} (x : ↥p) : ↑x ∈ p :=
  subtype.property x

@[simp] protected theorem eta {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} {p : submodule R M} (x : ↥p) (hx : ↑x ∈ p) :
    { val := ↑x, property := hx } = x :=
  subtype.eta x hx

protected instance add_comm_monoid {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : add_comm_monoid ↥p :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance semimodule {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : semimodule R ↥p :=
  semimodule.mk sorry sorry

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : linear_map R (↥p) M :=
  linear_map.mk coe sorry sorry

@[simp] theorem subtype_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) (x : ↥p) :
    coe_fn (submodule.subtype p) x = ↑x :=
  rfl

theorem subtype_eq_val {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M]
    {semimodule_M : semimodule R M} (p : submodule R M) : ⇑(submodule.subtype p) = subtype.val :=
  rfl

theorem neg_mem {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} (hx : x ∈ p) : -x ∈ p :=
  sub_mul_action.neg_mem (to_sub_mul_action p) hx

/-- Reinterpret a submodule as an additive subgroup. -/
def to_add_subgroup {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) : add_subgroup M :=
  add_subgroup.mk (add_submonoid.carrier (to_add_submonoid p)) sorry sorry sorry

@[simp] theorem coe_to_add_subgroup {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) : ↑(to_add_subgroup p) = ↑p :=
  rfl

theorem sub_mem {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} {y : M} :
    x ∈ p → y ∈ p → x - y ∈ p :=
  add_subgroup.sub_mem (to_add_subgroup p)

@[simp] theorem neg_mem_iff {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} : -x ∈ p ↔ x ∈ p :=
  add_subgroup.neg_mem_iff (to_add_subgroup p)

theorem add_mem_iff_left {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} {y : M} :
    y ∈ p → (x + y ∈ p ↔ x ∈ p) :=
  add_subgroup.add_mem_cancel_right (to_add_subgroup p)

theorem add_mem_iff_right {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) {x : M} {y : M} :
    x ∈ p → (x + y ∈ p ↔ y ∈ p) :=
  add_subgroup.add_mem_cancel_left (to_add_subgroup p)

protected instance has_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) : Neg ↥p :=
  { neg := fun (x : ↥p) => { val := -subtype.val x, property := sorry } }

@[simp] theorem coe_neg {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) (x : ↥p) : ↑(-x) = -↑x :=
  rfl

protected instance add_comm_group {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) : add_comm_group ↥p :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg add_comm_group.sub sorry sorry

@[simp] theorem coe_sub {R : Type u} {M : Type v} [ring R] [add_comm_group M]
    {semimodule_M : semimodule R M} (p : submodule R M) (x : ↥p) (y : ↥p) : ↑(x - y) = ↑x - ↑y :=
  rfl

end submodule


namespace submodule


theorem smul_mem_iff {R : Type u} {M : Type v} [division_ring R] [add_comm_group M] [module R M]
    (p : submodule R M) {r : R} {x : M} (r0 : r ≠ 0) : r • x ∈ p ↔ x ∈ p :=
  sub_mul_action.smul_mem_iff (to_sub_mul_action p) r0

end submodule


/-- Subspace of a vector space. Defined to equal `submodule`. -/
def subspace (R : Type u) (M : Type v) [field R] [add_comm_group M] [vector_space R M] :=
  submodule R M

end Mathlib