/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.group_action.defs
import Mathlib.group_theory.group_action.group
import Mathlib.group_theory.coset
import Mathlib.PostPort

universes u v u_1 w 

namespace Mathlib

/-!
# Basic properties of group actions
-/

namespace mul_action


/-- The orbit of an element under an action. -/
def orbit (α : Type u) {β : Type v} [monoid α] [mul_action α β] (b : β) : set β :=
  set.range fun (x : α) => x • b

theorem mem_orbit_iff {α : Type u} {β : Type v} [monoid α] [mul_action α β] {b₁ : β} {b₂ : β} :
    b₂ ∈ orbit α b₁ ↔ ∃ (x : α), x • b₁ = b₂ :=
  iff.rfl

@[simp] theorem mem_orbit {α : Type u} {β : Type v} [monoid α] [mul_action α β] (b : β) (x : α) :
    x • b ∈ orbit α b :=
  Exists.intro x rfl

@[simp] theorem mem_orbit_self {α : Type u} {β : Type v} [monoid α] [mul_action α β] (b : β) :
    b ∈ orbit α b :=
  sorry

/-- The stabilizer of an element under an action, i.e. what sends the element to itself. Note
that this is a set: for the group stabilizer see `stabilizer`. -/
def stabilizer_carrier (α : Type u) {β : Type v} [monoid α] [mul_action α β] (b : β) : set α :=
  set_of fun (x : α) => x • b = b

@[simp] theorem mem_stabilizer_iff {α : Type u} {β : Type v} [monoid α] [mul_action α β] {b : β}
    {x : α} : x ∈ stabilizer_carrier α b ↔ x • b = b :=
  iff.rfl

/-- The set of elements fixed under the whole action. -/
def fixed_points (α : Type u) (β : Type v) [monoid α] [mul_action α β] : set β :=
  set_of fun (b : β) => ∀ (x : α), x • b = b

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
def fixed_by (α : Type u) (β : Type v) [monoid α] [mul_action α β] (g : α) : set β :=
  set_of fun (x : β) => g • x = x

theorem fixed_eq_Inter_fixed_by (α : Type u) (β : Type v) [monoid α] [mul_action α β] :
    fixed_points α β = set.Inter fun (g : α) => fixed_by α β g :=
  sorry

@[simp] theorem mem_fixed_points {α : Type u} (β : Type v) [monoid α] [mul_action α β] {b : β} :
    b ∈ fixed_points α β ↔ ∀ (x : α), x • b = b :=
  iff.rfl

@[simp] theorem mem_fixed_by {α : Type u} (β : Type v) [monoid α] [mul_action α β] {g : α} {b : β} :
    b ∈ fixed_by α β g ↔ g • b = b :=
  iff.rfl

theorem mem_fixed_points' {α : Type u} (β : Type v) [monoid α] [mul_action α β] {b : β} :
    b ∈ fixed_points α β ↔ ∀ (b' : β), b' ∈ orbit α b → b' = b :=
  sorry

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
def stabilizer.submonoid (α : Type u) {β : Type v} [monoid α] [mul_action α β] (b : β) :
    submonoid α :=
  submonoid.mk (stabilizer_carrier α b) (one_smul α b) sorry

end mul_action


namespace mul_action


/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
def stabilizer (α : Type u) {β : Type v} [group α] [mul_action α β] (b : β) : subgroup α :=
  subgroup.mk (submonoid.carrier sorry) sorry sorry sorry

theorem orbit_eq_iff {α : Type u} {β : Type v} [group α] [mul_action α β] {a : β} {b : β} :
    orbit α a = orbit α b ↔ a ∈ orbit α b :=
  sorry

/-- The stabilizer of a point `b` as a subgroup of `α`. -/
def stabilizer.subgroup (α : Type u) {β : Type v} [group α] [mul_action α β] (b : β) : subgroup α :=
  subgroup.mk (submonoid.carrier (stabilizer.submonoid α b)) sorry sorry sorry

@[simp] theorem mem_orbit_smul (α : Type u) {β : Type v} [group α] [mul_action α β] (g : α)
    (a : β) : a ∈ orbit α (g • a) :=
  sorry

@[simp] theorem smul_mem_orbit_smul (α : Type u) {β : Type v} [group α] [mul_action α β] (g : α)
    (h : α) (a : β) : g • a ∈ orbit α (h • a) :=
  sorry

/-- The relation "in the same orbit". -/
def orbit_rel (α : Type u) (β : Type v) [group α] [mul_action α β] : setoid β :=
  setoid.mk (fun (a b : β) => a ∈ orbit α b) sorry

/-- Action on left cosets. -/
def mul_left_cosets {α : Type u} [group α] (H : subgroup α) (x : α)
    (y : quotient_group.quotient H) : quotient_group.quotient H :=
  quotient.lift_on' y (fun (y : α) => quotient_group.mk (x * y)) sorry

protected instance quotient {α : Type u} [group α] (H : subgroup α) :
    mul_action α (quotient_group.quotient H) :=
  mk sorry sorry

@[simp] theorem quotient.smul_mk {α : Type u} [group α] (H : subgroup α) (a : α) (x : α) :
    a • quotient_group.mk x = quotient_group.mk (a * x) :=
  rfl

@[simp] theorem quotient.smul_coe {α : Type u_1} [comm_group α] (H : subgroup α) (a : α) (x : α) :
    a • ↑x = ↑(a * x) :=
  rfl

protected instance mul_left_cosets_comp_subtype_val {α : Type u} [group α] (H : subgroup α)
    (I : subgroup α) : mul_action (↥I) (quotient_group.quotient H) :=
  comp_hom (quotient_group.quotient H) (subgroup.subtype I)

/-- The canonical map from the quotient of the stabilizer to the set. -/
def of_quotient_stabilizer (α : Type u) {β : Type v} [group α] [mul_action α β] (x : β)
    (g : quotient_group.quotient (stabilizer α x)) : β :=
  quotient.lift_on' g (fun (_x : α) => _x • x) sorry

@[simp] theorem of_quotient_stabilizer_mk (α : Type u) {β : Type v} [group α] [mul_action α β]
    (x : β) (g : α) : of_quotient_stabilizer α x (quotient_group.mk g) = g • x :=
  rfl

theorem of_quotient_stabilizer_mem_orbit (α : Type u) {β : Type v} [group α] [mul_action α β]
    (x : β) (g : quotient_group.quotient (stabilizer α x)) :
    of_quotient_stabilizer α x g ∈ orbit α x :=
  quotient.induction_on' g fun (g : α) => Exists.intro g rfl

theorem of_quotient_stabilizer_smul (α : Type u) {β : Type v} [group α] [mul_action α β] (x : β)
    (g : α) (g' : quotient_group.quotient (stabilizer α x)) :
    of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
  quotient.induction_on' g' fun (_x : α) => mul_smul g _x x

theorem injective_of_quotient_stabilizer (α : Type u) {β : Type v} [group α] [mul_action α β]
    (x : β) : function.injective (of_quotient_stabilizer α x) :=
  sorry

/-- Orbit-stabilizer theorem. -/
def orbit_equiv_quotient_stabilizer (α : Type u) {β : Type v} [group α] [mul_action α β] (b : β) :
    ↥(orbit α b) ≃ quotient_group.quotient (stabilizer α b) :=
  equiv.symm
    (equiv.of_bijective
      (fun (g : quotient_group.quotient (stabilizer α b)) =>
        { val := of_quotient_stabilizer α b g, property := of_quotient_stabilizer_mem_orbit α b g })
      sorry)

@[simp] theorem orbit_equiv_quotient_stabilizer_symm_apply (α : Type u) {β : Type v} [group α]
    [mul_action α β] (b : β) (a : α) :
    ↑(coe_fn (equiv.symm (orbit_equiv_quotient_stabilizer α b)) ↑a) = a • b :=
  rfl

end mul_action


theorem list.smul_sum {α : Type u} {β : Type v} [monoid α] [add_monoid β] [distrib_mul_action α β]
    {r : α} {l : List β} : r • list.sum l = list.sum (list.map (has_scalar.smul r) l) :=
  add_monoid_hom.map_list_sum (const_smul_hom β r) l

theorem multiset.smul_sum {α : Type u} {β : Type v} [monoid α] [add_comm_monoid β]
    [distrib_mul_action α β] {r : α} {s : multiset β} :
    r • multiset.sum s = multiset.sum (multiset.map (has_scalar.smul r) s) :=
  add_monoid_hom.map_multiset_sum (const_smul_hom β r) s

theorem finset.smul_sum {α : Type u} {β : Type v} {γ : Type w} [monoid α] [add_comm_monoid β]
    [distrib_mul_action α β] {r : α} {f : γ → β} {s : finset γ} :
    (r • finset.sum s fun (x : γ) => f x) = finset.sum s fun (x : γ) => r • f x :=
  add_monoid_hom.map_sum (const_smul_hom β r) f s

end Mathlib