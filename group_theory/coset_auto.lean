/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.subgroup
import PostPort

universes u_1 

namespace Mathlib

/-- The left coset `a*s` corresponding to an element `a : α` and a subset `s : set α` -/
def left_coset {α : Type u_1} [Mul α] (a : α) (s : set α) : set α :=
  (fun (x : α) => a * x) '' s

/-- The right coset `s*a` corresponding to an element `a : α` and a subset `s : set α` -/
def right_coset {α : Type u_1} [Mul α] (s : set α) (a : α) : set α :=
  (fun (x : α) => x * a) '' s

theorem mem_left_coset {α : Type u_1} [Mul α] {s : set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ left_coset a s :=
  set.mem_image_of_mem (fun (b : α) => a * b) hxS

theorem mem_right_coset {α : Type u_1} [Mul α] {s : set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ right_coset s a :=
  set.mem_image_of_mem (fun (b : α) => b * a) hxS

/-- Equality of two left cosets `a*s` and `b*s` -/
def left_coset_equiv {α : Type u_1} [Mul α] (s : set α) (a : α) (b : α)  :=
  left_coset a s = left_coset b s

theorem left_add_coset_equiv_rel {α : Type u_1} [Add α] (s : set α) : equivalence (left_add_coset_equiv s) :=
  mk_equivalence (left_add_coset_equiv s) (fun (a : α) => rfl) (fun (a b : α) => Eq.symm) fun (a b c : α) => Eq.trans

@[simp] theorem left_coset_assoc {α : Type u_1} [semigroup α] (s : set α) (a : α) (b : α) : left_coset a (left_coset b s) = left_coset (a * b) s := sorry

@[simp] theorem left_add_coset_assoc {α : Type u_1} [add_semigroup α] (s : set α) (a : α) (b : α) : left_add_coset a (left_add_coset b s) = left_add_coset (a + b) s := sorry

@[simp] theorem right_coset_assoc {α : Type u_1} [semigroup α] (s : set α) (a : α) (b : α) : right_coset (right_coset s a) b = right_coset s (a * b) := sorry

@[simp] theorem right_add_coset_assoc {α : Type u_1} [add_semigroup α] (s : set α) (a : α) (b : α) : right_add_coset (right_add_coset s a) b = right_add_coset s (a + b) := sorry

theorem left_add_coset_right_add_coset {α : Type u_1} [add_semigroup α] (s : set α) (a : α) (b : α) : right_add_coset (left_add_coset a s) b = left_add_coset a (right_add_coset s b) := sorry

@[simp] theorem one_left_coset {α : Type u_1} [monoid α] (s : set α) : left_coset 1 s = s := sorry

@[simp] theorem zero_left_add_coset {α : Type u_1} [add_monoid α] (s : set α) : left_add_coset 0 s = s := sorry

@[simp] theorem right_coset_one {α : Type u_1} [monoid α] (s : set α) : right_coset s 1 = s := sorry

@[simp] theorem right_add_coset_zero {α : Type u_1} [add_monoid α] (s : set α) : right_add_coset s 0 = s := sorry

theorem mem_own_left_coset {α : Type u_1} [monoid α] (s : submonoid α) (a : α) : a ∈ left_coset a ↑s := sorry

theorem mem_own_right_add_coset {α : Type u_1} [add_monoid α] (s : add_submonoid α) (a : α) : a ∈ right_add_coset (↑s) a := sorry

theorem mem_left_coset_left_coset {α : Type u_1} [monoid α] (s : submonoid α) {a : α} (ha : left_coset a ↑s = ↑s) : a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ s)) (Eq.symm (propext submonoid.mem_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ ↑s)) (Eq.symm ha))) (mem_own_left_coset s a))

theorem mem_right_add_coset_right_add_coset {α : Type u_1} [add_monoid α] (s : add_submonoid α) {a : α} (ha : right_add_coset (↑s) a = ↑s) : a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ s)) (Eq.symm (propext add_submonoid.mem_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ ↑s)) (Eq.symm ha))) (mem_own_right_add_coset s a))

theorem mem_left_coset_iff {α : Type u_1} [group α] {s : set α} {x : α} (a : α) : x ∈ left_coset a s ↔ a⁻¹ * x ∈ s := sorry

theorem mem_right_coset_iff {α : Type u_1} [group α] {s : set α} {x : α} (a : α) : x ∈ right_coset s a ↔ x * (a⁻¹) ∈ s := sorry

theorem left_coset_mem_left_coset {α : Type u_1} [group α] (s : subgroup α) {a : α} (ha : a ∈ s) : left_coset a ↑s = ↑s := sorry

theorem right_add_coset_mem_right_add_coset {α : Type u_1} [add_group α] (s : add_subgroup α) {a : α} (ha : a ∈ s) : right_add_coset (↑s) a = ↑s := sorry

theorem normal_of_eq_cosets {α : Type u_1} [group α] (s : subgroup α) (N : subgroup.normal s) (g : α) : left_coset g ↑s = right_coset (↑s) g := sorry

theorem eq_cosets_of_normal {α : Type u_1} [group α] (s : subgroup α) (h : ∀ (g : α), left_coset g ↑s = right_coset (↑s) g) : subgroup.normal s := sorry

theorem normal_iff_eq_add_cosets {α : Type u_1} [add_group α] (s : add_subgroup α) : add_subgroup.normal s ↔ ∀ (g : α), left_add_coset g ↑s = right_add_coset (↑s) g :=
  { mp := normal_of_eq_add_cosets s, mpr := eq_add_cosets_of_normal s }

namespace quotient_group


/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
def Mathlib.quotient_add_group.left_rel {α : Type u_1} [add_group α] (s : add_subgroup α) : setoid α :=
  setoid.mk (fun (x y : α) => -x + y ∈ s) sorry

protected instance left_rel_decidable {α : Type u_1} [group α] (s : subgroup α) [d : decidable_pred fun (a : α) => a ∈ s] : DecidableRel setoid.r :=
  fun (_x _x_1 : α) => d (_x⁻¹ * _x_1)

/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
def quotient {α : Type u_1} [group α] (s : subgroup α)  :=
  quotient (left_rel s)

end quotient_group


namespace quotient_add_group


/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
def quotient {α : Type u_1} [add_group α] (s : add_subgroup α)  :=
  quotient (left_rel s)

end quotient_add_group


namespace quotient_group


protected instance Mathlib.quotient_add_group.fintype {α : Type u_1} [add_group α] [fintype α] (s : add_subgroup α) [DecidableRel setoid.r] : fintype (quotient_add_group.quotient s) :=
  quotient.fintype (quotient_add_group.left_rel s)

/-- The canonical map from a group `α` to the quotient `α/s`. -/
def Mathlib.quotient_add_group.mk {α : Type u_1} [add_group α] {s : add_subgroup α} (a : α) : quotient_add_group.quotient s :=
  quotient.mk' a

theorem induction_on {α : Type u_1} [group α] {s : subgroup α} {C : quotient s → Prop} (x : quotient s) (H : ∀ (z : α), C (mk z)) : C x :=
  quotient.induction_on' x H

protected instance quotient.has_coe_t {α : Type u_1} [group α] {s : subgroup α} : has_coe_t α (quotient s) :=
  has_coe_t.mk mk

theorem induction_on' {α : Type u_1} [group α] {s : subgroup α} {C : quotient s → Prop} (x : quotient s) (H : ∀ (z : α), C ↑z) : C x :=
  quotient.induction_on' x H

protected instance quotient.inhabited {α : Type u_1} [group α] (s : subgroup α) : Inhabited (quotient s) :=
  { default := ↑1 }

protected theorem eq {α : Type u_1} [group α] {s : subgroup α} {a : α} {b : α} : ↑a = ↑b ↔ a⁻¹ * b ∈ s :=
  quotient.eq'

theorem Mathlib.quotient_add_group.eq_class_eq_left_coset {α : Type u_1} [add_group α] (s : add_subgroup α) (g : α) : (set_of fun (x : α) => ↑x = ↑g) = left_add_coset g ↑s := sorry

theorem preimage_image_coe {α : Type u_1} [group α] (N : subgroup α) (s : set α) : coe ⁻¹' (coe '' s) = set.Union fun (x : ↥N) => (fun (y : α) => y * ↑x) '' s := sorry

end quotient_group


namespace subgroup


/-- The natural bijection between the cosets `g*s` and `s` -/
def Mathlib.add_subgroup.left_coset_equiv_add_subgroup {α : Type u_1} [add_group α] {s : add_subgroup α} (g : α) : ↥(left_add_coset g ↑s) ≃ ↥s :=
  equiv.mk (fun (x : ↥(left_add_coset g ↑s)) => { val := -g + subtype.val x, property := sorry })
    (fun (x : ↥s) => { val := g + subtype.val x, property := sorry }) sorry sorry

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
def Mathlib.add_subgroup.add_group_equiv_quotient_times_add_subgroup {α : Type u_1} [add_group α] {s : add_subgroup α} : α ≃ quotient_add_group.quotient s × ↥s :=
  equiv.trans
    (equiv.trans
      (equiv.trans (equiv.symm (equiv.sigma_preimage_equiv quotient_add_group.mk))
        (equiv.sigma_congr_right
          fun (L : quotient_add_group.quotient s) =>
            eq.mpr sorry (id (eq.mpr sorry (equiv.refl (Subtype fun (x : α) => quotient.mk' x = L))))))
      (equiv.sigma_congr_right
        fun (L : quotient_add_group.quotient s) => add_subgroup.left_coset_equiv_add_subgroup (quotient.out' L)))
    (equiv.sigma_equiv_prod (quotient_add_group.quotient s) ↥s)

end subgroup


namespace quotient_group


-- FIXME -- why is there no `to_additive`?

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α/s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in
`α` and the product `s × t`. -/
def preimage_mk_equiv_subgroup_times_set {α : Type u_1} [group α] (s : subgroup α) (t : set (quotient s)) : ↥(mk ⁻¹' t) ≃ ↥s × ↥t :=
  (fun
      (h :
      ∀ {x : quotient s} {a : α}, x ∈ t → a ∈ s → quotient.mk' (quotient.out' x * a) = quotient.mk' (quotient.out' x)) =>
      equiv.mk (fun (_x : ↥(mk ⁻¹' t)) => sorry) (fun (_x : ↥s × ↥t) => sorry) sorry sorry)
    sorry

end quotient_group


/--
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
