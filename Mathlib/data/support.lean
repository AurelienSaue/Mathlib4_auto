/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.conditionally_complete_lattice
import Mathlib.algebra.big_operators.basic
import Mathlib.algebra.group.prod
import Mathlib.algebra.group.pi
import Mathlib.PostPort

universes u x w v y 

namespace Mathlib

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
-/

namespace function


/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def support {α : Type u} {A : Type x} [HasZero A] (f : α → A) : set α :=
  set_of fun (x : α) => f x ≠ 0

theorem nmem_support {α : Type u} {A : Type x} [HasZero A] {f : α → A} {x : α} : ¬x ∈ support f ↔ f x = 0 :=
  not_not

theorem mem_support {α : Type u} {A : Type x} [HasZero A] {f : α → A} {x : α} : x ∈ support f ↔ f x ≠ 0 :=
  iff.rfl

theorem support_subset_iff {α : Type u} {A : Type x} [HasZero A] {f : α → A} {s : set α} : support f ⊆ s ↔ ∀ (x : α), f x ≠ 0 → x ∈ s :=
  iff.rfl

theorem support_subset_iff' {α : Type u} {A : Type x} [HasZero A] {f : α → A} {s : set α} : support f ⊆ s ↔ ∀ (x : α), ¬x ∈ s → f x = 0 :=
  forall_congr fun (x : α) => not_imp_comm

@[simp] theorem support_eq_empty_iff {α : Type u} {A : Type x} [HasZero A] {f : α → A} : support f = ∅ ↔ f = 0 := sorry

@[simp] theorem support_zero' {α : Type u} {A : Type x} [HasZero A] : support 0 = ∅ :=
  iff.mpr support_eq_empty_iff rfl

@[simp] theorem support_zero {α : Type u} {A : Type x} [HasZero A] : (support fun (x : α) => 0) = ∅ :=
  support_zero'

theorem support_binop_subset {α : Type u} {A : Type x} [HasZero A] (op : A → A → A) (op0 : op 0 0 = 0) (f : α → A) (g : α → A) : (support fun (x : α) => op (f x) (g x)) ⊆ support f ∪ support g := sorry

theorem support_add {α : Type u} {A : Type x} [add_monoid A] (f : α → A) (g : α → A) : (support fun (x : α) => f x + g x) ⊆ support f ∪ support g :=
  support_binop_subset Add.add (zero_add 0) f g

@[simp] theorem support_neg {α : Type u} {A : Type x} [add_group A] (f : α → A) : (support fun (x : α) => -f x) = support f :=
  set.ext fun (x : α) => not_congr neg_eq_zero

theorem support_sub {α : Type u} {A : Type x} [add_group A] (f : α → A) (g : α → A) : (support fun (x : α) => f x - g x) ⊆ support f ∪ support g :=
  support_binop_subset Sub.sub (sub_self 0) f g

@[simp] theorem support_mul {α : Type u} {A : Type x} [mul_zero_class A] [no_zero_divisors A] (f : α → A) (g : α → A) : (support fun (x : α) => f x * g x) = support f ∩ support g := sorry

@[simp] theorem support_inv {α : Type u} {A : Type x} [division_ring A] (f : α → A) : (support fun (x : α) => f x⁻¹) = support f :=
  set.ext fun (x : α) => not_congr inv_eq_zero

@[simp] theorem support_div {α : Type u} {A : Type x} [division_ring A] (f : α → A) (g : α → A) : (support fun (x : α) => f x / g x) = support f ∩ support g := sorry

theorem support_sup {α : Type u} {A : Type x} [HasZero A] [semilattice_sup A] (f : α → A) (g : α → A) : (support fun (x : α) => f x ⊔ g x) ⊆ support f ∪ support g :=
  support_binop_subset has_sup.sup sup_idem f g

theorem support_inf {α : Type u} {A : Type x} [HasZero A] [semilattice_inf A] (f : α → A) (g : α → A) : (support fun (x : α) => f x ⊓ g x) ⊆ support f ∪ support g :=
  support_binop_subset has_inf.inf inf_idem f g

theorem support_max {α : Type u} {A : Type x} [HasZero A] [linear_order A] (f : α → A) (g : α → A) : (support fun (x : α) => max (f x) (g x)) ⊆ support f ∪ support g :=
  support_sup f g

theorem support_min {α : Type u} {A : Type x} [HasZero A] [linear_order A] (f : α → A) (g : α → A) : (support fun (x : α) => min (f x) (g x)) ⊆ support f ∪ support g :=
  support_inf f g

theorem support_supr {α : Type u} {ι : Sort w} {A : Type x} [HasZero A] [conditionally_complete_lattice A] [Nonempty ι] (f : ι → α → A) : (support fun (x : α) => supr fun (i : ι) => f i x) ⊆ set.Union fun (i : ι) => support (f i) := sorry

theorem support_infi {α : Type u} {ι : Sort w} {A : Type x} [HasZero A] [conditionally_complete_lattice A] [Nonempty ι] (f : ι → α → A) : (support fun (x : α) => infi fun (i : ι) => f i x) ⊆ set.Union fun (i : ι) => support (f i) :=
  support_supr f

theorem support_sum {α : Type u} {β : Type v} {A : Type x} [add_comm_monoid A] (s : finset α) (f : α → β → A) : (support fun (x : β) => finset.sum s fun (i : α) => f i x) ⊆
  set.Union fun (i : α) => set.Union fun (H : i ∈ s) => support (f i) := sorry

theorem support_prod_subset {α : Type u} {β : Type v} {A : Type x} [comm_monoid_with_zero A] (s : finset α) (f : α → β → A) : (support fun (x : β) => finset.prod s fun (i : α) => f i x) ⊆
  set.Inter fun (i : α) => set.Inter fun (H : i ∈ s) => support (f i) :=
  fun (x : β) (hx : x ∈ support fun (x : β) => finset.prod s fun (i : α) => f i x) =>
    iff.mpr set.mem_bInter_iff
      fun (i : α) (hi : i ∈ fun (i : α) => i ∈ finset.val s) (H : f i x = 0) => hx (finset.prod_eq_zero hi H)

theorem support_prod {α : Type u} {β : Type v} {A : Type x} [comm_monoid_with_zero A] [no_zero_divisors A] [nontrivial A] (s : finset α) (f : α → β → A) : (support fun (x : β) => finset.prod s fun (i : α) => f i x) =
  set.Inter fun (i : α) => set.Inter fun (H : i ∈ s) => support (f i) := sorry

theorem support_comp_subset {α : Type u} {A : Type x} {B : Type y} [HasZero A] [HasZero B] {g : A → B} (hg : g 0 = 0) (f : α → A) : support (g ∘ f) ⊆ support f := sorry

theorem support_subset_comp {α : Type u} {A : Type x} {B : Type y} [HasZero A] [HasZero B] {g : A → B} (hg : ∀ {x : A}, g x = 0 → x = 0) (f : α → A) : support f ⊆ support (g ∘ f) :=
  fun (x : α) => mt hg

theorem support_comp_eq {α : Type u} {A : Type x} {B : Type y} [HasZero A] [HasZero B] (g : A → B) (hg : ∀ {x : A}, g x = 0 ↔ x = 0) (f : α → A) : support (g ∘ f) = support f :=
  set.ext fun (x : α) => not_congr hg

theorem support_prod_mk {α : Type u} {A : Type x} {B : Type y} [HasZero A] [HasZero B] (f : α → A) (g : α → B) : (support fun (x : α) => (f x, g x)) = support f ∪ support g := sorry

