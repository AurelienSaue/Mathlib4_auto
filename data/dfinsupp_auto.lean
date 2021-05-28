/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.module.pi
import Mathlib.algebra.big_operators.basic
import Mathlib.data.set.finite
import Mathlib.group_theory.submonoid.basic
import PostPort

universes u v l v₁ v₂ w u_1 u_2 u_3 u_4 u₁ x 

namespace Mathlib

/-!
# Dependent functions with finite support

For a non-dependent version see `data/finsupp.lean`.
-/

namespace dfinsupp


structure pre (ι : Type u) (β : ι → Type v) [(i : ι) → HasZero (β i)] 
where
  to_fun : (i : ι) → β i
  pre_support : multiset ι
  zero : ∀ (i : ι), i ∈ pre_support ∨ to_fun i = 0

protected instance inhabited_pre (ι : Type u) (β : ι → Type v) [(i : ι) → HasZero (β i)] : Inhabited (pre ι β) :=
  { default := pre.mk (fun (i : ι) => 0) ∅ sorry }

protected instance pre.setoid (ι : Type u) (β : ι → Type v) [(i : ι) → HasZero (β i)] : setoid (pre ι β) :=
  setoid.mk (fun (x y : pre ι β) => ∀ (i : ι), pre.to_fun x i = pre.to_fun y i) sorry

end dfinsupp


/-- A dependent function `Π i, β i` with finite support. -/
def dfinsupp {ι : Type u} (β : ι → Type v) [(i : ι) → HasZero (β i)]  :=
  quotient sorry

infixl:25 " →ₚ " => Mathlib.dfinsupp

namespace dfinsupp


protected instance has_coe_to_fun {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] : has_coe_to_fun (dfinsupp fun (i : ι) => β i) :=
  has_coe_to_fun.mk (fun (_x : dfinsupp fun (i : ι) => β i) => (i : ι) → β i)
    fun (f : dfinsupp fun (i : ι) => β i) => quotient.lift_on f pre.to_fun sorry

protected instance has_zero {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] : HasZero (dfinsupp fun (i : ι) => β i) :=
  { zero := quotient.mk (pre.mk (fun (i : ι) => 0) ∅ sorry) }

protected instance inhabited {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] : Inhabited (dfinsupp fun (i : ι) => β i) :=
  { default := 0 }

@[simp] theorem zero_apply {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] (i : ι) : coe_fn 0 i = 0 :=
  rfl

theorem ext {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {f : dfinsupp fun (i : ι) => β i} {g : dfinsupp fun (i : ι) => β i} (H : ∀ (i : ι), coe_fn f i = coe_fn g i) : f = g := sorry

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `map_range f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`. -/
def map_range {ι : Type u} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i) (hf : ∀ (i : ι), f i 0 = 0) (g : dfinsupp fun (i : ι) => β₁ i) : dfinsupp fun (i : ι) => β₂ i :=
  quotient.lift_on g
    (fun (x : pre ι fun (i : ι) => β₁ i) =>
      quotient.mk (pre.mk (fun (i : ι) => f i (pre.to_fun x i)) (pre.pre_support x) sorry))
    sorry

@[simp] theorem map_range_apply {ι : Type u} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i) (hf : ∀ (i : ι), f i 0 = 0) (g : dfinsupp fun (i : ι) => β₁ i) (i : ι) : coe_fn (map_range f hf g) i = f i (coe_fn g i) :=
  quotient.induction_on g fun (x : pre ι fun (i : ι) => β₁ i) => rfl

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zip_with f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
def zip_with {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i → β i) (hf : ∀ (i : ι), f i 0 0 = 0) (g₁ : dfinsupp fun (i : ι) => β₁ i) (g₂ : dfinsupp fun (i : ι) => β₂ i) : dfinsupp fun (i : ι) => β i :=
  quotient.lift_on₂ g₁ g₂
    (fun (x : pre ι fun (i : ι) => β₁ i) (y : pre ι fun (i : ι) => β₂ i) =>
      quotient.mk
        (pre.mk (fun (i : ι) => f i (pre.to_fun x i) (pre.to_fun y i)) (pre.pre_support x + pre.pre_support y) sorry))
    sorry

@[simp] theorem zip_with_apply {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] (f : (i : ι) → β₁ i → β₂ i → β i) (hf : ∀ (i : ι), f i 0 0 = 0) (g₁ : dfinsupp fun (i : ι) => β₁ i) (g₂ : dfinsupp fun (i : ι) => β₂ i) (i : ι) : coe_fn (zip_with f hf g₁ g₂) i = f i (coe_fn g₁ i) (coe_fn g₂ i) :=
  quotient.induction_on₂ g₁ g₂ fun (_x : pre ι fun (i : ι) => β₁ i) (_x_1 : pre ι fun (i : ι) => β₂ i) => rfl

protected instance has_add {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] : Add (dfinsupp fun (i : ι) => β i) :=
  { add := zip_with (fun (_x : ι) => Add.add) sorry }

@[simp] theorem add_apply {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] (g₁ : dfinsupp fun (i : ι) => β i) (g₂ : dfinsupp fun (i : ι) => β i) (i : ι) : coe_fn (g₁ + g₂) i = coe_fn g₁ i + coe_fn g₂ i :=
  zip_with_apply (fun (_x : ι) => Add.add) has_add._proof_1 g₁ g₂ i

protected instance add_monoid {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] : add_monoid (dfinsupp fun (i : ι) => β i) :=
  add_monoid.mk Add.add sorry 0 sorry sorry

protected instance is_add_monoid_hom {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] {i : ι} : is_add_monoid_hom fun (g : dfinsupp fun (i : ι) => β i) => coe_fn g i :=
  is_add_monoid_hom.mk (zero_apply i)

protected instance has_neg {ι : Type u} {β : ι → Type v} [(i : ι) → add_group (β i)] : Neg (dfinsupp fun (i : ι) => β i) :=
  { neg := fun (f : dfinsupp fun (i : ι) => β i) => map_range (fun (_x : ι) => Neg.neg) sorry f }

protected instance add_comm_monoid {ι : Type u} {β : ι → Type v} [(i : ι) → add_comm_monoid (β i)] : add_comm_monoid (dfinsupp fun (i : ι) => β i) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

@[simp] theorem neg_apply {ι : Type u} {β : ι → Type v} [(i : ι) → add_group (β i)] (g : dfinsupp fun (i : ι) => β i) (i : ι) : coe_fn (-g) i = -coe_fn g i :=
  map_range_apply (fun (_x : ι) => Neg.neg) has_neg._proof_1 g i

protected instance add_group {ι : Type u} {β : ι → Type v} [(i : ι) → add_group (β i)] : add_group (dfinsupp fun (i : ι) => β i) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg
    (sub_neg_monoid.sub._default add_monoid.add sorry add_monoid.zero sorry sorry Neg.neg) sorry

@[simp] theorem sub_apply {ι : Type u} {β : ι → Type v} [(i : ι) → add_group (β i)] (g₁ : dfinsupp fun (i : ι) => β i) (g₂ : dfinsupp fun (i : ι) => β i) (i : ι) : coe_fn (g₁ - g₂) i = coe_fn g₁ i - coe_fn g₂ i := sorry

protected instance add_comm_group {ι : Type u} {β : ι → Type v} [(i : ι) → add_comm_group (β i)] : add_comm_group (dfinsupp fun (i : ι) => β i) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry sorry

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
protected instance has_scalar {ι : Type u} {β : ι → Type v} {γ : Type w} [semiring γ] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → semimodule γ (β i)] : has_scalar γ (dfinsupp fun (i : ι) => β i) :=
  has_scalar.mk fun (c : γ) (v : dfinsupp fun (i : ι) => β i) => map_range (fun (_x : ι) => has_scalar.smul c) sorry v

@[simp] theorem smul_apply {ι : Type u} {β : ι → Type v} {γ : Type w} [semiring γ] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → semimodule γ (β i)] (b : γ) (v : dfinsupp fun (i : ι) => β i) (i : ι) : coe_fn (b • v) i = b • coe_fn v i :=
  map_range_apply (fun (_x : ι) => has_scalar.smul b) (has_scalar._proof_1 b) v i

/-- Dependent functions with finite support inherit a semimodule structure from such a structure on
each coordinate. -/
protected instance semimodule {ι : Type u} {β : ι → Type v} {γ : Type w} [semiring γ] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → semimodule γ (β i)] : semimodule γ (dfinsupp fun (i : ι) => β i) :=
  semimodule.mk sorry sorry

/-- `filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] (p : ι → Prop) [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) : dfinsupp fun (i : ι) => β i :=
  quotient.lift_on f
    (fun (x : pre ι fun (i : ι) => β i) =>
      quotient.mk (pre.mk (fun (i : ι) => ite (p i) (pre.to_fun x i) 0) (pre.pre_support x) sorry))
    sorry

@[simp] theorem filter_apply {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] (p : ι → Prop) [decidable_pred p] (i : ι) (f : dfinsupp fun (i : ι) => β i) : coe_fn (filter p f) i = ite (p i) (coe_fn f i) 0 :=
  quotient.induction_on f fun (x : pre ι fun (i : ι) => β i) => rfl

theorem filter_apply_pos {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {p : ι → Prop} [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) {i : ι} (h : p i) : coe_fn (filter p f) i = coe_fn f i := sorry

theorem filter_apply_neg {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {p : ι → Prop} [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) {i : ι} (h : ¬p i) : coe_fn (filter p f) i = 0 := sorry

theorem filter_pos_add_filter_neg {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] (f : dfinsupp fun (i : ι) => β i) (p : ι → Prop) [decidable_pred p] : filter p f + filter (fun (i : ι) => ¬p i) f = f := sorry

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtype_domain {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] (p : ι → Prop) [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) : dfinsupp fun (i : Subtype p) => β ↑i :=
  quotient.lift_on f
    (fun (x : pre ι fun (i : ι) => β i) =>
      quotient.mk
        (pre.mk (fun (i : Subtype p) => pre.to_fun x ↑i)
          (multiset.map
            (fun (j : Subtype fun (x_1 : ι) => x_1 ∈ multiset.filter p (pre.pre_support x)) =>
              { val := ↑j, property := sorry })
            (multiset.attach (multiset.filter p (pre.pre_support x))))
          sorry))
    sorry

@[simp] theorem subtype_domain_zero {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {p : ι → Prop} [decidable_pred p] : subtype_domain p 0 = 0 :=
  rfl

@[simp] theorem subtype_domain_apply {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] {p : ι → Prop} [decidable_pred p] {i : Subtype p} {v : dfinsupp fun (i : ι) => β i} : coe_fn (subtype_domain p v) i = coe_fn v ↑i :=
  quotient.induction_on v fun (x : pre ι fun (i : ι) => β i) => rfl

@[simp] theorem subtype_domain_add {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] {p : ι → Prop} [decidable_pred p] {v : dfinsupp fun (i : ι) => β i} {v' : dfinsupp fun (i : ι) => β i} : subtype_domain p (v + v') = subtype_domain p v + subtype_domain p v' := sorry

protected instance subtype_domain.is_add_monoid_hom {ι : Type u} {β : ι → Type v} [(i : ι) → add_monoid (β i)] {p : ι → Prop} [decidable_pred p] : is_add_monoid_hom (subtype_domain p) :=
  is_add_monoid_hom.mk subtype_domain_zero

@[simp] theorem subtype_domain_neg {ι : Type u} {β : ι → Type v} [(i : ι) → add_group (β i)] {p : ι → Prop} [decidable_pred p] {v : dfinsupp fun (i : ι) => β i} : subtype_domain p (-v) = -subtype_domain p v := sorry

@[simp] theorem subtype_domain_sub {ι : Type u} {β : ι → Type v} [(i : ι) → add_group (β i)] {p : ι → Prop} [decidable_pred p] {v : dfinsupp fun (i : ι) => β i} {v' : dfinsupp fun (i : ι) => β i} : subtype_domain p (v - v') = subtype_domain p v - subtype_domain p v' := sorry

theorem finite_supp {ι : Type u} {β : ι → Type v} [(i : ι) → HasZero (β i)] (f : dfinsupp fun (i : ι) => β i) : set.finite (set_of fun (i : ι) => coe_fn f i ≠ 0) := sorry

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `finset`. -/
def mk {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] (s : finset ι) (x : (i : ↥↑s) → β ↑i) : dfinsupp fun (i : ι) => β i :=
  quotient.mk
    (pre.mk (fun (i : ι) => dite (i ∈ s) (fun (H : i ∈ s) => x { val := i, property := H }) fun (H : ¬i ∈ s) => 0)
      (finset.val s) sorry)

@[simp] theorem mk_apply {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {s : finset ι} {x : (i : ↥↑s) → β ↑i} {i : ι} : coe_fn (mk s x) i = dite (i ∈ s) (fun (H : i ∈ s) => x { val := i, property := H }) fun (H : ¬i ∈ s) => 0 :=
  rfl

theorem mk_injective {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] (s : finset ι) : function.injective (mk s) := sorry

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] (i : ι) (b : β i) : dfinsupp fun (i : ι) => β i :=
  mk (singleton i) fun (j : ↥↑(singleton i)) => eq.rec_on sorry b

@[simp] theorem single_apply {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} {i' : ι} {b : β i} : coe_fn (single i b) i' = dite (i = i') (fun (h : i = i') => eq.rec_on h b) fun (h : ¬i = i') => 0 := sorry

@[simp] theorem single_zero {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} : single i 0 = 0 := sorry

@[simp] theorem single_eq_same {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} {b : β i} : coe_fn (single i b) i = b := sorry

theorem single_eq_of_ne {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} {i' : ι} {b : β i} (h : i ≠ i') : coe_fn (single i b) i' = 0 := sorry

theorem single_injective {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} : function.injective (single i) := sorry

/-- Like `finsupp.single_eq_single_iff`, but with a `heq` due to dependent types -/
theorem single_eq_single_iff {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] (i : ι) (j : ι) (xi : β i) (xj : β j) : single i xi = single j xj ↔ i = j ∧ xi == xj ∨ xi = 0 ∧ xj = 0 := sorry

/-- Redefine `f i` to be `0`. -/
def erase {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] (i : ι) (f : dfinsupp fun (i : ι) => β i) : dfinsupp fun (i : ι) => β i :=
  quotient.lift_on f
    (fun (x : pre ι fun (i : ι) => β i) =>
      quotient.mk (pre.mk (fun (j : ι) => ite (j = i) 0 (pre.to_fun x j)) (pre.pre_support x) sorry))
    sorry

@[simp] theorem erase_apply {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} {j : ι} {f : dfinsupp fun (i : ι) => β i} : coe_fn (erase i f) j = ite (j = i) 0 (coe_fn f j) :=
  quotient.induction_on f fun (x : pre ι fun (i : ι) => β i) => rfl

@[simp] theorem erase_same {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} {f : dfinsupp fun (i : ι) => β i} : coe_fn (erase i f) i = 0 := sorry

theorem erase_ne {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {i : ι} {i' : ι} {f : dfinsupp fun (i : ι) => β i} (h : i' ≠ i) : coe_fn (erase i f) i' = coe_fn f i' := sorry

@[simp] theorem single_add {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {i : ι} {b₁ : β i} {b₂ : β i} : single i (b₁ + b₂) = single i b₁ + single i b₂ := sorry

/-- `dfinsupp.single` as an `add_monoid_hom`. -/
@[simp] theorem single_add_hom_apply {ι : Type u} (β : ι → Type v) [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] (i : ι) (b : β i) : coe_fn (single_add_hom β i) b = single i b :=
  Eq.refl (coe_fn (single_add_hom β i) b)

theorem single_add_erase {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {i : ι} {f : dfinsupp fun (i : ι) => β i} : single i (coe_fn f i) + erase i f = f := sorry

theorem erase_add_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {i : ι} {f : dfinsupp fun (i : ι) => β i} : erase i f + single i (coe_fn f i) = f := sorry

protected theorem induction {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {p : (dfinsupp fun (i : ι) => β i) → Prop} (f : dfinsupp fun (i : ι) => β i) (h0 : p 0) (ha : ∀ (i : ι) (b : β i) (f : dfinsupp fun (i : ι) => β i), coe_fn f i = 0 → b ≠ 0 → p f → p (single i b + f)) : p f := sorry

theorem induction₂ {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {p : (dfinsupp fun (i : ι) => β i) → Prop} (f : dfinsupp fun (i : ι) => β i) (h0 : p 0) (ha : ∀ (i : ι) (b : β i) (f : dfinsupp fun (i : ι) => β i), coe_fn f i = 0 → b ≠ 0 → p f → p (f + single i b)) : p f := sorry

@[simp] theorem add_closure_Union_range_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] : add_submonoid.closure (set.Union fun (i : ι) => set.range (single i)) = ⊤ := sorry

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {γ : Type w} [add_monoid γ] {f : (dfinsupp fun (i : ι) => β i) →+ γ} {g : (dfinsupp fun (i : ι) => β i) →+ γ} (H : ∀ (i : ι) (y : β i), coe_fn f (single i y) = coe_fn g (single i y)) : f = g := sorry

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
theorem add_hom_ext' {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {γ : Type w} [add_monoid γ] {f : (dfinsupp fun (i : ι) => β i) →+ γ} {g : (dfinsupp fun (i : ι) => β i) →+ γ} (H : ∀ (x : ι), add_monoid_hom.comp f (single_add_hom β x) = add_monoid_hom.comp g (single_add_hom β x)) : f = g :=
  add_hom_ext fun (x : ι) => add_monoid_hom.congr_fun (H x)

@[simp] theorem mk_add {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] {s : finset ι} {x : (i : ↥↑s) → β ↑i} {y : (i : ↥↑s) → β ↑i} : mk s (x + y) = mk s x + mk s y := sorry

@[simp] theorem mk_zero {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] {s : finset ι} : mk s 0 = 0 := sorry

@[simp] theorem mk_neg {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_group (β i)] {s : finset ι} {x : (i : ↥↑s) → β (subtype.val i)} : mk s (-x) = -mk s x := sorry

@[simp] theorem mk_sub {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_group (β i)] {s : finset ι} {x : (i : ↥↑s) → β (subtype.val i)} {y : (i : ↥↑s) → β (subtype.val i)} : mk s (x - y) = mk s x - mk s y := sorry

protected instance mk.is_add_group_hom {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_group (β i)] {s : finset ι} : is_add_group_hom (mk s) :=
  is_add_group_hom.mk

@[simp] theorem mk_smul {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] (γ : Type w) [semiring γ] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → semimodule γ (β i)] {s : finset ι} {c : γ} (x : (i : ↥↑s) → β (subtype.val i)) : mk s (c • x) = c • mk s x := sorry

@[simp] theorem single_smul {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] (γ : Type w) [semiring γ] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → semimodule γ (β i)] {i : ι} {c : γ} {x : β i} : single i (c • x) = c • single i x := sorry

/-- Set `{i | f x ≠ 0}` as a `finset`. -/
def support {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (f : dfinsupp fun (i : ι) => β i) : finset ι :=
  quotient.lift_on f
    (fun (x : pre ι fun (i : ι) => β i) =>
      finset.filter (fun (i : ι) => pre.to_fun x i ≠ 0) (multiset.to_finset (pre.pre_support x)))
    sorry

@[simp] theorem support_mk_subset {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {s : finset ι} {x : (i : ↥↑s) → β (subtype.val i)} : support (mk s x) ⊆ s :=
  fun (i : ι) (H : i ∈ support (mk s x)) => iff.mp multiset.mem_to_finset (and.left (iff.mp finset.mem_filter H))

@[simp] theorem mem_support_to_fun {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (f : dfinsupp fun (i : ι) => β i) (i : ι) : i ∈ support f ↔ coe_fn f i ≠ 0 := sorry

theorem eq_mk_support {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (f : dfinsupp fun (i : ι) => β i) : f = mk (support f) fun (i : ↥↑(support f)) => coe_fn f ↑i := sorry

@[simp] theorem support_zero {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] : support 0 = ∅ :=
  rfl

theorem mem_support_iff {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (f : dfinsupp fun (i : ι) => β i) (i : ι) : i ∈ support f ↔ coe_fn f i ≠ 0 :=
  mem_support_to_fun f

@[simp] theorem support_eq_empty {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {f : dfinsupp fun (i : ι) => β i} : support f = ∅ ↔ f = 0 := sorry

protected instance decidable_zero {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] : decidable_pred (Eq 0) :=
  fun (f : dfinsupp fun (i : ι) => β i) => decidable_of_iff (support f = ∅) sorry

theorem support_subset_iff {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {s : set ι} {f : dfinsupp fun (i : ι) => β i} : ↑(support f) ⊆ s ↔ ∀ (i : ι), ¬i ∈ s → coe_fn f i = 0 := sorry

theorem support_single_ne_zero {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {i : ι} {b : β i} (hb : b ≠ 0) : support (single i b) = singleton i := sorry

theorem support_single_subset {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {i : ι} {b : β i} : support (single i b) ⊆ singleton i :=
  support_mk_subset

theorem map_range_def {ι : Type u} [dec : DecidableEq ι] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] [(i : ι) → (x : β₁ i) → Decidable (x ≠ 0)] {f : (i : ι) → β₁ i → β₂ i} {hf : ∀ (i : ι), f i 0 = 0} {g : dfinsupp fun (i : ι) => β₁ i} : map_range f hf g = mk (support g) fun (i : ↥↑(support g)) => f (subtype.val i) (coe_fn g (subtype.val i)) := sorry

@[simp] theorem map_range_single {ι : Type u} [dec : DecidableEq ι] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] {f : (i : ι) → β₁ i → β₂ i} {hf : ∀ (i : ι), f i 0 = 0} {i : ι} {b : β₁ i} : map_range f hf (single i b) = single i (f i b) := sorry

theorem support_map_range {ι : Type u} [dec : DecidableEq ι] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] [(i : ι) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → (x : β₂ i) → Decidable (x ≠ 0)] {f : (i : ι) → β₁ i → β₂ i} {hf : ∀ (i : ι), f i 0 = 0} {g : dfinsupp fun (i : ι) => β₁ i} : support (map_range f hf g) ⊆ support g := sorry

theorem zip_with_def {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] [(i : ι) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → (x : β₂ i) → Decidable (x ≠ 0)] {f : (i : ι) → β₁ i → β₂ i → β i} {hf : ∀ (i : ι), f i 0 0 = 0} {g₁ : dfinsupp fun (i : ι) => β₁ i} {g₂ : dfinsupp fun (i : ι) => β₂ i} : zip_with f hf g₁ g₂ =
  mk (support g₁ ∪ support g₂)
    fun (i : ↥↑(support g₁ ∪ support g₂)) => f (subtype.val i) (coe_fn g₁ (subtype.val i)) (coe_fn g₂ (subtype.val i)) := sorry

theorem support_zip_with {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] [(i : ι) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → (x : β₂ i) → Decidable (x ≠ 0)] {f : (i : ι) → β₁ i → β₂ i → β i} {hf : ∀ (i : ι), f i 0 0 = 0} {g₁ : dfinsupp fun (i : ι) => β₁ i} {g₂ : dfinsupp fun (i : ι) => β₂ i} : support (zip_with f hf g₁ g₂) ⊆ support g₁ ∪ support g₂ := sorry

theorem erase_def {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (i : ι) (f : dfinsupp fun (i : ι) => β i) : erase i f = mk (finset.erase (support f) i) fun (j : ↥↑(finset.erase (support f) i)) => coe_fn f (subtype.val j) := sorry

@[simp] theorem support_erase {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (i : ι) (f : dfinsupp fun (i : ι) => β i) : support (erase i f) = finset.erase (support f) i := sorry

theorem filter_def {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {p : ι → Prop} [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) : filter p f = mk (finset.filter p (support f)) fun (i : ↥↑(finset.filter p (support f))) => coe_fn f (subtype.val i) := sorry

@[simp] theorem support_filter {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {p : ι → Prop} [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) : support (filter p f) = finset.filter p (support f) := sorry

theorem subtype_domain_def {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {p : ι → Prop} [decidable_pred p] (f : dfinsupp fun (i : ι) => β i) : subtype_domain p f = mk (finset.subtype p (support f)) fun (i : ↥↑(finset.subtype p (support f))) => coe_fn f ↑i := sorry

@[simp] theorem support_subtype_domain {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {p : ι → Prop} [decidable_pred p] {f : dfinsupp fun (i : ι) => β i} : support (subtype_domain p f) = finset.subtype p (support f) := sorry

theorem support_add {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {g₁ : dfinsupp fun (i : ι) => β i} {g₂ : dfinsupp fun (i : ι) => β i} : support (g₁ + g₂) ⊆ support g₁ ∪ support g₂ :=
  support_zip_with

@[simp] theorem support_neg {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_group (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {f : dfinsupp fun (i : ι) => β i} : support (-f) = support f := sorry

theorem support_smul {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [semiring γ] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → semimodule γ (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] (b : γ) (v : dfinsupp fun (i : ι) => β i) : support (b • v) ⊆ support v :=
  support_map_range

protected instance decidable_eq {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → HasZero (β i)] [(i : ι) → DecidableEq (β i)] : DecidableEq (dfinsupp fun (i : ι) => β i) :=
  fun (f g : dfinsupp fun (i : ι) => β i) =>
    decidable_of_iff (support f = support g ∧ ∀ (i : ι), i ∈ support f → coe_fn f i = coe_fn g i) sorry

-- [to_additive sum] for dfinsupp.prod doesn't work, the equation lemmas are not generated

/-- `sum f g` is the sum of `g i (f i)` over the support of `f`. -/
def sum {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] (f : dfinsupp fun (i : ι) => β i) (g : (i : ι) → β i → γ) : γ :=
  finset.sum (support f) fun (i : ι) => g i (coe_fn f i)

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
def prod {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [comm_monoid γ] (f : dfinsupp fun (i : ι) => β i) (g : (i : ι) → β i → γ) : γ :=
  finset.prod (support f) fun (i : ι) => g i (coe_fn f i)

theorem prod_map_range_index {ι : Type u} [dec : DecidableEq ι] {γ : Type w} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [(i : ι) → HasZero (β₁ i)] [(i : ι) → HasZero (β₂ i)] [(i : ι) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → (x : β₂ i) → Decidable (x ≠ 0)] [comm_monoid γ] {f : (i : ι) → β₁ i → β₂ i} {hf : ∀ (i : ι), f i 0 = 0} {g : dfinsupp fun (i : ι) => β₁ i} {h : (i : ι) → β₂ i → γ} (h0 : ∀ (i : ι), h i 0 = 1) : prod (map_range f hf g) h = prod g fun (i : ι) (b : β₁ i) => h i (f i b) := sorry

theorem sum_zero_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {h : (i : ι) → β i → γ} : sum 0 h = 0 :=
  rfl

theorem sum_single_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {i : ι} {b : β i} {h : (i : ι) → β i → γ} (h_zero : h i 0 = 0) : sum (single i b) h = h i b := sorry

theorem sum_neg_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_group (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {g : dfinsupp fun (i : ι) => β i} {h : (i : ι) → β i → γ} (h0 : ∀ (i : ι), h i 0 = 0) : sum (-g) h = sum g fun (i : ι) (b : β i) => h i (-b) :=
  sum_map_range_index h0

theorem sum_comm {γ : Type w} {ι₁ : Type u_1} {ι₂ : Type u_2} {β₁ : ι₁ → Type u_3} {β₂ : ι₂ → Type u_4} [DecidableEq ι₁] [DecidableEq ι₂] [(i : ι₁) → HasZero (β₁ i)] [(i : ι₂) → HasZero (β₂ i)] [(i : ι₁) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι₂) → (x : β₂ i) → Decidable (x ≠ 0)] [add_comm_monoid γ] (f₁ : dfinsupp fun (i : ι₁) => β₁ i) (f₂ : dfinsupp fun (i : ι₂) => β₂ i) (h : (i : ι₁) → β₁ i → (i : ι₂) → β₂ i → γ) : (sum f₁ fun (i₁ : ι₁) (x₁ : β₁ i₁) => sum f₂ fun (i₂ : ι₂) (x₂ : β₂ i₂) => h i₁ x₁ i₂ x₂) =
  sum f₂ fun (i₂ : ι₂) (x₂ : β₂ i₂) => sum f₁ fun (i₁ : ι₁) (x₁ : β₁ i₁) => h i₁ x₁ i₂ x₂ :=
  finset.sum_comm

@[simp] theorem sum_apply {ι : Type u} {β : ι → Type v} {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [(i₁ : ι₁) → HasZero (β₁ i₁)] [(i : ι₁) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → add_comm_monoid (β i)] {f : dfinsupp fun (i₁ : ι₁) => β₁ i₁} {g : (i₁ : ι₁) → β₁ i₁ → dfinsupp fun (i : ι) => β i} {i₂ : ι} : coe_fn (sum f g) i₂ = sum f fun (i₁ : ι₁) (b : β₁ i₁) => coe_fn (g i₁ b) i₂ :=
  Eq.symm (finset.sum_hom (support f) fun (f : dfinsupp fun (i : ι) => β i) => coe_fn f i₂)

theorem support_sum {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [(i₁ : ι₁) → HasZero (β₁ i₁)] [(i : ι₁) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {f : dfinsupp fun (i₁ : ι₁) => β₁ i₁} {g : (i₁ : ι₁) → β₁ i₁ → dfinsupp fun (i : ι) => β i} : support (sum f g) ⊆ finset.bUnion (support f) fun (i : ι₁) => support (g i (coe_fn f i)) := sorry

@[simp] theorem prod_one {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [comm_monoid γ] {f : dfinsupp fun (i : ι) => β i} : (prod f fun (i : ι) (b : β i) => 1) = 1 :=
  finset.prod_const_one

@[simp] theorem sum_add {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {f : dfinsupp fun (i : ι) => β i} {h₁ : (i : ι) → β i → γ} {h₂ : (i : ι) → β i → γ} : (sum f fun (i : ι) (b : β i) => h₁ i b + h₂ i b) = sum f h₁ + sum f h₂ :=
  finset.sum_add_distrib

@[simp] theorem sum_neg {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_group γ] {f : dfinsupp fun (i : ι) => β i} {h : (i : ι) → β i → γ} : (sum f fun (i : ι) (b : β i) => -h i b) = -sum f h :=
  finset.sum_hom (support f) Neg.neg

theorem prod_add_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [comm_monoid γ] {f : dfinsupp fun (i : ι) => β i} {g : dfinsupp fun (i : ι) => β i} {h : (i : ι) → β i → γ} (h_zero : ∀ (i : ι), h i 0 = 1) (h_add : ∀ (i : ι) (b₁ b₂ : β i), h i (b₁ + b₂) = h i b₁ * h i b₂) : prod (f + g) h = prod f h * prod g h := sorry

/--
When summing over an `add_monoid_hom`, the decidability assumption is not needed, and the result is
also an `add_monoid_hom`.
-/
def sum_add_hom {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_monoid (β i)] [add_comm_monoid γ] (φ : (i : ι) → β i →+ γ) : (dfinsupp fun (i : ι) => β i) →+ γ :=
  add_monoid_hom.mk
    (fun (f : dfinsupp fun (i : ι) => β i) =>
      quotient.lift_on f
        (fun (x : pre ι fun (i : ι) => β i) =>
          finset.sum (multiset.to_finset (pre.pre_support x)) fun (i : ι) => coe_fn (φ i) (pre.to_fun x i))
        sorry)
    sorry sorry

@[simp] theorem sum_add_hom_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_monoid (β i)] [add_comm_monoid γ] (φ : (i : ι) → β i →+ γ) (i : ι) (x : β i) : coe_fn (sum_add_hom φ) (single i x) = coe_fn (φ i) x := sorry

@[simp] theorem sum_add_hom_comp_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [add_comm_monoid γ] (f : (i : ι) → β i →+ γ) (i : ι) : add_monoid_hom.comp (sum_add_hom f) (single_add_hom β i) = f i :=
  add_monoid_hom.ext fun (x : β i) => sum_add_hom_single f i x

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sum_add_hom_apply {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] (φ : (i : ι) → β i →+ γ) (f : dfinsupp fun (i : ι) => β i) : coe_fn (sum_add_hom φ) f = sum f fun (x : ι) => ⇑(φ x) := sorry

/-- The `dfinsupp` version of `finsupp.lift_add_hom`,-/
@[simp] theorem lift_add_hom_symm_apply {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_monoid (β i)] [add_comm_monoid γ] (F : (dfinsupp fun (i : ι) => β i) →+ γ) (i : ι) : coe_fn (add_equiv.symm lift_add_hom) F i = add_monoid_hom.comp F (single_add_hom β i) :=
  Eq.refl (coe_fn (add_equiv.symm lift_add_hom) F i)

/-- The `dfinsupp` version of `finsupp.lift_add_hom_single_add_hom`,-/
@[simp] theorem lift_add_hom_single_add_hom {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_comm_monoid (β i)] : coe_fn lift_add_hom (single_add_hom β) = add_monoid_hom.id (dfinsupp fun (i : ι) => β i) :=
  iff.mpr (equiv.apply_eq_iff_eq_symm_apply (add_equiv.to_equiv lift_add_hom)) rfl

/-- The `dfinsupp` version of `finsupp.lift_add_hom_apply_single`,-/
theorem lift_add_hom_apply_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [add_comm_monoid γ] (f : (i : ι) → β i →+ γ) (i : ι) (x : β i) : coe_fn (coe_fn lift_add_hom f) (single i x) = coe_fn (f i) x := sorry

/-- The `dfinsupp` version of `finsupp.lift_add_hom_comp_single`,-/
theorem lift_add_hom_comp_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_monoid (β i)] [add_comm_monoid γ] (f : (i : ι) → β i →+ γ) (i : ι) : add_monoid_hom.comp (coe_fn lift_add_hom f) (single_add_hom β i) = f i := sorry

/-- The `dfinsupp` version of `finsupp.comp_lift_add_hom`,-/
theorem comp_lift_add_hom {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} {δ : Type u_1} [(i : ι) → add_comm_monoid (β i)] [add_comm_monoid γ] [add_comm_monoid δ] (g : γ →+ δ) (f : (i : ι) → β i →+ γ) : add_monoid_hom.comp g (coe_fn lift_add_hom f) = coe_fn lift_add_hom fun (a : ι) => add_monoid_hom.comp g (f a) := sorry

theorem sum_sub_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → add_comm_group (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_group γ] {f : dfinsupp fun (i : ι) => β i} {g : dfinsupp fun (i : ι) => β i} {h : (i : ι) → β i → γ} (h_sub : ∀ (i : ι) (b₁ b₂ : β i), h i (b₁ - b₂) = h i b₁ - h i b₂) : sum (f - g) h = sum f h - sum g h := sorry

theorem sum_finset_sum_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} {α : Type x} [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {s : finset α} {g : α → dfinsupp fun (i : ι) => β i} {h : (i : ι) → β i → γ} (h_zero : ∀ (i : ι), h i 0 = 0) (h_add : ∀ (i : ι) (b₁ b₂ : β i), h i (b₁ + b₂) = h i b₁ + h i b₂) : (finset.sum s fun (i : α) => sum (g i) h) = sum (finset.sum s fun (i : α) => g i) h := sorry

theorem sum_sum_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [(i₁ : ι₁) → HasZero (β₁ i₁)] [(i : ι₁) → (x : β₁ i) → Decidable (x ≠ 0)] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {f : dfinsupp fun (i₁ : ι₁) => β₁ i₁} {g : (i₁ : ι₁) → β₁ i₁ → dfinsupp fun (i : ι) => β i} {h : (i : ι) → β i → γ} (h_zero : ∀ (i : ι), h i 0 = 0) (h_add : ∀ (i : ι) (b₁ b₂ : β i), h i (b₁ + b₂) = h i b₁ + h i b₂) : sum (sum f g) h = sum f fun (i : ι₁) (b : β₁ i) => sum (g i b) h :=
  Eq.symm (sum_finset_sum_index h_zero h_add)

@[simp] theorem sum_single {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] [(i : ι) → add_comm_monoid (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] {f : dfinsupp fun (i : ι) => β i} : sum f single = f := sorry

theorem sum_subtype_domain_index {ι : Type u} {β : ι → Type v} [dec : DecidableEq ι] {γ : Type w} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [add_comm_monoid γ] {v : dfinsupp fun (i : ι) => β i} {p : ι → Prop} [decidable_pred p] {h : (i : ι) → β i → γ} (hp : ∀ (x : ι), x ∈ support v → p x) : (sum (subtype_domain p v) fun (i : Subtype p) (b : β ↑i) => h (↑i) b) = sum v h := sorry

theorem subtype_domain_sum {ι : Type u} {β : ι → Type v} {γ : Type w} [(i : ι) → add_comm_monoid (β i)] {s : finset γ} {h : γ → dfinsupp fun (i : ι) => β i} {p : ι → Prop} [decidable_pred p] : subtype_domain p (finset.sum s fun (c : γ) => h c) = finset.sum s fun (c : γ) => subtype_domain p (h c) :=
  Eq.symm (finset.sum_hom s (subtype_domain p))

theorem subtype_domain_finsupp_sum {ι : Type u} {β : ι → Type v} {γ : Type w} {δ : γ → Type x} [DecidableEq γ] [(c : γ) → HasZero (δ c)] [(c : γ) → (x : δ c) → Decidable (x ≠ 0)] [(i : ι) → add_comm_monoid (β i)] {p : ι → Prop} [decidable_pred p] {s : dfinsupp fun (c : γ) => δ c} {h : (c : γ) → δ c → dfinsupp fun (i : ι) => β i} : subtype_domain p (sum s h) = sum s fun (c : γ) (d : δ c) => subtype_domain p (h c d) :=
  subtype_domain_sum

end dfinsupp


/-! ### Product and sum lemmas for bundled morphisms -/

namespace monoid_hom


@[simp] theorem map_dfinsupp_prod {ι : Type u} {β : ι → Type v} [DecidableEq ι] {R : Type u_1} {S : Type u_2} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [comm_monoid R] [comm_monoid S] (h : R →* S) (f : dfinsupp fun (i : ι) => β i) (g : (i : ι) → β i → R) : coe_fn h (dfinsupp.prod f g) = dfinsupp.prod f fun (a : ι) (b : β a) => coe_fn h (g a b) :=
  map_prod h (fun (i : ι) => g i (coe_fn f i)) (dfinsupp.support f)

theorem coe_dfinsupp_prod {ι : Type u} {β : ι → Type v} [DecidableEq ι] {R : Type u_1} {S : Type u_2} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [monoid R] [comm_monoid S] (f : dfinsupp fun (i : ι) => β i) (g : (i : ι) → β i → R →* S) : ⇑(dfinsupp.prod f g) = dfinsupp.prod f fun (a : ι) (b : β a) => ⇑(g a b) :=
  coe_prod (fun (i : ι) => g i (coe_fn f i)) (dfinsupp.support f)

@[simp] theorem dfinsupp_prod_apply {ι : Type u} {β : ι → Type v} [DecidableEq ι] {R : Type u_1} {S : Type u_2} [(i : ι) → HasZero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)] [monoid R] [comm_monoid S] (f : dfinsupp fun (i : ι) => β i) (g : (i : ι) → β i → R →* S) (r : R) : coe_fn (dfinsupp.prod f g) r = dfinsupp.prod f fun (a : ι) (b : β a) => coe_fn (g a b) r :=
  finset_prod_apply (fun (i : ι) => g i (coe_fn f i)) (dfinsupp.support f) r

