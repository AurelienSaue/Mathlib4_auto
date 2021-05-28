/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.dfinsupp
import Mathlib.PostPort

universes v w u₁ u_1 

namespace Mathlib

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `direct_sum`.
This notation is in the `direct_sum` locale, accessible after `open_locale direct_sum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

/-- `direct_sum β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open_locale direct_sum` will enable the notation `⨁ i, β i` for `direct_sum β`. -/
def direct_sum (ι : Type v) (β : ι → Type w) [(i : ι) → add_comm_monoid (β i)]  :=
  dfinsupp fun (i : ι) => β i

namespace direct_sum


protected instance add_comm_group {ι : Type v} (β : ι → Type w) [(i : ι) → add_comm_group (β i)] : add_comm_group (direct_sum ι β) :=
  dfinsupp.add_comm_group

@[simp] theorem sub_apply {ι : Type v} {β : ι → Type w} [(i : ι) → add_comm_group (β i)] (g₁ : direct_sum ι fun (i : ι) => β i) (g₂ : direct_sum ι fun (i : ι) => β i) (i : ι) : coe_fn (g₁ - g₂) i = coe_fn g₁ i - coe_fn g₂ i :=
  dfinsupp.sub_apply g₁ g₂ i

@[simp] theorem zero_apply {ι : Type v} (β : ι → Type w) [(i : ι) → add_comm_monoid (β i)] (i : ι) : coe_fn 0 i = 0 :=
  rfl

@[simp] theorem add_apply {ι : Type v} {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] (g₁ : direct_sum ι fun (i : ι) => β i) (g₂ : direct_sum ι fun (i : ι) => β i) (i : ι) : coe_fn (g₁ + g₂) i = coe_fn g₁ i + coe_fn g₂ i :=
  dfinsupp.add_apply g₁ g₂ i

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
def mk {ι : Type v} [dec_ι : DecidableEq ι] (β : ι → Type w) [(i : ι) → add_comm_monoid (β i)] (s : finset ι) : ((i : ↥↑s) → β (subtype.val i)) →+ direct_sum ι fun (i : ι) => β i :=
  add_monoid_hom.mk (dfinsupp.mk s) sorry sorry

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
def of {ι : Type v} [dec_ι : DecidableEq ι] (β : ι → Type w) [(i : ι) → add_comm_monoid (β i)] (i : ι) : β i →+ direct_sum ι fun (i : ι) => β i :=
  dfinsupp.single_add_hom β i

theorem mk_injective {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] (s : finset ι) : function.injective ⇑(mk β s) :=
  dfinsupp.mk_injective s

theorem of_injective {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] (i : ι) : function.injective ⇑(of β i) :=
  dfinsupp.single_injective

protected theorem induction_on {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {C : (direct_sum ι fun (i : ι) => β i) → Prop} (x : direct_sum ι fun (i : ι) => β i) (H_zero : C 0) (H_basic : ∀ (i : ι) (x : β i), C (coe_fn (of β i) x)) (H_plus : ∀ (x y : direct_sum ι fun (i : ι) => β i), C x → C y → C (x + y)) : C x :=
  dfinsupp.induction x H_zero
    fun (i : ι) (b : β i) (f : dfinsupp fun (i : ι) => (fun (i : ι) => (fun (i : ι) => β i) i) i) (h1 : coe_fn f i = 0)
      (h2 : b ≠ 0) (ih : C f) => H_plus (dfinsupp.single i b) f (H_basic i b) ih

/-- `to_add_monoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
def to_add_monoid {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {γ : Type u₁} [add_comm_monoid γ] (φ : (i : ι) → β i →+ γ) : (direct_sum ι fun (i : ι) => β i) →+ γ :=
  coe_fn dfinsupp.lift_add_hom φ

@[simp] theorem to_add_monoid_of {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {γ : Type u₁} [add_comm_monoid γ] (φ : (i : ι) → β i →+ γ) (i : ι) (x : β i) : coe_fn (to_add_monoid φ) (coe_fn (of β i) x) = coe_fn (φ i) x :=
  dfinsupp.lift_add_hom_apply_single φ i x

theorem to_add_monoid.unique {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {γ : Type u₁} [add_comm_monoid γ] (ψ : (direct_sum ι fun (i : ι) => β i) →+ γ) (f : direct_sum ι fun (i : ι) => β i) : coe_fn ψ f = coe_fn (to_add_monoid fun (i : ι) => add_monoid_hom.comp ψ (of β i)) f := sorry

/-- `from_add_monoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
def from_add_monoid {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {γ : Type u₁} [add_comm_monoid γ] : (direct_sum ι fun (i : ι) => γ →+ β i) →+ γ →+ direct_sum ι fun (i : ι) => β i :=
  to_add_monoid fun (i : ι) => coe_fn add_monoid_hom.comp_hom (of β i)

@[simp] theorem from_add_monoid_of {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {γ : Type u₁} [add_comm_monoid γ] (i : ι) (f : γ →+ β i) : coe_fn from_add_monoid (coe_fn (of (fun (i : ι) => γ →+ β i) i) f) = add_monoid_hom.comp (of (fun (i : ι) => β i) i) f := sorry

theorem from_add_monoid_of_apply {ι : Type v} [dec_ι : DecidableEq ι] {β : ι → Type w} [(i : ι) → add_comm_monoid (β i)] {γ : Type u₁} [add_comm_monoid γ] (i : ι) (f : γ →+ β i) (x : γ) : coe_fn (coe_fn from_add_monoid (coe_fn (of (fun (i : ι) => γ →+ β i) i) f)) x =
  coe_fn (of (fun (i : ι) => β i) i) (coe_fn f x) := sorry

/-- `set_to_set β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
-- TODO: generalize this to remove the assumption `S ⊆ T`.

def set_to_set {ι : Type v} [dec_ι : DecidableEq ι] (β : ι → Type w) [(i : ι) → add_comm_monoid (β i)] (S : set ι) (T : set ι) (H : S ⊆ T) : (direct_sum ↥S fun (i : ↥S) => β ↑i) →+ direct_sum ↥T fun (i : ↥T) => β ↑i :=
  to_add_monoid fun (i : ↥S) => of (fun (i : Subtype T) => β ↑i) { val := ↑i, property := sorry }

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def id (M : Type v) (ι : optParam (Type u_1) PUnit) [add_comm_monoid M] [unique ι] : (direct_sum ι fun (_x : ι) => M) ≃+ M :=
  add_equiv.mk ⇑(to_add_monoid fun (_x : ι) => add_monoid_hom.id M) ⇑(of (fun (_x : ι) => M) Inhabited.default) sorry
    sorry sorry

