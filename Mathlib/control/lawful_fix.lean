/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.apply
import Mathlib.control.fix
import Mathlib.order.omega_complete_partial_order
import Mathlib.PostPort

universes u_3 l u_1 u_2 

namespace Mathlib

/-!
# Lawful fixed point operators

This module defines the laws required of a `has_fix` instance, using the theory of
omega complete partial orders (ωCPO). Proofs of the lawfulness of all `has_fix` instances in
`control.fix` are provided.

## Main definition

 * class `lawful_fix`
-/

/-- Intuitively, a fixed point operator `fix` is lawful if it satisfies `fix f = f (fix f)` for all
`f`, but this is inconsistent / uninteresting in most cases due to the existence of "exotic"
functions `f`, such as the function that is defined iff its argument is not, familiar from the
halting problem. Instead, this requirement is limited to only functions that are `continuous` in the
sense of `ω`-complete partial orders, which excludes the example because it is not monotone
(making the input argument less defined can make `f` more defined). -/
class lawful_fix (α : Type u_3) [omega_complete_partial_order α] 
extends has_fix α
where
  fix_eq : ∀ {f : α →ₘ α}, omega_complete_partial_order.continuous f → has_fix.fix ⇑f = coe_fn f (has_fix.fix ⇑f)

theorem lawful_fix.fix_eq' {α : Type u_1} [omega_complete_partial_order α] [lawful_fix α] {f : α → α} (hf : omega_complete_partial_order.continuous' f) : has_fix.fix f = f (has_fix.fix f) :=
  lawful_fix.fix_eq (omega_complete_partial_order.continuous.to_bundled f hf)

namespace roption


namespace fix


theorem approx_mono' {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) {i : ℕ} : approx (⇑f) i ≤ approx (⇑f) (Nat.succ i) := sorry

theorem approx_mono {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) {i : ℕ} {j : ℕ} (hij : i ≤ j) : approx (⇑f) i ≤ approx (⇑f) j := sorry

theorem mem_iff {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) (a : α) (b : β a) : b ∈ roption.fix (⇑f) a ↔ ∃ (i : ℕ), b ∈ approx (⇑f) i a := sorry

theorem approx_le_fix {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) (i : ℕ) : approx (⇑f) i ≤ roption.fix ⇑f :=
  fun (a : α) (b : β a) (hh : b ∈ approx (⇑f) i a) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (b ∈ roption.fix (⇑f) a)) (propext (mem_iff f a b)))) (Exists.intro i hh)

theorem exists_fix_le_approx {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) (x : α) : ∃ (i : ℕ), roption.fix (⇑f) x ≤ approx (⇑f) i x := sorry

/-- The series of approximations of `fix f` (see `approx`) as a `chain` -/
def approx_chain {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) : omega_complete_partial_order.chain ((a : α) → roption (β a)) :=
  preorder_hom.mk (approx ⇑f) sorry

theorem le_f_of_mem_approx {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) {x : (a : α) → roption (β a)} (hx : x ∈ approx_chain f) : x ≤ coe_fn f x :=
  eq.mpr (id (propext exists_imp_distrib))
    (fun (i : ℕ) (hx : x = coe_fn (approx_chain f) i) => Eq._oldrec (approx_mono' f) (Eq.symm hx)) hx

theorem approx_mem_approx_chain {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) {i : ℕ} : approx (⇑f) i ∈ approx_chain f :=
  stream.mem_of_nth_eq rfl

end fix


theorem fix_eq_ωSup {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) : roption.fix ⇑f = omega_complete_partial_order.ωSup (fix.approx_chain f) := sorry

theorem fix_le {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)) {X : (a : α) → roption (β a)} (hX : coe_fn f X ≤ X) : roption.fix ⇑f ≤ X := sorry

theorem fix_eq {α : Type u_1} {β : α → Type u_2} {f : ((a : α) → roption (β a)) →ₘ (a : α) → roption (β a)} (hc : omega_complete_partial_order.continuous f) : roption.fix ⇑f = coe_fn f (roption.fix ⇑f) := sorry

end roption


namespace roption


/-- `to_unit` as a monotone function -/
def to_unit_mono {α : Type u_1} (f : roption α →ₘ roption α) : (Unit → roption α) →ₘ Unit → roption α :=
  preorder_hom.mk (fun (x : Unit → roption α) (u : Unit) => coe_fn f (x u)) sorry

theorem to_unit_cont {α : Type u_1} (f : roption α →ₘ roption α) (hc : omega_complete_partial_order.continuous f) : omega_complete_partial_order.continuous (to_unit_mono f) := sorry

protected instance lawful_fix {α : Type u_1} : lawful_fix (roption α) :=
  lawful_fix.mk sorry

end roption


namespace pi


protected instance lawful_fix {α : Type u_1} {β : Type u_2} : lawful_fix (α → roption β) :=
  lawful_fix.mk sorry

/-- `sigma.curry` as a monotone function. -/
def monotone_curry (α : Type u_1) (β : α → Type u_2) (γ : (a : α) → β a → Type u_3) [(x : α) → (y : β x) → preorder (γ x y)] : ((x : sigma fun (a : α) => β a) → γ (sigma.fst x) (sigma.snd x)) →ₘ (a : α) → (b : β a) → γ a b :=
  preorder_hom.mk sigma.curry sorry

/-- `sigma.uncurry` as a monotone function. -/
@[simp] theorem monotone_uncurry_to_fun (α : Type u_1) (β : α → Type u_2) (γ : (a : α) → β a → Type u_3) [(x : α) → (y : β x) → preorder (γ x y)] (f : (x : α) → (y : β x) → (fun (a : α) (b : β a) => γ a b) x y) (x : sigma fun (a : α) => β a) : coe_fn (monotone_uncurry α β γ) f x = sigma.uncurry f x :=
  Eq.refl (coe_fn (monotone_uncurry α β γ) f x)

theorem continuous_curry (α : Type u_1) (β : α → Type u_2) (γ : (a : α) → β a → Type u_3) [(x : α) → (y : β x) → omega_complete_partial_order (γ x y)] : omega_complete_partial_order.continuous (monotone_curry α β γ) := sorry

theorem continuous_uncurry (α : Type u_1) (β : α → Type u_2) (γ : (a : α) → β a → Type u_3) [(x : α) → (y : β x) → omega_complete_partial_order (γ x y)] : omega_complete_partial_order.continuous (monotone_uncurry α β γ) := sorry

protected instance has_fix {α : Type u_1} {β : α → Type u_2} {γ : (a : α) → β a → Type u_3} [has_fix ((x : sigma β) → γ (sigma.fst x) (sigma.snd x))] : has_fix ((x : α) → (y : β x) → γ x y) :=
  has_fix.mk
    fun (f : ((x : α) → (y : β x) → γ x y) → (x : α) → (y : β x) → γ x y) =>
      sigma.curry (has_fix.fix (sigma.uncurry ∘ f ∘ sigma.curry))

theorem uncurry_curry_continuous {α : Type u_1} {β : α → Type u_2} {γ : (a : α) → β a → Type u_3} [(x : α) → (y : β x) → omega_complete_partial_order (γ x y)] {f : ((x : α) → (y : β x) → γ x y) →ₘ (x : α) → (y : β x) → γ x y} (hc : omega_complete_partial_order.continuous f) : omega_complete_partial_order.continuous
  (preorder_hom.comp (monotone_uncurry α β γ) (preorder_hom.comp f (monotone_curry α β γ))) :=
  omega_complete_partial_order.continuous_comp (preorder_hom.comp f (monotone_curry α β γ)) (monotone_uncurry α β γ)
    (omega_complete_partial_order.continuous_comp (monotone_curry α β γ) f (continuous_curry α β γ) hc)
    (continuous_uncurry α β γ)

protected instance pi.lawful_fix' {α : Type u_1} {β : α → Type u_2} {γ : (a : α) → β a → Type u_3} [(x : α) → (y : β x) → omega_complete_partial_order (γ x y)] [lawful_fix ((x : sigma β) → γ (sigma.fst x) (sigma.snd x))] : lawful_fix ((x : α) → (y : β x) → γ x y) :=
  lawful_fix.mk sorry

