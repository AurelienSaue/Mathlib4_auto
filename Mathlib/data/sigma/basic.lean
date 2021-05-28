/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.lint.default
import Mathlib.tactic.ext
import Mathlib.PostPort

universes u_1 u_4 u_2 u_3 u_5 u_6 

namespace Mathlib

namespace sigma


protected instance inhabited {α : Type u_1} {β : α → Type u_4} [Inhabited α] [Inhabited (β Inhabited.default)] : Inhabited (sigma β) :=
  { default := mk Inhabited.default Inhabited.default }

protected instance decidable_eq {α : Type u_1} {β : α → Type u_4} [h₁ : DecidableEq α] [h₂ : (a : α) → DecidableEq (β a)] : DecidableEq (sigma β) :=
  sorry

@[simp] theorem mk.inj_iff {α : Type u_1} {β : α → Type u_4} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂} : mk a₁ b₁ = mk a₂ b₂ ↔ a₁ = a₂ ∧ b₁ == b₂ := sorry

@[simp] theorem eta {α : Type u_1} {β : α → Type u_4} (x : sigma fun (a : α) => β a) : mk (fst x) (snd x) = x :=
  cases_on x
    fun (x_fst : α) (x_snd : β x_fst) =>
      idRhs (mk (fst (mk x_fst x_snd)) (snd (mk x_fst x_snd)) = mk (fst (mk x_fst x_snd)) (snd (mk x_fst x_snd))) rfl

theorem ext {α : Type u_1} {β : α → Type u_4} {x₀ : sigma β} {x₁ : sigma β} (h₀ : fst x₀ = fst x₁) (h₁ : snd x₀ == snd x₁) : x₀ = x₁ := sorry

theorem ext_iff {α : Type u_1} {β : α → Type u_4} {x₀ : sigma β} {x₁ : sigma β} : x₀ = x₁ ↔ fst x₀ = fst x₁ ∧ snd x₀ == snd x₁ :=
  cases_on x₀ fun (x₀_fst : α) (x₀_snd : β x₀_fst) => cases_on x₁ fun (x₁_fst : α) (x₁_snd : β x₁_fst) => mk.inj_iff

@[simp] theorem forall {α : Type u_1} {β : α → Type u_4} {p : (sigma fun (a : α) => β a) → Prop} : (∀ (x : sigma fun (a : α) => β a), p x) ↔ ∀ (a : α) (b : β a), p (mk a b) := sorry

@[simp] theorem exists {α : Type u_1} {β : α → Type u_4} {p : (sigma fun (a : α) => β a) → Prop} : (∃ (x : sigma fun (a : α) => β a), p x) ↔ ∃ (a : α), ∃ (b : β a), p (mk a b) := sorry

/-- Map the left and right components of a sigma -/
def map {α₁ : Type u_2} {α₂ : Type u_3} {β₁ : α₁ → Type u_5} {β₂ : α₂ → Type u_6} (f₁ : α₁ → α₂) (f₂ : (a : α₁) → β₁ a → β₂ (f₁ a)) (x : sigma β₁) : sigma β₂ :=
  mk (f₁ (fst x)) (f₂ (fst x) (snd x))

end sigma


theorem sigma_mk_injective {α : Type u_1} {β : α → Type u_4} {i : α} : function.injective (sigma.mk i) := sorry

theorem function.injective.sigma_map {α₁ : Type u_2} {α₂ : Type u_3} {β₁ : α₁ → Type u_5} {β₂ : α₂ → Type u_6} {f₁ : α₁ → α₂} {f₂ : (a : α₁) → β₁ a → β₂ (f₁ a)} (h₁ : function.injective f₁) (h₂ : ∀ (a : α₁), function.injective (f₂ a)) : function.injective (sigma.map f₁ f₂) := sorry

theorem function.surjective.sigma_map {α₁ : Type u_2} {α₂ : Type u_3} {β₁ : α₁ → Type u_5} {β₂ : α₂ → Type u_6} {f₁ : α₁ → α₂} {f₂ : (a : α₁) → β₁ a → β₂ (f₁ a)} (h₁ : function.surjective f₁) (h₂ : ∀ (a : α₁), function.surjective (f₂ a)) : function.surjective (sigma.map f₁ f₂) := sorry

/-- Interpret a function on `Σ x : α, β x` as a dependent function with two arguments. -/
def sigma.curry {α : Type u_1} {β : α → Type u_4} {γ : (a : α) → β a → Type u_2} (f : (x : sigma β) → γ (sigma.fst x) (sigma.snd x)) (x : α) (y : β x) : γ x y :=
  f (sigma.mk x y)

/-- Interpret a dependent function with two arguments as a function on `Σ x : α, β x` -/
def sigma.uncurry {α : Type u_1} {β : α → Type u_4} {γ : (a : α) → β a → Type u_2} (f : (x : α) → (y : β x) → γ x y) (x : sigma β) : γ (sigma.fst x) (sigma.snd x) :=
  f (sigma.fst x) (sigma.snd x)

/-- Convert a product type to a Σ-type. -/
@[simp] def prod.to_sigma {α : Type u_1} {β : Type u_2} : α × β → sigma fun (_x : α) => β :=
  sorry

@[simp] theorem prod.fst_to_sigma {α : Type u_1} {β : Type u_2} (x : α × β) : sigma.fst (prod.to_sigma x) = prod.fst x :=
  prod.cases_on x fun (x_fst : α) (x_snd : β) => Eq.refl (sigma.fst (prod.to_sigma (x_fst, x_snd)))

@[simp] theorem prod.snd_to_sigma {α : Type u_1} {β : Type u_2} (x : α × β) : sigma.snd (prod.to_sigma x) = prod.snd x :=
  prod.cases_on x fun (x_fst : α) (x_snd : β) => Eq.refl (sigma.snd (prod.to_sigma (x_fst, x_snd)))

namespace psigma


/-- Nondependent eliminator for `psigma`. -/
def elim {α : Sort u_1} {β : α → Sort u_2} {γ : Sort u_3} (f : (a : α) → β a → γ) (a : psigma β) : γ :=
  cases_on a f

@[simp] theorem elim_val {α : Sort u_1} {β : α → Sort u_2} {γ : Sort u_3} (f : (a : α) → β a → γ) (a : α) (b : β a) : elim f (mk a b) = f a b :=
  rfl

protected instance inhabited {α : Sort u_1} {β : α → Sort u_2} [Inhabited α] [Inhabited (β Inhabited.default)] : Inhabited (psigma β) :=
  { default := mk Inhabited.default Inhabited.default }

protected instance decidable_eq {α : Sort u_1} {β : α → Sort u_2} [h₁ : DecidableEq α] [h₂ : (a : α) → DecidableEq (β a)] : DecidableEq (psigma β) :=
  sorry

theorem mk.inj_iff {α : Sort u_1} {β : α → Sort u_2} {a₁ : α} {a₂ : α} {b₁ : β a₁} {b₂ : β a₂} : mk a₁ b₁ = mk a₂ b₂ ↔ a₁ = a₂ ∧ b₁ == b₂ := sorry

theorem ext {α : Sort u_1} {β : α → Sort u_2} {x₀ : psigma β} {x₁ : psigma β} (h₀ : fst x₀ = fst x₁) (h₁ : snd x₀ == snd x₁) : x₀ = x₁ := sorry

theorem ext_iff {α : Sort u_1} {β : α → Sort u_2} {x₀ : psigma β} {x₁ : psigma β} : x₀ = x₁ ↔ fst x₀ = fst x₁ ∧ snd x₀ == snd x₁ :=
  cases_on x₀ fun (x₀_fst : α) (x₀_snd : β x₀_fst) => cases_on x₁ fun (x₁_fst : α) (x₁_snd : β x₁_fst) => mk.inj_iff

/-- Map the left and right components of a sigma -/
def map {α₁ : Sort u_3} {α₂ : Sort u_4} {β₁ : α₁ → Sort u_5} {β₂ : α₂ → Sort u_6} (f₁ : α₁ → α₂) (f₂ : (a : α₁) → β₁ a → β₂ (f₁ a)) : psigma β₁ → psigma β₂ :=
  sorry

