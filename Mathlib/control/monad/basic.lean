/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes u v u₀ u₁ v₀ v₁ 

namespace Mathlib

/-!
# Monad

## Attributes

 * ext
 * functor_norm
 * monad_norm

## Implementation Details

Set of rewrite rules and automation for monads in general and
`reader_t`, `state_t`, `except_t` and `option_t` in particular.

The rewrite rules for monads are carefully chosen so that `simp with
functor_norm` will not introduce monadic vocabulary in a context where
applicatives would do just fine but will handle monadic notation
already present in an expression.

In a context where monadic reasoning is desired `simp with monad_norm`
will translate functor and applicative notation into monad notation
and use regular `functor_norm` rules as well.

## Tags

functor, applicative, monad, simp

-/

theorem map_eq_bind_pure_comp (m : Type u → Type v) [Monad m] [is_lawful_monad m] {α : Type u} {β : Type u} (f : α → β) (x : m α) : f <$> x = x >>= pure ∘ f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f <$> x = x >>= pure ∘ f)) (bind_pure_comp_eq_map f x))) (Eq.refl (f <$> x))

/-- run a `state_t` program and discard the final state -/
def state_t.eval {m : Type u → Type v} [Functor m] {σ : Type u} {α : Type u} (cmd : state_t σ m α) (s : σ) : m α :=
  prod.fst <$> state_t.run cmd s

/-- reduce the equivalence between two state monads to the equivalence between
their respective function spaces -/
def state_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ : Type u₀} {σ₁ : Type u₀} {α₂ : Type u₁} {σ₂ : Type u₁} (F : (σ₁ → m₁ (α₁ × σ₁)) ≃ (σ₂ → m₂ (α₂ × σ₂))) : state_t σ₁ m₁ α₁ ≃ state_t σ₂ m₂ α₂ :=
  equiv.mk (fun (_x : state_t σ₁ m₁ α₁) => sorry) (fun (_x : state_t σ₂ m₂ α₂) => sorry) sorry sorry

/-- reduce the equivalence between two reader monads to the equivalence between
their respective function spaces -/
def reader_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ : Type u₀} {ρ₁ : Type u₀} {α₂ : Type u₁} {ρ₂ : Type u₁} (F : (ρ₁ → m₁ α₁) ≃ (ρ₂ → m₂ α₂)) : reader_t ρ₁ m₁ α₁ ≃ reader_t ρ₂ m₂ α₂ :=
  equiv.mk (fun (_x : reader_t ρ₁ m₁ α₁) => sorry) (fun (_x : reader_t ρ₂ m₂ α₂) => sorry) sorry sorry

