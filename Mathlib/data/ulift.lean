/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Jannis Limperg

Facts about `ulift` and `plift`.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u v u_1 u_2 u_3 

namespace Mathlib

namespace plift


/-- Functorial action. -/
@[simp] protected def map {α : Sort u} {β : Sort v} (f : α → β) : plift α → plift β :=
  sorry

/-- Embedding of pure values. -/
@[simp] protected def pure {α : Sort u} : α → plift α :=
  up

/-- Applicative sequencing. -/
@[simp] protected def seq {α : Sort u} {β : Sort v} : plift (α → β) → plift α → plift β :=
  sorry

/-- Monadic bind. -/
@[simp] protected def bind {α : Sort u} {β : Sort v} : plift α → (α → plift β) → plift β :=
  sorry

protected instance monad : Monad plift :=
  { toApplicative :=
      { toFunctor := { map := plift.map, mapConst := fun (α β : Type u_1) => plift.map ∘ function.const β },
        toPure := { pure := plift.pure }, toSeq := { seq := plift.seq },
        toSeqLeft :=
          { seqLeft := fun (α β : Type u_1) (a : plift α) (b : plift β) => plift.seq (plift.map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : plift α) (b : plift β) => plift.seq (plift.map (function.const α id) a) b } },
    toBind := { bind := plift.bind } }

protected instance is_lawful_functor : is_lawful_functor plift :=
  is_lawful_functor.mk (fun (α : Type u_1) (_x : plift α) => sorry)
    fun (α β γ : Type u_1) (g : α → β) (h : β → γ) (_x : plift α) => sorry

protected instance is_lawful_applicative : is_lawful_applicative plift :=
  is_lawful_applicative.mk (fun (α β : Type u_1) (g : α → β) (_x : plift α) => sorry)
    (fun (α β : Type u_1) (g : α → β) (x : α) => rfl) (fun (α β : Type u_1) (_x : plift (α → β)) => sorry)
    fun (α β γ : Type u_1) (_x : plift α) => sorry

protected instance is_lawful_monad : is_lawful_monad plift :=
  is_lawful_monad.mk (fun (α β : Type u_1) (x : α) (f : α → plift β) => rfl)
    fun (α β γ : Type u_1) (_x : plift α) => sorry

@[simp] theorem rec.constant {α : Sort u} {β : Type v} (b : β) : (plift.rec fun (_x : α) => b) = fun (_x : plift α) => b :=
  funext fun (x : plift α) => cases_on x fun (a : α) => Eq.refl (plift.rec (fun (_x : α) => b) (up a))

end plift


namespace ulift


/-- Functorial action. -/
@[simp] protected def map {α : Type u} {β : Type v} (f : α → β) : ulift α → ulift β :=
  sorry

/-- Embedding of pure values. -/
@[simp] protected def pure {α : Type u} : α → ulift α :=
  up

/-- Applicative sequencing. -/
@[simp] protected def seq {α : Type u} {β : Type v} : ulift (α → β) → ulift α → ulift β :=
  sorry

/-- Monadic bind. -/
@[simp] protected def bind {α : Type u} {β : Type v} : ulift α → (α → ulift β) → ulift β :=
  sorry

-- The `up ∘ down` gives us more universe polymorphism than simply `f a`.

protected instance monad : Monad ulift :=
  { toApplicative :=
      { toFunctor := { map := ulift.map, mapConst := fun (α β : Type u_1) => ulift.map ∘ function.const β },
        toPure := { pure := ulift.pure }, toSeq := { seq := ulift.seq },
        toSeqLeft :=
          { seqLeft := fun (α β : Type u_1) (a : ulift α) (b : ulift β) => ulift.seq (ulift.map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : ulift α) (b : ulift β) => ulift.seq (ulift.map (function.const α id) a) b } },
    toBind := { bind := ulift.bind } }

protected instance is_lawful_functor : is_lawful_functor ulift :=
  is_lawful_functor.mk (fun (α : Type u_1) (_x : ulift α) => sorry)
    fun (α β γ : Type u_1) (g : α → β) (h : β → γ) (_x : ulift α) => sorry

protected instance is_lawful_applicative : is_lawful_applicative ulift :=
  is_lawful_applicative.mk (fun (α β : Type u_1) (g : α → β) (_x : ulift α) => sorry)
    (fun (α β : Type u_1) (g : α → β) (x : α) => rfl) (fun (α β : Type u_1) (_x : ulift (α → β)) => sorry)
    fun (α β γ : Type u_1) (_x : ulift α) => sorry

protected instance is_lawful_monad : is_lawful_monad ulift :=
  is_lawful_monad.mk
    (fun (α β : Type u_1) (x : α) (f : α → ulift β) =>
      id (cases_on (f x) fun (down : β) => Eq.refl (up (down (up down)))))
    fun (α β γ : Type u_1) (_x : ulift α) => sorry

@[simp] theorem rec.constant {α : Type u} {β : Sort v} (b : β) : (ulift.rec fun (_x : α) => b) = fun (_x : ulift α) => b :=
  funext fun (x : ulift α) => cases_on x fun (a : α) => Eq.refl (ulift.rec (fun (_x : α) => b) (up a))

