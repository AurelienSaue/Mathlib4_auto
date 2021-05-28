/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import PrePort
import Lean3Lib.init.logic
import Lean3Lib.init.wf
import PostPort

universes u v 

namespace Mathlib

theorem ex_of_psig {α : Type u} {p : α → Prop} : (psigma fun (x : α) => p x) → ∃ (x : α), p x :=
  fun (ᾰ : psigma fun (x : α) => p x) =>
    psigma.cases_on ᾰ fun (ᾰ_fst : α) (ᾰ_snd : p ᾰ_fst) => idRhs (∃ (x : α), p x) (Exists.intro ᾰ_fst ᾰ_snd)

protected theorem sigma.eq {α : Type u} {β : α → Type v} {p₁ : sigma fun (a : α) => β a} {p₂ : sigma fun (a : α) => β a} (h₁ : sigma.fst p₁ = sigma.fst p₂) : eq.rec_on h₁ (sigma.snd p₁) = sigma.snd p₂ → p₁ = p₂ := sorry

protected theorem psigma.eq {α : Sort u} {β : α → Sort v} {p₁ : psigma β} {p₂ : psigma β} (h₁ : psigma.fst p₁ = psigma.fst p₂) : eq.rec_on h₁ (psigma.snd p₁) = psigma.snd p₂ → p₁ = p₂ := sorry

