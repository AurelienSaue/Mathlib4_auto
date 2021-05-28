/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.data.sigma.basic
import Lean3Lib.init.meta.default
import PostPort

universes u v 

namespace Mathlib

namespace psigma


inductive lex {α : Sort u} {β : α → Sort v} (r : α → α → Prop) (s : (a : α) → β a → β a → Prop) : psigma β → psigma β → Prop
where
| left : ∀ {a₁ : α} (b₁ : β a₁) {a₂ : α} (b₂ : β a₂), r a₁ a₂ → lex r s (mk a₁ b₁) (mk a₂ b₂)
| right : ∀ (a : α) {b₁ b₂ : β a}, s a b₁ b₂ → lex r s (mk a b₁) (mk a b₂)

def lex_accessible {α : Sort u} {β : α → Sort v} {r : α → α → Prop} {s : (a : α) → β a → β a → Prop} {a : α} (aca : acc r a) (acb : ∀ (a : α), well_founded (s a)) (b : β a) : acc (lex r s) (mk a b) := sorry

def lex_wf {α : Sort u} {β : α → Sort v} {r : α → α → Prop} {s : (a : α) → β a → β a → Prop} (ha : well_founded r) (hb : ∀ (x : α), well_founded (s x)) : well_founded (lex r s) :=
  well_founded.intro fun (_x : psigma fun (a : α) => β a) => sorry

def lex_ndep {α : Sort u} {β : Sort v} (r : α → α → Prop) (s : β → β → Prop) : (psigma fun (a : α) => β) → (psigma fun (a : α) => β) → Prop :=
  lex r fun (a : α) => s

def lex_ndep_wf {α : Sort u} {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} (ha : well_founded r) (hb : well_founded s) : well_founded (lex_ndep r s) :=
  well_founded.intro fun (_x : psigma fun (a : α) => β) => sorry

inductive rev_lex {α : Sort u} {β : Sort v} (r : α → α → Prop) (s : β → β → Prop) : (psigma fun (a : α) => β) → (psigma fun (a : α) => β) → Prop
where
| left : ∀ {a₁ a₂ : α} (b : β), r a₁ a₂ → rev_lex r s (mk a₁ b) (mk a₂ b)
| right : ∀ (a₁ : α) {b₁ : β} (a₂ : α) {b₂ : β}, s b₁ b₂ → rev_lex r s (mk a₁ b₁) (mk a₂ b₂)

def rev_lex_accessible {α : Sort u} {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} {b : β} (acb : acc s b) (aca : ∀ (a : α), acc r a) (a : α) : acc (rev_lex r s) (mk a b) := sorry

def rev_lex_wf {α : Sort u} {β : Sort v} {r : α → α → Prop} {s : β → β → Prop} (ha : well_founded r) (hb : well_founded s) : well_founded (rev_lex r s) :=
  well_founded.intro fun (_x : psigma fun (a : α) => β) => sorry

def skip_left (α : Type u) {β : Type v} (s : β → β → Prop) : (psigma fun (a : α) => β) → (psigma fun (a : α) => β) → Prop :=
  rev_lex empty_relation s

def skip_left_wf (α : Type u) {β : Type v} {s : β → β → Prop} (hb : well_founded s) : well_founded (skip_left α s) :=
  rev_lex_wf empty_wf hb

def mk_skip_left {α : Type u} {β : Type v} {b₁ : β} {b₂ : β} {s : β → β → Prop} (a₁ : α) (a₂ : α) (h : s b₁ b₂) : skip_left α s (mk a₁ b₁) (mk a₂ b₂) :=
  rev_lex.right a₁ a₂ h

protected instance has_well_founded {α : Type u} {β : α → Type v} [s₁ : has_well_founded α] [s₂ : (a : α) → has_well_founded (β a)] : has_well_founded (psigma β) :=
  has_well_founded.mk (lex has_well_founded.r fun (a : α) => has_well_founded.r) sorry

