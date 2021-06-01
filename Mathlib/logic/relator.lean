/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Relator for functions, pairs, sums, and lists.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.reserved_notation
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ u_1 u_2 

namespace Mathlib

namespace relator


/- TODO(johoelzl):
 * should we introduce relators of datatypes as recursive function or as inductive
predicate? For now we stick to the recursor approach.
 * relation lift for datatypes, Π, Σ, set, and subtype types
 * proof composition and identity laws
 * implement method to derive relators from datatype
-/

def lift_fun {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂} (R : α → β → Prop) (S : γ → δ → Prop) (f : α → γ) (g : β → δ) :=
  ∀ {a : α} {b : β}, R a b → S (f a) (g b)

infixr:40 " ⇒ " => Mathlib.relator.lift_fun

def right_total {α : Type u₁} {β : outParam (Type u₂)} (R : outParam (α → β → Prop)) :=
  ∀ (b : β), ∃ (a : α), R a b

def left_total {α : Type u₁} {β : outParam (Type u₂)} (R : outParam (α → β → Prop)) :=
  ∀ (a : α), ∃ (b : β), R a b

def bi_total {α : Type u₁} {β : outParam (Type u₂)} (R : outParam (α → β → Prop)) :=
  left_total R ∧ right_total R

def left_unique {α : Type u₁} {β : Type u₂} (R : α → β → Prop) :=
  ∀ {a : α} {b : β} {c : α}, R a b → R c b → a = c

def right_unique {α : Type u₁} {β : Type u₂} (R : α → β → Prop) :=
  ∀ {a : α} {b c : β}, R a b → R a c → b = c

theorem rel_forall_of_right_total {α : Type u₁} {β : Type u₂} (R : α → β → Prop) [t : right_total R] : lift_fun (R ⇒ implies) implies (fun (p : α → Prop) => ∀ (i : α), p i) fun (q : β → Prop) => ∀ (i : β), q i :=
  fun (p : α → Prop) (q : β → Prop) (Hrel : lift_fun R implies p q) (H : ∀ (i : α), p i) (b : β) =>
    exists.elim (t b) fun (a : α) (Rab : R a b) => Hrel Rab (H a)

theorem rel_exists_of_left_total {α : Type u₁} {β : Type u₂} (R : α → β → Prop) [t : left_total R] : lift_fun (R ⇒ implies) implies (fun (p : α → Prop) => ∃ (i : α), p i) fun (q : β → Prop) => ∃ (i : β), q i := sorry

theorem rel_forall_of_total {α : Type u₁} {β : Type u₂} (R : α → β → Prop) [t : bi_total R] : lift_fun (R ⇒ Iff) Iff (fun (p : α → Prop) => ∀ (i : α), p i) fun (q : β → Prop) => ∀ (i : β), q i := sorry

theorem rel_exists_of_total {α : Type u₁} {β : Type u₂} (R : α → β → Prop) [t : bi_total R] : lift_fun (R ⇒ Iff) Iff (fun (p : α → Prop) => ∃ (i : α), p i) fun (q : β → Prop) => ∃ (i : β), q i := sorry

theorem left_unique_of_rel_eq {α : Type u₁} {β : Type u₂} (R : α → β → Prop) {eq' : β → β → Prop} (he : lift_fun R (R ⇒ Iff) Eq eq') : left_unique R :=
  fun {a : α} {b : β} {c : α} (ᾰ : R a b) (ᾰ_1 : R c b) =>
    idRhs (a = c) ((fun (this : eq' b b) => iff.mpr (he ᾰ ᾰ_1) this) (iff.mp (he ᾰ ᾰ) rfl))

theorem rel_imp : lift_fun Iff (Iff ⇒ Iff) implies implies :=
  fun (p q : Prop) (h : p ↔ q) (r s : Prop) (l : r ↔ s) => imp_congr h l

theorem rel_not : lift_fun Iff Iff Not Not :=
  fun (p q : Prop) (h : p ↔ q) => not_congr h

-- (this is an instance is always applies, since the relation is an out-param)

protected instance bi_total_eq {α : Type u₁} : bi_total Eq :=
  { left := fun (a : α) => Exists.intro a rfl, right := fun (a : α) => Exists.intro a rfl }

def bi_unique {α : Type u_1} {β : Type u_2} (r : α → β → Prop) :=
  left_unique r ∧ right_unique r

theorem left_unique_flip {α : Type u_1} {β : Type u_2} {r : α → β → Prop} (h : left_unique r) : right_unique (flip r) :=
  fun {a : β} {b c : α} (ᾰ : flip r a b) (ᾰ_1 : flip r a c) => idRhs (b = c) (h ᾰ ᾰ_1)

theorem rel_and : lift_fun Iff (Iff ⇒ Iff) And And :=
  fun (a b : Prop) (h₁ : a ↔ b) (c d : Prop) (h₂ : c ↔ d) => and_congr h₁ h₂

theorem rel_or : lift_fun Iff (Iff ⇒ Iff) Or Or :=
  fun (a b : Prop) (h₁ : a ↔ b) (c d : Prop) (h₂ : c ↔ d) => or_congr h₁ h₂

theorem rel_iff : lift_fun Iff (Iff ⇒ Iff) Iff Iff :=
  fun (a b : Prop) (h₁ : a ↔ b) (c d : Prop) (h₂ : c ↔ d) => iff_congr h₁ h₂

theorem rel_eq {α : Type u_1} {β : Type u_2} {r : α → β → Prop} (hr : bi_unique r) : lift_fun r (r ⇒ Iff) Eq Eq :=
  fun (a : α) (b : β) (h₁ : r a b) (c : α) (d : β) (h₂ : r c d) =>
    { mp := fun (h : a = c) => Eq._oldrec (fun (h₂ : r a d) => and.right hr a b d h₁ h₂) h h₂,
      mpr := fun (h : b = d) => Eq._oldrec (fun (h₂ : r c b) => and.left hr a b c h₁ h₂) h h₂ }

