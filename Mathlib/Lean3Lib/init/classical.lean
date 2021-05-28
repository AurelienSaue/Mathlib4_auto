/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.subtype.basic
import Mathlib.Lean3Lib.init.funext
import Mathlib.PostPort

universes u v 

namespace Mathlib

namespace classical


/- the axiom -/

axiom choice {α : Sort u} : Nonempty α → αtheorem indefinite_description {α : Sort u} (p : α → Prop) (h : ∃ (x : α), p x) : Subtype fun (x : α) => p x := sorry

def some {α : Sort u} {p : α → Prop} (h : ∃ (x : α), p x) : α :=
  subtype.val (indefinite_description p h)

theorem some_spec {α : Sort u} {p : α → Prop} (h : ∃ (x : α), p x) : p (some h) :=
  subtype.property (indefinite_description p h)

/- Diaconescu's theorem: using function extensionality and propositional extensionality,
   we can get excluded middle from this. -/

/- TODO(Leo): check why the code generator is not ignoring (some exU)
   when we mark u as def. -/

theorem em (p : Prop) : p ∨ ¬p :=
  or.elim (not_uv_or_p p) (fun (hne : u p ≠ v p) => Or.inr (mt (p_implies_uv p) hne)) Or.inl

theorem exists_true_of_nonempty {α : Sort u} : Nonempty α → ∃ (x : α), True :=
  fun (ᾰ : Nonempty α) => nonempty.dcases_on ᾰ fun (ᾰ : α) => idRhs (∃ (x : α), True) (Exists.intro ᾰ trivial)

def inhabited_of_nonempty {α : Sort u} (h : Nonempty α) : Inhabited α :=
  { default := Classical.choice h }

def inhabited_of_exists {α : Sort u} {p : α → Prop} (h : ∃ (x : α), p x) : Inhabited α :=
  inhabited_of_nonempty sorry

/- all propositions are decidable -/

def prop_decidable (a : Prop) : Decidable a :=
  Classical.choice sorry

def decidable_inhabited (a : Prop) : Inhabited (Decidable a) :=
  { default := prop_decidable a }

def type_decidable_eq (α : Sort u) : DecidableEq α :=
  fun (x y : α) => prop_decidable (x = y)

def type_decidable (α : Sort u) : psum α (α → False) :=
  sorry

theorem strong_indefinite_description {α : Sort u} (p : α → Prop) (h : Nonempty α) : Subtype fun (x : α) => (∃ (y : α), p y) → p x := sorry

/- the Hilbert epsilon function -/

def epsilon {α : Sort u} [h : Nonempty α] (p : α → Prop) : α :=
  subtype.val (strong_indefinite_description p h)

theorem epsilon_spec_aux {α : Sort u} (h : Nonempty α) (p : α → Prop) : (∃ (y : α), p y) → p (epsilon p) :=
  subtype.property (strong_indefinite_description p h)

theorem epsilon_spec {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y) : p (epsilon p) :=
  epsilon_spec_aux (nonempty_of_exists hex) p hex

theorem epsilon_singleton {α : Sort u} (x : α) : (epsilon fun (y : α) => y = x) = x :=
  epsilon_spec (Exists.intro x rfl)

/- the axiom of choice -/

theorem axiom_of_choice {α : Sort u} {β : α → Sort v} {r : (x : α) → β x → Prop} (h : ∀ (x : α), ∃ (y : β x), r x y) : ∃ (f : (x : α) → β x), ∀ (x : α), r x (f x) :=
  Exists.intro (fun (x : α) => some (h x)) fun (x : α) => some_spec (h x)

theorem skolem {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → Prop} : (∀ (x : α), ∃ (y : b x), p x y) ↔ ∃ (f : (x : α) → b x), ∀ (x : α), p x (f x) := sorry

theorem prop_complete (a : Prop) : a = True ∨ a = False :=
  or.elim (em a) (fun (t : a) => Or.inl (eq_true_intro t)) fun (f : ¬a) => Or.inr (eq_false_intro f)

def eq_true_or_eq_false (a : Prop) : a = True ∨ a = False :=
  prop_complete

theorem cases_true_false (p : Prop → Prop) (h1 : p True) (h2 : p False) (a : Prop) : p a :=
  or.elim (prop_complete a) (fun (ht : a = True) => Eq.symm ht ▸ h1) fun (hf : a = False) => Eq.symm hf ▸ h2

theorem cases_on (a : Prop) {p : Prop → Prop} (h1 : p True) (h2 : p False) : p a :=
  cases_true_false p h1 h2 a

-- this supercedes by_cases in decidable

def by_cases {p : Prop} {q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q :=
  decidable.by_cases hpq hnpq

-- this supercedes by_contradiction in decidable

theorem by_contradiction {p : Prop} (h : ¬p → False) : p :=
  decidable.by_contradiction h

theorem eq_false_or_eq_true (a : Prop) : a = False ∨ a = True :=
  or.symm (prop_complete a)

