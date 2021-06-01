/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.core
 

universes u v w l u_1 r s 

namespace Mathlib

@[simp] theorem opt_param_eq (α : Sort u) (default : α) : optParam α default = α :=
  rfl

def id {α : Sort u} (a : α) : α :=
  a

def flip {α : Sort u} {β : Sort v} {φ : Sort w} (f : α → β → φ) : β → α → φ :=
  fun (b : β) (a : α) => f a b

/- implication -/

def implies (a : Prop) (b : Prop)  :=
  a → b

/-- Implication `→` is transitive. If `P → Q` and `Q → R` then `P → R`. -/
theorem implies.trans {p : Prop} {q : Prop} {r : Prop} (h₁ : implies p q) (h₂ : implies q r) : implies p r :=
  fun (hp : p) => h₂ (h₁ hp)

def trivial : True :=
  True.intro

/-- We can't have `a` and `¬a`, that would be absurd!-/
def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : ¬a) : b :=
  False._oldrec (h₂ h₁)

theorem not.intro {a : Prop} (h : a → False) : ¬a :=
  h

/-- Modus tollens. If an implication is true, then so is its contrapositive. -/
theorem mt {a : Prop} {b : Prop} (h₁ : a → b) (h₂ : ¬b) : ¬a :=
  fun (ha : a) => h₂ (h₁ ha)

/- not -/

theorem not_false : ¬False :=
  id

def non_contradictory (a : Prop)  :=
  ¬¬a

theorem non_contradictory_intro {a : Prop} (ha : a) : ¬¬a :=
  fun (hna : ¬a) => absurd ha hna

/- false -/

def false.elim {C : Sort u} (h : False) : C :=
  False._oldrec h

/- eq -/

-- proof irrelevance is built in

theorem proof_irrel {a : Prop} (h₁ : a) (h₂ : a) : h₁ = h₂ :=
  rfl

@[simp] theorem id.def {α : Sort u} (a : α) : id a = a :=
  rfl

def eq.mp {α : Sort u} {β : Sort u} : α = β → α → β :=
  eq.rec_on

def eq.mpr {α : Sort u} {β : Sort u} : α = β → β → α :=
  fun (h₁ : α = β) (h₂ : β) => eq.rec_on sorry h₂

theorem eq.substr {α : Sort u} {p : α → Prop} {a : α} {b : α} (h₁ : b = a) : p a → p b :=
  Eq.subst (Eq.symm h₁)

theorem congr {α : Sort u} {β : Sort v} {f₁ : α → β} {f₂ : α → β} {a₁ : α} {a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
  h₁ ▸ h₂ ▸ rfl

theorem congr_fun {α : Sort u} {β : α → Sort v} {f : (x : α) → β x} {g : (x : α) → β x} (h : f = g) (a : α) : f a = g a :=
  h ▸ Eq.refl (f a)

theorem congr_arg {α : Sort u} {β : Sort v} {a₁ : α} {a₂ : α} (f : α → β) : a₁ = a₂ → f a₁ = f a₂ :=
  congr rfl

theorem trans_rel_left {α : Sort u} {a : α} {b : α} {c : α} (r : α → α → Prop) (h₁ : r a b) (h₂ : b = c) : r a c :=
  h₂ ▸ h₁

theorem trans_rel_right {α : Sort u} {a : α} {b : α} {c : α} (r : α → α → Prop) (h₁ : a = b) (h₂ : r b c) : r a c :=
  Eq.symm h₁ ▸ h₂

theorem of_eq_true {p : Prop} (h : p = True) : p :=
  Eq.symm h ▸ trivial

theorem not_of_eq_false {p : Prop} (h : p = False) : ¬p :=
  fun (hp : p) => h ▸ hp

def cast {α : Sort u} {β : Sort u} (h : α = β) (a : α) : β :=
  Eq._oldrec a h

theorem cast_proof_irrel {α : Sort u} {β : Sort u} (h₁ : α = β) (h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a :=
  rfl

theorem cast_eq {α : Sort u} (h : α = α) (a : α) : cast h a = a :=
  rfl

/- ne -/

def ne {α : Sort u} (a : α) (b : α)  :=
  ¬a = b

infixl:50 " ≠ " => Mathlib.ne

@[simp] theorem ne.def {α : Sort u} (a : α) (b : α) : a ≠ b = (¬a = b) :=
  rfl

namespace ne


theorem intro {α : Sort u} {a : α} {b : α} (h : a = b → False) : a ≠ b :=
  h

theorem elim {α : Sort u} {a : α} {b : α} (h : a ≠ b) : a = b → False :=
  h

theorem irrefl {α : Sort u} {a : α} (h : a ≠ a) : False :=
  h rfl

theorem symm {α : Sort u} {a : α} {b : α} (h : a ≠ b) : b ≠ a :=
  fun (h₁ : b = a) => h (Eq.symm h₁)

end ne


theorem false_of_ne {α : Sort u} {a : α} : a ≠ a → False :=
  ne.irrefl

theorem ne_false_of_self {p : Prop} : p → p ≠ False :=
  fun (hp : p) (heq : p = False) => heq ▸ hp

theorem ne_true_of_not {p : Prop} : ¬p → p ≠ True :=
  fun (hnp : ¬p) (heq : p = True) => Eq.subst heq hnp trivial

theorem true_ne_false : ¬True = False :=
  ne_false_of_self trivial

theorem heq.elim {α : Sort u} {a : α} {p : α → Sort v} {b : α} (h₁ : a == b) : p a → p b :=
  eq.rec_on (eq_of_heq h₁)

theorem heq.subst {α : Sort u} {β : Sort u} {a : α} {b : β} {p : (T : Sort u) → T → Prop} : a == b → p α a → p β b :=
  heq.rec_on

theorem heq.symm {α : Sort u} {β : Sort u} {a : α} {b : β} (h : a == b) : b == a :=
  heq.rec_on h (HEq.refl a)

theorem heq_of_eq {α : Sort u} {a : α} {a' : α} (h : a = a') : a == a' :=
  h ▸ HEq.refl a

theorem heq.trans {α : Sort u} {β : Sort u} {φ : Sort u} {a : α} {b : β} {c : φ} (h₁ : a == b) (h₂ : b == c) : a == c :=
  HEq.subst h₂ h₁

theorem heq_of_heq_of_eq {α : Sort u} {β : Sort u} {a : α} {b : β} {b' : β} (h₁ : a == b) (h₂ : b = b') : a == b' :=
  HEq.trans h₁ (heq_of_eq h₂)

theorem heq_of_eq_of_heq {α : Sort u} {β : Sort u} {a : α} {a' : α} {b : β} (h₁ : a = a') (h₂ : a' == b) : a == b :=
  HEq.trans (heq_of_eq h₁) h₂

def type_eq_of_heq {α : Sort u} {β : Sort u} {a : α} {b : β} (h : a == b) : α = β :=
  heq.rec_on h (Eq.refl α)

theorem eq_rec_heq {α : Sort u} {φ : α → Sort v} {a : α} {a' : α} (h : a = a') (p : φ a) : eq.rec_on h p == p := sorry

theorem heq_of_eq_rec_left {α : Sort u} {φ : α → Sort v} {a : α} {a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a = a') (h₂ : eq.rec_on e p₁ = p₂) : p₁ == p₂ := sorry

theorem heq_of_eq_rec_right {α : Sort u} {φ : α → Sort v} {a : α} {a' : α} {p₁ : φ a} {p₂ : φ a'} (e : a' = a) (h₂ : p₁ = eq.rec_on e p₂) : p₁ == p₂ := sorry

theorem of_heq_true {a : Prop} (h : a == True) : a :=
  of_eq_true (eq_of_heq h)

theorem eq_rec_compose {α : Sort u} {β : Sort u} {φ : Sort u} (p₁ : β = φ) (p₂ : α = β) (a : α) : eq.rec_on p₁ (eq.rec_on p₂ a) = eq.rec_on (Eq.trans p₂ p₁) a := sorry

theorem cast_heq {α : Sort u} {β : Sort u} (h : α = β) (a : α) : cast h a == a := sorry

infixr:35 " /\ " => Mathlib.and

infixr:35 " ∧ " => Mathlib.and

/- and -/

theorem and.elim {a : Prop} {b : Prop} {c : Prop} (h₁ : a ∧ b) (h₂ : a → b → c) : c :=
  And._oldrec h₂ h₁

theorem and.swap {a : Prop} {b : Prop} : a ∧ b → b ∧ a :=
  fun (_x : a ∧ b) =>
    (fun (_a : a ∧ b) => and.dcases_on _a fun (left : a) (right : b) => idRhs (b ∧ a) { left := right, right := left }) _x

def and.symm {a : Prop} {b : Prop} : a ∧ b → b ∧ a :=
  and.swap

infixr:30 " \/ " => Mathlib.or

infixr:30 " ∨ " => Mathlib.or

/- or -/

namespace or


theorem elim {a : Prop} {b : Prop} {c : Prop} (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → c) : c :=
  Or._oldrec h₂ h₃ h₁

end or


theorem non_contradictory_em (a : Prop) : ¬¬(a ∨ ¬a) :=
  fun (not_em : ¬(a ∨ ¬a)) =>
    (fun (neg_a : ¬a) => absurd (Or.inr neg_a) not_em) fun (pos_a : a) => absurd (Or.inl pos_a) not_em

def not_not_em (a : Prop) : ¬¬(a ∨ ¬a) :=
  non_contradictory_em

theorem or.swap {a : Prop} {b : Prop} : a ∨ b → b ∨ a :=
  Or._oldrec Or.inr Or.inl

def or.symm {a : Prop} {b : Prop} : a ∨ b → b ∨ a :=
  or.swap

/- xor -/

def xor (a : Prop) (b : Prop)  :=
  a ∧ ¬b ∨ b ∧ ¬a

/- iff -/

/-- `iff P Q`, with notation `P ↔ Q`, is the proposition asserting that `P` and `Q` are equivalent,
that is, have the same truth value. -/
not foundinfixl:20 " <-> " => Mathlib.iff

infixl:20 " ↔ " => Mathlib.iff

theorem iff.elim {a : Prop} {b : Prop} {c : Prop} : ((a → b) → (b → a) → c) → (a ↔ b) → c :=
  Iff._oldrec

theorem iff.elim_left {a : Prop} {b : Prop} : (a ↔ b) → a → b :=
  iff.mp

theorem iff.elim_right {a : Prop} {b : Prop} : (a ↔ b) → b → a :=
  iff.mpr

theorem iff_iff_implies_and_implies (a : Prop) (b : Prop) : a ↔ b ↔ (a → b) ∧ (b → a) :=
  { mp := fun (h : a ↔ b) => { left := iff.mp h, right := iff.mpr h },
    mpr := fun (h : (a → b) ∧ (b → a)) => { mp := and.left h, mpr := and.right h } }

theorem iff.refl (a : Prop) : a ↔ a :=
  { mp := fun (h : a) => h, mpr := fun (h : a) => h }

theorem iff.rfl {a : Prop} : a ↔ a :=
  iff.refl a

theorem iff.trans {a : Prop} {b : Prop} {c : Prop} (h₁ : a ↔ b) (h₂ : b ↔ c) : a ↔ c :=
  { mp := fun (ha : a) => iff.mp h₂ (iff.mp h₁ ha), mpr := fun (hc : c) => iff.mpr h₁ (iff.mpr h₂ hc) }

theorem iff.symm {a : Prop} {b : Prop} (h : a ↔ b) : b ↔ a :=
  { mp := iff.elim_right h, mpr := iff.elim_left h }

theorem iff.comm {a : Prop} {b : Prop} : a ↔ b ↔ (b ↔ a) :=
  { mp := iff.symm, mpr := iff.symm }

theorem eq.to_iff {a : Prop} {b : Prop} (h : a = b) : a ↔ b :=
  eq.rec_on h iff.rfl

theorem neq_of_not_iff {a : Prop} {b : Prop} : ¬(a ↔ b) → a ≠ b :=
  fun (h₁ : ¬(a ↔ b)) (h₂ : a = b) => (fun (this : a ↔ b) => absurd this h₁) (h₂ ▸ iff.refl a)

theorem not_iff_not_of_iff {a : Prop} {b : Prop} (h₁ : a ↔ b) : ¬a ↔ ¬b :=
  { mp := fun (hna : ¬a) (hb : b) => hna (iff.elim_right h₁ hb),
    mpr := fun (hnb : ¬b) (ha : a) => hnb (iff.elim_left h₁ ha) }

theorem of_iff_true {a : Prop} (h : a ↔ True) : a :=
  iff.mp (iff.symm h) trivial

theorem not_of_iff_false {a : Prop} : (a ↔ False) → ¬a :=
  iff.mp

theorem iff_true_intro {a : Prop} (h : a) : a ↔ True :=
  { mp := fun (hl : a) => trivial, mpr := fun (hr : True) => h }

theorem iff_false_intro {a : Prop} (h : ¬a) : a ↔ False :=
  { mp := h, mpr := False._oldrec }

theorem not_non_contradictory_iff_absurd (a : Prop) : ¬¬¬a ↔ ¬a :=
  { mp := fun (hl : ¬¬¬a) (ha : a) => hl (non_contradictory_intro ha), mpr := absurd }

def not_not_not_iff (a : Prop) : ¬¬¬a ↔ ¬a :=
  not_non_contradictory_iff_absurd

theorem imp_congr {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a → b ↔ c → d :=
  { mp := fun (hab : a → b) (hc : c) => iff.mp h₂ (hab (iff.mpr h₁ hc)),
    mpr := fun (hcd : c → d) (ha : a) => iff.mpr h₂ (hcd (iff.mp h₁ ha)) }

theorem imp_congr_ctx {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a ↔ c) (h₂ : c → (b ↔ d)) : a → b ↔ c → d :=
  { mp := fun (hab : a → b) (hc : c) => (fun (ha : a) => (fun (hb : b) => iff.mp (h₂ hc) hb) (hab ha)) (iff.mpr h₁ hc),
    mpr := fun (hcd : c → d) (ha : a) => (fun (hc : c) => (fun (hd : d) => iff.mpr (h₂ hc) hd) (hcd hc)) (iff.mp h₁ ha) }

theorem imp_congr_right {a : Prop} {b : Prop} {c : Prop} (h : a → (b ↔ c)) : a → b ↔ a → c :=
  { mp := fun (hab : a → b) (ha : a) => iff.elim_left (h ha) (hab ha),
    mpr := fun (hab : a → c) (ha : a) => iff.elim_right (h ha) (hab ha) }

theorem not_not_intro {a : Prop} (ha : a) : ¬¬a :=
  fun (hna : ¬a) => hna ha

theorem not_of_not_not_not {a : Prop} (h : ¬¬¬a) : ¬a :=
  fun (ha : a) => absurd (not_not_intro ha) h

@[simp] theorem not_true : ¬True ↔ False :=
  iff_false_intro (not_not_intro trivial)

def not_true_iff : ¬True ↔ False :=
  not_true

@[simp] theorem not_false_iff : ¬False ↔ True :=
  iff_true_intro not_false

theorem not_congr {a : Prop} {b : Prop} (h : a ↔ b) : ¬a ↔ ¬b :=
  { mp := fun (h₁ : ¬a) (h₂ : b) => h₁ (iff.mpr h h₂), mpr := fun (h₁ : ¬b) (h₂ : a) => h₁ (iff.mp h h₂) }

@[simp] theorem ne_self_iff_false {α : Sort u} (a : α) : ¬a = a ↔ False :=
  { mp := false_of_ne, mpr := false.elim }

@[simp] theorem eq_self_iff_true {α : Sort u} (a : α) : a = a ↔ True :=
  iff_true_intro rfl

@[simp] theorem heq_self_iff_true {α : Sort u} (a : α) : a == a ↔ True :=
  iff_true_intro (HEq.refl a)

@[simp] theorem iff_not_self (a : Prop) : a ↔ ¬a ↔ False :=
  iff_false_intro fun (h : a ↔ ¬a) => (fun (h' : ¬a) => h' (iff.mpr h h')) fun (ha : a) => iff.mp h ha ha

@[simp] theorem not_iff_self (a : Prop) : ¬a ↔ a ↔ False :=
  iff_false_intro fun (h : ¬a ↔ a) => (fun (h' : ¬a) => h' (iff.mp h h')) fun (ha : a) => iff.mpr h ha ha

@[simp] theorem true_iff_false : True ↔ False ↔ False :=
  iff_false_intro fun (h : True ↔ False) => iff.mp h trivial

@[simp] theorem false_iff_true : False ↔ True ↔ False :=
  iff_false_intro fun (h : False ↔ True) => iff.mpr h trivial

theorem false_of_true_iff_false : (True ↔ False) → False :=
  fun (h : True ↔ False) => iff.mp h trivial

theorem false_of_true_eq_false : True = False → False :=
  fun (h : True = False) => h ▸ trivial

theorem true_eq_false_of_false : False → True = False :=
  false.elim

theorem eq_comm {α : Sort u} {a : α} {b : α} : a = b ↔ b = a :=
  { mp := Eq.symm, mpr := Eq.symm }

/- and simp rules -/

theorem and.imp {a : Prop} {b : Prop} {c : Prop} {d : Prop} (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d := sorry

def and_implies {a : Prop} {b : Prop} {c : Prop} {d : Prop} (hac : a → c) (hbd : b → d) : a ∧ b → c ∧ d :=
  and.imp

theorem and_congr {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d :=
  { mp := and.imp (iff.mp h₁) (iff.mp h₂), mpr := and.imp (iff.mpr h₁) (iff.mpr h₂) }

theorem and_congr_right {a : Prop} {b : Prop} {c : Prop} (h : a → (b ↔ c)) : a ∧ b ↔ a ∧ c := sorry

theorem and.comm {a : Prop} {b : Prop} : a ∧ b ↔ b ∧ a :=
  { mp := and.swap, mpr := and.swap }

theorem and_comm (a : Prop) (b : Prop) : a ∧ b ↔ b ∧ a :=
  and.comm

theorem and.assoc {a : Prop} {b : Prop} {c : Prop} : (a ∧ b) ∧ c ↔ a ∧ b ∧ c := sorry

theorem and_assoc {c : Prop} (a : Prop) (b : Prop) : (a ∧ b) ∧ c ↔ a ∧ b ∧ c :=
  and.assoc

theorem and.left_comm {a : Prop} {b : Prop} {c : Prop} : a ∧ b ∧ c ↔ b ∧ a ∧ c :=
  iff.trans (iff.symm and.assoc) (iff.trans (and_congr and.comm (iff.refl c)) and.assoc)

theorem and_iff_left {a : Prop} {b : Prop} (hb : b) : a ∧ b ↔ a :=
  { mp := and.left, mpr := fun (ha : a) => { left := ha, right := hb } }

theorem and_iff_right {a : Prop} {b : Prop} (ha : a) : a ∧ b ↔ b :=
  { mp := and.right, mpr := And.intro ha }

@[simp] theorem and_true (a : Prop) : a ∧ True ↔ a :=
  and_iff_left trivial

@[simp] theorem true_and (a : Prop) : True ∧ a ↔ a :=
  and_iff_right trivial

@[simp] theorem and_false (a : Prop) : a ∧ False ↔ False :=
  iff_false_intro and.right

@[simp] theorem false_and (a : Prop) : False ∧ a ↔ False :=
  iff_false_intro and.left

@[simp] theorem not_and_self (a : Prop) : ¬a ∧ a ↔ False :=
  iff_false_intro fun (h : ¬a ∧ a) => and.elim h fun (h₁ : ¬a) (h₂ : a) => absurd h₂ h₁

@[simp] theorem and_not_self (a : Prop) : a ∧ ¬a ↔ False :=
  iff_false_intro
    fun (_x : a ∧ ¬a) =>
      (fun (_a : a ∧ ¬a) => and.dcases_on _a fun (left : a) (right : ¬a) => idRhs False (absurd left right)) _x

@[simp] theorem and_self (a : Prop) : a ∧ a ↔ a :=
  { mp := and.left, mpr := fun (h : a) => { left := h, right := h } }

/- or simp rules -/

theorem or.imp {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₂ : a → c) (h₃ : b → d) : a ∨ b → c ∨ d :=
  Or._oldrec (fun (h : a) => Or.inl (h₂ h)) fun (h : b) => Or.inr (h₃ h)

theorem or.imp_left {a : Prop} {b : Prop} {c : Prop} (h : a → b) : a ∨ c → b ∨ c :=
  or.imp h id

theorem or.imp_right {a : Prop} {b : Prop} {c : Prop} (h : a → b) : c ∨ a → c ∨ b :=
  or.imp id h

theorem or_congr {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∨ b ↔ c ∨ d :=
  { mp := or.imp (iff.mp h₁) (iff.mp h₂), mpr := or.imp (iff.mpr h₁) (iff.mpr h₂) }

theorem or.comm {a : Prop} {b : Prop} : a ∨ b ↔ b ∨ a :=
  { mp := or.swap, mpr := or.swap }

theorem or_comm (a : Prop) (b : Prop) : a ∨ b ↔ b ∨ a :=
  or.comm

theorem or.assoc {a : Prop} {b : Prop} {c : Prop} : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  { mp := Or._oldrec (or.imp_right Or.inl) fun (h : c) => Or.inr (Or.inr h),
    mpr := Or._oldrec (fun (h : a) => Or.inl (Or.inl h)) (or.imp_left Or.inr) }

theorem or_assoc {c : Prop} (a : Prop) (b : Prop) : (a ∨ b) ∨ c ↔ a ∨ b ∨ c :=
  or.assoc

theorem or.left_comm {a : Prop} {b : Prop} {c : Prop} : a ∨ b ∨ c ↔ b ∨ a ∨ c :=
  iff.trans (iff.symm or.assoc) (iff.trans (or_congr or.comm (iff.refl c)) or.assoc)

theorem or_iff_right_of_imp {a : Prop} {b : Prop} (ha : a → b) : a ∨ b ↔ b :=
  { mp := Or._oldrec ha id, mpr := Or.inr }

theorem or_iff_left_of_imp {a : Prop} {b : Prop} (hb : b → a) : a ∨ b ↔ a :=
  { mp := Or._oldrec id hb, mpr := Or.inl }

@[simp] theorem or_true (a : Prop) : a ∨ True ↔ True :=
  iff_true_intro (Or.inr trivial)

@[simp] theorem true_or (a : Prop) : True ∨ a ↔ True :=
  iff_true_intro (Or.inl trivial)

@[simp] theorem or_false (a : Prop) : a ∨ False ↔ a :=
  { mp := Or._oldrec id false.elim, mpr := Or.inl }

@[simp] theorem false_or (a : Prop) : False ∨ a ↔ a :=
  iff.trans or.comm (or_false a)

@[simp] theorem or_self (a : Prop) : a ∨ a ↔ a :=
  { mp := Or._oldrec id id, mpr := Or.inl }

theorem not_or {a : Prop} {b : Prop} : ¬a → ¬b → ¬(a ∨ b) :=
  fun (ᾰ : ¬a) (ᾰ_1 : ¬b) (ᾰ_2 : a ∨ b) =>
    or.dcases_on ᾰ_2 (fun (ᾰ_1 : a) => idRhs False (absurd ᾰ_1 ᾰ)) fun (ᾰ_1_1 : b) => idRhs False (absurd ᾰ_1_1 ᾰ_1)

/- or resolution rulse -/

def or.resolve_left {a : Prop} {b : Prop} (h : a ∨ b) (na : ¬a) : b :=
  or.elim h (fun (ha : a) => absurd ha na) id

def or.neg_resolve_left {a : Prop} {b : Prop} (h : ¬a ∨ b) (ha : a) : b :=
  or.elim h (fun (na : ¬a) => absurd ha na) id

def or.resolve_right {a : Prop} {b : Prop} (h : a ∨ b) (nb : ¬b) : a :=
  or.elim h id fun (hb : b) => absurd hb nb

def or.neg_resolve_right {a : Prop} {b : Prop} (h : a ∨ ¬b) (hb : b) : a :=
  or.elim h id fun (nb : ¬b) => absurd hb nb

/- iff simp rules -/

@[simp] theorem iff_true (a : Prop) : a ↔ True ↔ a :=
  { mp := fun (h : a ↔ True) => iff.mpr h trivial, mpr := iff_true_intro }

@[simp] theorem true_iff (a : Prop) : True ↔ a ↔ a :=
  iff.trans iff.comm (iff_true a)

@[simp] theorem iff_false (a : Prop) : a ↔ False ↔ ¬a :=
  { mp := iff.mp, mpr := iff_false_intro }

@[simp] theorem false_iff (a : Prop) : False ↔ a ↔ ¬a :=
  iff.trans iff.comm (iff_false a)

@[simp] theorem iff_self (a : Prop) : a ↔ a ↔ True :=
  iff_true_intro iff.rfl

theorem iff_congr {a : Prop} {b : Prop} {c : Prop} {d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ↔ b ↔ (c ↔ d) :=
  iff.trans (iff_iff_implies_and_implies a b)
    (iff.trans (and_congr (imp_congr h₁ h₂) (imp_congr h₂ h₁)) (iff.symm (iff_iff_implies_and_implies c d)))

/- implies simp rule -/

@[simp] theorem implies_true_iff (α : Sort u) : α → True ↔ True :=
  { mp := fun (h : α → True) => trivial, mpr := fun (ha : True) (h : α) => trivial }

@[simp] theorem false_implies_iff (a : Prop) : False → a ↔ True :=
  { mp := fun (h : False → a) => trivial, mpr := fun (ha : True) (h : False) => false.elim h }

@[simp] theorem true_implies_iff (α : Prop) : True → α ↔ α :=
  { mp := fun (h : True → α) => h trivial, mpr := fun (h : α) (h' : True) => h }

/--
The existential quantifier.

To prove a goal of the form `⊢ ∃ x, p x`, you can provide a witness `y` with the tactic `existsi y`.
If you are working in a project that depends on mathlib, then we recommend the `use` tactic
instead.
You'll then be left with the goal `⊢ p y`.

To extract a witness `x` and proof `hx : p x` from a hypothesis `h : ∃ x, p x`,
use the tactic `cases h with x hx`. See also the mathlib tactics `obtain` and `rcases`.
-/
not founddef exists.intro {α : Sort u_1} {p : α → Prop} (w : α) (h : p w) : Exists p :=
  Exists.intro

theorem exists.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ (x : α), p x) (h₂ : ∀ (a : α), p a → b) : b :=
  Exists._oldrec h₂ h₁

/- exists unique -/

def exists_unique {α : Sort u} (p : α → Prop)  :=
  ∃ (x : α), p x ∧ ∀ (y : α), p y → y = x

theorem exists_unique.intro {α : Sort u} {p : α → Prop} (w : α) (h₁ : p w) (h₂ : ∀ (y : α), p y → y = w) : exists_unique fun (x : α) => p x :=
  exists.intro w { left := h₁, right := h₂ }

theorem exists_unique.elim {α : Sort u} {p : α → Prop} {b : Prop} (h₂ : exists_unique fun (x : α) => p x) (h₁ : ∀ (x : α), p x → (∀ (y : α), p y → y = x) → b) : b :=
  exists.elim h₂ fun (w : α) (hw : (fun (x : α) => p x) w ∧ ∀ (y : α), p y → y = w) => h₁ w (and.left hw) (and.right hw)

theorem exists_unique_of_exists_of_unique {α : Type u} {p : α → Prop} (hex : ∃ (x : α), p x) (hunique : ∀ (y₁ y₂ : α), p y₁ → p y₂ → y₁ = y₂) : exists_unique fun (x : α) => p x :=
  exists.elim hex fun (x : α) (px : p x) => exists_unique.intro x px fun (y : α) (this : p y) => hunique y x this px

theorem exists_of_exists_unique {α : Sort u} {p : α → Prop} (h : exists_unique fun (x : α) => p x) : ∃ (x : α), p x :=
  exists.elim h fun (x : α) (hx : (fun (x : α) => p x) x ∧ ∀ (y : α), p y → y = x) => Exists.intro x (and.left hx)

theorem unique_of_exists_unique {α : Sort u} {p : α → Prop} (h : exists_unique fun (x : α) => p x) {y₁ : α} {y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
  exists_unique.elim h
    fun (x : α) (this : p x) (unique : ∀ (y : α), p y → y = x) =>
      (fun (this : y₁ = y₂) => this) (Eq.trans (unique y₁ py₁) (Eq.symm (unique y₂ py₂)))

/- exists, forall, exists unique congruences -/

theorem forall_congr {α : Sort u} {p : α → Prop} {q : α → Prop} (h : ∀ (a : α), p a ↔ q a) : (∀ (a : α), p a) ↔ ∀ (a : α), q a :=
  { mp := fun (p_1 : ∀ (a : α), p a) (a : α) => iff.mp (h a) (p_1 a),
    mpr := fun (q_1 : ∀ (a : α), q a) (a : α) => iff.mpr (h a) (q_1 a) }

theorem exists_imp_exists {α : Sort u} {p : α → Prop} {q : α → Prop} (h : ∀ (a : α), p a → q a) : (∃ (a : α), p a) → ∃ (a : α), q a :=
  fun (p_1 : ∃ (a : α), p a) => exists.elim p_1 fun (a : α) (hp : p a) => Exists.intro a (h a hp)

theorem exists_congr {α : Sort u} {p : α → Prop} {q : α → Prop} (h : ∀ (a : α), p a ↔ q a) : Exists p ↔ ∃ (a : α), q a :=
  { mp := exists_imp_exists fun (a : α) => iff.mp (h a), mpr := exists_imp_exists fun (a : α) => iff.mpr (h a) }

theorem exists_unique_congr {α : Sort u} {p₁ : α → Prop} {p₂ : α → Prop} (h : ∀ (x : α), p₁ x ↔ p₂ x) : exists_unique p₁ ↔ exists_unique fun (x : α) => p₂ x :=
  exists_congr fun (x : α) => and_congr (h x) (forall_congr fun (y : α) => imp_congr (h y) iff.rfl)

theorem forall_not_of_not_exists {α : Sort u} {p : α → Prop} : (¬∃ (x : α), p x) → ∀ (x : α), ¬p x :=
  fun (hne : ¬∃ (x : α), p x) (x : α) (hp : p x) => hne (Exists.intro x hp)

/- decidable -/

def decidable.to_bool (p : Prop) [h : Decidable p] : Bool :=
  decidable.cases_on h (fun (h₁ : ¬p) => false) fun (h₂ : p) => tt

@[simp] theorem to_bool_true_eq_tt (h : Decidable True) : to_bool True = tt :=
  decidable.cases_on h (fun (h : ¬True) => false.elim (iff.mp not_true h)) fun (_x : True) => rfl

@[simp] theorem to_bool_false_eq_ff (h : Decidable False) : to_bool False = false :=
  decidable.cases_on h (fun (h : ¬False) => rfl) fun (h : False) => false.elim h

protected instance decidable.true : Decidable True :=
  is_true trivial

protected instance decidable.false : Decidable False :=
  is_false not_false

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition

-- to the branches

def dite (c : Prop) [h : Decidable c] {α : Sort u} : (c → α) → (¬c → α) → α :=
  fun (t : c → α) (e : ¬c → α) => decidable.rec_on h e t

/- if-then-else -/

def ite (c : Prop) [h : Decidable c] {α : Sort u} (t : α) (e : α) : α :=
  decidable.rec_on h (fun (hnc : ¬c) => e) fun (hc : c) => t

namespace decidable


def rec_on_true {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : p) (h₄ : h₁ h₃) : decidable.rec_on h h₂ h₁ :=
  decidable.rec_on h (fun (h : ¬p) => False._oldrec (h h₃)) fun (h : p) => h₄

def rec_on_false {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} (h₃ : ¬p) (h₄ : h₂ h₃) : decidable.rec_on h h₂ h₁ :=
  decidable.rec_on h (fun (h : ¬p) => h₄) fun (h : p) => False._oldrec (h₃ h)

def by_cases {p : Prop} {q : Sort u} [φ : Decidable p] : (p → q) → (¬p → q) → q :=
  dite p

theorem em (p : Prop) [Decidable p] : p ∨ ¬p :=
  by_cases Or.inl Or.inr

theorem by_contradiction {p : Prop} [Decidable p] (h : ¬p → False) : p :=
  dite p (fun (h₁ : p) => h₁) fun (h₁ : ¬p) => False._oldrec (h h₁)

theorem of_not_not {p : Prop} [Decidable p] : ¬¬p → p :=
  fun (hnn : ¬¬p) => by_contradiction fun (hn : ¬p) => absurd hn hnn

theorem not_not_iff (p : Prop) [Decidable p] : ¬¬p ↔ p :=
  { mp := of_not_not, mpr := not_not_intro }

theorem not_and_iff_or_not (p : Prop) (q : Prop) [d₁ : Decidable p] [d₂ : Decidable q] : ¬(p ∧ q) ↔ ¬p ∨ ¬q := sorry

theorem not_or_iff_and_not (p : Prop) (q : Prop) [d₁ : Decidable p] [d₂ : Decidable q] : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

end decidable


def decidable_of_decidable_of_iff {p : Prop} {q : Prop} (hp : Decidable p) (h : p ↔ q) : Decidable q :=
  dite p (fun (hp : p) => is_true (iff.mp h hp)) fun (hp : ¬p) => is_false sorry

def decidable_of_decidable_of_eq {p : Prop} {q : Prop} (hp : Decidable p) (h : p = q) : Decidable q :=
  decidable_of_decidable_of_iff hp (eq.to_iff h)

protected def or.by_cases {p : Prop} {q : Prop} [Decidable p] [Decidable q] {α : Sort u} (h : p ∨ q) (h₁ : p → α) (h₂ : q → α) : α :=
  dite p (fun (hp : p) => h₁ hp)
    fun (hp : ¬p) => dite q (fun (hq : q) => h₂ hq) fun (hq : ¬q) => False._oldrec (or.elim h hp hq)

protected instance and.decidable {p : Prop} {q : Prop} [Decidable p] [Decidable q] : Decidable (p ∧ q) :=
  dite p (fun (hp : p) => dite q (fun (hq : q) => is_true { left := hp, right := hq }) fun (hq : ¬q) => is_false sorry)
    fun (hp : ¬p) => is_false sorry

protected instance or.decidable {p : Prop} {q : Prop} [Decidable p] [Decidable q] : Decidable (p ∨ q) :=
  dite p (fun (hp : p) => is_true (Or.inl hp))
    fun (hp : ¬p) => dite q (fun (hq : q) => is_true (Or.inr hq)) fun (hq : ¬q) => is_false (Or._oldrec hp hq)

protected instance not.decidable {p : Prop} [Decidable p] : Decidable (¬p) :=
  dite p (fun (hp : p) => is_false (absurd hp)) fun (hp : ¬p) => is_true hp

protected instance implies.decidable {p : Prop} {q : Prop} [Decidable p] [Decidable q] : Decidable (p → q) :=
  dite p (fun (hp : p) => dite q (fun (hq : q) => is_true sorry) fun (hq : ¬q) => is_false sorry)
    fun (hp : ¬p) => is_true sorry

protected instance iff.decidable {p : Prop} {q : Prop} [Decidable p] [Decidable q] : Decidable (p ↔ q) :=
  dite p (fun (hp : p) => dite q (fun (hq : q) => is_true sorry) fun (hq : ¬q) => is_false sorry)
    fun (hp : ¬p) => dite q (fun (hq : q) => is_false sorry) fun (hq : ¬q) => is_true sorry

protected instance xor.decidable {p : Prop} {q : Prop} [Decidable p] [Decidable q] : Decidable (xor p q) :=
  dite p (fun (hp : p) => dite q (fun (hq : q) => is_false sorry) fun (hq : ¬q) => is_true sorry)
    fun (hp : ¬p) => dite q (fun (hq : q) => is_true sorry) fun (hq : ¬q) => is_false sorry

protected instance exists_prop_decidable {p : Prop} (P : p → Prop) [Dp : Decidable p] [DP : (h : p) → Decidable (P h)] : Decidable (∃ (h : p), P h) :=
  dite p (fun (h : p) => decidable_of_decidable_of_iff (DP h) sorry) fun (h : ¬p) => is_false sorry

protected instance forall_prop_decidable {p : Prop} (P : p → Prop) [Dp : Decidable p] [DP : (h : p) → Decidable (P h)] : Decidable (∀ (h : p), P h) :=
  dite p (fun (h : p) => decidable_of_decidable_of_iff (DP h) sorry) fun (h : ¬p) => is_true sorry

protected instance ne.decidable {α : Sort u} [DecidableEq α] (a : α) (b : α) : Decidable (a ≠ b) :=
  implies.decidable

theorem bool.ff_ne_tt : false = tt → False :=
  fun (ᾰ : false = tt) => eq.dcases_on ᾰ (fun (H_1 : tt = false) => bool.no_confusion H_1) (Eq.refl tt) (HEq.refl ᾰ)

def is_dec_eq {α : Sort u} (p : α → α → Bool)  :=
  ∀ {x y : α}, p x y = tt → x = y

def is_dec_refl {α : Sort u} (p : α → α → Bool)  :=
  ∀ (x : α), p x x = tt

protected instance bool.decidable_eq : DecidableEq Bool :=
  sorry

def decidable_eq_of_bool_pred {α : Sort u} {p : α → α → Bool} (h₁ : is_dec_eq p) (h₂ : is_dec_refl p) : DecidableEq α :=
  fun (x y : α) => dite (p x y = tt) (fun (hp : p x y = tt) => is_true (h₁ hp)) fun (hp : ¬p x y = tt) => is_false sorry

theorem decidable_eq_inl_refl {α : Sort u} [h : DecidableEq α] (a : α) : h a a = is_true (Eq.refl a) := sorry

theorem decidable_eq_inr_neg {α : Sort u} [h : DecidableEq α] {a : α} {b : α} (n : a ≠ b) : h a b = is_false n := sorry

/- inhabited -/

not founddef arbitrary (α : Sort u) [Inhabited α] : α :=
  Inhabited.default

protected instance prop.inhabited : Inhabited Prop :=
  { default := True }

protected instance pi.inhabited (α : Sort u) {β : α → Sort v} [(x : α) → Inhabited (β x)] : Inhabited ((x : α) → β x) :=
  { default := fun (a : α) => Inhabited.default }

protected instance bool.inhabited : Inhabited Bool :=
  { default := false }

protected instance true.inhabited : Inhabited True :=
  { default := trivial }

not foundprotected def nonempty.elim {α : Sort u} {p : Prop} (h₁ : Nonempty α) (h₂ : α → p) : p :=
  Nonempty._oldrec h₂ h₁

protected instance nonempty_of_inhabited {α : Sort u} [Inhabited α] : Nonempty α :=
  Nonempty.intro Inhabited.default

theorem nonempty_of_exists {α : Sort u} {p : α → Prop} : (∃ (x : α), p x) → Nonempty α :=
  fun (ᾰ : ∃ (x : α), p x) => Exists.dcases_on ᾰ fun (ᾰ_w : α) (ᾰ_h : p ᾰ_w) => idRhs (Nonempty α) (Nonempty.intro ᾰ_w)

/- subsingleton -/

class inductive subsingleton (α : Sort u) 
where
| intro : (∀ (a b : α), a = b) → subsingleton α

protected def subsingleton.elim {α : Sort u} [h : subsingleton α] (a : α) (b : α) : a = b :=
  subsingleton._oldrec (fun (p : ∀ (a b : α), a = b) => p) h

protected def subsingleton.helim {α : Sort u} {β : Sort u} [h : subsingleton α] : α = β → ∀ (a : α) (b : β), a == b :=
  fun (h_1 : α = β) => eq.rec_on h_1 fun (a b : α) => heq_of_eq (subsingleton.elim a b)

protected instance subsingleton_prop (p : Prop) : subsingleton p :=
  subsingleton.intro fun (a b : p) => proof_irrel a b

protected instance decidable.subsingleton (p : Prop) : subsingleton (Decidable p) :=
  subsingleton.intro fun (d₁ : Decidable p) => sorry

protected theorem rec_subsingleton {p : Prop} [h : Decidable p] {h₁ : p → Sort u} {h₂ : ¬p → Sort u} [h₃ : ∀ (h : p), subsingleton (h₁ h)] [h₄ : ∀ (h : ¬p), subsingleton (h₂ h)] : subsingleton (decidable.rec_on h h₂ h₁) := sorry

theorem if_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t : α} {e : α} : ite c t e = t := sorry

theorem if_neg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t : α} {e : α} : ite c t e = e := sorry

@[simp] theorem if_t_t (c : Prop) [h : Decidable c] {α : Sort u} (t : α) : ite c t t = t := sorry

theorem implies_of_if_pos {c : Prop} {t : Prop} {e : Prop} [Decidable c] (h : ite c t e) : c → t :=
  fun (hc : c) => eq.rec_on (if_pos hc) h

theorem implies_of_if_neg {c : Prop} {t : Prop} {e : Prop} [Decidable c] (h : ite c t e) : ¬c → e :=
  fun (hnc : ¬c) => eq.rec_on (if_neg hnc) h

theorem if_ctx_congr {α : Sort u} {b : Prop} {c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x : α} {y : α} {u : α} {v : α} (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) : ite b x y = ite c u v := sorry

theorem if_congr {α : Sort u} {b : Prop} {c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x : α} {y : α} {u : α} {v : α} (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v :=
  if_ctx_congr h_c (fun (h : c) => h_t) fun (h : ¬c) => h_e

@[simp] theorem if_true {α : Sort u} {h : Decidable True} (t : α) (e : α) : ite True t e = t :=
  if_pos trivial

@[simp] theorem if_false {α : Sort u} {h : Decidable False} (t : α) (e : α) : ite False t e = e :=
  if_neg not_false

theorem if_ctx_congr_prop {b : Prop} {c : Prop} {x : Prop} {y : Prop} {u : Prop} {v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v := sorry

theorem if_congr_prop {b : Prop} {c : Prop} {x : Prop} {y : Prop} {u : Prop} {v : Prop} [dec_b : Decidable b] [dec_c : Decidable c] (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c (fun (h : c) => h_t) fun (h : ¬c) => h_e

theorem if_ctx_simp_congr_prop {b : Prop} {c : Prop} {x : Prop} {y : Prop} {u : Prop} {v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) : ite b x y ↔ ite c u v :=
  if_ctx_congr_prop h_c h_t h_e

theorem if_simp_congr_prop {b : Prop} {c : Prop} {x : Prop} {y : Prop} {u : Prop} {v : Prop} [dec_b : Decidable b] (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) : ite b x y ↔ ite c u v :=
  if_ctx_simp_congr_prop h_c (fun (h : c) => h_t) fun (h : ¬c) => h_e

@[simp] theorem dif_pos {c : Prop} [h : Decidable c] (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc := sorry

@[simp] theorem dif_neg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = e hnc := sorry

theorem dif_ctx_congr {α : Sort u} {b : Prop} {c : Prop} [dec_b : Decidable b] [dec_c : Decidable c] {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ (h : c), x (iff.mpr h_c h) = u h) (h_e : ∀ (h : ¬c), y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) : dite b x y = dite c u v := sorry

theorem dif_ctx_simp_congr {α : Sort u} {b : Prop} {c : Prop} [dec_b : Decidable b] {x : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α} (h_c : b ↔ c) (h_t : ∀ (h : c), x (iff.mpr h_c h) = u h) (h_e : ∀ (h : ¬c), y (iff.mpr (not_iff_not_of_iff h_c) h) = v h) : dite b x y = dite c u v :=
  dif_ctx_congr h_c h_t h_e

-- Remark: dite and ite are "defally equal" when we ignore the proofs.

theorem dif_eq_if (c : Prop) [h : Decidable c] {α : Sort u} (t : α) (e : α) : (dite c (fun (h : c) => t) fun (h : ¬c) => e) = ite c t e := sorry

protected instance ite.decidable {c : Prop} {t : Prop} {e : Prop} [d_c : Decidable c] [d_t : Decidable t] [d_e : Decidable e] : Decidable (ite c t e) :=
  sorry

protected instance dite.decidable {c : Prop} {t : c → Prop} {e : ¬c → Prop} [d_c : Decidable c] [d_t : (h : c) → Decidable (t h)] [d_e : (h : ¬c) → Decidable (e h)] : Decidable (dite c (fun (h : c) => t h) fun (h : ¬c) => e h) :=
  sorry

def as_true (c : Prop) [Decidable c]  :=
  ite c True False

def as_false (c : Prop) [Decidable c]  :=
  ite c False True

def of_as_true {c : Prop} [h₁ : Decidable c] (h₂ : as_true c) : c :=
  sorry

/-- Universe lifting operation -/
structure ulift (α : Type s) 
  up ::
where (down : α)

namespace ulift


/- Bijection between α and ulift.{v} α -/

theorem up_down {α : Type u} (b : ulift α) : up (down b) = b :=
  cases_on b fun (b : α) => idRhs (up (down (up b)) = up (down (up b))) rfl

end ulift


theorem ulift.down_up {α : Type u} (a : α) : ulift.down (ulift.up a) = a :=
  rfl

/-- Universe lifting operation from Sort to Type -/
structure plift (α : Sort u) 
  up ::
where (down : α)

namespace plift


/- Bijection between α and plift α -/

theorem up_down {α : Sort u} (b : plift α) : up (down b) = b :=
  cases_on b fun (b : α) => idRhs (up (down (up b)) = up (down (up b))) rfl

end plift


theorem plift.down_up {α : Sort u} (a : α) : plift.down (plift.up a) = a :=
  rfl

/- Equalities for rewriting let-expressions -/

theorem let_value_eq {α : Sort u} {β : Sort v} {a₁ : α} {a₂ : α} (b : α → β) : a₁ = a₂ →
  (let x : α := a₁;
    b x) =
    let x : α := a₂;
    b x :=
  fun (h : a₁ = a₂) => eq.rec_on h rfl

theorem let_value_heq {α : Sort v} {β : α → Sort u} {a₁ : α} {a₂ : α} (b : (x : α) → β x) : a₁ = a₂ →
  (let x : α := a₁;
    b x) ==
    let x : α := a₂;
    b x :=
  fun (h : a₁ = a₂) => eq.rec_on h (HEq.refl (b a₁))

theorem let_body_eq {α : Sort v} {β : α → Sort u} (a : α) {b₁ : (x : α) → β x} {b₂ : (x : α) → β x} : (∀ (x : α), b₁ x = b₂ x) →
  (let x : α := a;
    b₁ x) =
    let x : α := a;
    b₂ x :=
  fun (h : ∀ (x : α), b₁ x = b₂ x) => h a

theorem let_eq {α : Sort v} {β : Sort u} {a₁ : α} {a₂ : α} {b₁ : α → β} {b₂ : α → β} : a₁ = a₂ →
  (∀ (x : α), b₁ x = b₂ x) →
    (let x : α := a₁;
      b₁ x) =
      let x : α := a₂;
      b₂ x :=
  fun (h₁ : a₁ = a₂) (h₂ : ∀ (x : α), b₁ x = b₂ x) => eq.rec_on h₁ (h₂ a₁)

def reflexive {β : Sort v} (r : β → β → Prop)  :=
  ∀ (x : β), r x x

def symmetric {β : Sort v} (r : β → β → Prop)  :=
  ∀ {x y : β}, r x y → r y x

def transitive {β : Sort v} (r : β → β → Prop)  :=
  ∀ {x y z : β}, r x y → r y z → r x z

def equivalence {β : Sort v} (r : β → β → Prop)  :=
  reflexive r ∧ symmetric r ∧ transitive r

def total {β : Sort v} (r : β → β → Prop)  :=
  ∀ (x y : β), r x y ∨ r y x

def mk_equivalence {β : Sort v} (r : β → β → Prop) (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) : equivalence r :=
  { left := rfl, right := { left := symm, right := trans } }

def irreflexive {β : Sort v} (r : β → β → Prop)  :=
  ∀ (x : β), ¬r x x

def anti_symmetric {β : Sort v} (r : β → β → Prop)  :=
  ∀ {x y : β}, r x y → r y x → x = y

def empty_relation {α : Sort u} (a₁ : α) (a₂ : α)  :=
  False

def subrelation {β : Sort v} (q : β → β → Prop) (r : β → β → Prop)  :=
  ∀ {x y : β}, q x y → r x y

def inv_image {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) : α → α → Prop :=
  fun (a₁ a₂ : α) => r (f a₁) (f a₂)

theorem inv_image.trans {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
  fun (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃) => h h₁ h₂

theorem inv_image.irreflexive {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
  fun (a : α) (h₁ : inv_image r f a a) => h (f a) h₁

inductive tc {α : Sort u} (r : α → α → Prop) : α → α → Prop
where
| base : ∀ (a b : α), r a b → tc r a b
| trans : ∀ (a b c : α), tc r a b → tc r b c → tc r a c

def commutative {α : Type u} (f : α → α → α)  :=
  ∀ (a b : α), f a b = f b a

def associative {α : Type u} (f : α → α → α)  :=
  ∀ (a b c : α), f (f a b) c = f a (f b c)

def left_identity {α : Type u} (f : α → α → α) (one : α)  :=
  ∀ (a : α), f one a = a

def right_identity {α : Type u} (f : α → α → α) (one : α)  :=
  ∀ (a : α), f a one = a

def right_inverse {α : Type u} (f : α → α → α) (inv : α → α) (one : α)  :=
  ∀ (a : α), f a (inv a) = one

def left_cancelative {α : Type u} (f : α → α → α)  :=
  ∀ (a b c : α), f a b = f a c → b = c

def right_cancelative {α : Type u} (f : α → α → α)  :=
  ∀ (a b c : α), f a b = f c b → a = c

def left_distributive {α : Type u} (f : α → α → α) (g : α → α → α)  :=
  ∀ (a b c : α), f a (g b c) = g (f a b) (f a c)

def right_distributive {α : Type u} (f : α → α → α) (g : α → α → α)  :=
  ∀ (a b c : α), f (g a b) c = g (f a c) (f b c)

def right_commutative {α : Type u} {β : Type v} (h : β → α → β)  :=
  ∀ (b : β) (a₁ a₂ : α), h (h b a₁) a₂ = h (h b a₂) a₁

def left_commutative {α : Type u} {β : Type v} (h : α → β → β)  :=
  ∀ (a₁ a₂ : α) (b : β), h a₁ (h a₂ b) = h a₂ (h a₁ b)

theorem left_comm {α : Type u} (f : α → α → α) : commutative f → associative f → left_commutative f :=
  fun (hcomm : commutative f) (hassoc : associative f) (a b c : α) =>
    Eq.trans (Eq.trans (Eq.symm (hassoc a b c)) (hcomm a b ▸ rfl)) (hassoc b a c)

theorem right_comm {α : Type u} (f : α → α → α) : commutative f → associative f → right_commutative f :=
  fun (hcomm : commutative f) (hassoc : associative f) (a b c : α) =>
    Eq.trans (Eq.trans (hassoc a b c) (hcomm b c ▸ rfl)) (Eq.symm (hassoc a c b))

