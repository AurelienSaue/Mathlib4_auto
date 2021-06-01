/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.nat.basic
import Mathlib.Lean3Lib.init.data.prod

universes u l v 

namespace Mathlib

inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop where
| intro : ∀ (x : α), (∀ (y : α), r y x → acc r y) → acc r x

namespace acc


def inv {α : Sort u} {r : α → α → Prop} {x : α} {y : α} (h₁ : acc r x) (h₂ : r y x) : acc r y :=
  acc.rec_on h₁
    (fun (x₁ : α) (ac₁ : ∀ (y : α), r y x₁ → acc r y)
      (ih : ∀ (y_1 : α), r y_1 x₁ → r y y_1 → acc r y) (h₂ : r y x₁) => ac₁ y h₂)
    h₂

end acc


/-- A relation `r : α → α → Prop` is well-founded when `∀ x, (∀ y, r y x → P y → P x) → P x` for all predicates `P`.
Once you know that a relation is well_founded, you can use it to define fixpoint functions on `α`.-/
structure well_founded {α : Sort u} (r : α → α → Prop) where
  intro :: (apply : ∀ (a : α), acc r a)

class has_well_founded (α : Sort u) where
  r : α → α → Prop
  wf : well_founded r

namespace well_founded


def recursion {α : Sort u} {r : α → α → Prop} (hwf : well_founded r) {C : α → Sort v} (a : α)
    (h : (x : α) → ((y : α) → r y x → C y) → C x) : C a :=
  acc.rec_on (apply hwf a)
    fun (x₁ : α) (ac₁ : ∀ (y : α), r y x₁ → acc r y) (ih : (y : α) → r y x₁ → C y) => h x₁ ih

theorem induction {α : Sort u} {r : α → α → Prop} (hwf : well_founded r) {C : α → Prop} (a : α)
    (h : ∀ (x : α), (∀ (y : α), r y x → C y) → C x) : C a :=
  recursion hwf a h

def fix_F {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) (a : acc r x) : C x :=
  acc.rec_on a
    fun (x₁ : α) (ac₁ : ∀ (y : α), r y x₁ → acc r y) (ih : (y : α) → r y x₁ → C y) => F x₁ ih

theorem fix_F_eq {α : Sort u} {r : α → α → Prop} {C : α → Sort v}
    (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) (acx : acc r x) :
    fix_F F x acx = F x fun (y : α) (p : r y x) => fix_F F y (acc.inv acx p) :=
  sorry

/-- Well-founded fixpoint -/
def fix {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (hwf : well_founded r)
    (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) : C x :=
  fix_F F x sorry

/-- Well-founded fixpoint satisfies fixpoint equation -/
theorem fix_eq {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (hwf : well_founded r)
    (F : (x : α) → ((y : α) → r y x → C y) → C x) (x : α) :
    fix hwf F x = F x fun (y : α) (h : r y x) => fix hwf F y :=
  fix_F_eq F x (apply hwf x)

end well_founded


/-- Empty relation is well-founded -/
def empty_wf {α : Sort u} : well_founded empty_relation :=
  well_founded.intro fun (a : α) => acc.intro a fun (b : α) (lt : False) => False._oldrec lt

/- Subrelation of a well-founded relation is well-founded -/

namespace subrelation


def accessible {α : Sort u} {r : α → α → Prop} {Q : α → α → Prop} (h₁ : subrelation Q r) {a : α}
    (ac : acc r a) : acc Q a :=
  acc.rec_on ac
    fun (x : α) (ax : ∀ (y : α), r y x → acc r y) (ih : ∀ (y : α), r y x → acc Q y) =>
      acc.intro x fun (y : α) (lt : Q y x) => ih y (h₁ lt)

def wf {α : Sort u} {r : α → α → Prop} {Q : α → α → Prop} (h₁ : subrelation Q r)
    (h₂ : well_founded r) : well_founded Q :=
  well_founded.intro fun (a : α) => accessible h₁ (well_founded.apply h₂ a)

end subrelation


-- The inverse image of a well-founded relation is well-founded

namespace inv_image


def accessible {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β) {a : α} (ac : acc r (f a)) :
    acc (inv_image r f) a :=
  acc_aux f ac a rfl

def wf {α : Sort u} {β : Sort v} {r : β → β → Prop} (f : α → β) (h : well_founded r) :
    well_founded (inv_image r f) :=
  well_founded.intro fun (a : α) => accessible f (well_founded.apply h (f a))

end inv_image


-- The transitive closure of a well-founded relation is well-founded

namespace tc


def accessible {α : Sort u} {r : α → α → Prop} {z : α} (ac : acc r z) : acc (tc r) z :=
  acc.rec_on ac
    fun (x : α) (acx : ∀ (y : α), r y x → acc r y) (ih : ∀ (y : α), r y x → acc (tc r) y) =>
      acc.intro x
        fun (y : α) (rel : tc r y x) =>
          tc.rec_on rel
            (fun (a b : α) (rab : r a b) (acx : ∀ (y : α), r y b → acc r y)
              (ih : ∀ (y : α), r y b → acc (tc r) y) => ih a rab)
            (fun (a b c : α) (rab : tc r a b) (rbc : tc r b c)
              (ih₁ :
              (∀ (y : α), r y b → acc r y) → (∀ (y : α), r y b → acc (tc r) y) → acc (tc r) a)
              (ih₂ :
              (∀ (y : α), r y c → acc r y) → (∀ (y : α), r y c → acc (tc r) y) → acc (tc r) b)
              (acx : ∀ (y : α), r y c → acc r y) (ih : ∀ (y : α), r y c → acc (tc r) y) =>
              acc.inv (ih₂ acx ih) rab)
            acx ih

def wf {α : Sort u} {r : α → α → Prop} (h : well_founded r) : well_founded (tc r) :=
  well_founded.intro fun (a : α) => accessible (well_founded.apply h a)

end tc


/-- less-than is well-founded -/
def nat.lt_wf : well_founded nat.lt :=
  well_founded.intro
    (Nat.rec (acc.intro 0 fun (n : ℕ) (h : n < 0) => absurd h (nat.not_lt_zero n))
      fun (n : ℕ) (ih : acc Less n) =>
        acc.intro (Nat.succ n)
          fun (m : ℕ) (h : m < Nat.succ n) =>
            or.elim (nat.eq_or_lt_of_le (nat.le_of_succ_le_succ h))
              (fun (e : m = n) => eq.substr e ih) (acc.inv ih))

def measure {α : Sort u} : (α → ℕ) → α → α → Prop := inv_image Less

def measure_wf {α : Sort u} (f : α → ℕ) : well_founded (measure f) := inv_image.wf f nat.lt_wf

def sizeof_measure (α : Sort u) [SizeOf α] : α → α → Prop := measure sizeof

def sizeof_measure_wf (α : Sort u) [SizeOf α] : well_founded (sizeof_measure α) := measure_wf sizeof

protected instance has_well_founded_of_has_sizeof (α : Sort u) [SizeOf α] : has_well_founded α :=
  has_well_founded.mk (sizeof_measure α) (sizeof_measure_wf α)

namespace prod


inductive lex {α : Type u} {β : Type v} (ra : α → α → Prop) (rb : β → β → Prop) :
    α × β → α × β → Prop
    where
| left : ∀ {a₁ : α} (b₁ : β) {a₂ : α} (b₂ : β), ra a₁ a₂ → lex ra rb (a₁, b₁) (a₂, b₂)
| right : ∀ (a : α) {b₁ b₂ : β}, rb b₁ b₂ → lex ra rb (a, b₁) (a, b₂)

inductive rprod {α : Type u} {β : Type v} (ra : α → α → Prop) (rb : β → β → Prop) :
    α × β → α × β → Prop
    where
| intro : ∀ {a₁ : α} {b₁ : β} {a₂ : α} {b₂ : β}, ra a₁ a₂ → rb b₁ b₂ → rprod ra rb (a₁, b₁) (a₂, b₂)

def lex_accessible {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} {a : α}
    (aca : acc ra a) (acb : ∀ (b : β), acc rb b) (b : β) : acc (lex ra rb) (a, b) :=
  acc.rec_on aca
    fun (xa : α) (aca : ∀ (y : α), ra y xa → acc ra y)
      (iha : ∀ (y : α), ra y xa → ∀ (b : β), acc (lex ra rb) (y, b)) (b : β) =>
      acc.rec_on (acb b)
        fun (xb : β) (acb : ∀ (y : β), rb y xb → acc rb y)
          (ihb : ∀ (y : β), rb y xb → acc (lex ra rb) (xa, y)) =>
          acc.intro (xa, xb)
            fun (p : α × β) (lt : lex ra rb p (xa, xb)) =>
              (fun (aux : xa = xa → xb = xb → acc (lex ra rb) p) => aux rfl rfl)
                (lex.rec_on lt
                  (fun (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β) (h : ra a₁ a₂) (eq₂ : a₂ = xa)
                    (eq₃ : b₂ = xb) => iha a₁ (eq.rec_on eq₂ h) b₁)
                  fun (a : α) (b₁ b₂ : β) (h : rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb) =>
                    eq.rec_on (Eq.symm eq₂) (ihb b₁ (eq.rec_on eq₃ h)))

def lex_wf {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} (ha : well_founded ra)
    (hb : well_founded rb) : well_founded (lex ra rb) :=
  well_founded.intro
    fun (p : α × β) =>
      cases_on p
        fun (a : α) (b : β) => lex_accessible (well_founded.apply ha a) (well_founded.apply hb) b

def rprod_sub_lex {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop} (a : α × β)
    (b : α × β) : rprod ra rb a b → lex ra rb a b :=
  fun (h : rprod ra rb a b) =>
    rprod.rec_on h
      fun (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β) (h₁ : ra a₁ a₂) (h₂ : rb b₁ b₂) => lex.left b₁ b₂ h₁

def rprod_wf {α : Type u} {β : Type v} {ra : α → α → Prop} {rb : β → β → Prop}
    (ha : well_founded ra) (hb : well_founded rb) : well_founded (rprod ra rb) :=
  subrelation.wf rprod_sub_lex (lex_wf ha hb)

protected instance has_well_founded {α : Type u} {β : Type v} [s₁ : has_well_founded α]
    [s₂ : has_well_founded β] : has_well_founded (α × β) :=
  has_well_founded.mk (lex has_well_founded.r has_well_founded.r) sorry

end Mathlib