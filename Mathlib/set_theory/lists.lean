/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

A computable model of hereditarily finite sets with atoms
(ZFA without infinity). This is useful for calculations in naive
set theory.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.data.sigma.default
import Mathlib.PostPort

universes u l u_1 u_2 u_3 

namespace Mathlib

inductive lists' (α : Type u) : Bool → Type u
where
| atom : α → lists' α false
| nil : lists' α tt
| cons' : {b : Bool} → lists' α b → lists' α tt → lists' α tt

def lists (α : Type u_1) :=
  sigma fun (b : Bool) => lists' α b

namespace lists'


protected instance inhabited {α : Type u_1} [Inhabited α] (b : Bool) : Inhabited (lists' α b) :=
  sorry

def cons {α : Type u_1} : lists α → lists' α tt → lists' α tt :=
  sorry

@[simp] def to_list {α : Type u_1} {b : Bool} : lists' α b → List (lists α) :=
  sorry

@[simp] theorem to_list_cons {α : Type u_1} (a : lists α) (l : lists' α tt) : to_list (cons a l) = a :: to_list l := sorry

@[simp] def of_list {α : Type u_1} : List (lists α) → lists' α tt :=
  sorry

@[simp] theorem to_of_list {α : Type u_1} (l : List (lists α)) : to_list (of_list l) = l := sorry

@[simp] theorem of_to_list {α : Type u_1} (l : lists' α tt) : of_list (to_list l) = l := sorry

end lists'


def lists'.subset {α : Type u_1} : lists' α tt → lists' α tt → Prop :=
  fun (ᾰ ᾰ_1 : lists' α tt) =>
    lists.equiv._mut_
      ((fun (idx : psigma fun (ᾰ : lists' α tt) => psigma fun (ᾰ : lists' α tt) => Unit) => psum.inr idx)
        ((fun (ᾰ ᾰ_2 : lists' α tt) => psigma.mk ᾰ (psigma.mk ᾰ_2 Unit.unit)) ᾰ ᾰ_1))

namespace lists'


protected instance has_subset {α : Type u_1} : has_subset (lists' α tt) :=
  has_subset.mk subset

protected instance has_mem {α : Type u_1} {b : Bool} : has_mem (lists α) (lists' α b) :=
  has_mem.mk fun (a : lists α) (l : lists' α b) => ∃ (a' : lists α), ∃ (H : a' ∈ to_list l), lists.equiv a a'

theorem mem_def {α : Type u_1} {b : Bool} {a : lists α} {l : lists' α b} : a ∈ l ↔ ∃ (a' : lists α), ∃ (H : a' ∈ to_list l), lists.equiv a a' :=
  iff.rfl

@[simp] theorem mem_cons {α : Type u_1} {a : lists α} {y : lists α} {l : lists' α tt} : a ∈ cons y l ↔ lists.equiv a y ∨ a ∈ l := sorry

theorem cons_subset {α : Type u_1} {a : lists α} {l₁ : lists' α tt} {l₂ : lists' α tt} : cons a l₁ ⊆ l₂ ↔ a ∈ l₂ ∧ l₁ ⊆ l₂ := sorry

theorem of_list_subset {α : Type u_1} {l₁ : List (lists α)} {l₂ : List (lists α)} (h : l₁ ⊆ l₂) : of_list l₁ ⊆ of_list l₂ := sorry

theorem subset.refl {α : Type u_1} {l : lists' α tt} : l ⊆ l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (l ⊆ l)) (Eq.symm (of_to_list l)))) (of_list_subset (list.subset.refl (to_list l)))

theorem subset_nil {α : Type u_1} {l : lists' α tt} : l ⊆ nil → l = nil := sorry

theorem mem_of_subset' {α : Type u_1} {a : lists α} {l₁ : lists' α tt} {l₂ : lists' α tt} (s : l₁ ⊆ l₂) (h : a ∈ to_list l₁) : a ∈ l₂ := sorry

theorem subset_def {α : Type u_1} {l₁ : lists' α tt} {l₂ : lists' α tt} : l₁ ⊆ l₂ ↔ ∀ (a : lists α), a ∈ to_list l₁ → a ∈ l₂ := sorry

end lists'


namespace lists


def atom {α : Type u_1} (a : α) : lists α :=
  sigma.mk false (lists'.atom a)

def of' {α : Type u_1} (l : lists' α tt) : lists α :=
  sigma.mk tt l

@[simp] def to_list {α : Type u_1} : lists α → List (lists α) :=
  sorry

def is_list {α : Type u_1} (l : lists α) :=
  ↥(sigma.fst l)

def of_list {α : Type u_1} (l : List (lists α)) : lists α :=
  of' (lists'.of_list l)

theorem is_list_to_list {α : Type u_1} (l : List (lists α)) : is_list (of_list l) :=
  Eq.refl (sigma.fst (of_list l))

theorem to_of_list {α : Type u_1} (l : List (lists α)) : to_list (of_list l) = l := sorry

theorem of_to_list {α : Type u_1} {l : lists α} : is_list l → of_list (to_list l) = l := sorry

protected instance inhabited {α : Type u_1} : Inhabited (lists α) :=
  { default := of' lists'.nil }

protected instance decidable_eq {α : Type u_1} [DecidableEq α] : DecidableEq (lists α) :=
  eq.mpr sorry fun (a b : sigma fun (b : Bool) => lists' α b) => sigma.decidable_eq a b

protected instance has_sizeof {α : Type u_1} [SizeOf α] : SizeOf (lists α) :=
  eq.mpr sorry (sigma.has_sizeof Bool fun (b : Bool) => lists' α b)

def induction_mut {α : Type u_1} (C : lists α → Sort u_2) (D : lists' α tt → Sort u_3) (C0 : (a : α) → C (atom a)) (C1 : (l : lists' α tt) → D l → C (of' l)) (D0 : D lists'.nil) (D1 : (a : lists α) → (l : lists' α tt) → C a → D l → D (lists'.cons a l)) : PProd ((l : lists α) → C l) ((l : lists' α tt) → D l) :=
  { fst := fun (_x : lists α) => sorry,
    snd :=
      fun (l : lists' α tt) =>
        pprod.snd
          ((fun (b : Bool) (l : lists' α b) =>
              lists'.rec (fun (a : α) => { fst := C0 a, snd := PUnit.unit }) { fst := C1 lists'.nil D0, snd := D0 }
                (fun {b : Bool} (a : lists' α b) (l : lists' α tt) (IH₁ : PProd (C (sigma.mk b a)) sorry)
                  (IH₂ : PProd (C (sigma.mk tt l)) sorry) =>
                  { fst := C1 (lists'.cons' a l) (D1 (sigma.mk b a) l (pprod.fst IH₁) (pprod.snd IH₂)),
                    snd := D1 (sigma.mk b a) l (pprod.fst IH₁) (pprod.snd IH₂) })
                l)
            tt l) }

def mem {α : Type u_1} (a : lists α) : lists α → Prop :=
  sorry

protected instance has_mem {α : Type u_1} : has_mem (lists α) (lists α) :=
  has_mem.mk mem

theorem is_list_of_mem {α : Type u_1} {a : lists α} {l : lists α} : a ∈ l → is_list l := sorry

theorem equiv.antisymm_iff {α : Type u_1} {l₁ : lists' α tt} {l₂ : lists' α tt} : equiv (of' l₁) (of' l₂) ↔ l₁ ⊆ l₂ ∧ l₂ ⊆ l₁ := sorry

theorem equiv_atom {α : Type u_1} {a : α} {l : lists α} : equiv (atom a) l ↔ atom a = l := sorry

theorem equiv.symm {α : Type u_1} {l₁ : lists α} {l₂ : lists α} (h : equiv l₁ l₂) : equiv l₂ l₁ := sorry

theorem equiv.trans {α : Type u_1} {l₁ : lists α} {l₂ : lists α} {l₃ : lists α} : equiv l₁ l₂ → equiv l₂ l₃ → equiv l₁ l₃ := sorry

protected instance setoid {α : Type u_1} : setoid (lists α) :=
  setoid.mk equiv sorry

@[simp] def equiv.decidable_meas {α : Type u_1} : psum (psigma fun (l₁ : lists α) => lists α)
    (psum (psigma fun (l₁ : lists' α tt) => lists' α tt) (psigma fun (a : lists α) => lists' α tt)) →
  ℕ :=
  sorry

theorem sizeof_pos {α : Type u_1} {b : Bool} (l : lists' α b) : 0 < sizeof l := sorry

theorem lt_sizeof_cons' {α : Type u_1} {b : Bool} (a : lists' α b) (l : lists' α tt) : sizeof (sigma.mk b a) < sizeof (lists'.cons' a l) := sorry

instance mem.decidable {α : Type u_1} [DecidableEq α] (a : lists α) (l : lists' α tt) : Decidable (a ∈ l) :=
  sorry

end lists


namespace lists'


theorem mem_equiv_left {α : Type u_1} {l : lists' α tt} {a : lists α} {a' : lists α} : lists.equiv a a' → (a ∈ l ↔ a' ∈ l) := sorry

theorem mem_of_subset {α : Type u_1} {a : lists α} {l₁ : lists' α tt} {l₂ : lists' α tt} (s : l₁ ⊆ l₂) : a ∈ l₁ → a ∈ l₂ := sorry

theorem subset.trans {α : Type u_1} {l₁ : lists' α tt} {l₂ : lists' α tt} {l₃ : lists' α tt} (h₁ : l₁ ⊆ l₂) (h₂ : l₂ ⊆ l₃) : l₁ ⊆ l₃ :=
  iff.mpr subset_def fun (a₁ : lists α) (m₁ : a₁ ∈ to_list l₁) => mem_of_subset h₂ (mem_of_subset' h₁ m₁)

end lists'


def finsets (α : Type u_1) :=
  quotient lists.setoid

namespace finsets


protected instance has_emptyc {α : Type u_1} : has_emptyc (finsets α) :=
  has_emptyc.mk (quotient.mk (lists.of' lists'.nil))

protected instance inhabited {α : Type u_1} : Inhabited (finsets α) :=
  { default := ∅ }

protected instance decidable_eq {α : Type u_1} [DecidableEq α] : DecidableEq (finsets α) :=
  eq.mpr sorry fun (a b : quotient lists.setoid) => quotient.decidable_eq a b

