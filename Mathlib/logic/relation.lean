/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Transitive reflexive as well as reflexive closure of relations.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

namespace relation


/--
The composition of two relations, yielding a new relation.  The result
relates a term of `α` and a term of `γ` if there is an intermediate
term of `β` related to both.
-/
def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) :=
  ∃ (b : β), r a b ∧ p b c

theorem comp_eq {α : Type u_1} {β : Type u_2} {r : α → β → Prop} : comp r Eq = r := sorry

theorem eq_comp {α : Type u_1} {β : Type u_2} {r : α → β → Prop} : comp Eq r = r := sorry

theorem iff_comp {α : Type u_1} {r : Prop → α → Prop} : comp Iff r = r := sorry

theorem comp_iff {α : Type u_1} {r : α → Prop → Prop} : comp r Iff = r := sorry

theorem comp_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop} : comp (comp r p) q = comp r (comp p q) := sorry

theorem flip_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → β → Prop} {p : β → γ → Prop} : flip (comp r p) = comp (flip p) (flip r) := sorry

/--
The map of a relation `r` through a pair of functions pushes the
relation to the codomains of the functions.  The resulting relation is
defined by having pairs of terms related if they have preimages
related by `r`.
-/
protected def map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (r : α → β → Prop) (f : α → γ) (g : β → δ) : γ → δ → Prop :=
  fun (c : γ) (d : δ) => ∃ (a : α), ∃ (b : β), r a b ∧ f a = c ∧ g b = d

/-- `refl_trans_gen r`: reflexive transitive closure of `r` -/
inductive refl_trans_gen {α : Type u_1} (r : α → α → Prop) (a : α) : α → Prop
where
| refl : refl_trans_gen r a a
| tail : ∀ {b c : α}, refl_trans_gen r a b → r b c → refl_trans_gen r a c

/-- `refl_gen r`: reflexive closure of `r` -/
inductive refl_gen {α : Type u_1} (r : α → α → Prop) (a : α) : α → Prop
where
| refl : refl_gen r a a
| single : ∀ {b : α}, r a b → refl_gen r a b

/-- `trans_gen r`: transitive closure of `r` -/
inductive trans_gen {α : Type u_1} (r : α → α → Prop) (a : α) : α → Prop
where
| single : ∀ {b : α}, r a b → trans_gen r a b
| tail : ∀ {b c : α}, trans_gen r a b → r b c → trans_gen r a c

theorem refl_gen.to_refl_trans_gen {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} : refl_gen r a b → refl_trans_gen r a b := sorry

namespace refl_trans_gen


theorem trans {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : refl_trans_gen r a b) (hbc : refl_trans_gen r b c) : refl_trans_gen r a c := sorry

theorem single {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} (hab : r a b) : refl_trans_gen r a b :=
  tail refl hab

theorem head {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : r a b) (hbc : refl_trans_gen r b c) : refl_trans_gen r a c := sorry

theorem symmetric {α : Type u_1} {r : α → α → Prop} (h : symmetric r) : symmetric (refl_trans_gen r) := sorry

theorem cases_tail {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} : refl_trans_gen r a b → b = a ∨ ∃ (c : α), refl_trans_gen r a c ∧ r c b :=
  iff.mp (cases_tail_iff r a b)

theorem head_induction_on {α : Type u_1} {r : α → α → Prop} {b : α} {P : (a : α) → refl_trans_gen r a b → Prop} {a : α} (h : refl_trans_gen r a b) (refl : P b refl) (head : ∀ {a c : α} (h' : r a c) (h : refl_trans_gen r c b), P c h → P a (head h' h)) : P a h := sorry

theorem trans_induction_on {α : Type u_1} {r : α → α → Prop} {P : {a b : α} → refl_trans_gen r a b → Prop} {a : α} {b : α} (h : refl_trans_gen r a b) (ih₁ : α → P refl) (ih₂ : ∀ {a b : α} (h : r a b), P (single h)) (ih₃ : ∀ {a b c : α} (h₁ : refl_trans_gen r a b) (h₂ : refl_trans_gen r b c), P h₁ → P h₂ → P (trans h₁ h₂)) : P h := sorry

theorem cases_head {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} (h : refl_trans_gen r a b) : a = b ∨ ∃ (c : α), r a c ∧ refl_trans_gen r c b := sorry

theorem cases_head_iff {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} : refl_trans_gen r a b ↔ a = b ∨ ∃ (c : α), r a c ∧ refl_trans_gen r c b := sorry

theorem total_of_right_unique {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (U : relator.right_unique r) (ab : refl_trans_gen r a b) (ac : refl_trans_gen r a c) : refl_trans_gen r b c ∨ refl_trans_gen r c b := sorry

end refl_trans_gen


namespace trans_gen


theorem to_refl {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} (h : trans_gen r a b) : refl_trans_gen r a b :=
  trans_gen.drec (fun {b : α} (h : r a b) => refl_trans_gen.single h)
    (fun {b c : α} (h_ᾰ : trans_gen r a b) (bc : r b c) (ab : refl_trans_gen r a b) => refl_trans_gen.tail ab bc) h

theorem trans_left {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : trans_gen r a b) (hbc : refl_trans_gen r b c) : trans_gen r a c := sorry

theorem trans {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : trans_gen r a b) (hbc : trans_gen r b c) : trans_gen r a c :=
  trans_left hab (to_refl hbc)

theorem head' {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : r a b) (hbc : refl_trans_gen r b c) : trans_gen r a c :=
  trans_left (single hab) hbc

theorem tail' {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : refl_trans_gen r a b) (hbc : r b c) : trans_gen r a c := sorry

theorem trans_right {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : refl_trans_gen r a b) (hbc : trans_gen r b c) : trans_gen r a c := sorry

theorem head {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (hab : r a b) (hbc : trans_gen r b c) : trans_gen r a c :=
  head' hab (to_refl hbc)

theorem tail'_iff {α : Type u_1} {r : α → α → Prop} {a : α} {c : α} : trans_gen r a c ↔ ∃ (b : α), refl_trans_gen r a b ∧ r b c := sorry

theorem head'_iff {α : Type u_1} {r : α → α → Prop} {a : α} {c : α} : trans_gen r a c ↔ ∃ (b : α), r a b ∧ refl_trans_gen r b c := sorry

theorem trans_gen_eq_self {α : Type u_1} {r : α → α → Prop} (trans : transitive r) : trans_gen r = r := sorry

theorem transitive_trans_gen {α : Type u_1} {r : α → α → Prop} : transitive (trans_gen r) :=
  fun (a b c : α) => trans

theorem trans_gen_idem {α : Type u_1} {r : α → α → Prop} : trans_gen (trans_gen r) = trans_gen r :=
  trans_gen_eq_self transitive_trans_gen

theorem trans_gen_lift {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} {a : α} {b : α} (f : α → β) (h : ∀ (a b : α), r a b → p (f a) (f b)) (hab : trans_gen r a b) : trans_gen p (f a) (f b) := sorry

theorem trans_gen_lift' {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} {a : α} {b : α} (f : α → β) (h : ∀ (a b : α), r a b → trans_gen p (f a) (f b)) (hab : trans_gen r a b) : trans_gen p (f a) (f b) :=
  eq.mpr (id (Eq.refl (trans_gen p (f a) (f b))))
    (eq.mp (congr_fun (congr_fun trans_gen_idem (f a)) (f b)) (trans_gen_lift f h hab))

theorem trans_gen_closed {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {p : α → α → Prop} : (∀ (a b : α), r a b → trans_gen p a b) → trans_gen r a b → trans_gen p a b :=
  trans_gen_lift' id

end trans_gen


theorem refl_trans_gen_iff_eq {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} (h : ∀ (b : α), ¬r a b) : refl_trans_gen r a b ↔ b = a := sorry

theorem refl_trans_gen_iff_eq_or_trans_gen {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} : refl_trans_gen r a b ↔ b = a ∨ trans_gen r a b := sorry

theorem refl_trans_gen_lift {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} {a : α} {b : α} (f : α → β) (h : ∀ (a b : α), r a b → p (f a) (f b)) (hab : refl_trans_gen r a b) : refl_trans_gen p (f a) (f b) :=
  refl_trans_gen.trans_induction_on hab (fun (a : α) => refl_trans_gen.refl)
    (fun (a b : α) => refl_trans_gen.single ∘ h a b)
    fun (a b c : α) (_x : refl_trans_gen r a b) (_x : refl_trans_gen r b c) => refl_trans_gen.trans

theorem refl_trans_gen_mono {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {p : α → α → Prop} : (∀ (a b : α), r a b → p a b) → refl_trans_gen r a b → refl_trans_gen p a b :=
  refl_trans_gen_lift id

theorem refl_trans_gen_eq_self {α : Type u_1} {r : α → α → Prop} (refl : reflexive r) (trans : transitive r) : refl_trans_gen r = r := sorry

theorem reflexive_refl_trans_gen {α : Type u_1} {r : α → α → Prop} : reflexive (refl_trans_gen r) :=
  fun (a : α) => refl_trans_gen.refl

theorem transitive_refl_trans_gen {α : Type u_1} {r : α → α → Prop} : transitive (refl_trans_gen r) :=
  fun (a b c : α) => refl_trans_gen.trans

theorem refl_trans_gen_idem {α : Type u_1} {r : α → α → Prop} : refl_trans_gen (refl_trans_gen r) = refl_trans_gen r :=
  refl_trans_gen_eq_self reflexive_refl_trans_gen transitive_refl_trans_gen

theorem refl_trans_gen_lift' {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} {a : α} {b : α} (f : α → β) (h : ∀ (a b : α), r a b → refl_trans_gen p (f a) (f b)) (hab : refl_trans_gen r a b) : refl_trans_gen p (f a) (f b) :=
  eq.mpr (id (Eq.refl (refl_trans_gen p (f a) (f b))))
    (eq.mp (congr_fun (congr_fun refl_trans_gen_idem (f a)) (f b)) (refl_trans_gen_lift f h hab))

theorem refl_trans_gen_closed {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {p : α → α → Prop} : (∀ (a b : α), r a b → refl_trans_gen p a b) → refl_trans_gen r a b → refl_trans_gen p a b :=
  refl_trans_gen_lift' id

/--
The join of a relation on a single type is a new relation for which
pairs of terms are related if there is a third term they are both
related to.  For example, if `r` is a relation representing rewrites
in a term rewriting system, then *confluence* is the property that if
`a` rewrites to both `b` and `c`, then `join r` relates `b` and `c`
(see `relation.church_rosser`).
-/
def join {α : Type u_1} (r : α → α → Prop) : α → α → Prop :=
  fun (a b : α) => ∃ (c : α), r a c ∧ r b c

theorem church_rosser {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {c : α} (h : ∀ (a b c : α), r a b → r a c → ∃ (d : α), refl_gen r b d ∧ refl_trans_gen r c d) (hab : refl_trans_gen r a b) (hac : refl_trans_gen r a c) : join (refl_trans_gen r) b c := sorry

theorem join_of_single {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} (h : reflexive r) (hab : r a b) : join r a b :=
  Exists.intro b { left := hab, right := h b }

theorem symmetric_join {α : Type u_1} {r : α → α → Prop} : symmetric (join r) := sorry

theorem reflexive_join {α : Type u_1} {r : α → α → Prop} (h : reflexive r) : reflexive (join r) :=
  fun (a : α) => Exists.intro a { left := h a, right := h a }

theorem transitive_join {α : Type u_1} {r : α → α → Prop} (ht : transitive r) (h : ∀ (a b c : α), r a b → r a c → join r b c) : transitive (join r) := sorry

theorem equivalence_join {α : Type u_1} {r : α → α → Prop} (hr : reflexive r) (ht : transitive r) (h : ∀ (a b c : α), r a b → r a c → join r b c) : equivalence (join r) :=
  { left := reflexive_join hr, right := { left := symmetric_join, right := transitive_join ht h } }

theorem equivalence_join_refl_trans_gen {α : Type u_1} {r : α → α → Prop} (h : ∀ (a b c : α), r a b → r a c → ∃ (d : α), refl_gen r b d ∧ refl_trans_gen r c d) : equivalence (join (refl_trans_gen r)) :=
  equivalence_join reflexive_refl_trans_gen transitive_refl_trans_gen fun (a b c : α) => church_rosser h

theorem join_of_equivalence {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {r' : α → α → Prop} (hr : equivalence r) (h : ∀ (a b : α), r' a b → r a b) : join r' a b → r a b := sorry

theorem refl_trans_gen_of_transitive_reflexive {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {r' : α → α → Prop} (hr : reflexive r) (ht : transitive r) (h : ∀ (a b : α), r' a b → r a b) (h' : refl_trans_gen r' a b) : r a b :=
  refl_trans_gen.drec (hr a)
    (fun {b c : α} (hab : refl_trans_gen r' a b) (hbc : r' b c) (ih : r a b) => ht ih (h b c hbc)) h'

theorem refl_trans_gen_of_equivalence {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} {r' : α → α → Prop} (hr : equivalence r) : (∀ (a b : α), r' a b → r a b) → refl_trans_gen r' a b → r a b :=
  refl_trans_gen_of_transitive_reflexive (and.left hr) (and.right (and.right hr))

theorem eqv_gen_iff_of_equivalence {α : Type u_1} {r : α → α → Prop} {a : α} {b : α} (h : equivalence r) : eqv_gen r a b ↔ r a b := sorry

theorem eqv_gen_mono {α : Type u_1} {a : α} {b : α} {r : α → α → Prop} {p : α → α → Prop} (hrp : ∀ (a b : α), r a b → p a b) (h : eqv_gen r a b) : eqv_gen p a b := sorry

