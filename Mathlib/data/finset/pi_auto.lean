/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.basic
import Mathlib.data.multiset.pi
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# The cartesian product of finsets
-/

namespace finset


/-! ### pi -/

/-- The empty dependent product function, defined on the empty set. The assumption `a ∈ ∅` is never
satisfied. -/
def pi.empty {α : Type u_1} (β : α → Type u_2) (a : α) (h : a ∈ ∅) : β a := multiset.pi.empty β a h

/-- Given a finset `s` of `α` and for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `s.pi t` of all functions defined on elements of `s` taking values in `t a` for `a ∈ s`.
Note that the elements of `s.pi t` are only partially defined, on `s`. -/
def pi {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] (s : finset α)
    (t : (a : α) → finset (δ a)) : finset ((a : α) → a ∈ s → δ a) :=
  mk (multiset.pi (val s) fun (a : α) => val (t a)) sorry

@[simp] theorem pi_val {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] (s : finset α)
    (t : (a : α) → finset (δ a)) : val (pi s t) = multiset.pi (val s) fun (a : α) => val (t a) :=
  rfl

@[simp] theorem mem_pi {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] {s : finset α}
    {t : (a : α) → finset (δ a)} {f : (a : α) → a ∈ s → δ a} :
    f ∈ pi s t ↔ ∀ (a : α) (h : a ∈ s), f a h ∈ t a :=
  multiset.mem_pi (val s) (fun (a : α) => (fun (a : α) => val (t a)) a) f

/-- Given a function `f` defined on a finset `s`, define a new function on the finset `s ∪ {a}`,
equal to `f` on `s` and sending `a` to a given value `b`. This function is denoted
`s.pi.cons a b f`. If `a` already belongs to `s`, the new function takes the value `b` at `a`
anyway. -/
def pi.cons {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] (s : finset α) (a : α) (b : δ a)
    (f : (a : α) → a ∈ s → δ a) (a' : α) (h : a' ∈ insert a s) : δ a' :=
  multiset.pi.cons (val s) a b f a' sorry

@[simp] theorem pi.cons_same {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] (s : finset α)
    (a : α) (b : δ a) (f : (a : α) → a ∈ s → δ a) (h : a ∈ insert a s) : pi.cons s a b f a h = b :=
  multiset.pi.cons_same (pi.cons._proof_1 s a a h)

theorem pi.cons_ne {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] {s : finset α} {a : α} {a' : α}
    {b : δ a} {f : (a : α) → a ∈ s → δ a} {h : a' ∈ insert a s} (ha : a ≠ a') :
    pi.cons s a b f a' h = f a' (or.resolve_left (iff.mp mem_insert h) (ne.symm ha)) :=
  multiset.pi.cons_ne (pi.cons._proof_1 s a a' h) (ne.symm ha)

theorem pi_cons_injective {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] {a : α} {b : δ a}
    {s : finset α} (hs : ¬a ∈ s) : function.injective (pi.cons s a b) :=
  sorry

@[simp] theorem pi_empty {α : Type u_1} {δ : α → Type u_2} [DecidableEq α]
    {t : (a : α) → finset (δ a)} : pi ∅ t = singleton (pi.empty δ) :=
  rfl

@[simp] theorem pi_insert {α : Type u_1} {δ : α → Type u_2} [DecidableEq α]
    [(a : α) → DecidableEq (δ a)] {s : finset α} {t : (a : α) → finset (δ a)} {a : α}
    (ha : ¬a ∈ s) :
    pi (insert a s) t = finset.bUnion (t a) fun (b : δ a) => image (pi.cons s a b) (pi s t) :=
  sorry

theorem pi_singletons {α : Type u_1} [DecidableEq α] {β : Type u_2} (s : finset α) (f : α → β) :
    (pi s fun (a : α) => singleton (f a)) = singleton fun (a : α) (_x : a ∈ s) => f a :=
  sorry

theorem pi_const_singleton {α : Type u_1} [DecidableEq α] {β : Type u_2} (s : finset α) (i : β) :
    (pi s fun (_x : α) => singleton i) = singleton fun (_x : α) (_x : _x ∈ s) => i :=
  pi_singletons s fun (_x : α) => i

theorem pi_subset {α : Type u_1} {δ : α → Type u_2} [DecidableEq α] {s : finset α}
    (t₁ : (a : α) → finset (δ a)) (t₂ : (a : α) → finset (δ a))
    (h : ∀ (a : α), a ∈ s → t₁ a ⊆ t₂ a) : pi s t₁ ⊆ pi s t₂ :=
  fun (g : (a : α) → a ∈ s → δ a) (hg : g ∈ pi s t₁) =>
    iff.mpr mem_pi fun (a : α) (ha : a ∈ s) => h a ha (iff.mp mem_pi hg a ha)

theorem pi_disjoint_of_disjoint {α : Type u_1} [DecidableEq α] {δ : α → Type u_2}
    [(a : α) → DecidableEq (δ a)] {s : finset α} [DecidableEq ((a : α) → a ∈ s → δ a)]
    (t₁ : (a : α) → finset (δ a)) (t₂ : (a : α) → finset (δ a)) {a : α} (ha : a ∈ s)
    (h : disjoint (t₁ a) (t₂ a)) : disjoint (pi s t₁) (pi s t₂) :=
  sorry

end Mathlib