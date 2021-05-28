/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Zorn's lemmas.

Ported from Isabelle/HOL (written by Jacques D. Fleuriot, Tobias Nipkow, and Christian Sternagel).
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.lattice
import PostPort

universes u u_1 u_2 

namespace Mathlib

namespace zorn


/-- A chain is a subset `c` satisfying
  `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ c`. -/
def chain {α : Type u} (r : α → α → Prop) (c : set α)  :=
  set.pairwise_on c fun (x y : α) => r x y ∨ r y x

theorem chain.total_of_refl {α : Type u} {r : α → α → Prop} [is_refl α r] {c : set α} (H : chain r c) {x : α} {y : α} (hx : x ∈ c) (hy : y ∈ c) : r x y ∨ r y x :=
  dite (x = y) (fun (e : x = y) => Or.inl (e ▸ refl x)) fun (e : ¬x = y) => H x hx y hy e

theorem chain.mono {α : Type u} {r : α → α → Prop} {c : set α} {c' : set α} : c' ⊆ c → chain r c → chain r c' :=
  set.pairwise_on.mono

theorem chain.directed_on {α : Type u} {r : α → α → Prop} [is_refl α r] {c : set α} (H : chain r c) : directed_on r c := sorry

theorem chain_insert {α : Type u} {r : α → α → Prop} {c : set α} {a : α} (hc : chain r c) (ha : ∀ (b : α), b ∈ c → b ≠ a → r a b ∨ r b a) : chain r (insert a c) := sorry

/-- `super_chain c₁ c₂` means that `c₂ is a chain that strictly includes `c₁`. -/
def super_chain {α : Type u} {r : α → α → Prop} (c₁ : set α) (c₂ : set α)  :=
  chain r c₂ ∧ c₁ ⊂ c₂

/-- A chain `c` is a maximal chain if there does not exists a chain strictly including `c`. -/
def is_max_chain {α : Type u} {r : α → α → Prop} (c : set α)  :=
  chain r c ∧ ¬∃ (c' : set α), super_chain c c'

/-- Given a set `c`, if there exists a chain `c'` strictly including `c`, then `succ_chain c`
is one of these chains. Otherwise it is `c`. -/
def succ_chain {α : Type u} {r : α → α → Prop} (c : set α) : set α :=
  dite (∃ (c' : set α), chain r c ∧ super_chain c c')
    (fun (h : ∃ (c' : set α), chain r c ∧ super_chain c c') => classical.some h)
    fun (h : ¬∃ (c' : set α), chain r c ∧ super_chain c c') => c

theorem succ_spec {α : Type u} {r : α → α → Prop} {c : set α} (h : ∃ (c' : set α), chain r c ∧ super_chain c c') : super_chain c (succ_chain c) := sorry

theorem chain_succ {α : Type u} {r : α → α → Prop} {c : set α} (hc : chain r c) : chain r (succ_chain c) := sorry

theorem super_of_not_max {α : Type u} {r : α → α → Prop} {c : set α} (hc₁ : chain r c) (hc₂ : ¬is_max_chain c) : super_chain c (succ_chain c) := sorry

theorem succ_increasing {α : Type u} {r : α → α → Prop} {c : set α} : c ⊆ succ_chain c := sorry

/-- Set of sets reachable from `∅` using `succ_chain` and `⋃₀`. -/
inductive chain_closure {α : Type u} {r : α → α → Prop} : set α → Prop
where
| succ : ∀ {s : set α}, chain_closure s → chain_closure (succ_chain s)
| union : ∀ {s : set (set α)}, (∀ (a : set α), a ∈ s → chain_closure a) → chain_closure (⋃₀s)

theorem chain_closure_empty {α : Type u} {r : α → α → Prop} : chain_closure ∅ := sorry

theorem chain_closure_closure {α : Type u} {r : α → α → Prop} : chain_closure (⋃₀chain_closure) :=
  chain_closure.union fun (s : set α) (hs : s ∈ chain_closure) => hs

theorem chain_closure_total {α : Type u} {r : α → α → Prop} {c₁ : set α} {c₂ : set α} (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
  (fun (this : c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁) =>
      or.imp_right (fun (this : succ_chain c₂ ⊆ c₁) => set.subset.trans succ_increasing this) this)
    (chain_closure_succ_total_aux hc₁ hc₂ fun (c₃ : set α) (hc₃ : chain_closure c₃) => chain_closure_succ_total hc₃ hc₂)

theorem chain_closure_succ_fixpoint {α : Type u} {r : α → α → Prop} {c₁ : set α} {c₂ : set α} (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) (h_eq : succ_chain c₂ = c₂) : c₁ ⊆ c₂ := sorry

theorem chain_closure_succ_fixpoint_iff {α : Type u} {r : α → α → Prop} {c : set α} (hc : chain_closure c) : succ_chain c = c ↔ c = ⋃₀chain_closure := sorry

theorem chain_chain_closure {α : Type u} {r : α → α → Prop} {c : set α} (hc : chain_closure c) : chain r c := sorry

/-- `max_chain` is the union of all sets in the chain closure. -/
def max_chain {α : Type u} {r : α → α → Prop} : set α :=
  ⋃₀chain_closure

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec {α : Type u} {r : α → α → Prop} : is_max_chain max_chain := sorry

/-- Zorn's lemma

If every chain has an upper bound, then there is a maximal element -/
theorem exists_maximal_of_chains_bounded {α : Type u} {r : α → α → Prop} (h : ∀ (c : set α), chain r c → ∃ (ub : α), ∀ (a : α), a ∈ c → r a ub) (trans : ∀ {a b c : α}, r a b → r b c → r a c) : ∃ (m : α), ∀ (a : α), r m a → r a m := sorry

theorem zorn_partial_order {α : Type u} [partial_order α] (h : ∀ (c : set α), chain LessEq c → ∃ (ub : α), ∀ (a : α), a ∈ c → a ≤ ub) : ∃ (m : α), ∀ (a : α), m ≤ a → a = m := sorry

theorem zorn_partial_order₀ {α : Type u} [partial_order α] (s : set α) (ih : ∀ (c : set α) (H : c ⊆ s), chain LessEq c → ∀ (y : α) (H : y ∈ c), ∃ (ub : α), ∃ (H : ub ∈ s), ∀ (z : α), z ∈ c → z ≤ ub) (x : α) (hxs : x ∈ s) : ∃ (m : α), ∃ (H : m ∈ s), x ≤ m ∧ ∀ (z : α), z ∈ s → m ≤ z → z = m := sorry

theorem zorn_subset {α : Type u} (S : set (set α)) (h : ∀ (c : set (set α)) (H : c ⊆ S),
  chain has_subset.subset c → ∃ (ub : set α), ∃ (H : ub ∈ S), ∀ (s : set α), s ∈ c → s ⊆ ub) : ∃ (m : set α), ∃ (H : m ∈ S), ∀ (a : set α), a ∈ S → m ⊆ a → a = m := sorry

theorem zorn_subset₀ {α : Type u} (S : set (set α)) (H : ∀ (c : set (set α)) (H : c ⊆ S),
  chain has_subset.subset c → set.nonempty c → ∃ (ub : set α), ∃ (H : ub ∈ S), ∀ (s : set α), s ∈ c → s ⊆ ub) (x : set α) (hx : x ∈ S) : ∃ (m : set α), ∃ (H : m ∈ S), x ⊆ m ∧ ∀ (a : set α), a ∈ S → m ⊆ a → a = m := sorry

theorem chain.total {α : Type u} [preorder α] {c : set α} (H : chain LessEq c) {x : α} {y : α} : x ∈ c → y ∈ c → x ≤ y ∨ y ≤ x :=
  chain.total_of_refl H

theorem chain.image {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) (f : α → β) (h : ∀ (x y : α), r x y → s (f x) (f y)) {c : set α} (hrc : chain r c) : chain s (f '' c) := sorry

end zorn


theorem directed_of_chain {α : Type u_1} {β : Type u_2} {r : β → β → Prop} [is_refl β r] {f : α → β} {c : set α} (h : zorn.chain (f ⁻¹'o r) c) : directed r fun (x : Subtype fun (a : α) => a ∈ c) => f ↑x := sorry

