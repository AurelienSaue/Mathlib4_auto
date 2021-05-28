/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Disjointed sets
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.lattice
import Mathlib.tactic.wlog
import PostPort

universes u_1 u v 

namespace Mathlib

/-- A relation `p` holds pairwise if `p i j` for all `i ≠ j`. -/
def pairwise {α : Type u_1} (p : α → α → Prop)  :=
  ∀ (i j : α), i ≠ j → p i j

theorem set.pairwise_on_univ {α : Type u} {r : α → α → Prop} : set.pairwise_on set.univ r ↔ pairwise r := sorry

theorem set.pairwise_on.on_injective {α : Type u} {β : Type v} {s : set α} {r : α → α → Prop} (hs : set.pairwise_on s r) {f : β → α} (hf : function.injective f) (hfs : ∀ (x : β), f x ∈ s) : pairwise (r on f) :=
  fun (i j : β) (hij : i ≠ j) => hs (f i) (hfs i) (f j) (hfs j) (function.injective.ne hf hij)

theorem pairwise.mono {α : Type u} {p : α → α → Prop} {q : α → α → Prop} (h : ∀ {i j : α}, p i j → q i j) (hp : pairwise p) : pairwise q :=
  fun (i j : α) (hij : i ≠ j) => h (hp i j hij)

theorem pairwise_on_bool {α : Type u} {r : α → α → Prop} (hr : symmetric r) {a : α} {b : α} : pairwise (r on fun (c : Bool) => cond c a b) ↔ r a b := sorry

theorem pairwise_disjoint_on_bool {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} : pairwise (disjoint on fun (c : Bool) => cond c a b) ↔ disjoint a b :=
  pairwise_on_bool disjoint.symm

theorem pairwise.pairwise_on {α : Type u} {p : α → α → Prop} (h : pairwise p) (s : set α) : set.pairwise_on s p :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) => h x y

theorem pairwise_disjoint_fiber {α : Type u} {β : Type v} (f : α → β) : pairwise (disjoint on fun (y : β) => f ⁻¹' singleton y) :=
  iff.mp set.pairwise_on_univ (set.pairwise_on_disjoint_fiber f set.univ)

namespace set


/-- If `f : ℕ → set α` is a sequence of sets, then `disjointed f` is
  the sequence formed with each set subtracted from the later ones
  in the sequence, to form a disjoint sequence. -/
def disjointed {α : Type u} (f : ℕ → set α) (n : ℕ) : set α :=
  f n ∩ Inter fun (i : ℕ) => Inter fun (H : i < n) => f iᶜ

theorem disjoint_disjointed {α : Type u} {f : ℕ → set α} : pairwise (disjoint on disjointed f) := sorry

theorem disjoint_disjointed' {α : Type u} {f : ℕ → set α} (i : ℕ) (j : ℕ) : i ≠ j → disjointed f i ∩ disjointed f j = ∅ :=
  fun (hij : i ≠ j) => iff.mp disjoint_iff (disjoint_disjointed i j hij)

theorem disjointed_subset {α : Type u} {f : ℕ → set α} {n : ℕ} : disjointed f n ⊆ f n :=
  inter_subset_left (f n) (Inter fun (i : ℕ) => Inter fun (H : i < n) => f iᶜ)

theorem Union_lt_succ {α : Type u} {f : ℕ → set α} {n : ℕ} : (Union fun (i : ℕ) => Union fun (H : i < Nat.succ n) => f i) = f n ∪ Union fun (i : ℕ) => Union fun (H : i < n) => f i := sorry

theorem Inter_lt_succ {α : Type u} {f : ℕ → set α} {n : ℕ} : (Inter fun (i : ℕ) => Inter fun (H : i < Nat.succ n) => f i) = f n ∩ Inter fun (i : ℕ) => Inter fun (H : i < n) => f i := sorry

theorem subset_Union_disjointed {α : Type u} {f : ℕ → set α} {n : ℕ} : f n ⊆ Union fun (i : ℕ) => Union fun (H : i < Nat.succ n) => disjointed f i := sorry

theorem Union_disjointed {α : Type u} {f : ℕ → set α} : (Union fun (n : ℕ) => disjointed f n) = Union fun (n : ℕ) => f n := sorry

theorem disjointed_induct {α : Type u} {f : ℕ → set α} {n : ℕ} {p : set α → Prop} (h₁ : p (f n)) (h₂ : ∀ (t : set α) (i : ℕ), p t → p (t \ f i)) : p (disjointed f n) := sorry

theorem disjointed_of_mono {α : Type u} {f : ℕ → set α} {n : ℕ} (hf : monotone f) : disjointed f (n + 1) = f (n + 1) \ f n := sorry

theorem Union_disjointed_of_mono {α : Type u} {f : ℕ → set α} (hf : monotone f) (n : ℕ) : (Union fun (i : ℕ) => Union fun (H : i < Nat.succ n) => disjointed f i) = f n := sorry

