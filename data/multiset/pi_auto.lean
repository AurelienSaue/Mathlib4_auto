/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.multiset.nodup
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# The cartesian product of multisets
-/

namespace multiset


/-- Given `δ : α → Type*`, `pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
def pi.empty {α : Type u_1} (δ : α → Type u_2) (a : α) (H : a ∈ 0) : δ a :=
  sorry

/-- Given `δ : α → Type*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
def pi.cons {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (m : multiset α) (a : α) (b : δ a) (f : (a : α) → a ∈ m → δ a) (a' : α) (H : a' ∈ a ::ₘ m) : δ a' :=
  dite (a' = a) (fun (h : a' = a) => Eq._oldrec b (Eq.symm h)) fun (h : ¬a' = a) => f a' sorry

theorem pi.cons_same {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} {m : multiset α} {a : α} {b : δ a} {f : (a : α) → a ∈ m → δ a} (h : a ∈ a ::ₘ m) : pi.cons m a b f a h = b :=
  dif_pos rfl

theorem pi.cons_ne {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} {m : multiset α} {a : α} {a' : α} {b : δ a} {f : (a : α) → a ∈ m → δ a} (h' : a' ∈ a ::ₘ m) (h : a' ≠ a) : pi.cons m a b f a' h' = f a' (or.resolve_left (iff.mp mem_cons h') h) :=
  dif_neg h

theorem pi.cons_swap {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} {a : α} {a' : α} {b : δ a} {b' : δ a'} {m : multiset α} {f : (a : α) → a ∈ m → δ a} (h : a ≠ a') : pi.cons (a' ::ₘ m) a b (pi.cons m a' b' f) == pi.cons (a ::ₘ m) a' b' (pi.cons m a b f) := sorry

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
def pi {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (m : multiset α) (t : (a : α) → multiset (δ a)) : multiset ((a : α) → a ∈ m → δ a) :=
  multiset.rec_on m (singleton sorry)
    (fun (a : α) (m : multiset α) (p : multiset ((a : α) → a ∈ m → δ a)) => bind (t a) fun (b : δ a) => map sorry p) sorry

@[simp] theorem pi_zero {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (t : (a : α) → multiset (δ a)) : pi 0 t = pi.empty δ ::ₘ 0 :=
  rfl

@[simp] theorem pi_cons {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (m : multiset α) (t : (a : α) → multiset (δ a)) (a : α) : pi (a ::ₘ m) t = bind (t a) fun (b : δ a) => map (pi.cons m a b) (pi m t) :=
  rec_on_cons a m

theorem pi_cons_injective {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} {a : α} {b : δ a} {s : multiset α} (hs : ¬a ∈ s) : function.injective (pi.cons s a b) := sorry

theorem card_pi {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (m : multiset α) (t : (a : α) → multiset (δ a)) : coe_fn card (pi m t) = prod (map (fun (a : α) => coe_fn card (t a)) m) := sorry

theorem nodup_pi {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} {s : multiset α} {t : (a : α) → multiset (δ a)} : nodup s → (∀ (a : α), a ∈ s → nodup (t a)) → nodup (pi s t) := sorry

theorem mem_pi {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (m : multiset α) (t : (a : α) → multiset (δ a)) (f : (a : α) → a ∈ m → δ a) : f ∈ pi m t ↔ ∀ (a : α) (h : a ∈ m), f a h ∈ t a := sorry

