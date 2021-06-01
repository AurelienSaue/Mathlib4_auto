/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.finset.default
import Mathlib.data.fintype.basic
import Mathlib.algebra.geom_sum
import Mathlib.tactic.default
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Colex

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`finset ℕ` as the "binary" ordering. That is, order A based on
`∑_{i ∈ A} 2^i`.
It's defined here in a slightly more general way, requiring only `has_lt α` in
the definition of colex on `finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `colex_hom`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `forall_lt_of_colex_lt_of_forall_lt`: if A < B in colex, and everything
  in B is < t, then everything in A is < t. This confirms the idea that
  an enumeration under colex will exhaust all sets using elements < t before
  allowing t to be included.
* `binary_iff`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## Notation
We define `<` and `≤` to denote colex ordering, useful in particular when
multiple orderings are available in context.

## Tags
colex, colexicographic, binary

## References
* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Todo
Show the subset ordering is a sub-relation of the colex ordering.
-/

/--
We define this type synonym to refer to the colexicographic ordering on finsets
rather than the natural subset ordering.
-/
def finset.colex (α : Type u_1) := finset α

/--
A convenience constructor to turn a `finset α` into a `finset.colex α`, useful in order to
use the colex ordering rather than the subset ordering.
-/
def finset.to_colex {α : Type u_1} (s : finset α) : finset.colex α := s

@[simp] theorem colex.eq_iff {α : Type u_1} (A : finset α) (B : finset α) :
    finset.to_colex A = finset.to_colex B ↔ A = B :=
  iff.refl (finset.to_colex A = finset.to_colex B)

/--
`A` is less than `B` in the colex ordering if the largest thing that's not in both sets is in B.
In other words, max (A ▵ B) ∈ B (if the maximum exists).
-/
protected instance finset.colex.has_lt {α : Type u_1} [HasLess α] : HasLess (finset.colex α) :=
  { Less :=
      fun (A B : finset α) => ∃ (k : α), (∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)) ∧ ¬k ∈ A ∧ k ∈ B }

/-- We can define (≤) in the obvious way. -/
protected instance finset.colex.has_le {α : Type u_1} [HasLess α] : HasLessEq (finset.colex α) :=
  { LessEq := fun (A B : finset.colex α) => A < B ∨ A = B }

theorem colex.lt_def {α : Type u_1} [HasLess α] (A : finset α) (B : finset α) :
    finset.to_colex A < finset.to_colex B ↔
        ∃ (k : α), (∀ {x : α}, k < x → (x ∈ A ↔ x ∈ B)) ∧ ¬k ∈ A ∧ k ∈ B :=
  iff.rfl

theorem colex.le_def {α : Type u_1} [HasLess α] (A : finset α) (B : finset α) :
    finset.to_colex A ≤ finset.to_colex B ↔ finset.to_colex A < finset.to_colex B ∨ A = B :=
  iff.rfl

/-- If everything in A is less than k, we can bound the sum of powers. -/
theorem nat.sum_pow_two_lt {k : ℕ} {A : finset ℕ} (h₁ : ∀ {x : ℕ}, x ∈ A → x < k) :
    finset.sum A (pow (bit0 1)) < bit0 1 ^ k :=
  sorry

namespace colex


/-- Strictly monotone functions preserve the colex ordering. -/
theorem hom {α : Type u_1} {β : Type u_2} [linear_order α] [DecidableEq β] [preorder β] {f : α → β}
    (h₁ : strict_mono f) (A : finset α) (B : finset α) :
    finset.to_colex (finset.image f A) < finset.to_colex (finset.image f B) ↔
        finset.to_colex A < finset.to_colex B :=
  sorry

/-- A special case of `colex_hom` which is sometimes useful. -/
@[simp] theorem hom_fin {n : ℕ} (A : finset (fin n)) (B : finset (fin n)) :
    finset.to_colex (finset.image (fun (n_1 : fin n) => ↑n_1) A) <
          finset.to_colex (finset.image (fun (n_1 : fin n) => ↑n_1) B) ↔
        finset.to_colex A < finset.to_colex B :=
  hom (fun (x y : fin n) (k : x < y) => k) A B

protected instance has_lt.lt.is_irrefl {α : Type u_1} [HasLess α] :
    is_irrefl (finset.colex α) Less :=
  is_irrefl.mk
    fun (A : finset.colex α) (h : A < A) =>
      exists.elim h
        fun (_x : α) (_x : (∀ {x : α}, _x < x → (x ∈ A ↔ x ∈ A)) ∧ ¬_x ∈ A ∧ _x ∈ A) => sorry

theorem lt_trans {α : Type u_1} [linear_order α] {a : finset.colex α} {b : finset.colex α}
    {c : finset.colex α} : a < b → b < c → a < c :=
  sorry

theorem le_trans {α : Type u_1} [linear_order α] (a : finset.colex α) (b : finset.colex α)
    (c : finset.colex α) : a ≤ b → b ≤ c → a ≤ c :=
  fun (AB : a ≤ b) (BC : b ≤ c) =>
    or.elim AB
      (fun (k : a < b) =>
        or.elim BC (fun (t : b < c) => Or.inl (lt_trans k t)) fun (t : b = c) => t ▸ AB)
      fun (k : a = b) => Eq.symm k ▸ BC

protected instance has_lt.lt.is_trans {α : Type u_1} [linear_order α] :
    is_trans (finset.colex α) Less :=
  is_trans.mk fun (_x _x_1 _x_2 : finset.colex α) => lt_trans

protected instance has_lt.lt.is_asymm {α : Type u_1} [linear_order α] :
    is_asymm (finset.colex α) Less :=
  Mathlib.is_asymm_of_is_trans_of_is_irrefl

protected instance has_lt.lt.is_strict_order {α : Type u_1} [linear_order α] :
    is_strict_order (finset.colex α) Less :=
  is_strict_order.mk

theorem lt_trichotomy {α : Type u_1} [linear_order α] (A : finset.colex α) (B : finset.colex α) :
    A < B ∨ A = B ∨ B < A :=
  sorry

protected instance has_lt.lt.is_trichotomous {α : Type u_1} [linear_order α] :
    is_trichotomous (finset.colex α) Less :=
  is_trichotomous.mk lt_trichotomy

-- It should be possible to do this computably but it doesn't seem to make any difference for now.

protected instance finset.colex.linear_order {α : Type u_1} [linear_order α] :
    linear_order (finset.colex α) :=
  linear_order.mk LessEq (partial_order.lt._default LessEq) sorry le_trans sorry sorry
    (classical.dec_rel LessEq) Mathlib.decidable_eq_of_decidable_le
    Mathlib.decidable_lt_of_decidable_le

protected instance has_lt.lt.is_incomp_trans {α : Type u_1} [linear_order α] :
    is_incomp_trans (finset.colex α) Less :=
  is_incomp_trans.mk
    fun (A B C : finset.colex α) (ᾰ : ¬A < B ∧ ¬B < A) (ᾰ_1 : ¬B < C ∧ ¬C < B) =>
      and.dcases_on ᾰ
        fun (nAB : ¬A < B) (nBA : ¬B < A) =>
          and.dcases_on ᾰ_1
            fun (nBC : ¬B < C) (nCB : ¬C < B) =>
              eq.mpr
                (id
                  (Eq._oldrec (Eq.refl (¬A < C ∧ ¬C < A))
                    (or.resolve_right (or.resolve_left (lt_trichotomy A B) nAB) nBA)))
                (eq.mpr
                  (id
                    (Eq._oldrec (Eq.refl (¬B < C ∧ ¬C < B))
                      (or.resolve_right (or.resolve_left (lt_trichotomy B C) nBC) nCB)))
                  (eq.mpr
                    (id (Eq._oldrec (Eq.refl (¬C < C ∧ ¬C < C)) (propext (and_self (¬C < C)))))
                    (irrefl C)))

protected instance has_lt.lt.is_strict_weak_order {α : Type u_1} [linear_order α] :
    is_strict_weak_order (finset.colex α) Less :=
  is_strict_weak_order.mk

protected instance has_lt.lt.is_strict_total_order {α : Type u_1} [linear_order α] :
    is_strict_total_order (finset.colex α) Less :=
  is_strict_total_order.mk

/-- If {r} is less than or equal to s in the colexicographical sense,
  then s contains an element greater than or equal to r. -/
theorem mem_le_of_singleton_le {α : Type u_1} [linear_order α] {r : α} {s : finset α} :
    finset.to_colex (singleton r) ≤ finset.to_colex s → ∃ (x : α), ∃ (H : x ∈ s), r ≤ x :=
  sorry

/-- s.to_colex < finset.to_colex {r} iff all elements of s are less than r. -/
theorem lt_singleton_iff_mem_lt {α : Type u_1} [linear_order α] {r : α} {s : finset α} :
    finset.to_colex s < finset.to_colex (singleton r) ↔ ∀ (x : α), x ∈ s → x < r :=
  sorry

/-- Colex is an extension of the base ordering on α. -/
theorem singleton_lt_iff_lt {α : Type u_1} [linear_order α] {r : α} {s : α} :
    finset.to_colex (singleton r) < finset.to_colex (singleton s) ↔ r < s :=
  sorry

/--
If A is before B in colex, and everything in B is small, then everything in A is small.
-/
theorem forall_lt_of_colex_lt_of_forall_lt {α : Type u_1} [linear_order α] {A : finset α}
    {B : finset α} (t : α) (h₁ : finset.to_colex A < finset.to_colex B)
    (h₂ : ∀ (x : α), x ∈ B → x < t) (x : α) (H : x ∈ A) : x < t :=
  sorry

/-- Colex doesn't care if you remove the other set -/
@[simp] theorem sdiff_lt_sdiff_iff_lt {α : Type u_1} [HasLess α] [DecidableEq α] (A : finset α)
    (B : finset α) :
    finset.to_colex (A \ B) < finset.to_colex (B \ A) ↔ finset.to_colex A < finset.to_colex B :=
  sorry

/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
theorem sum_pow_two_lt_iff_lt (A : finset ℕ) (B : finset ℕ) :
    finset.sum A (pow (bit0 1)) < finset.sum B (pow (bit0 1)) ↔
        finset.to_colex A < finset.to_colex B :=
  sorry

end Mathlib