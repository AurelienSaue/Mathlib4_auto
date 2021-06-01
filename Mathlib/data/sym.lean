/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.basic
import Mathlib.data.vector2
import Mathlib.tactic.tidy
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym2`.

TODO: This was created as supporting material for `data.sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

/--
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def sym (α : Type u) (n : ℕ) :=
  Subtype fun (s : multiset α) => coe_fn multiset.card s = n

/--
This is the `list.perm` setoid lifted to `vector`.
-/
def vector.perm.is_setoid (α : Type u) (n : ℕ) : setoid (vector α n) :=
  setoid.mk (fun (a b : vector α n) => subtype.val a ~ subtype.val b) sorry

namespace sym


/--
This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
def of_vector {α : Type u} {n : ℕ} (x : vector α n) : sym α n :=
  { val := ↑(subtype.val x), property := sorry }

protected instance has_lift {α : Type u} {n : ℕ} : has_lift (vector α n) (sym α n) :=
  has_lift.mk of_vector

/--
The unique element in `sym α 0`.
-/
def nil {α : Type u} : sym α 0 :=
  { val := 0, property := sorry }

/--
Inserts an element into the term of `sym α n`, increasing the length by one.
-/
def cons {α : Type u} {n : ℕ} : α → sym α n → sym α (Nat.succ n) :=
  sorry

infixr:67 " :: " => Mathlib.sym.cons

@[simp] theorem cons_inj_right {α : Type u} {n : ℕ} (a : α) (s : sym α n) (s' : sym α n) : a :: s = a :: s' ↔ s = s' := sorry

@[simp] theorem cons_inj_left {α : Type u} {n : ℕ} (a : α) (a' : α) (s : sym α n) : a :: s = a' :: s ↔ a = a' := sorry

theorem cons_swap {α : Type u} {n : ℕ} (a : α) (b : α) (s : sym α n) : a :: b :: s = b :: a :: s := sorry

/--
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
def mem {α : Type u} {n : ℕ} (a : α) (s : sym α n) :=
  a ∈ subtype.val s

protected instance has_mem {α : Type u} {n : ℕ} : has_mem α (sym α n) :=
  has_mem.mk mem

protected instance decidable_mem {α : Type u} {n : ℕ} [DecidableEq α] (a : α) (s : sym α n) : Decidable (a ∈ s) :=
  subtype.cases_on s
    fun (s_val : multiset α) (s_property : coe_fn multiset.card s_val = n) => id (multiset.decidable_mem a s_val)

@[simp] theorem mem_cons {α : Type u} {n : ℕ} {a : α} {b : α} {s : sym α n} : a ∈ b :: s ↔ a = b ∨ a ∈ s := sorry

theorem mem_cons_of_mem {α : Type u} {n : ℕ} {a : α} {b : α} {s : sym α n} (h : a ∈ s) : a ∈ b :: s :=
  iff.mpr mem_cons (Or.inr h)

@[simp] theorem mem_cons_self {α : Type u} {n : ℕ} (a : α) (s : sym α n) : a ∈ a :: s :=
  iff.mpr mem_cons (Or.inl rfl)

theorem cons_of_coe_eq {α : Type u} {n : ℕ} (a : α) (v : vector α n) : a :: ↑v = ↑(a::ᵥv) := sorry

theorem sound {α : Type u} {n : ℕ} {a : vector α n} {b : vector α n} (h : subtype.val a ~ subtype.val b) : ↑a = ↑b := sorry

/--
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type u) (n : ℕ) :=
  quotient (vector.perm.is_setoid α n)

/--
This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type u} {n : ℕ} : α → sym' α n → sym' α (Nat.succ n) :=
  fun (a : α) => quotient.map (vector.cons a) sorry

infixr:67 " :: " => Mathlib.sym.cons'

/--
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' {α : Type u} {n : ℕ} : sym α n ≃ sym' α n :=
  equiv.subtype_quotient_equiv_quotient_subtype (fun (l : List α) => list.length l = n)
    (fun (s : multiset α) => coe_fn multiset.card s = n) sorry sorry

theorem cons_equiv_eq_equiv_cons (α : Type u) (n : ℕ) (a : α) (s : sym α n) : a :: coe_fn sym_equiv_sym' s = coe_fn sym_equiv_sym' (a :: s) := sorry

-- Instances to make the linter happy

protected instance inhabited_sym {α : Type u} [Inhabited α] (n : ℕ) : Inhabited (sym α n) :=
  { default := { val := multiset.repeat Inhabited.default n, property := sorry } }

protected instance inhabited_sym' {α : Type u} [Inhabited α] (n : ℕ) : Inhabited (sym' α n) :=
  { default := quotient.mk' (vector.repeat Inhabited.default n) }

