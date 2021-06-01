/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

Tuples are lists of a fixed size.
It is implemented as a subtype.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.list.default
import Mathlib.Lean3Lib.init.data.subtype.default
import Mathlib.Lean3Lib.init.meta.interactive
import Mathlib.Lean3Lib.init.data.fin.default
 

universes u u_1 v w 

namespace Mathlib

def vector (α : Type u) (n : ℕ)  :=
  Subtype fun (l : List α) => list.length l = n

namespace vector


protected instance decidable_eq {α : Type u} {n : ℕ} [DecidableEq α] : DecidableEq (vector α n) :=
  eq.mpr sorry fun (a b : Subtype fun (l : List α) => list.length l = n) => subtype.decidable_eq a b

def nil {α : Type u} : vector α 0 :=
  { val := [], property := sorry }

def cons {α : Type u} {n : ℕ} : α → vector α n → vector α (Nat.succ n) :=
  sorry

def length {α : Type u} {n : ℕ} (v : vector α n) : ℕ :=
  n

def head {α : Type u} {n : ℕ} : vector α (Nat.succ n) → α :=
  sorry

theorem head_cons {α : Type u} {n : ℕ} (a : α) (v : vector α n) : head (cons a v) = a := sorry

def tail {α : Type u} {n : ℕ} : vector α n → vector α (n - 1) :=
  sorry

theorem tail_cons {α : Type u} {n : ℕ} (a : α) (v : vector α n) : tail (cons a v) = v := sorry

@[simp] theorem cons_head_tail {α : Type u} {n : ℕ} (v : vector α (Nat.succ n)) : cons (head v) (tail v) = v := sorry

def to_list {α : Type u} {n : ℕ} (v : vector α n) : List α :=
  subtype.val v

def nth {α : Type u} {n : ℕ} (v : vector α n) : fin n → α :=
  sorry

def append {α : Type u} {n : ℕ} {m : ℕ} : vector α n → vector α m → vector α (n + m) :=
  sorry

def elim {α : Type u_1} {C : {n : ℕ} → vector α n → Sort u} (H : (l : List α) → C { val := l, property := elim._proof_1 l }) {n : ℕ} (v : vector α n) : C v :=
  sorry

/- map -/

def map {α : Type u} {β : Type v} {n : ℕ} (f : α → β) : vector α n → vector β n :=
  sorry

@[simp] theorem map_nil {α : Type u} {β : Type v} (f : α → β) : map f nil = nil :=
  rfl

theorem map_cons {α : Type u} {β : Type v} {n : ℕ} (f : α → β) (a : α) (v : vector α n) : map f (cons a v) = cons (f a) (map f v) := sorry

def map₂ {α : Type u} {β : Type v} {φ : Type w} {n : ℕ} (f : α → β → φ) : vector α n → vector β n → vector φ n :=
  sorry

def repeat {α : Type u} (a : α) (n : ℕ) : vector α n :=
  { val := list.repeat a n, property := list.length_repeat a n }

def drop {α : Type u} {n : ℕ} (i : ℕ) : vector α n → vector α (n - i) :=
  sorry

def take {α : Type u} {n : ℕ} (i : ℕ) : vector α n → vector α (min i n) :=
  sorry

def remove_nth {α : Type u} {n : ℕ} (i : fin n) : vector α n → vector α (n - 1) :=
  sorry

def of_fn {α : Type u} {n : ℕ} : (fin n → α) → vector α n :=
  sorry

def map_accumr {α : Type u} {β : Type v} {n : ℕ} {σ : Type} (f : α → σ → σ × β) : vector α n → σ → σ × vector β n :=
  sorry

def map_accumr₂ {n : ℕ} {α : Type} {β : Type} {σ : Type} {φ : Type} (f : α → β → σ → σ × φ) : vector α n → vector β n → σ → σ × vector φ n :=
  sorry

protected theorem eq {α : Type u} {n : ℕ} (a1 : vector α n) (a2 : vector α n) : to_list a1 = to_list a2 → a1 = a2 := sorry

protected theorem eq_nil {α : Type u} (v : vector α 0) : v = nil :=
  vector.eq v nil (list.eq_nil_of_length_eq_zero (subtype.property v))

@[simp] theorem to_list_mk {α : Type u} {n : ℕ} (v : List α) (P : list.length v = n) : to_list { val := v, property := P } = v :=
  rfl

@[simp] theorem to_list_nil {α : Type u} : to_list nil = [] :=
  rfl

@[simp] theorem to_list_length {α : Type u} {n : ℕ} (v : vector α n) : list.length (to_list v) = n :=
  subtype.property v

@[simp] theorem to_list_cons {α : Type u} {n : ℕ} (a : α) (v : vector α n) : to_list (cons a v) = a :: to_list v :=
  subtype.cases_on v
    fun (v_val : List α) (v_property : list.length v_val = n) =>
      Eq.refl (to_list (cons a { val := v_val, property := v_property }))

@[simp] theorem to_list_append {α : Type u} {n : ℕ} {m : ℕ} (v : vector α n) (w : vector α m) : to_list (append v w) = to_list v ++ to_list w := sorry

@[simp] theorem to_list_drop {α : Type u} {n : ℕ} {m : ℕ} (v : vector α m) : to_list (drop n v) = list.drop n (to_list v) :=
  subtype.cases_on v
    fun (v_val : List α) (v_property : list.length v_val = m) =>
      Eq.refl (to_list (drop n { val := v_val, property := v_property }))

@[simp] theorem to_list_take {α : Type u} {n : ℕ} {m : ℕ} (v : vector α m) : to_list (take n v) = list.take n (to_list v) :=
  subtype.cases_on v
    fun (v_val : List α) (v_property : list.length v_val = m) =>
      Eq.refl (to_list (take n { val := v_val, property := v_property }))

