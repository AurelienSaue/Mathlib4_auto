/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.data.nat.default
import Lean3Lib.init.data.bool.default
import Lean3Lib.init.ite_simp
import PostPort

universes u l u_1 w v 

namespace Mathlib

/-- In the VM, d_array is implemented as a persistent array. -/
structure d_array (n : ℕ) (α : fin n → Type u) 
where
  data : (i : fin n) → α i

namespace d_array


/-- The empty array. -/
def nil {α : fin 0 → Type u_1} : d_array 0 α :=
  mk fun (_x : fin 0) => sorry

/-- `read a i` reads the `i`th member of `a`. Has builtin VM implementation. -/
def read {n : ℕ} {α : fin n → Type u} (a : d_array n α) (i : fin n) : α i :=
  data a i

/-- `write a i v` sets the `i`th member of `a` to be `v`. Has builtin VM implementation. -/
def write {n : ℕ} {α : fin n → Type u} (a : d_array n α) (i : fin n) (v : α i) : d_array n α :=
  mk fun (j : fin n) => dite (i = j) (fun (h : i = j) => eq.rec_on h v) fun (h : ¬i = j) => read a j

def iterate_aux {n : ℕ} {α : fin n → Type u} {β : Type w} (a : d_array n α) (f : (i : fin n) → α i → β → β) (i : ℕ) : i ≤ n → β → β :=
  sorry

/-- Fold over the elements of the given array in ascending order. Has builtin VM implementation. -/
def iterate {n : ℕ} {α : fin n → Type u} {β : Type w} (a : d_array n α) (b : β) (f : (i : fin n) → α i → β → β) : β :=
  iterate_aux a f n sorry b

/-- Map the array. Has builtin VM implementation. -/
def foreach {n : ℕ} {α : fin n → Type u} {α' : fin n → Type v} (a : d_array n α) (f : (i : fin n) → α i → α' i) : d_array n α' :=
  mk fun (i : fin n) => f i (read a i)

def map {n : ℕ} {α : fin n → Type u} {α' : fin n → Type v} (f : (i : fin n) → α i → α' i) (a : d_array n α) : d_array n α' :=
  foreach a f

def map₂ {n : ℕ} {α : fin n → Type u} {α' : fin n → Type v} {α'' : fin n → Type w} (f : (i : fin n) → α i → α' i → α'' i) (a : d_array n α) (b : d_array n α') : d_array n α'' :=
  foreach b fun (i : fin n) => f i (read a i)

def foldl {n : ℕ} {α : fin n → Type u} {β : Type w} (a : d_array n α) (b : β) (f : (i : fin n) → α i → β → β) : β :=
  iterate a b f

def rev_iterate_aux {n : ℕ} {α : fin n → Type u} {β : Type w} (a : d_array n α) (f : (i : fin n) → α i → β → β) (i : ℕ) : i ≤ n → β → β :=
  sorry

def rev_iterate {n : ℕ} {α : fin n → Type u} {β : Type w} (a : d_array n α) (b : β) (f : (i : fin n) → α i → β → β) : β :=
  rev_iterate_aux a f n sorry b

@[simp] theorem read_write {n : ℕ} {α : fin n → Type u} (a : d_array n α) (i : fin n) (v : α i) : read (write a i v) i = v := sorry

@[simp] theorem read_write_of_ne {n : ℕ} {α : fin n → Type u} (a : d_array n α) {i : fin n} {j : fin n} (v : α i) : i ≠ j → read (write a i v) j = read a j := sorry

protected theorem ext {n : ℕ} {α : fin n → Type u} {a : d_array n α} {b : d_array n α} (h : ∀ (i : fin n), read a i = read b i) : a = b := sorry

protected theorem ext' {n : ℕ} {α : fin n → Type u} {a : d_array n α} {b : d_array n α} (h : ∀ (i : ℕ) (h : i < n), read a { val := i, property := h } = read b { val := i, property := h }) : a = b := sorry

protected def beq_aux {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] (a : d_array n α) (b : d_array n α) (i : ℕ) : i ≤ n → Bool :=
  sorry

/-- Boolean element-wise equality check. -/
protected def beq {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] (a : d_array n α) (b : d_array n α) : Bool :=
  d_array.beq_aux a b n sorry

theorem of_beq_aux_eq_tt {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] {a : d_array n α} {b : d_array n α} (i : ℕ) (h : i ≤ n) : d_array.beq_aux a b i h = tt →
  ∀ (j : ℕ) (h' : j < i),
    read a { val := j, property := lt_of_lt_of_le h' h } = read b { val := j, property := lt_of_lt_of_le h' h } := sorry

theorem of_beq_eq_tt {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] {a : d_array n α} {b : d_array n α} : d_array.beq a b = tt → a = b := sorry

theorem of_beq_aux_eq_ff {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] {a : d_array n α} {b : d_array n α} (i : ℕ) (h : i ≤ n) : d_array.beq_aux a b i h = false →
  ∃ (j : ℕ),
    ∃ (h' : j < i),
      read a { val := j, property := lt_of_lt_of_le h' h } ≠ read b { val := j, property := lt_of_lt_of_le h' h } := sorry

theorem of_beq_eq_ff {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] {a : d_array n α} {b : d_array n α} : d_array.beq a b = false → a ≠ b := sorry

protected instance decidable_eq {n : ℕ} {α : fin n → Type u} [(i : fin n) → DecidableEq (α i)] : DecidableEq (d_array n α) :=
  fun (a b : d_array n α) =>
    dite (d_array.beq a b = tt) (fun (h : d_array.beq a b = tt) => is_true sorry)
      fun (h : ¬d_array.beq a b = tt) => isFalse sorry

end d_array


/-- A non-dependent array (see `d_array`). Implemented in the VM as a persistent array.  -/
def array (n : ℕ) (α : Type u)  :=
  d_array n fun (_x : fin n) => α

/-- `mk_array n v` creates a new array of length `n` where each element is `v`. Has builtin VM implementation. -/
def mk_array {α : Type u_1} (n : ℕ) (v : α) : array n α :=
  d_array.mk fun (_x : fin n) => v

namespace array


def nil {α : Type u_1} : array 0 α :=
  d_array.nil

def read {n : ℕ} {α : Type u} (a : array n α) (i : fin n) : α :=
  d_array.read a i

def write {n : ℕ} {α : Type u} (a : array n α) (i : fin n) (v : α) : array n α :=
  d_array.write a i v

/-- Fold array starting from 0, folder function includes an index argument. -/
def iterate {n : ℕ} {α : Type u} {β : Type v} (a : array n α) (b : β) (f : fin n → α → β → β) : β :=
  d_array.iterate a b f

/-- Map each element of the given array with an index argument. -/
def foreach {n : ℕ} {α : Type u} {β : Type v} (a : array n α) (f : fin n → α → β) : array n β :=
  d_array.foreach a f

def map₂ {n : ℕ} {α : Type u} (f : α → α → α) (a : array n α) (b : array n α) : array n α :=
  foreach b fun (i : fin n) => f (read a i)

def foldl {n : ℕ} {α : Type u} {β : Type v} (a : array n α) (b : β) (f : α → β → β) : β :=
  iterate a b fun (_x : fin n) => f

def rev_list {n : ℕ} {α : Type u} (a : array n α) : List α :=
  foldl a [] fun (_x : α) (_y : List α) => _x :: _y

def rev_iterate {n : ℕ} {α : Type u} {β : Type v} (a : array n α) (b : β) (f : fin n → α → β → β) : β :=
  d_array.rev_iterate a b f

def rev_foldl {n : ℕ} {α : Type u} {β : Type v} (a : array n α) (b : β) (f : α → β → β) : β :=
  rev_iterate a b fun (_x : fin n) => f

def to_list {n : ℕ} {α : Type u} (a : array n α) : List α :=
  rev_foldl a [] fun (_x : α) (_y : List α) => _x :: _y

theorem push_back_idx {j : ℕ} {n : ℕ} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
  nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂

/-- `push_back a v` pushes value `v` to the end of the array. Has builtin VM implementation. -/
def push_back {n : ℕ} {α : Type u} (a : array n α) (v : α) : array (n + 1) α :=
  d_array.mk fun (_x : fin (n + 1)) => sorry

theorem pop_back_idx {j : ℕ} {n : ℕ} (h : j < n) : j < n + 1 :=
  nat.lt.step h

/-- Discard _last_ element in the array. Has builtin VM implementation. -/
def pop_back {n : ℕ} {α : Type u} (a : array (n + 1) α) : array n α :=
  d_array.mk fun (_x : fin n) => sorry

/-- Auxilliary function for monadically mapping a function over an array. -/
def mmap_core {n : ℕ} {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (a : array n α) (f : α → m β) (i : ℕ) (H : i ≤ n) : m (array i β) :=
  sorry

/-- Monadically map a function over the array. -/
def mmap {n : ℕ} {α : Type u} {β : Type v} {m : Type v → Type u_1} [Monad m] (a : array n α) (f : α → m β) : m (array n β) :=
  mmap_core a f n sorry

/-- Map a function over the array. -/
def map {n : ℕ} {α : Type u} {β : Type v} (a : array n α) (f : α → β) : array n β :=
  d_array.map (fun (_x : fin n) => f) a

protected def mem {n : ℕ} {α : Type u} (v : α) (a : array n α)  :=
  ∃ (i : fin n), read a i = v

protected instance has_mem {n : ℕ} {α : Type u} : has_mem α (array n α) :=
  has_mem.mk array.mem

theorem read_mem {n : ℕ} {α : Type u} (a : array n α) (i : fin n) : read a i ∈ a :=
  exists.intro i rfl

protected instance has_repr {n : ℕ} {α : Type u} [has_repr α] : has_repr (array n α) :=
  has_repr.mk (repr ∘ to_list)

@[simp] theorem read_write {n : ℕ} {α : Type u} (a : array n α) (i : fin n) (v : α) : read (write a i v) i = v :=
  d_array.read_write a i v

@[simp] theorem read_write_of_ne {n : ℕ} {α : Type u} (a : array n α) {i : fin n} {j : fin n} (v : α) : i ≠ j → read (write a i v) j = read a j :=
  d_array.read_write_of_ne a v

def read' {n : ℕ} {β : Type v} [Inhabited β] (a : array n β) (i : ℕ) : β :=
  dite (i < n) (fun (h : i < n) => read a { val := i, property := h }) fun (h : ¬i < n) => Inhabited.default

def write' {n : ℕ} {α : Type u} (a : array n α) (i : ℕ) (v : α) : array n α :=
  dite (i < n) (fun (h : i < n) => write a { val := i, property := h } v) fun (h : ¬i < n) => a

theorem read_eq_read' {n : ℕ} {α : Type u} [Inhabited α] (a : array n α) {i : ℕ} (h : i < n) : read a { val := i, property := h } = read' a i := sorry

theorem write_eq_write' {n : ℕ} {α : Type u} (a : array n α) {i : ℕ} (h : i < n) (v : α) : write a { val := i, property := h } v = write' a i v := sorry

protected theorem ext {n : ℕ} {α : Type u} {a : array n α} {b : array n α} (h : ∀ (i : fin n), read a i = read b i) : a = b :=
  d_array.ext h

protected theorem ext' {n : ℕ} {α : Type u} {a : array n α} {b : array n α} (h : ∀ (i : ℕ) (h : i < n), read a { val := i, property := h } = read b { val := i, property := h }) : a = b :=
  d_array.ext' h

protected instance decidable_eq {n : ℕ} {α : Type u} [DecidableEq α] : DecidableEq (array n α) :=
  eq.mpr sorry fun (a b : d_array n fun (_x : fin n) => α) => d_array.decidable_eq a b

