/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u w u_1 

namespace Mathlib

def buffer (α : Type u)  :=
  sigma fun (n : ℕ) => array n α

def mk_buffer {α : Type u} : buffer α :=
  sigma.mk 0 (d_array.mk fun (i : fin 0) => fin.elim0 i)

def array.to_buffer {α : Type u} {n : ℕ} (a : array n α) : buffer α :=
  sigma.mk n a

namespace buffer


def nil {α : Type u} : buffer α :=
  mk_buffer

def size {α : Type u} (b : buffer α) : ℕ :=
  sigma.fst b

def to_array {α : Type u} (b : buffer α) : array (size b) α :=
  sigma.snd b

def push_back {α : Type u} : buffer α → α → buffer α :=
  sorry

def pop_back {α : Type u} : buffer α → buffer α :=
  sorry

def read {α : Type u} (b : buffer α) : fin (size b) → α :=
  sorry

def write {α : Type u} (b : buffer α) : fin (size b) → α → buffer α :=
  sorry

def read' {α : Type u} [Inhabited α] : buffer α → ℕ → α :=
  sorry

def write' {α : Type u} : buffer α → ℕ → α → buffer α :=
  sorry

theorem read_eq_read' {α : Type u} [Inhabited α] (b : buffer α) (i : ℕ) (h : i < size b) : read b { val := i, property := h } = read' b i := sorry

theorem write_eq_write' {α : Type u} (b : buffer α) (i : ℕ) (h : i < size b) (v : α) : write b { val := i, property := h } v = write' b i v := sorry

def to_list {α : Type u} (b : buffer α) : List α :=
  array.to_list (to_array b)

protected def to_string (b : buffer char) : string :=
  list.as_string (array.to_list (to_array b))

def append_list {α : Type u} : buffer α → List α → buffer α :=
  sorry

def append_string (b : buffer char) (s : string) : buffer char :=
  append_list b (string.to_list s)

theorem lt_aux_1 {a : ℕ} {b : ℕ} {c : ℕ} (h : a + c < b) : a < b :=
  lt_of_le_of_lt (nat.le_add_right a c) h

theorem lt_aux_2 {n : ℕ} (h : n > 0) : n - 1 < n :=
  (fun (h₁ : 1 > 0) => nat.sub_lt h h₁) (of_as_true trivial)

theorem lt_aux_3 {n : ℕ} {i : ℕ} (h : i + 1 < n) : n - bit0 1 - i < n := sorry

def append_array {α : Type u} {n : ℕ} (nz : n > 0) : buffer α → array n α → (i : ℕ) → i < n → buffer α :=
  sorry

protected def append {α : Type u} : buffer α → buffer α → buffer α :=
  sorry

def iterate {α : Type u} {β : Type w} (b : buffer α) : β → (fin (size b) → α → β → β) → β :=
  sorry

def foreach {α : Type u} (b : buffer α) : (fin (size b) → α → α) → buffer α :=
  sorry

/-- Monadically map a function over the buffer. -/
def mmap {α : Type u} {β : Type w} {m : Type w → Type u_1} [Monad m] (b : buffer α) (f : α → m β) : m (buffer β) :=
  do 
    let b' ← array.mmap (sigma.snd b) f 
    return (array.to_buffer b')

/-- Map a function over the buffer. -/
def map {α : Type u} {β : Type w} : buffer α → (α → β) → buffer β :=
  sorry

def foldl {α : Type u} {β : Type w} : buffer α → β → (α → β → β) → β :=
  sorry

def rev_iterate {α : Type u} {β : Type w} (b : buffer α) : β → (fin (size b) → α → β → β) → β :=
  sorry

def take {α : Type u} (b : buffer α) (n : ℕ) : buffer α :=
  dite (n ≤ size b) (fun (h : n ≤ size b) => sigma.mk n (array.take (to_array b) n h)) fun (h : ¬n ≤ size b) => b

def take_right {α : Type u} (b : buffer α) (n : ℕ) : buffer α :=
  dite (n ≤ size b) (fun (h : n ≤ size b) => sigma.mk n (array.take_right (to_array b) n h)) fun (h : ¬n ≤ size b) => b

def drop {α : Type u} (b : buffer α) (n : ℕ) : buffer α :=
  dite (n ≤ size b) (fun (h : n ≤ size b) => sigma.mk (size b - n) (array.drop (to_array b) n h))
    fun (h : ¬n ≤ size b) => b

def reverse {α : Type u} (b : buffer α) : buffer α :=
  sigma.mk (size b) (array.reverse (to_array b))

protected def mem {α : Type u} (v : α) (a : buffer α)  :=
  ∃ (i : fin (size a)), read a i = v

protected instance has_mem {α : Type u} : has_mem α (buffer α) :=
  has_mem.mk buffer.mem

protected instance has_append {α : Type u} : Append (buffer α) :=
  { append := buffer.append }

protected instance has_repr {α : Type u} [has_repr α] : has_repr (buffer α) :=
  has_repr.mk (repr ∘ to_list)

end buffer


def list.to_buffer {α : Type u} (l : List α) : buffer α :=
  buffer.append_list mk_buffer l

def char_buffer  :=
  buffer char

/-- Convert a format object into a character buffer with the provided
    formatting options. -/
def string.to_char_buffer (s : string) : char_buffer :=
  buffer.append_string buffer.nil s

