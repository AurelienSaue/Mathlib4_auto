/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import PrePort
import Lean3Lib.init.data.nat.default
import Lean3Lib.init.data.array.basic
import Lean3Lib.init.data.nat.lemmas
import PostPort

universes u 

namespace Mathlib

namespace array


def slice {α : Type u} {n : ℕ} (a : array n α) (k : ℕ) (l : ℕ) (h₁ : k ≤ l) (h₂ : l ≤ n) : array (l - k) α :=
  d_array.mk fun (_x : fin (l - k)) => sorry

def take {α : Type u} {n : ℕ} (a : array n α) (m : ℕ) (h : m ≤ n) : array m α :=
  cast sorry (slice a 0 m (nat.zero_le m) h)

def drop {α : Type u} {n : ℕ} (a : array n α) (m : ℕ) (h : m ≤ n) : array (n - m) α :=
  slice a m n h sorry

def take_right {α : Type u} {n : ℕ} (a : array n α) (m : ℕ) (h : m ≤ n) : array m α :=
  cast sorry (drop a (n - m) (nat.sub_le n m))

def reverse {α : Type u} {n : ℕ} (a : array n α) : array n α :=
  d_array.mk fun (_x : fin n) => sorry

