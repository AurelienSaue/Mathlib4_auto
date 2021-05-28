/-
Copyright (c) 2020 Gabriel Ebner, Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ext
import Mathlib.Lean3Lib.data.stream
import Mathlib.data.list.basic
import Mathlib.data.list.range
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Additional instances and attributes for streams
-/

protected instance stream.inhabited {α : Type u_1} [Inhabited α] : Inhabited (stream α) :=
  { default := stream.const Inhabited.default }

namespace stream


/-- `take s n` returns a list of the `n` first elements of stream `s` -/
def take {α : Type u_1} (s : stream α) (n : ℕ) : List α :=
  list.map s (list.range n)

theorem length_take {α : Type u_1} (s : stream α) (n : ℕ) : list.length (take s n) = n := sorry

/-- Use a state monad to generate a stream through corecursion -/
def corec_state {σ : Type u_1} {α : Type u_1} (cmd : state σ α) (s : σ) : stream α :=
  corec prod.fst (state_t.run cmd ∘ prod.snd) (state_t.run cmd s)

