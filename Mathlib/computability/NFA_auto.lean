/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.computability.DFA
import Mathlib.PostPort

universes u v l 

namespace Mathlib

/-!
# Nondeterministic Finite Automata
This file contains the definition of a Nondeterministic Finite Automaton (NFA), a state machine
which determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular
set by evaluating the string over every possible path.
We show that DFA's are equivalent to NFA's however the construction from NFA to DFA uses an
exponential number of states.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true NFA's.
-/

/-- An NFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `set` of states. These are the states that it
  may be sent to. -/
structure NFA (α : Type u) (σ : Type v) where
  step : σ → α → set σ
  start : set σ
  accept : set σ

namespace NFA


protected instance inhabited {α : Type u} {σ : Type v} : Inhabited (NFA α σ) :=
  { default := mk (fun (_x : σ) (_x : α) => ∅) ∅ ∅ }

/-- `M.step_set S a` is the union of `M.step s a` for all `s ∈ S`. -/
def step_set {α : Type u} {σ : Type v} (M : NFA α σ) : set σ → α → set σ :=
  fun (Ss : set σ) (a : α) =>
    do 
      let S ← Ss 
      step M S a

theorem mem_step_set {α : Type u} {σ : Type v} (M : NFA α σ) (s : σ) (S : set σ) (a : α) :
    s ∈ step_set M S a ↔ ∃ (t : σ), ∃ (H : t ∈ S), s ∈ step M t a :=
  sorry

/-- `M.eval_from S x` computes all possible paths though `M` with input `x` starting at an element
  of `S`. -/
def eval_from {α : Type u} {σ : Type v} (M : NFA α σ) (start : set σ) : List α → set σ :=
  list.foldl (step_set M) start

/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval {α : Type u} {σ : Type v} (M : NFA α σ) : List α → set σ := eval_from M (start M)

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def accepts {α : Type u} {σ : Type v} (M : NFA α σ) : language α :=
  fun (x : List α) => ∃ (S : σ), ∃ (H : S ∈ accept M), S ∈ eval M x

/-- `M.to_DFA` is an `DFA` constructed from a `NFA` `M` using the subset construction. The
  states is the type of `set`s of `M.state` and the step function is `M.step_set`. -/
def to_DFA {α : Type u} {σ : Type v} (M : NFA α σ) : DFA α (set σ) :=
  DFA.mk (step_set M) (start M) (set_of fun (S : set σ) => ∃ (s : σ), ∃ (H : s ∈ S), s ∈ accept M)

@[simp] theorem to_DFA_correct {α : Type u} {σ : Type v} (M : NFA α σ) :
    DFA.accepts (to_DFA M) = accepts M :=
  sorry

end NFA


namespace DFA


/-- `M.to_NFA` is an `NFA` constructed from a `DFA` `M` by using the same start and accept
  states and a transition function which sends `s` with input `a` to the singleton `M.step s a`. -/
def to_NFA {α : Type u} {σ' : Type v} (M : DFA α σ') : NFA α σ' :=
  NFA.mk (fun (s : σ') (a : α) => singleton (step M s a)) (singleton (start M)) (accept M)

@[simp] theorem to_NFA_eval_from_match {α : Type u} {σ : Type v} (M : DFA α σ) (start : σ)
    (s : List α) : NFA.eval_from (to_NFA M) (singleton start) s = singleton (eval_from M start s) :=
  sorry

@[simp] theorem to_NFA_correct {α : Type u} {σ : Type v} (M : DFA α σ) :
    NFA.accepts (to_NFA M) = accepts M :=
  sorry

end Mathlib