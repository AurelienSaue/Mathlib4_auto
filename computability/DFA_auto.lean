/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.computability.language
import PostPort

universes u v l 

namespace Mathlib

/-!
# Deterministic Finite Automata
This file contains the definition of a Deterministic Finite Automaton (DFA), a state machine which
determines whether a string (implemented as a list over an arbitrary alphabet) is in a regular set
in linear time.
Note that this definition allows for Automaton with infinite states, a `fintype` instance must be
supplied for true DFA's.
-/

/-- A DFA is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`). -/
structure DFA (α : Type u) (σ : Type v) 
where
  step : σ → α → σ
  start : σ
  accept : set σ

namespace DFA


protected instance inhabited {α : Type u} {σ : Type v} [Inhabited σ] : Inhabited (DFA α σ) :=
  { default := mk (fun (_x : σ) (_x : α) => Inhabited.default) Inhabited.default ∅ }

/-- `M.eval_from s x` evaluates `M` with input `x` starting from the state `s`. -/
def eval_from {α : Type u} {σ : Type v} (M : DFA α σ) (start : σ) : List α → σ :=
  list.foldl (step M) start

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
def eval {α : Type u} {σ : Type v} (M : DFA α σ) : List α → σ :=
  eval_from M (start M)

/-- `M.accepts` is the language of `x` such that `M.eval x` is an accept state. -/
def accepts {α : Type u} {σ : Type v} (M : DFA α σ) : language α :=
  fun (x : List α) => eval M x ∈ accept M

