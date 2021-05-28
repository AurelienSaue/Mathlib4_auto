/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Simple command line interface for debugging Lean programs and tactics.
-/
import PrePort
import Lean3Lib.init.default
import Lean3Lib.tools.debugger.util
import PostPort

universes l 

namespace Mathlib

namespace debugger


inductive mode 
where
| init : mode
| step : mode
| run : mode
| done : mode

structure state 
where
  md : mode
  csz : ℕ
  fn_bps : List name
  active_bps : List (ℕ × name)

def init_state : state :=
  state.mk mode.init 0 [] []

def prune_active_bps_core (csz : ℕ) : List (ℕ × name) → List (ℕ × name) :=
  sorry

