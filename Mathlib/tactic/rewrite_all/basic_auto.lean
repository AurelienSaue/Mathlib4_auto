/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mllist
import Mathlib.tactic.core
import Mathlib.PostPort

universes l 

namespace Mathlib

inductive side where
| L : side
| R : side

def side.other : side → side := sorry

def side.to_string : side → string := sorry

protected instance side.has_to_string : has_to_string side := has_to_string.mk side.to_string

namespace tactic.rewrite_all


end Mathlib