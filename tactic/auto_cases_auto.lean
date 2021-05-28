/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.hint
import PostPort

namespace Mathlib

namespace tactic


namespace auto_cases


/-- Structure representing a tactic which can be used by `tactic.auto_cases`. -/
