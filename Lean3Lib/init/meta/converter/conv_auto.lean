/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.
-/
import PrePort
import Lean3Lib.init.meta.tactic
import Lean3Lib.init.meta.simp_tactic
import Lean3Lib.init.meta.interactive
import Lean3Lib.init.meta.congr_lemma
import Lean3Lib.init.meta.match_tactic
import PostPort

namespace Mathlib

/-- `conv α` is a tactic for discharging goals of the form `lhs ~ rhs` for some relation `~` (usually equality) and fixed lhs, rhs.
Known in the literature as a __conversion__ tactic.
So for example, if one had the lemma `p : x = y`, then the conversion for `p` would be one that solves `p`.
-/