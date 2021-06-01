/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
 

namespace Mathlib

namespace tactic


/- Given a local constant `H : C x₁ ... xₙ = D y₁ ... yₘ`, where `C` and `D` are
fully applied constructors, `injection_with H ns base offset` does the
following:

- If `C ≠ D`, it solves the goal (using the no-confusion rule).
- If `C = D` (and thus `n = m`), it adds hypotheses
  `h₁ : x₁ = y₁, ..., hₙ : xₙ = yₙ` to the local context. Names for the `hᵢ`
  are taken from `ns`. If `ns` does not contain enough names, then the names
  are derived from `base` and `offset` (by default `h_1`, `h_2` etc.; see
  `intro_fresh`).
- Special case: if `C = D` and `n = 0` (i.e. the constructors have no
  arguments), the hypothesis `h : true` is added to the context.

`injection_with` returns the new hypotheses and the leftover names from `ns`
(i.e. those names that were not used to name the new hypotheses). If (and only
if) the goal was solved, the list of new hypotheses is empty.
-/

