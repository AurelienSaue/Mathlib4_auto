/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.monotonicity.default
import Mathlib.PostPort

namespace Mathlib

namespace tactic


/-- Apply the function `f` given by `e : pexpr` to the local hypothesis `hyp`, which must either be
of the form `a = b` or `a ≤ b`, replacing the type of `hyp` with `f a = f b` or `f a ≤ f b`. If
`hyp` names an inequality then a new goal `monotone f` is created, unless the name of a proof of
this fact is passed as the optional argument `mono_lem`, or the `mono` tactic can prove it.
-/
namespace interactive


/--
Apply a function to some local assumptions which are either equalities
or inequalities. For instance, if the context contains `h : a = b` and
some function `f` then `apply_fun f at h` turns `h` into
`h : f a = f b`. When the assumption is an inequality `h : a ≤ b`, a side
goal `monotone f` is created, unless this condition is provided using
`apply_fun f at h using P` where `P : monotone f`, or the `mono` tactic
can prove it.

Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end
```
 -/
