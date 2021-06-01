/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# The `unify_equations` tactic

This module defines `unify_equations`, a first-order unification tactic that
unifies one or more equations in the context. It implements the Qnify algorithm
from [McBride, Inverting Inductively Defined Relations in LEGO][mcbride1996].

The tactic takes as input some equations which it simplifies one after the
other. Each equation is simplified by applying one of several possible
unification steps. Each such step may output other (simpler) equations which are
unified recursively until no unification step applies any more. See
`tactic.interactive.unify_equations` for an example and an explanation of the
different steps.
-/

namespace tactic


namespace unify_equations


/--
The result of a unification step:

- `simplified hs` means that the step succeeded and produced some new (simpler)
  equations `hs`. `hs` can be empty.
- `goal_solved` means that the step succeeded and solved the goal (by deriving a
  contradiction from the given equation).
- `not_simplified` means that the step failed to simplify the equation.
-/
/--
A unification step is a tactic that attempts to simplify a given equation and
returns a `unification_step_result`. The inputs are:

- `equ`, the equation being processed. Must be a local constant.
- `lhs_type` and `rhs_type`, the types of equ's LHS and RHS. For homogeneous
  equations, these are defeq.
- `lhs` and `rhs`, `equ`'s LHS and RHS.
- `lhs_whnf` and `rhs_whnf`, `equ`'s LHS and RHS in WHNF.
- `u`, `equ`'s level.

So `equ : @eq.{u} lhs_type lhs rhs` or `equ : @heq.{u} lhs_type lhs rhs_type rhs`.
-/
/--
For `equ : t == u` with `t : T` and `u : U`, if `T` and `U` are defeq,
we replace `equ` with `equ : t = u`.
-/
/--
For `equ : t = u`, if `t` and `u` are defeq, we delete `equ`.
-/
/--
For `equ : x = t` or `equ : t = x`, where `x` is a local constant, we
substitute `x` with `t` in the goal.
-/
-- TODO This is an improved version of `injection_with` from core

-- (init/meta/injection_tactic). Remove when the improvements have landed in

-- core.

/--
Given `equ : C x₁ ... xₙ = D y₁ ... yₘ` with `C` and `D` constructors of the
same datatype `I`:

- If `C ≠ D`, we solve the goal by contradiction using the no-confusion rule.
- If `C = D`, we clear `equ` and add equations `x₁ = y₁`, ..., `xₙ = yₙ`.
-/
/--
For `type = I x₁ ... xₙ`, where `I` is an inductive type, `get_sizeof type`
returns the constant `I.sizeof`. Fails if `type` is not of this form or if no
such constant exists.
-/
theorem add_add_one_ne (n : ℕ) (m : ℕ) : n + (m + 1) ≠ n :=
  ne_of_gt
    (nat.lt_add_of_pos_right (nat.pos_of_ne_zero (id fun (ᾰ : m + 1 = 0) => nat.no_confusion ᾰ)))

-- Linarith could prove this, but I want to avoid that dependency.

/--
`match_n_plus_m n e` matches `e` of the form `nat.succ (... (nat.succ e')...)`.
It returns `n` plus the number of `succ` constructors and `e'`. The matching is
performed up to normalisation with transparency `md`.
-/
/--
Given `equ : n + m = n` or `equ : n = n + m` with `n` and `m` natural numbers
and `m` a nonzero literal, this tactic produces a proof of `false`. More
precisely, the two sides of the equation must be of the form
`nat.succ (... (nat.succ e)...)` with different numbers of `nat.succ`
constructors. Matching is performed with transparency `md`.
-/
/--
Given `equ : t = u` with `t, u : I` and `I.sizeof t ≠ I.sizeof u`, we solve the
goal by contradiction.
-/
/--
`orelse_step s t` first runs the unification step `s`. If this was successful
(i.e. `s` simplified or solved the goal), it returns the result of `s`.
Otherwise, it runs `t` and returns its result.
-/
/--
For `equ : t = u`, try the following methods in order: `unify_defeq`,
`unify_var`, `unify_constructor_headed`, `unify_cyclic`. If any of them is
successful, stop and return its result. If none is successful, fail.
-/
end unify_equations


/--
If `equ` is the display name of a local constant with type `t = u` or `t == u`,
then `unify_equation_once equ` simplifies it once using
`unify_equations.unify_homogeneous` or `unify_equations.unify_heterogeneous`.

Otherwise it fails.
-/
/--
Given a list of display names of local hypotheses that are (homogeneous or
heterogeneous) equations, `unify_equations` performs first-order unification on
each hypothesis in order. See `tactic.interactive.unify_equations` for an
example and an explanation of what unification does.

Returns true iff the goal has been solved during the unification process.

Note: you must make sure that the input names are unique in the context.
-/
namespace interactive


/--
`unify_equations eq₁ ... eqₙ` performs a form of first-order unification on the
hypotheses `eqᵢ`. The `eqᵢ` must be homogeneous or heterogeneous equations.
Unification means that the equations are simplified using various facts about
constructors. For instance, consider this goal:

```
P : ∀ n, fin n → Prop
n m : ℕ
f : fin n
g : fin m
h₁ : n + 1 = m + 1
h₂ : f == g
h₃ : P n f
⊢ P m g
```

After `unify_equations h₁ h₂`, we get

```
P : ∀ n, fin n → Prop
n : ℕ
f : fin n
h₃ : P n f
⊢ P n f
```

In the example, `unify_equations` uses the fact that every constructor is
injective to conclude `n = m` from `h₁`. Then it replaces every `m` with `n` and
moves on to `h₂`. The types of `f` and `g` are now equal, so the heterogeneous
equation turns into a homogeneous one and `g` is replaced by `f`. Note that the
equations are processed from left to right, so `unify_equations h₂ h₁` would not
simplify as much.

In general, `unify_equations` uses the following steps on each equation until
none of them applies any more:

- Constructor injectivity: if `nat.succ n = nat.succ m` then `n = m`.
- Substitution: if `x = e` for some hypothesis `x`, then `x` is replaced by `e`
  everywhere.
- No-confusion: `nat.succ n = nat.zero` is a contradiction. If we have such an
  equation, the goal is solved immediately.
- Cycle elimination: `n = nat.succ n` is a contradiction.
- Redundancy: if `t = u` but `t` and `u` are already definitionally equal, then
  this equation is removed.
- Downgrading of heterogeneous equations: if `t == u` but `t` and `u` have the
  same type (up to definitional equality), then the equation is replaced by
  `t = u`.
-/
end Mathlib