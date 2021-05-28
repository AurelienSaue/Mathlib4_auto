/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.rcases
import PostPort

universes u v l w 

namespace Mathlib

/-!
# lift tactic

This file defines the `lift` tactic, allowing the user to lift elements from one type to another
under a specified condition.

## Tags

lift, tactic
-/

/-- A class specifying that you can lift elements from `α` to `β` assuming `cond` is true.
  Used by the tactic `lift`. -/
class can_lift (α : Type u) (β : Type v) 
where
  coe : β → α
  cond : α → Prop
  prf : ∀ (x : α), cond x → ∃ (y : β), coe y = x

/--
A user attribute used internally by the `lift` tactic.
This should not be applied by hand.
-/
protected instance nat.can_lift : can_lift ℤ ℕ :=
  can_lift.mk coe (fun (n : ℤ) => 0 ≤ n) sorry

/-- Enable automatic handling of pi types in `can_lift`. -/
protected instance pi.can_lift (ι : Type u) (α : ι → Type v) (β : ι → Type w) [(i : ι) → can_lift (α i) (β i)] : can_lift ((i : ι) → α i) ((i : ι) → β i) :=
  can_lift.mk (fun (f : (i : ι) → β i) (i : ι) => can_lift.coe (f i))
    (fun (f : (i : ι) → α i) => ∀ (i : ι), can_lift.cond (β i) (f i)) sorry

namespace tactic


/--
Construct the proof of `cond x` in the lift tactic.
*  `e` is the expression being lifted and `h` is the specified proof of `can_lift.cond e`.
*  `old_tp` and `new_tp` are the arguments to `can_lift` and `inst` is the `can_lift`-instance.
*  `s` and `to_unfold` contain the information of the simp set used to simplify.

If the proof was specified, we check whether it has the correct type.
If it doesn't have the correct type, we display an error message
(but first call dsimp on the expression in the message).

If the proof was not specified, we create assert it as a local constant.
(The name of this local constant doesn't matter, since `lift` will remove it from the context.)
-/
/-- Lift the expression `p` to the type `t`, with proof obligation given by `h`.
  The list `n` is used for the two newly generated names, and to specify whether `h` should
  remain in the local context. See the doc string of `tactic.interactive.lift` for more information.
  -/
/-- Parses an optional token "using" followed by a trailing `pexpr`. -/
/-- Parses a token "to" followed by a trailing `pexpr`. -/
namespace interactive


/--
Lift an expression to another type.
* Usage: `'lift' expr 'to' expr ('using' expr)? ('with' id (id id?)?)?`.
* If `n : ℤ` and `hn : n ≥ 0` then the tactic `lift n to ℕ using hn` creates a new
  constant of type `ℕ`, also named `n` and replaces all occurrences of the old variable `(n : ℤ)`
  with `↑n` (where `n` in the new variable). It will remove `n` and `hn` from the context.
  + So for example the tactic `lift n to ℕ using hn` transforms the goal
    `n : ℤ, hn : n ≥ 0, h : P n ⊢ n = 3` to `n : ℕ, h : P ↑n ⊢ ↑n = 3`
    (here `P` is some term of type `ℤ → Prop`).
* The argument `using hn` is optional, the tactic `lift n to ℕ` does the same, but also creates a
  new subgoal that `n ≥ 0` (where `n` is the old variable).
  + So for example the tactic `lift n to ℕ` transforms the goal
    `n : ℤ, h : P n ⊢ n = 3` to two goals
    `n : ℕ, h : P ↑n ⊢ ↑n = 3` and `n : ℤ, h : P n ⊢ n ≥ 0`.
* You can also use `lift n to ℕ using e` where `e` is any expression of type `n ≥ 0`.
* Use `lift n to ℕ with k` to specify the name of the new variable.
* Use `lift n to ℕ with k hk` to also specify the name of the equality `↑k = n`. In this case, `n`
  will remain in the context. You can use `rfl` for the name of `hk` to substitute `n` away
  (i.e. the default behavior).
* You can also use `lift e to ℕ with k hk` where `e` is any expression of type `ℤ`.
  In this case, the `hk` will always stay in the context, but it will be used to rewrite `e` in
  all hypotheses and the target.
  + So for example the tactic `lift n + 3 to ℕ using hn with k hk` transforms the goal
    `n : ℤ, hn : n + 3 ≥ 0, h : P (n + 3) ⊢ n + 3 = 2 * n` to the goal
    `n : ℤ, k : ℕ, hk : ↑k = n + 3, h : P ↑k ⊢ ↑k = 2 * n`.
* The tactic `lift n to ℕ using h` will remove `h` from the context. If you want to keep it,
  specify it again as the third argument to `with`, like this: `lift n to ℕ using h with n rfl h`.
* More generally, this can lift an expression from `α` to `β` assuming that there is an instance
  of `can_lift α β`. In this case the proof obligation is specified by `can_lift.cond`.
* Given an instance `can_lift β γ`, it can also lift `α → β` to `α → γ`; more generally, given
  `β : Π a : α, Type*`, `γ : Π a : α, Type*`, and `[Π a : α, can_lift (β a) (γ a)]`, it
  automatically generates an instance `can_lift (Π a, β a) (Π a, γ a)`.

`lift` is in some sense dual to the `zify` tactic. `lift (z : ℤ) to ℕ` will change the type of an
integer `z` (in the supertype) to `ℕ` (the subtype), given a proof that `z ≥ 0`;
propositions concerning `z` will still be over `ℤ`. `zify` changes propositions about `ℕ` (the
subtype) to propositions about `ℤ` (the supertype), without changing the type of any variable.
-/
