/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

namespace Mathlib

/-!
# `choose` tactic

Performs Skolemization, that is, given `h : ∀ a:α, ∃ b:β, p a b |- G` produces
`f : α → β, hf: ∀ a, p a (f a) |- G`.
-/

namespace tactic


/-- Given `α : Sort u`, `nonemp : nonempty α`, `p : α → Prop`, a context of local variables
`ctxt`, and a pair of an element `val : α` and `spec : p val`,
`mk_sometimes u α nonemp p ctx (val, spec)` produces another pair `val', spec'`
such that `val'` does not have any free variables from elements of `ctxt` whose types are
propositions. This is done by applying `function.sometimes` to abstract over all the propositional
arguments. -/
/-- Changes `(h : ∀xs, ∃a:α, p a) ⊢ g` to `(d : ∀xs, a) (s : ∀xs, p (d xs)) ⊢ g` and
`(h : ∀xs, p xs ∧ q xs) ⊢ g` to `(d : ∀xs, p xs) (s : ∀xs, q xs) ⊢ g`.
`choose1` returns a pair of the second local constant it introduces,
and the error result (see below).

If `nondep` is true and `α` is inhabited, then it will remove the dependency of `d` on
all propositional assumptions in `xs`. For example if `ys` are propositions then
`(h : ∀xs ys, ∃a:α, p a) ⊢ g` becomes `(d : ∀xs, a) (s : ∀xs ys, p (d xs)) ⊢ g`.

The second value returned by `choose1` is the result of nondep elimination:
* `none`: nondep elimination was not attempted or was not applicable
* `some none`: nondep elimination was successful
* ``some (some `(nonempty α))``: nondep elimination was unsuccessful
  because we could not find a `nonempty α` instance
-/
/-- Changes `(h : ∀xs, ∃as, p as ∧ q as) ⊢ g` to a list of functions `as`,
and a final hypothesis on `p as` and `q as`. If `nondep` is true then the functions will
be made to not depend on propositional arguments, when possible.

The last argument is an internal recursion variable, indicating whether nondep elimination
has been useful so far. The tactic fails if `nondep` is true, and nondep elimination is
attempted at least once, and it fails every time it is attempted, in which case it returns
an error complaining about the first attempt.
-/
namespace interactive


/-- `choose a b h h' using hyp` takes an hypothesis `hyp` of the form
`∀ (x : X) (y : Y), ∃ (a : A) (b : B), P x y a b ∧ Q x y a b`
for some `P Q : X → Y → A → B → Prop` and outputs
into context a function `a : X → Y → A`, `b : X → Y → B` and two assumptions:
`h : ∀ (x : X) (y : Y), P x y (a x y) (b x y)` and
`h' : ∀ (x : X) (y : Y), Q x y (a x y) (b x y)`. It also works with dependent versions.

`choose! a b h h' using hyp` does the same, except that it will remove dependency of
the functions on propositional arguments if possible. For example if `Y` is a proposition
and `A` and `B` are nonempty in the above example then we will instead get
`a : X → A`, `b : X → B`, and the assumptions
`h : ∀ (x : X) (y : Y), P x y (a x) (b x)` and
`h' : ∀ (x : X) (y : Y), Q x y (a x) (b x)`.

Examples:

```lean
example (h : ∀n m : ℕ, ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i : ℕ → ℕ → ℕ,
  guard_hyp j : ℕ → ℕ → ℕ,
  guard_hyp h : ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n,
  trivial
end
```

```lean
example (h : ∀ i : ℕ, i < 7 → ∃ j, i < j ∧ j < i+i) : true :=
begin
  choose! f h h' using h,
  guard_hyp f : ℕ → ℕ,
  guard_hyp h : ∀ (i : ℕ), i < 7 → i < f i,
  guard_hyp h' : ∀ (i : ℕ), i < 7 → f i < i + i,
  trivial,
end
```
-/
