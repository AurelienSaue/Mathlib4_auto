/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Minchao Wu
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# `#explode` command

Displays a proof term in a line by line format somewhat akin to a Fitch style
proof or the Metamath proof style.
-/

namespace tactic


namespace explode


inductive status 
where
| reg : status
| intro : status
| lam : status
| sintro : status

/--
A type to distinguish introduction or elimination rules represented as 
strings from theorems referred to by their names.
-/
/--
Turn a thm into a string.
-/
end explode


/--
`#explode decl_name` displays a proof term in a line-by-line format somewhat akin to a Fitch-style
proof or the Metamath proof style.
`#explode_widget decl_name` renders a widget that displays an `#explode` proof.

`#explode iff_true_intro` produces

```lean
iff_true_intro : ∀ {a : Prop}, a → (a ↔ true)
0│   │ a         ├ Prop
1│   │ h         ├ a
2│   │ hl        │ ┌ a
3│   │ trivial   │ │ true
4│2,3│ ∀I        │ a → true
5│   │ hr        │ ┌ true
6│5,1│ ∀I        │ true → a
7│4,6│ iff.intro │ a ↔ true
8│1,7│ ∀I        │ a → (a ↔ true)
9│0,8│ ∀I        │ ∀ {a : Prop}, a → (a ↔ true)
```

In more detail:

The output of `#explode` is a Fitch-style proof in a four-column diagram modeled after Metamath
proof displays like [this](http://us.metamath.org/mpeuni/ru.html). The headers of the columns are
"Step", "Hyp", "Ref", "Type" (or "Expression" in the case of Metamath):
* Step: An increasing sequence of numbers to number each step in the proof, used in the Hyp field.
* Hyp: The direct children of the current step. Most theorems are implications like `A -> B -> C`,
  and so on the step proving `C` the Hyp field will refer to the steps that prove `A` and `B`.
* Ref: The name of the theorem being applied. This is well-defined in Metamath, but in Lean there
  are some special steps that may have long names because the structure of proof terms doesn't
  exactly match this mold.
  * If the theorem is `foo (x y : Z) : A x -> B y -> C x y`:
    * the Ref field will contain `foo`,
    * `x` and `y` will be suppressed, because term construction is not interesting, and
    * the Hyp field will reference steps proving `A x` and `B y`. This corresponds to a proof term
      like `@foo x y pA pB` where `pA` and `pB` are subproofs.
  * If the head of the proof term is a local constant or lambda, then in this case the Ref will
    say `∀E` for forall-elimination. This happens when you have for example `h : A -> B` and
    `ha : A` and prove `b` by `h ha`; we reinterpret this as if it said `∀E h ha` where `∀E` is
    (n-ary) modus ponens.
  * If the proof term is a lambda, we will also use `∀I` for forall-introduction, referencing the
    body of the lambda. The indentation level will increase, and a bracket will surround the proof
    of the body of the lambda, starting at a proof step labeled with the name of the lambda variable
    and its type, and ending with the `∀I` step. Metamath doesn't have steps like this, but the
    style is based on Fitch proofs in first-order logic.
* Type: This contains the type of the proof term, the theorem being proven at the current step.
  This proof layout differs from `#print` in using lots of intermediate step displays so that you
  can follow along and don't have to see term construction steps because they are implicitly in the
  intermediate step displays.

Also, it is common for a Lean theorem to begin with a sequence of lambdas introducing local
constants of the theorem. In order to minimize the indentation level, the `∀I` steps at the end of
the proof will be introduced in a group and the indentation will stay fixed. (The indentation
brackets are only needed in order to delimit the scope of assumptions, and these assumptions
have global scope anyway so detailed tracking is not necessary.)
-/
