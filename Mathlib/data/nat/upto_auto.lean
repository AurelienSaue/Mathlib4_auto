/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.basic
import PostPort

namespace Mathlib

/-!
# `nat.upto`

`nat.upto p`, with `p` a predicate on `ℕ`, is a subtype of elements `n : ℕ` such that no value
(strictly) below `n` satisfies `p`.

This type has the property that `>` is well-founded when `∃ i, p i`, which allows us to implement
searches on `ℕ`, starting at `0` and with an unknown upper-bound.

It is similar to the well founded relation constructed to define `nat.find` with
the difference that, in `nat.upto p`, `p` does not need to be decidable. In fact,
`nat.find` could be slightly altered to factor decidability out of its
well founded relation and would then fulfill the same purpose as this file.
-/

namespace nat


/-- The subtype of natural numbers `i` which have the property that
no `j` less than `i` satisfies `p`. This is an initial segment of the
natural numbers, up to and including the first value satisfying `p`.

We will be particularly interested in the case where there exists a value
satisfying `p`, because in this case the `>` relation is well-founded.  -/
def upto (p : ℕ → Prop)  :=
  Subtype fun (i : ℕ) => ∀ (j : ℕ), j < i → ¬p j

namespace upto


/-- Lift the "greater than" relation on natural numbers to `nat.upto`. -/
protected def gt (p : ℕ → Prop) (x : upto p) (y : upto p)  :=
  subtype.val x > subtype.val y

protected instance has_lt {p : ℕ → Prop} : HasLess (upto p) :=
  { Less := fun (x y : upto p) => subtype.val x < subtype.val y }

/-- The "greater than" relation on `upto p` is well founded if (and only if) there exists a value
satisfying `p`. -/
protected theorem wf {p : ℕ → Prop} : (∃ (x : ℕ), p x) → well_founded (upto.gt p) := sorry

/-- Zero is always a member of `nat.upto p` because it has no predecessors. -/
def zero {p : ℕ → Prop} : upto p :=
  { val := 0, property := sorry }

/-- The successor of `n` is in `nat.upto p` provided that `n` doesn't satisfy `p`. -/
def succ {p : ℕ → Prop} (x : upto p) (h : ¬p (subtype.val x)) : upto p :=
  { val := Nat.succ (subtype.val x), property := sorry }

