/-
Copyright (c) 2018 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.nth_rewrite.congr
import PostPort

namespace Mathlib

/-!
# Advanced rewriting tactics

This file provides three interactive tactics
that give the user more control over where to perform a rewrite.

## Main definitions

* `nth_rewrite n rules`: performs only the `n`th possible rewrite using the `rules`.
* `nth_rewrite_lhs`: as above, but only rewrites on the left hand side of an equation or iff.
* `nth_rewrite_rhs`: as above, but only rewrites on the right hand side of an equation or iff.

## Implementation details

There are two alternative backends, provided by `.congr` and `.kabstract`.
The kabstract backend is not currently available through mathlib.

The kabstract backend is faster, but if there are multiple identical occurrences of the
same rewritable subexpression, all are rewritten simultaneously,
and this isn't always what we want.
(In particular, `rewrite_search` is much less capable on the `category_theory` library.)
-/

namespace tactic


/-- Returns the target of the goal when passed `none`,
otherwise, return the type of `h` in `some h`. -/
/-- Replace the target, or a hypothesis, depending on whether `none` or `some h` is given as the
first argument. -/
/-- Preprocess a rewrite rule for use in `get_nth_rewrite`. -/
/-- Get the `n`th rewrite of rewrite rules `q` in expression `e`,
or fail if there are not enough such rewrites. -/
/-- Rewrite the `n`th occurrence of the rewrite rules `q` of (optionally after zooming into) a
hypothesis or target `h` which is an application of a relation. -/
/-- Rewrite the `n`th occurrence of the rewrite rules `q` (optionally on a side)
at all the locations `loc`. -/
namespace interactive


/-- `nth_rewrite n rules` performs only the `n`th possible rewrite using the `rules`.
The tactics `nth_rewrite_lhs` and `nth_rewrite_rhs` are variants
that operate on the left and right hand sides of an equation or iff.

Note: `n` is zero-based, so `nth_rewrite 0 h`
will rewrite along `h` at the first possible location.

In more detail, given `rules = [h1, ..., hk]`,
this tactic will search for all possible locations
where one of `h1, ..., hk` can be rewritten,
and perform the `n`th occurrence.

Example: Given a goal of the form `a + x = x + b`, and hypothesis `h : x = y`,
the tactic `nth_rewrite 1 h` will change the goal to `a + x = y + b`.

The core `rewrite` has a `occs` configuration setting intended to achieve a similar
purpose, but this doesn't really work. (If a rule matches twice, but with different
values of arguments, the second match will not be identified.) -/
