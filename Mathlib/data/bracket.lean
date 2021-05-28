/-
Copyright (c) 2021 Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Lutz and Oliver Nash.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u_1 u_2 l 

namespace Mathlib

/-!
# Bracket Notation

This file provides notation which can be used for the Lie bracket, for the commutator of two
subgroups, and for other similar operations.

## Main Definitions

* `has_bracket L M` for a binary operation that takes something in `L` and something in `M` and
produces something in `M`. Defining an instance of this structure gives access to the notation `⁅ ⁆`

## Notation

We introduce the notation `⁅x, y⁆` for the `bracket` of any `has_bracket` structure. Note that
these are the Unicode "square with quill" brackets rather than the usual square brackets.
-/

/-- The has_bracket class has three intended uses:

  1. for certain binary operations on structures, like the product `⁅x, y⁆` of two elements
    `x`, `y` in a Lie algebra or the commutator of two elements `x` and `y` in a group.

  2. for certain actions of one structure on another, like the action `⁅x, m⁆` of an element `x`
    of a Lie algebra on an element `m` in one of its modules (analogous to `has_scalar` in the
    associative setting).

  3. for binary operations on substructures, like the commutator `⁅H, K⁆` of two subgroups `H` and
     `K` of a group. -/
class has_bracket (L : Type u_1) (M : Type u_2) 
where
  bracket : L → M → M

