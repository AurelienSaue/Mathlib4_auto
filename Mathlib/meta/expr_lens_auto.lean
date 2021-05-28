/-
Copyright (c) 2020 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.meta.expr
import PostPort

universes l 

namespace Mathlib

/-!
# A lens for zooming into nested `expr` applications

A "lens" for looking into the subterms of an expression, tracking where we've been, so that
when we "zoom out" after making a change we know exactly which order of `congr_fun`s and
`congr_arg`s we need to make things work.

This file defines the `expr_lens` inductive type, defines basic operations this type, and defines a
useful map-like function `expr.app_map` on `expr`s which maps over applications.

This file is for non-tactics.

## Tags

expr, expr_lens, congr, environment, meta, metaprogramming, tactic
-/

/-! ### Declarations about `expr_lens` -/

/-- You're supposed to think of an `expr_lens` as a big set of nested applications with a single
hole which needs to be filled, either in a function spot or argument spot. `expr_lens.fill` can
fill this hole and turn your lens back into a real `expr`. -/
namespace expr_lens


/-- Inductive type with two constructors `F` and `A`,
that represent the function-part `f` and arg-part `a` of an application `f a`. They specify the
directions in which an `expr_lens` should zoom into an `expr`.

This type is used in the development of rewriting tactics such as `nth_rewrite` and
`rewrite_search`. -/
inductive dir 
where
| F : dir
| A : dir

/-- String representation of `dir`. -/
def dir.to_string : dir → string :=
  sorry

protected instance dir.has_to_string : has_to_string dir :=
  has_to_string.mk dir.to_string

