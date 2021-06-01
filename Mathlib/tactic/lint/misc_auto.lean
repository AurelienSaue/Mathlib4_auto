/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.lint.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Various linters

This file defines several small linters:
  - `ge_or_gt` checks that `>` and `≥` do not occur in the statement of theorems.
  - `dup_namespace` checks that no declaration has a duplicated namespace such as `list.list.monad`.
  - `unused_arguments` checks that definitions and theorems do not have unused arguments.
  - `doc_blame` checks that every definition has a documentation string
  - `doc_blame_thm` checks that every theorem has a documentation string (not enabled by default)
  - `def_lemma` checks that a declaration is a lemma iff its type is a proposition.
-/

/-!
## Linter against use of `>`/`≥`
-/

/-- The names of `≥` and `>`, mostly disallowed in lemma statements -/
/--
  Checks whether `≥` and `>` occurs in an illegal way in the expression.
  The main ways we legally use these orderings are:
  - `f (≥)`
  - `∃ x ≥ t, b`. This corresponds to the expression
    `@Exists α (fun (x : α), (@Exists (x > t) (λ (H : x > t), b)))`
  This function returns `tt` when it finds `ge`/`gt`, except in the following patterns
  (which are the same for `gt`):
  - `f (@ge _ _)`
  - `f (&0 ≥ y) (λ x : t, b)`
  - `λ H : &0 ≥ t, b`
  Here `&0` is the 0-th de Bruijn variable.
-/
/-- Checks whether a `>`/`≥` is used in the statement of `d`.

It first does a quick check to see if there is any `≥` or `>` in the statement, and then does a
slower check whether the occurrences of `≥` and `>` are allowed.
Currently it checks only the conclusion of the declaration, to eliminate false positive from
binders such as `∀ ε > 0, ...` -/
-- TODO: the commented out code also checks for classicality in statements, but needs fixing

-- TODO: this probably needs to also check whether the argument is a variable or @eq <var> _ _

-- meta def illegal_constants_in_statement (d : declaration) : tactic (option string) :=

-- return $ if d.type.contains_constant (λ n, (n.get_prefix = `classical ∧

--   n.last ∈ ["prop_decidable", "dec", "dec_rel", "dec_eq"]) ∨ n ∈ [`gt, `ge])

-- then

--   let illegal1 := [`classical.prop_decidable, `classical.dec, `classical.dec_rel, `classical.dec_eq],

--       illegal2 := [`gt, `ge],

--       occur1 := illegal1.filter (λ n, d.type.contains_constant (eq n)),

--       occur2 := illegal2.filter (λ n, d.type.contains_constant (eq n)) in

--   some $ sformat!"the type contains the following declarations: {occur1 ++ occur2}." ++

--     (if occur1 = [] then "" else " Add decidability type-class arguments instead.") ++

--     (if occur2 = [] then "" else " Use ≤/< instead.")

-- else none

/-- A linter for checking whether illegal constants (≥, >) appear in a declaration's type. -/
/--
Currently, the linter forbids the use of `>` and `≥` in definitions and
end Mathlib