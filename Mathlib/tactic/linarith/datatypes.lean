/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.meta.rb_map
import Mathlib.tactic.ring
import Mathlib.tactic.linarith.lemmas
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Datatypes for `linarith`

Some of the data structures here are used in multiple parts of the tactic.
We split them into their own file.

This file also contains a few convenient auxiliary functions.
-/

namespace linarith


/-- A shorthand for tracing when the `trace.linarith` option is set to true. -/
/--
A shorthand for tracing the types of a list of proof terms
when the `trace.linarith` option is set to true.
-/
/-! ### Linear expressions -/

/--
A linear expression is a list of pairs of variable indices and coefficients,
representing the sum of the products of each coefficient with its corresponding variable.

Some functions on `linexp` assume that `n : ℕ` occurs at most once as the first element of a pair,
and that the list is sorted in decreasing order of the first argument.
This is not enforced by the type but the operations here preserve it.
-/
def linexp  :=
  List (ℕ × ℤ)

namespace linexp


/--
Add two `linexp`s together componentwise.
Preserves sorting and uniqueness of the first argument.
-/
/-- `l.scale c` scales the values in `l` by `c` without modifying the order or keys. -/
def scale (c : ℤ) (l : linexp) : linexp :=
  ite (c = 0) [] (ite (c = 1) l (list.map (fun (_x : ℕ × ℤ) => sorry) l))

/--
`l.get n` returns the value in `l` associated with key `n`, if it exists, and `none` otherwise.
This function assumes that `l` is sorted in decreasing order of the first argument,
that is, it will return `none` as soon as it finds a key smaller than `n`.
-/
def get (n : ℕ) : linexp → Option ℤ :=
  sorry

/--
`l.contains n` is true iff `n` is the first element of a pair in `l`.
-/
def contains (n : ℕ) : linexp → Bool :=
  option.is_some ∘ get n

/--
`l.zfind n` returns the value associated with key `n` if there is one, and 0 otherwise.
-/
def zfind (n : ℕ) (l : linexp) : ℤ :=
  sorry

/-- `l.vars` returns the list of variables that occur in `l`. -/
def vars (l : linexp) : List ℕ :=
  list.map prod.fst l

/--
Defines a lex ordering on `linexp`. This function is performance critical.
-/
def cmp : linexp → linexp → ordering :=
  sorry

end linexp


/-! ### Inequalities -/

/-- The three-element type `ineq` is used to represent the strength of a comparison between terms. -/
inductive ineq 
where
| eq : ineq
| le : ineq
| lt : ineq

namespace ineq


/--
`max R1 R2` computes the strength of the sum of two inequalities. If `t1 R1 0` and `t2 R2 0`,
then `t1 + t2 (max R1 R2) 0`.
-/
def max : ineq → ineq → ineq :=
  sorry

/-- `ineq` is ordered `eq < le < lt`. -/
def cmp : ineq → ineq → ordering :=
  sorry

/-- Prints an `ineq` as the corresponding infix symbol. -/
def to_string : ineq → string :=
  sorry

/-- Finds the name of a multiplicative lemma corresponding to an inequality strength. -/
protected instance has_to_string : has_to_string ineq :=
  has_to_string.mk to_string

end ineq


/-! ### Comparisons with 0 -/

/--
The main datatype for FM elimination.
Variables are represented by natural numbers, each of which has an integer coefficient.
Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
The represented term is `coeffs.sum (λ ⟨k, v⟩, v * Var[k])`.
str determines the strength of the comparison -- is it < 0, ≤ 0, or = 0?
-/
structure comp 
where
  str : ineq
  coeffs : linexp

/-- `c.vars` returns the list of variables that appear in the linear expression contained in `c`. -/
def comp.vars : comp → List ℕ :=
  linexp.vars ∘ comp.coeffs

/-- `comp.coeff_of c a` projects the coefficient of variable `a` out of `c`. -/
def comp.coeff_of (c : comp) (a : ℕ) : ℤ :=
  linexp.zfind a (comp.coeffs c)

/-- `comp.scale c n` scales the coefficients of `c` by `n`. -/
def comp.scale (c : comp) (n : ℕ) : comp :=
  comp.mk (comp.str c) (linexp.scale (↑n) (comp.coeffs c))

/--
`comp.add c1 c2` adds the expressions represented by `c1` and `c2`.
The coefficient of variable `a` in `c1.add c2`
is the sum of the coefficients of `a` in `c1` and `c2`.
 -/
/-- `comp` has a lex order. First the `ineq`s are compared, then the `coeff`s. -/
/--
A `comp` represents a contradiction if its expression has no coefficients and its strength is <,
that is, it represents the fact `0 < 0`.
 -/
/-! ### Parsing into linear form -/

/-! ### Control -/

/--
A preprocessor transforms a proof of a proposition into a proof of a different propositon.
The return type is `list expr`, since some preprocessing steps may create multiple new hypotheses,
and some may remove a hypothesis from the list.
A "no-op" preprocessor should return its input as a singleton list.
-/
/--
Some preprocessors need to examine the full list of hypotheses instead of working item by item.
As with `preprocessor`, the input to a `global_preprocessor` is replaced by, not added to, its output.
-/
/--
Some preprocessors perform branching case splits. A `branch` is used to track one of these case
splits. The first component, an `expr`, is the goal corresponding to this branch of the split,
given as a metavariable. The `list expr` component is the list of hypotheses for `linarith`
in this branch. Every `expr` in this list should be type correct in the context of the associated goal.
-/
/--
Some preprocessors perform branching case splits.
A `global_branching_preprocessor` produces a list of branches to run.
Each branch is independent, so hypotheses that appear in multiple branches should be duplicated.
The preprocessor is responsible for making sure that each branch contains the correct goal
metavariable.
-/
/--
A `preprocessor` lifts to a `global_preprocessor` by folding it over the input list.
-/
/--
A `global_preprocessor` lifts to a `global_branching_preprocessor` by producing only one branch.
-/
/--
`process pp l` runs `pp.transform` on `l` and returns the result,
tracing the result if `trace.linarith` is on.
-/
/--
A `certificate_oracle` is a function `produce_certificate : list comp → ℕ → tactic (rb_map ℕ ℕ)`.
`produce_certificate hyps max_var` tries to derive a contradiction from the comparisons in `hyps`
by eliminating all variables ≤ `max_var`.
If successful, it returns a map `coeff : ℕ → ℕ` as a certificate.
This map represents that we can find a contradiction by taking the sum  `∑ (coeff i) * hyps[i]`.

The default `certificate_oracle` used by `linarith` is `linarith.fourier_motzkin.produce_certificate`
-/
/-- A configuration object for `linarith`. -/
