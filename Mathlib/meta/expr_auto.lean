/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.string.defs
import Mathlib.tactic.derive_inhabited
import Mathlib.PostPort

namespace Mathlib

/-!
# Additional operations on expr and related types

This file defines basic operations on the types expr, name, declaration, level, environment.

This file is mostly for non-tactics. Tactics should generally be placed in `tactic.core`.

## Tags

expr, name, declaration, level, environment, meta, metaprogramming, tactic
-/

namespace binder_info


/-! ### Declarations about `binder_info` -/

protected instance inhabited : Inhabited binder_info := { default := default }

/-- The brackets corresponding to a given binder_info. -/
def brackets : binder_info → string × string := sorry

end binder_info


namespace name


/-! ### Declarations about `name` -/

/-- Find the largest prefix `n` of a `name` such that `f n ≠ none`, then replace this prefix
with the value of `f n`. -/
def map_prefix (f : name → Option name) : name → name := sorry

/-- If `nm` is a simple name (having only one string component) starting with `_`, then
`deinternalize_field nm` removes the underscore. Otherwise, it does nothing. -/
/-- `get_nth_prefix nm n` removes the last `n` components from `nm` -/
/-- Auxilliary definition for `pop_nth_prefix` -/
/-- Pops the top `n` prefixes from the given name. -/
/-- Pop the prefix of a name -/
/-- Auxilliary definition for `from_components` -/
/-- Build a name from components. For example `from_components ["foo","bar"]` becomes
  ``` `foo.bar``` -/
def from_components : List string → name := from_components_aux anonymous

/-- `name`s can contain numeral pieces, which are not legal names
  when typed/passed directly to the parser. We turn an arbitrary
  name into a legal identifier name by turning the numbers to strings. -/
/-- Append a string to the last component of a name -/
def append_suffix : name → string → name := sorry

/-- The first component of a name, turning a number to a string -/
/-- Tests whether the first component of a name is `"_private"` -/
/-- Get the last component of a name, and convert it to a string. -/
/-- Returns the number of characters used to print all the string components of a name,
  including periods between name segments. Ignores numerical parts of a name. -/
/-- Checks whether `nm` has a prefix (including itself) such that P is true -/
def has_prefix (P : name → Bool) : name → Bool := sorry

/-- Appends `'` to the end of a name. -/
/-- `last_string n` returns the rightmost component of `n`, ignoring numeral components.
For example, ``last_string `a.b.c.33`` will return `` `c ``. -/
def last_string : name → string := sorry

/--
Constructs a (non-simple) name from a string.

Example: ``name.from_string "foo.bar" = `foo.bar``
-/
/--
In surface Lean, we can write anonymous Π binders (i.e. binders where the
argument is not named) using the function arrow notation:

```lean
inductive test : Type
| intro : unit → test
```

After elaboration, however, every binder must have a name, so Lean generates
one. In the example, the binder in the type of `intro` is anonymous, so Lean
gives it the name `ᾰ`:

```lean
test.intro : ∀ (ᾰ : unit), test
```

When there are multiple anonymous binders, they are named `ᾰ_1`, `ᾰ_2` etc.

Thus, when we want to know whether the user named a binder, we can check whether
the name follows this scheme. Note, however, that this is not reliable. When the
user writes (for whatever reason)

```lean
inductive test : Type
| intro : ∀ (ᾰ : unit), test
```

we cannot tell that the binder was, in fact, named.

The function `name.is_likely_generated_binder_name` checks if
a name is of the form `ᾰ`, `ᾰ_1`, etc.
-/
/--
Check whether a simple name was likely generated by Lean to name an anonymous
binder. Such names are either `ᾰ` or `ᾰ_n` for some natural `n`. See
note [likely generated binder names].
-/
/--
Check whether a name was likely generated by Lean to name an anonymous binder.
Such names are either `ᾰ` or `ᾰ_n` for some natural `n`. See
note [likely generated binder names].
-/
end name


namespace level


/-! ### Declarations about `level` -/

/-- Tests whether a universe level is non-zero for all assignments of its variables -/
/--
`l.fold_mvar f` folds a function `f : name → α → α`
over each `n : name` appearing in a `level.mvar n` in `l`.
-/
end level


/-! ### Declarations about `binder` -/

/-- The type of binders containing a name, the binding info and the binding type -/
namespace binder


/-- Turn a binder into a string. Uses expr.to_string for the type. -/
end binder


/-!
### Converting between expressions and numerals

There are a number of ways to convert between expressions and numerals, depending on the input and
output types and whether you want to infer the necessary type classes.

See also the tactics `expr.of_nat`, `expr.of_int`, `expr.of_rat`.
-/

/--
`nat.mk_numeral n` embeds `n` as a numeral expression inside a type with 0, 1, and +.
`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`: expressions of the type `has_zero %%type`, etc.
 -/
/--
`int.mk_numeral z` embeds `z` as a numeral expression inside a type with 0, 1, +, and -.
`type`: an expression representing the target type. This must live in Type 0.
`has_zero`, `has_one`, `has_add`, `has_neg`: expressions of the type `has_zero %%type`, etc.
 -/
/--
`nat.to_pexpr n` creates a `pexpr` that will evaluate to `n`.
The `pexpr` does not hold any typing information:
`to_expr ``((%%(nat.to_pexpr 5) : ℤ))` will create a native integer numeral `(5 : ℤ)`.
-/
namespace expr


/--
Turns an expression into a natural number, assuming it is only built up from
`has_one.one`, `bit0`, `bit1`, `has_zero.zero`, `nat.zero`, and `nat.succ`.
-/
/--
Turns an expression into a integer, assuming it is only built up from
`has_one.one`, `bit0`, `bit1`, `has_zero.zero` and a optionally a single `has_neg.neg` as head.
-/
/--
`is_num_eq n1 n2` returns true if `n1` and `n2` are both numerals with the same numeral structure,
ignoring differences in type and type class arguments.
-/
end expr


/-! ### Declarations about `expr` -/

namespace expr


/-- List of names removed by `clean`. All these names must resolve to functions defeq `id`. -/
/-- Clean an expression by removing `id`s listed in `clean_ids`. -/
/-- `replace_with e s s'` replaces ocurrences of `s` with `s'` in `e`. -/
/-- Apply a function to each constant (inductive type, defined function etc) in an expression. -/
/-- Match a variable. -/
/-- Match a sort. -/
/-- Match a constant. -/
/-- Match a metavariable. -/
/-- Match a local constant. -/
/-- Match an application. -/
/-- Match an abstraction. -/
/-- Match a Π type. -/
/-- Match a let. -/
/-- Match a macro. -/
/-- Tests whether an expression is a meta-variable. -/
/-- Tests whether an expression is a sort. -/
/-- Get the universe levels of a `const` expression -/
/--
Replace any metavariables in the expression with underscores, in preparation for printing
`refine ...` statements.
-/
/-- If `e` is a local constant, `to_implicit_local_const e` changes the binder info of `e` to
 `implicit`. See also `to_implicit_binder`, which also changes lambdas and pis. -/
/-- If `e` is a local constant, lamda, or pi expression, `to_implicit_binder e` changes the binder
info of `e` to `implicit`. See also `to_implicit_local_const`, which only changes local constants. -/
/-- Returns a list of all local constants in an expression (without duplicates). -/
/-- Returns the set of all local constants in an expression. -/
/-- Returns the unique names of all local constants in an expression. -/
/-- Returns a name_set of all constants in an expression. -/
/-- Returns a list of all meta-variables in an expression (without duplicates). -/
/-- Returns the set of all meta-variables in an expression. -/
/-- Returns a list of all universe meta-variables in an expression (without duplicates). -/
/--
Test `t` contains the specified subexpression `e`, or a metavariable.
This represents the notion that `e` "may occur" in `t`,
possibly after subsequent unification.
-/
-- We can't use `t.has_meta_var` here, as that detects universe metavariables, too.

/-- Returns a name_set of all constants in an expression starting with a certain prefix. -/
/-- Returns true if `e` contains a name `n` where `p n` is true.
  Returns `true` if `p name.anonymous` is true. -/
/--
Returns true if `e` contains a `sorry`.
-/
/--
`app_symbol_in e l` returns true iff `e` is an application of a constant whose name is in `l`.
-/
/-- `get_simp_args e` returns the arguments of `e` that simp can reach via congruence lemmas. -/
-- `mk_specialized_congr_lemma_simp` throws an assertion violation if its argument is not an app

/-- Simplifies the expression `t` with the specified options.
  The result is `(new_e, pr)` with the new expression `new_e` and a proof
  `pr : e = new_e`. -/
/-- Definitionally simplifies the expression `t` with the specified options.
  The result is the simplified expression. -/
/-- Get the names of the bound variables by a sequence of pis or lambdas. -/
/-- head-reduce a single let expression -/
/-- head-reduce all let expressions -/
/-- Instantiate lambdas in the second argument by expressions from the first. -/
/-- Repeatedly apply `expr.subst`. -/
/-- `instantiate_lambdas_or_apps es e` instantiates lambdas in `e` by expressions from `es`.
If the length of `es` is larger than the number of lambdas in `e`,
then the term is applied to the remaining terms.
Also reduces head let-expressions in `e`, including those after instantiating all lambdas.

This is very similar to `expr.substs`, but this also reduces head let-expressions. -/
/--
Some declarations work with open expressions, i.e. an expr that has free variables.
end Mathlib