/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.dlist.basic
import Mathlib.logic.function.basic
import Mathlib.control.basic
import Mathlib.meta.expr
import Mathlib.meta.rb_map
import Mathlib.data.bool
import Mathlib.tactic.binder_matching
import Mathlib.tactic.lean_core_docs
import Mathlib.tactic.interactive_expr
import Lean3Lib.system.io
import PostPort

universes u_1 l_2 l_1 

namespace Mathlib

protected instance pos.has_lt : HasLess pos :=
  { Less := fun (x y : pos) => (pos.line x, pos.column x) < (pos.line y, pos.column y) }

namespace expr


/-- Given an expr `α` representing a type with numeral structure,
`of_nat α n` creates the `α`-valued numeral expression corresponding to `n`. -/
/-- Given an expr `α` representing a type with numeral structure,
`of_int α n` creates the `α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
/-- Generates an expression of the form `∃(args), inner`. `args` is assumed to be a list of local
constants. When possible, `p ∧ q` is used instead of `∃(_ : p), q`. -/
/-- `traverse f e` applies the monadic function `f` to the direct descendants of `e`. -/
/-- `mfoldl f a e` folds the monadic function `f` over the subterms of the expression `e`,
with initial value `a`. -/
/-- `kreplace e old new` replaces all occurrences of the expression `old` in `e`
with `new`. The occurrences of `old` in `e` are determined using keyed matching
with transparency `md`; see `kabstract` for details. If `unify` is true,
we may assign metavariables in `e` as we match subterms of `e` against `old`. -/
end expr


namespace interaction_monad


/-- `get_state` returns the underlying state inside an interaction monad, from within that monad. -/
-- Note that this is a generalization of `tactic.read` in core.

/-- `set_state` sets the underlying state inside an interaction monad, from within that monad. -/
-- Note that this is a generalization of `tactic.write` in core.

/--
`run_with_state state tac` applies `tac` to the given state `state` and returns the result,
subsequently restoring the original state.
If `tac` fails, then `run_with_state` does too.
-/
end interaction_monad


namespace format


/-- `join' [a,b,c]` produces the format object `abc`.
It differs from `format.join` by using `format.nil` instead of `""` for the empty list. -/
/-- `intercalate x [a, b, c]` produces the format object `a.x.b.x.c`,
where `.` represents `format.join`. -/
/-- `soft_break` is similar to `line`. Whereas in `group (x ++ line ++ y ++ line ++ z)`
the result either fits on one line or in three, `x ++ soft_break ++ y ++ soft_break ++ z`
each line break is decided independently -/
/-- Format a list as a comma separated list, without any brackets. -/
end format


/-- format a `list` by separating elements with `soft_break` instead of `line` -/
namespace tactic


/-- Private work function for `add_local_consts_as_local_hyps`: given
    `mappings : list (expr × expr)` corresponding to pairs `(var, hyp)` of variables and the local
    hypothesis created as a result and `(var :: rest) : list expr` of more local variables we
    examine `var` to see if it contains any other variables in `rest`. If it does, we put it to the
    back of the queue and recurse. If it does not, then we perform replacements inside the type of
    `var` using the `mappings`, create a new associate local hypothesis, add this to the list of
    mappings, and recurse. We are done once all local hypotheses have been processed.

    If the list of passed local constants have types which depend on one another (which can only
    happen by hand-crafting the `expr`s manually), this function will loop forever. -/
/-- `add_local_consts_as_local_hyps vars` add the given list `vars` of `expr.local_const`s to the
    tactic state. This is harder than it sounds, since the list of local constants which we have
    been passed can have dependencies between their types.

    For example, suppose we have two local constants `n : ℕ` and `h : n = 3`. Then we cannot blindly
    add `h` as a local hypothesis, since we need the `n` to which it refers to be the `n` created as
    a new local hypothesis, not the old local constant `n` with the same name. Of course, these
    dependencies can be nested arbitrarily deep.

    If the list of passed local constants have types which depend on one another (which can only
    happen by hand-crafting the `expr`s manually), this function will loop forever. -/
/- The `list.reverse` below is a performance optimisation since the list of available variables
   reported by the system is often mostly the reverse of the order in which they are dependent. -/

/-- Compute the arity of explicit arguments of `type`. -/
/-- Compute the arity of explicit arguments of `fn`'s type. -/
/--
For `e = f x₁ ... xₙ`, `get_app_fn_args_whnf e` returns `(f, [x₁, ..., xₙ])`. `e`
is normalised as necessary; for example:

```
get_app_fn_args_whnf `(let f := g x in f y) = (`(g), [`(x), `(y)])
```

The returned expression is in whnf, but the arguments are generally not.
-/
/--
`get_app_fn_whnf e md unfold_ginductive` is like `expr.get_app_fn e` but `e` is
normalised as necessary (with transparency `md`). `unfold_ginductive` controls
whether constructors of generalised inductive types are unfolded. The returned
expression is in whnf.
-/
/--
`get_app_fn_const_whnf e md unfold_ginductive` expects that `e = C x₁ ... xₙ`,
where `C` is a constant, after normalisation with transparency `md`. If so, the
name of `C` is returned. Otherwise the tactic fails. `unfold_ginductive`
controls whether constructors of generalised inductive types are unfolded.
-/
/--
`get_app_args_whnf e md unfold_ginductive` is like `expr.get_app_args e` but `e`
is normalised as necessary (with transparency `md`). `unfold_ginductive`
controls whether constructors of generalised inductive types are unfolded. The
returned expressions are not necessarily in whnf.
-/
/-- `pis loc_consts f` is used to create a pi expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with pi binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``pis [a, b] `(f a b)`` will return the expression
`Π (a : Ta) (b : Tb), f a b`. -/
/-- `lambdas loc_consts f` is used to create a lambda expression whose body is `f`.
`loc_consts` should be a list of local constants. The function will abstract these local
constants from `f` and bind them with lambda binders.

For example, if `a, b` are local constants with types `Ta, Tb`,
``lambdas [a, b] `(f a b)`` will return the expression
`λ (a : Ta) (b : Tb), f a b`. -/
-- TODO: move to `declaration` namespace in `meta/expr.lean`

/-- `mk_theorem n ls t e` creates a theorem declaration with name `n`, universe parameters named
`ls`, type `t`, and body `e`. -/
/-- `add_theorem_by n ls type tac` uses `tac` to synthesize a term with type `type`, and adds this
to the environment as a theorem with name `n` and universe parameters `ls`. -/
/-- `eval_expr' α e` attempts to evaluate the expression `e` in the type `α`.
This is a variant of `eval_expr` in core. Due to unexplained behavior in the VM, in rare
situations the latter will fail but the former will succeed. -/
/-- `mk_fresh_name` returns identifiers starting with underscores,
which are not legal when emitted by tactic programs. `mk_user_fresh_name`
turns the useful source of random names provided by `mk_fresh_name` into
names which are usable by tactic programs.

The returned name has four components which are all strings. -/
/-- `has_attribute' attr_name decl_name` checks
whether `decl_name` exists and has attribute `attr_name`. -/
/-- Checks whether the name is a simp lemma -/
/-- Checks whether the name is an instance. -/
/-- `local_decls` returns a dictionary mapping names to their corresponding declarations.
Covers all declarations from the current file. -/
/-- `get_decls_from` returns a dictionary mapping names to their
corresponding declarations.  Covers all declarations the files listed
in `fs`, with the current file listed as `none`.

The path of the file names is expected to be relative to
the root of the project (i.e. the location of `leanpkg.toml` when it
is present); e.g. `"src/tactic/core.lean"`

Possible issue: `get_decls_from` uses `get_cwd`, the current working
directory, which may not always point at the root of the project.
It would work better if it searched for the root directory or,
better yet, if Lean exposed its path information.
-/
/-- If `{nm}_{n}` doesn't exist in the environment, returns that, otherwise tries `{nm}_{n+1}` -/
/-- Return a name which doesn't already exist in the environment. If `nm` doesn't exist, it
returns that, otherwise it tries `nm_2`, `nm_3`, ... -/
/--
Returns a pair `(e, t)`, where `e ← mk_const d.to_name`, and `t = d.type`
but with universe params updated to match the fresh universe metavariables in `e`.

This should have the same effect as just
```lean
do e ← mk_const d.to_name,
   t ← infer_type e,
   return (e, t)
```
but is hopefully faster.
-/
/--
Replace every universe metavariable in an expression with a universe parameter.

(This is useful when making new declarations.)
-/
/-- `mk_local n` creates a dummy local variable with name `n`.
The type of this local constant is a constant with name `n`, so it is very unlikely to be
a meaningful expression. -/
/-- `mk_psigma [x,y,z]`, with `[x,y,z]` list of local constants of types `x : tx`,
`y : ty x` and `z : tz x y`, creates an expression of sigma type:
`⟨x,y,z⟩ : Σ' (x : tx) (y : ty x), tz x y`.
-/
/--
Update the type of a local constant or metavariable. For local constants and
metavariables obtained via, for example, `tactic.get_local`, the type stored in
the expression is not necessarily the same as the type returned by `infer_type`.
This tactic, given a local constant or metavariable, updates the stored type to
match the output of `infer_type`. If the input is not a local constant or
metavariable, `update_type` does nothing.
-/
/-- `elim_gen_prod n e _ ns` with `e` an expression of type `psigma _`, applies `cases` on `e` `n`
times and uses `ns` to name the resulting variables. Returns a triple: list of new variables,
remaining term and unused variable names.
-/
/-- `elim_gen_sum n e` applies cases on `e` `n` times. `e` is assumed to be a local constant whose
type is a (nested) sum `⊕`. Returns the list of local constants representing the components of `e`.
-/
/-- Given `elab_def`, a tactic to solve the current goal,
`extract_def n trusted elab_def` will create an auxiliary definition named `n` and use it
to close the goal. If `trusted` is false, it will be a meta definition. -/
/-- Attempts to close the goal with `dec_trivial`. -/
/-- Runs a tactic for a result, reverting the state after completion. -/
/-- Runs a tactic for a result, reverting the state after completion or error. -/
/-- Repeat a tactic at least once, calling it recursively on all subgoals,
until it fails. This tactic fails if the first invocation fails. -/
/-- `iterate_range m n t`: Repeat the given tactic at least `m` times and
at most `n` times or until `t` fails. Fails if `t` does not run at least `m` times. -/
/--
Given a tactic `tac` that takes an expression
and returns a new expression and a proof of equality,
use that tactic to change the type of the hypotheses listed in `hs`,
as well as the goal if `tgt = tt`.

Returns `tt` if any types were successfully changed.
-/
/-- `revert_after e` reverts all local constants after local constant `e`. -/
/-- `revert_target_deps` reverts all local constants on which the target depends (recursively).
  Returns the number of local constants that have been reverted. -/
/-- `generalize' e n` generalizes the target with respect to `e`. It creates a new local constant
with name `n` of the same type as `e` and replaces all occurrences of `e` by `n`.

`generalize'` is similar to `generalize` but also succeeds when `e` does not occur in the
goal, in which case it just calls `assert`.
In contrast to `generalize` it already introduces the generalized variable. -/
/--
`intron_no_renames n` calls `intro` `n` times, using the pretty-printing name
provided by the binder to name the new local constant.
Unlike `intron`, it does not rename introduced constants if the names shadow existing constants.
-/
/-!
### Various tactics related to local definitions (local constants of the form `x : α := t`)

We call `t` the value of `x`.
-/

/-- `local_def_value e` returns the value of the expression `e`, assuming that `e` has been defined
  locally using a `let` expression. Otherwise it fails. -/
/-- `is_local_def e` succeeds when `e` is a local definition (a local constant of the form
`e : α := t`) and otherwise fails. -/
/-- like `split_on_p p xs`, `partition_local_deps_aux vs xs acc` searches for matches in `xs`
(using membership to `vs` instead of a predicate) and breaks `xs` when matches are found.
whereas `split_on_p p xs` removes the matches, `partition_local_deps_aux vs xs acc` includes
them in the following partition. Also, `partition_local_deps_aux vs xs acc` discards the partition
running up to the first match. -/
/-- `partition_local_deps vs`, with `vs` a list of local constants,
reorders `vs` in the order they appear in the local context together
with the variables that follow them. If local context is `[a,b,c,d,e,f]`,
and that we call `partition_local_deps [d,b]`, we get `[[d,e,f], [b,c]]`.
The head of each list is one of the variables given as a parameter. -/
/-- `clear_value [e₀, e₁, e₂, ...]` clears the body of the local definitions `e₀`, `e₁`, `e₂`, ...
changing them into regular hypotheses. A hypothesis `e : α := t` is changed to `e : α`. The order of
locals `e₀`, `e₁`, `e₂` does not matter as a permutation will be chosen so as to preserve type
correctness. This tactic is called `clearbody` in Coq. -/
/--
`context_has_local_def` is true iff there is at least one local definition in
the context.
-/
/--
`context_upto_hyp_has_local_def h` is true iff any of the hypotheses in the
context up to and including `h` is a local definition.
-/
/-- A variant of `simplify_bottom_up`. Given a tactic `post` for rewriting subexpressions,
`simp_bottom_up post e` tries to rewrite `e` starting at the leaf nodes. Returns the resulting
expression and a proof of equality. -/
/-- Caches unary type classes on a type `α : Type.{univ}`. -/
/-- Creates an `instance_cache` for the type `α`. -/
namespace instance_cache


/-- If `n` is the name of a type class with one parameter, `get c n` tries to find an instance of
`n c.α` by checking the cache `c`. If there is no entry in the cache, it tries to find the instance
via type class resolution, and updates the cache. -/
/-- If `e` is a `pi` expression that binds an instance-implicit variable of type `n`,
`append_typeclasses e c l` searches `c` for an instance `p` of type `n` and returns `p :: l`. -/
/-- Creates the application `n c.α p l`, where `p` is a type class instance found in the cache `c`.
-/
/-- `c.of_nat n` creates the `c.α`-valued numeral expression corresponding to `n`. -/
/-- `c.of_int n` creates the `c.α`-valued numeral expression corresponding to `n`.
The output is either a numeral or the negation of a numeral. -/
end instance_cache


/-- A variation on `assert` where a (possibly incomplete)
proof of the assertion is provided as a parameter.

``(h,gs) ← local_proof `h p tac`` creates a local `h : p` and
use `tac` to (partially) construct a proof for it. `gs` is the
list of remaining goals in the proof of `h`.

The benefits over assert are:
- unlike with ``h ← assert `h p, tac`` , `h` cannot be used by `tac`;
- when `tac` does not complete the proof of `h`, returning the list
  of goals allows one to write a tactic using `h` and with the confidence
  that a proof will not boil over to goals left over from the proof of `h`,
  unlike what would be the case when using `tactic.swap`.
-/
/-- `var_names e` returns a list of the unique names of the initial pi bindings in `e`. -/
/-- When `struct_n` is the name of a structure type,
`subobject_names struct_n` returns two lists of names `(instances, fields)`.
The names in `instances` are the projections from `struct_n` to the structures that it extends
(assuming it was defined with `old_structure_cmd false`).
The names in `fields` are the standard fields of `struct_n`. -/
/-- `expanded_field_list struct_n` produces a list of the names of the fields of the structure
named `struct_n`. These are returned as pairs of names `(prefix, name)`, where the full name
of the projection is `prefix.name`.

`struct_n` cannot be a synonym for a `structure`, it must be itself a `structure` -/
/--
Return a list of all type classes which can be instantiated
for the given expression.
-/
/--
Finds an instance of an implication `cond → tgt`.
Returns a pair of a local constant `e` of type `cond`, and an instance of `tgt` that can mention
`e`. The local constant `e` is added as an hypothesis to the tactic state, but should not be used,
since it has been "proven" by a metavariable.
-/
/-- Create a list of `n` fresh metavariables. -/
/-- Returns the only goal, or fails if there isn't just one goal. -/
/-- `iterate_at_most_on_all_goals n t`: repeat the given tactic at most `n` times on all goals,
or until it fails. Always succeeds. -/
/-- `iterate_at_most_on_subgoals n t`: repeat the tactic `t` at most `n` times on the first
goal and on all subgoals thus produced, or until it fails. Fails iff `t` fails on
current goal. -/
/-- This makes sure that the execution of the tactic does not change the tactic state.
This can be helpful while using rewrite, apply, or expr munging.
Remember to instantiate your metavariables before you're done! -/
/--
`apply_list l`, for `l : list (tactic expr)`,
tries to apply the lemmas generated by the tactics in `l` on the first goal, and
fail if none succeeds.
-/
/--
Constructs a list of `tactic expr` given a list of p-expressions, as follows:
- if the p-expression is the name of a theorem, use `i_to_expr_for_apply` on it
- if the p-expression is a user attribute, add all the theorems with this attribute
  to the list.

We need to return a list of `tactic expr`, rather than just `expr`, because these expressions
will be repeatedly applied against goals, and we need to ensure that metavariables don't get stuck.
-/
/--`apply_rules hs n`: apply the list of rules `hs` (given as pexpr) and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times.

Unlike `solve_by_elim`, `apply_rules` does not do any backtracking, and just greedily applies
a lemma from the list until it can't.
 -/
/-- `replace h p` elaborates the pexpr `p`, clears the existing hypothesis named `h` from the local
context, and adds a new hypothesis named `h`. The type of this hypothesis is the type of `p`.
Fails if there is nothing named `h` in the local context. -/
/-- Auxiliary function for `iff_mp` and `iff_mpr`. Takes a name, which should be either `` `iff.mp``
or `` `iff.mpr``. If the passed expression is an iterated function type eventually producing an
`iff`, returns an expression with the `iff` converted to either the forwards or backwards
implication, as requested. -/
/-- `iff_mp_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., A → B`. -/
/-- `iff_mpr_core e ty` assumes that `ty` is the type of `e`.
If `ty` has the shape `Π ..., A ↔ B`, returns an expression whose type is `Π ..., B → A`. -/
/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the forward implication. -/
/-- Given an expression whose type is (a possibly iterated function producing) an `iff`,
create the expression which is the reverse implication. -/
/--
Attempts to apply `e`, and if that fails, if `e` is an `iff`,
try applying both directions separately.
-/
/--
Configuration options for `apply_any`:
* `use_symmetry`: if `apply_any` fails to apply any lemma, call `symmetry` and try again.
* `use_exfalso`: if `apply_any` fails to apply any lemma, call `exfalso` and try again.
* `apply`: specify an alternative to `tactic.apply`; usually `apply := tactic.eapply`.
-/
/--
This is a version of `apply_any` that takes a list of `tactic expr`s instead of `expr`s,
and evaluates these as thunks before trying to apply them.

We need to do this to avoid metavariables getting stuck during subsequent rounds of `apply`.
-/
/--
`apply_any lemmas` tries to apply one of the list `lemmas` to the current goal.

`apply_any lemmas opt` allows control over how lemmas are applied.
`opt` has fields:
* `use_symmetry`: if no lemma applies, call `symmetry` and try again. (Defaults to `tt`.)
* `use_exfalso`: if no lemma applies, call `exfalso` and try again. (Defaults to `tt`.)
* `apply`: use a tactic other than `tactic.apply` (e.g. `tactic.fapply` or `tactic.eapply`).

`apply_any lemmas tac` calls the tactic `tac` after a successful application.
Defaults to `skip`. This is used, for example, by `solve_by_elim` to arrange
recursive invocations of `apply_any`.
-/
/-- Try to apply a hypothesis from the local context to the goal. -/
/-- `change_core e none` is equivalent to `change e`. It tries to change the goal to `e` and fails
if this is not a definitional equality.

`change_core e (some h)` assumes `h` is a local constant, and tries to change the type of `h` to `e`
by reverting `h`, changing the goal, and reintroducing hypotheses. -/
/--
`change_with_at olde newe hyp` replaces occurences of `olde` with `newe` at hypothesis `hyp`,
assuming `olde` and `newe` are defeq when elaborated.
-/
/-- Returns a list of all metavariables in the current partial proof. This can differ from
the list of goals, since the goals can be manually edited. -/
/--
`sorry_if_contains_sorry` will solve any goal already containing `sorry` in its type with `sorry`,
and fail otherwise.
-/
/-- Fail if the target contains a metavariable. -/
/-- Succeeds only if the current goal is a proposition. -/
/-- Succeeds only if we can construct an instance showing the
  current goal is a subsingleton type. -/
/--
Succeeds only if the current goal is "terminal",
in the sense that no other goals depend on it
(except possibly through shared metavariables; see `independent_goal`).
-/
/--
Succeeds only if the current goal is "independent", in the sense
that no other goals depend on it, even through shared meta-variables.
-/
/-- `triv'` tries to close the first goal with the proof `trivial : true`. Unlike `triv`,
it only unfolds reducible definitions, so it sometimes fails faster. -/
/-- Apply a tactic as many times as possible, collecting the results in a list.
Fail if the tactic does not succeed at least once. -/
/-- Introduces one or more variables and returns the new local constants.
Fails if `intro` cannot be applied. -/
/-- Run a tactic "under binders", by running `intros` before, and `revert` afterwards. -/
namespace interactive


/-- Run a tactic "under binders", by running `intros` before, and `revert` afterwards. -/
end interactive


/-- `successes` invokes each tactic in turn, returning the list of successful results. -/
/--
Try all the tactics in a list, each time starting at the original `tactic_state`,
returning the list of successful results,
and reverting to the original `tactic_state`.
-/
-- Note this is not the same as `successes`, which keeps track of the evolving `tactic_state`.

/--
Try all the tactics in a list, each time starting at the original `tactic_state`,
returning the list of successful results sorted by
the value produced by a subsequent execution of the `sort_by` tactic,
and reverting to the original `tactic_state`.
-/
/-- Return target after instantiating metavars and whnf. -/
/--
Just like `split`, `fsplit` applies the constructor when the type of the target is
an inductive data type with one constructor.
However it does not reorder goals or invoke `auto_param` tactics.
-/
-- FIXME check if we can remove `auto_param := ff`

/-- Calls `injection` on each hypothesis, and then, for each hypothesis on which `injection`
succeeds, clears the old hypothesis. -/
/-- Calls `cases` on every local hypothesis, succeeding if
it succeeds on at least one hypothesis. -/
/--
`note_anon t v`, given a proof `v : t`,
adds `h : t` to the current context, where the name `h` is fresh.

`note_anon none v` will infer the type `t` from `v`.
-/
-- While `note` provides a default value for `t`, it doesn't seem this could ever be used.

/-- `find_local t` returns a local constant with type t, or fails if none exists. -/
/-- `dependent_pose_core l`: introduce dependent hypotheses, where the proofs depend on the values
of the previous local constants. `l` is a list of local constants and their values. -/
/--
Instantiates metavariables that appear in the current goal.
-/
/--
Instantiates metavariables in all goals.
-/
/-- Protect the declaration `n` -/
end tactic


namespace lean.parser


/-- `emit_command_here str` behaves as if the string `str` were placed as a user command at the
current line. -/
/-- Inner recursion for `emit_code_here`. -/
/-- `emit_code_here str` behaves as if the string `str` were placed at the current location in
source code. -/
/-- `run_parser p` is like `run_cmd` but for the parser monad. It executes parser `p` at the
top level, giving access to operations like `emit_code_here`. -/
/-- `get_current_namespace` returns the current namespace (it could be `name.anonymous`).

This function deserves a C++ implementation in core lean, and will fail if it is not called from
the body of a command (i.e. anywhere else that the `lean.parser` monad can be invoked). -/
/-- `get_variables` returns a list of existing variable names, along with their types and binder
info. -/
/-- `get_included_variables` returns those variables `v` returned by `get_variables` which have been
"included" by an `include v` statement and are not (yet) `omit`ed. -/
/-- From the `lean.parser` monad, synthesize a `tactic_state` which includes all of the local
variables referenced in `es : list pexpr`, and those variables which have been `include`ed in the
local context---precisely those variables which would be ambiently accessible if we were in a
tactic-mode block where the goals had types `es.mmap to_expr`, for example.

Returns a new `ts : tactic_state` with these local variables added, and
`mappings : list (expr × expr)`, for which pairs `(var, hyp)` correspond to an existing variable
`var` and the local hypothesis `hyp` which was added to the tactic state `ts` as a result. -/
end lean.parser


namespace tactic


/--
Hole command used to fill in a structure's field when specifying an instance.

In the following:

```lean
instance : monad id :=
{! !}
```

invoking the hole command "Instance Stub" ("Generate a skeleton for the structure under
construction.") produces:

```lean
instance : monad id :=
{ map := _,
  map_const := _,
  pure := _,
  seq := _,
  seq_left := _,
  seq_right := _,
  bind := _ }
```
-/
/-- Like `resolve_name` except when the list of goals is
empty. In that situation `resolve_name` fails whereas
`resolve_name'` simply proceeds on a dummy goal -/
/-- Strips unnecessary prefixes from a name, e.g. if a namespace is open. -/
/-- Used to format return strings for the hole commands `match_stub` and `eqn_stub`. -/
/--
Hole command used to generate a `match` expression.

In the following:

```lean
meta def foo (e : expr) : tactic unit :=
{! e !}
```

invoking hole command "Match Stub" ("Generate a list of equations for a `match` expression")
produces:

```lean
meta def foo (e : expr) : tactic unit :=
match e with
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
end
```
-/
/--
Invoking hole command "Equations Stub" ("Generate a list of equations for a recursive definition")
in the following:

```lean
meta def foo : {! expr → tactic unit !} -- `:=` is omitted
```

produces:

```lean
meta def foo : expr → tactic unit
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

A similar result can be obtained by invoking "Equations Stub" on the following:

```lean
meta def foo : expr → tactic unit := -- do not forget to write `:=`!!
{! !}
```

```lean
meta def foo : expr → tactic unit := -- don't forget to erase `:=`!!
| (expr.var a) := _
| (expr.sort a) := _
| (expr.const a a_1) := _
| (expr.mvar a a_1 a_2) := _
| (expr.local_const a a_1 a_2 a_3) := _
| (expr.app a a_1) := _
| (expr.lam a a_1 a_2 a_3) := _
| (expr.pi a a_1 a_2 a_3) := _
| (expr.elet a a_1 a_2 a_3) := _
| (expr.macro a a_1) := _
```

-/
/--
This command lists the constructors that can be used to satisfy the expected type.

Invoking "List Constructors" ("Show the list of constructors of the expected type")
in the following hole:

```lean
def foo : ℤ ⊕ ℕ :=
{! !}
```

produces:

```lean
def foo : ℤ ⊕ ℕ :=
{! sum.inl, sum.inr !}
```

and will display:

```lean
sum.inl : ℤ → ℤ ⊕ ℕ

sum.inr : ℕ → ℤ ⊕ ℕ
```

-/
/-- Makes the declaration `classical.prop_decidable` available to type class inference.
This asserts that all propositions are decidable, but does not have computational content. -/
/-- `mk_comp v e` checks whether `e` is a sequence of nested applications `f (g (h v))`, and if so,
returns the expression `f ∘ g ∘ h`. -/
/-- Given two expressions `e₀` and `e₁`, return the expression `` `(%%e₀ ↔ %%e₁)``. -/
/--
From a lemma of the shape `∀ x, f (g x) = h x`
derive an auxiliary lemma of the form `f ∘ g = h`
for reasoning about higher-order functions.
-/
/-- A user attribute that applies to lemmas of the shape `∀ x, f (g x) = h x`.
It derives an auxiliary lemma of the form `f ∘ g = h` for reasoning about higher-order functions.
-/
@[simp] theorem Mathlib.is_lawful_applicative.map_comp_pure {f : Type l_2 → Type l_1} [Applicative f] [c : is_lawful_applicative f] {α : Type l_2} {β : Type l_2} (g : α → β) : Functor.map g ∘ pure = pure ∘ g :=
  funext fun (x : α) => map_pure g x

/--
Copies a definition into the `tactic.interactive` namespace to make it usable
in proof scripts. It allows one to write

```lean
@[interactive]
meta def my_tactic := ...
```

instead of

```lean
meta def my_tactic := ...

run_cmd add_interactive [``my_tactic]
```
-/
/--
Use `refine` to partially discharge the goal,
or call `fconstructor` and try again.
-/
/-- Similar to `existsi`, `use l` will use entries in `l` to instantiate existential obligations
at the beginning of a target. Unlike `existsi`, the pexprs in `l` are elaborated with respect to
the expected type.

```lean
example : ∃ x : ℤ, x = x :=
by tactic.use ``(42)
```

See the doc string for `tactic.interactive.use` for more information.
 -/
/-- `clear_aux_decl_aux l` clears all expressions in `l` that represent aux decls from the
local context. -/
/-- `clear_aux_decl` clears all expressions from the local context that represent aux decls. -/
/-- `apply_at_aux e et [] h ht` (with `et` the type of `e` and `ht` the type of `h`)
finds a list of expressions `vs` and returns `(e.mk_args (vs ++ [h]), vs)`. -/
/-- `apply_at e h` applies implication `e` on hypothesis `h` and replaces `h` with the result. -/
/-- `symmetry_hyp h` applies `symmetry` on hypothesis `h`. -/
/-- `setup_tactic_parser` is a user command that opens the namespaces used in writing
interactive tactics, and declares the local postfix notation `?` for `optional` and `*` for `many`.
It does *not* use the `namespace` command, so it will typically be used after
`namespace tactic.interactive`.
-/
/-- `finally tac finalizer` runs `tac` first, then runs `finalizer` even if
`tac` fails. `finally tac finalizer` fails if either `tac` or `finalizer` fails. -/
/--
`on_exception handler tac` runs `tac` first, and then runs `handler` only if `tac` failed.
-/
/-- `decorate_error add_msg tac` prepends `add_msg` to an exception produced by `tac` -/
/-- Applies tactic `t`. If it succeeds, revert the state, and return the value. If it fails,
  returns the error message. -/
/-- Applies tactic `t`. If it succeeds, return the value. If it fails, returns the error message. -/
/-- This tactic succeeds if `t` succeeds or fails with message `msg` such that `p msg` is `tt`.
-/
/-- `trace_error msg t` executes the tactic `t`. If `t` fails, traces `msg` and the failure message
of `t`. -/
/--
``trace_if_enabled `n msg`` traces the message `msg`
only if tracing is enabled for the name `n`.

Create new names registered for tracing with `declare_trace n`.
Then use `set_option trace.n true/false` to enable or disable tracing for `n`.
-/
/--
``trace_state_if_enabled `n msg`` prints the tactic state,
preceded by the optional string `msg`,
only if tracing is enabled for the name `n`.
-/
/--
This combinator is for testing purposes. It succeeds if `t` fails with message `msg`,
and fails otherwise.
-/
/--
Construct a `Try this: refine ...` or `Try this: exact ...` string which would construct `g`.
-/
/-- `with_local_goals gs tac` runs `tac` on the goals `gs` and then restores the
initial goals and returns the goals `tac` ended on. -/
/-- like `with_local_goals` but discards the resulting goals -/
/-- Representation of a proof goal that lends itself to comparison. The
following goal:

```lean
l₀ : T,
l₁ : T
⊢ ∀ v : T, foo
```

is represented as

```
(2, ∀ l₀ l₁ v : T, foo)
```

The number 2 indicates that first the two bound variables of the
`∀` are actually local constant. Comparing two such goals with `=`
rather than `=ₐ` or `is_def_eq` tells us that proof script should
not see the difference between the two.
 -/
/-- proof state made of multiple `goal` meant for comparing
the result of running different tactics -/
/-- create a `packaged_goal` corresponding to the current goal -/
/-- `goal_of_mvar g`, with `g` a meta variable, creates a
`packaged_goal` corresponding to `g` interpretted as a proof goal -/
/-- `get_proof_state` lists the user visible goal for each goal
of the current state and for each goal, abstracts all of the
meta variables of the other gaols.

This produces a list of goals in the form of `ℕ × expr` where
the `expr` encodes the following proof state:

```lean
2 goals
l₁ : t₁,
l₂ : t₂,
l₃ : t₃
⊢ tgt₁

⊢ tgt₂
```

as

```lean
[ (3, ∀ (mv : tgt₁) (mv : tgt₂) (l₁ : t₁) (l₂ : t₂) (l₃ : t₃), tgt₁),
  (0, ∀ (mv : tgt₁) (mv : tgt₂), tgt₂) ]
```

with 2 goals, the first 2 bound variables encode the meta variable
of all the goals, the next 3 (in the first goal) and 0 (in the second goal)
are the local constants.

This representation allows us to compare goals and proof states while
ignoring information like the unique name of local constants and
the equality or difference of meta variables that encode the same goal.
-/
/--
Run `tac` in a disposable proof state and return the state.
See `proof_state`, `goal` and `get_proof_state`.
-/
/-- A type alias for `tactic format`, standing for "pretty print format". -/
/-- `mk` lifts `fmt : format` to the tactic monad (`pformat`). -/
/-- an alias for `pp`. -/
/-- See `format!` in `init/meta/interactive_base.lean`.

The main differences are that `pp` is called instead of `to_fmt` and that we can use
arguments of type `tactic α` in the quotations.

Now, consider the following:
```lean
e ← to_expr ``(3 + 7),
trace format!"{e}"  -- outputs `has_add.add.{0} nat nat.has_add
                    -- (bit1.{0} nat nat.has_one nat.has_add (has_one.one.{0} nat nat.has_one)) ...`
trace pformat!"{e}" -- outputs `3 + 7`
```

The difference is significant. And now, the following is expressible:

```lean
e ← to_expr ``(3 + 7),
trace pformat!"{e} : {infer_type e}" -- outputs `3 + 7 : ℕ`
```

See also: `trace!` and `fail!`
-/
/--
The combination of `pformat` and `fail`.
-/
/--
The combination of `pformat` and `trace`.
-/
/-- A hackish way to get the `src` directory of mathlib. -/
/-- Checks whether a declaration with the given name is declared in mathlib.
If you want to run this tactic many times, you should use `environment.is_prefix_of_file` instead,
since it is expensive to execute `get_mathlib_dir` many times. -/
/--
Runs a tactic by name.
If it is a `tactic string`, return whatever string it returns.
If it is a `tactic unit`, return the name.
(This is mostly used in invoking "self-reporting tactics", e.g. by `tidy` and `hint`.)
-/
/-- auxiliary function for `apply_under_n_pis` -/
/--
Assumes `pi_expr` is of the form `Π x1 ... xn xn+1..., _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
/--
Assumes `pi_expr` is of the form `Π x1 ... xn, _`.
Creates a pexpr of the form `Π x1 ... xn, func (arg x1 ... xn)`.
All arguments (implicit and explicit) to `arg` should be supplied. -/
/--
If `func` is a `pexpr` representing a function that takes an argument `a`,
`get_pexpr_arg_arity_with_tgt func tgt` returns the arity of `a`.
When `tgt` is a `pi` expr, `func` is elaborated in a context
with the domain of `tgt`.

Examples:
* ```get_pexpr_arg_arity ``(ring) `(true)``` returns 0, since `ring` takes one non-function
  argument.
* ```get_pexpr_arg_arity_with_tgt ``(monad) `(true)``` returns 1, since `monad` takes one argument
  of type `α → α`.
* ```get_pexpr_arg_arity_with_tgt ``(module R) `(Π (R : Type), comm_ring R → true)``` returns 0
-/
/-- `find_private_decl n none` finds a private declaration named `n` in any of the imported files.

`find_private_decl n (some m)` finds a private declaration named `n` in the same file where a
declaration named `m` can be found. -/
/-- `import_private foo from bar` finds a private declaration `foo` in the same file as `bar`
and creates a local notation to refer to it.

`import_private foo` looks for `foo` in all imported files.

When possible, make `foo` non-private rather than using this feature.
 -/
/--
The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.

This command is preferred to using ``run_cmd mk_simp_attr `simp_name`` since it adds a doc string
to the attribute that is defined. If you need to create a simp set in a file where this command is
not available, you should use
```lean
run_cmd mk_simp_attr `simp_name
run_cmd add_doc_string `simp_attr.simp_name "Description of the simp set here"
```
-/
