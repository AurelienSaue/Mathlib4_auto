/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.function
import Mathlib.Lean3Lib.init.data.option.basic
import Mathlib.Lean3Lib.init.util
import Mathlib.Lean3Lib.init.control.combinators
import Mathlib.Lean3Lib.init.control.monad
import Mathlib.Lean3Lib.init.control.alternative
import Mathlib.Lean3Lib.init.control.monad_fail
import Mathlib.Lean3Lib.init.data.nat.div
import Mathlib.Lean3Lib.init.meta.exceptional
import Mathlib.Lean3Lib.init.meta.format
import Mathlib.Lean3Lib.init.meta.environment
import Mathlib.Lean3Lib.init.meta.pexpr
import Mathlib.Lean3Lib.init.data.repr
import Mathlib.Lean3Lib.init.data.string.basic
import Mathlib.Lean3Lib.init.meta.interaction_monad
import Mathlib.Lean3Lib.init.classical
import Mathlib.PostPort

universes l 

namespace Mathlib

infixl:2 " >>=[tactic] " => Mathlib.interaction_monad_bind

infixl:2 " >>[tactic] " => Mathlib.interaction_monad_seq

namespace tactic_state


/-- Format the given tactic state. If `target_lhs_only` is true and the target
    is of the form `lhs ~ rhs`, where `~` is a simplification relation,
    then only the `lhs` is displayed.

    Remark: the parameter `target_lhs_only` is a temporary hack used to implement
    the `conv` monad. It will be removed in the future. -/
/-- Format expression with respect to the main goal in the tactic state.
   If the tactic state does not contain any goals, then format expression
   using an empty local context. -/
end tactic_state


/-- `tactic` is the monad for building tactics.
    You use this to:
    - View and modify the local goals and hypotheses in the prover's state.
    - Invoke type checking and elaboration of terms.
    - View and modify the environment.
    - Build new tactics out of existing ones such as `simp` and `rewrite`.
-/
namespace tactic


end tactic


namespace tactic_result


end tactic_result


namespace interactive


/-- Typeclass for custom interaction monads, which provides
    the information required to convert an interactive-mode
    construction to a `tactic` which can actually be executed.

    Given a `[monad m]`, `execute_with` explains how to turn a `begin ... end`
    block, or a `by ...` statement into a `tactic α` which can actually be
    executed. The `inhabited` first argument facilitates the passing of an
    optional configuration parameter `config`, using the syntax:
    ```
    begin [custom_monad] with config,
        ...
    end
    ```
-/
/-- Default `executor` instance for `tactic`s themselves -/
end interactive


namespace tactic


/-- Does nothing. -/
/--
`try_core t` acts like `t`, but succeeds even if `t` fails. It returns the
result of `t` if `t` succeeded and `none` otherwise.
-/
/--
`try t` acts like `t`, but succeeds even if `t` fails.
-/
/--
`fail_if_success t` acts like `t`, but succeeds if `t` fails and fails if `t`
succeeds. Changes made by `t` to the `tactic_state` are preserved only if `t`
succeeds.
-/
/--
`success_if_fail t` acts like `t`, but succeeds if `t` fails and fails if `t`
succeeds. Changes made by `t` to the `tactic_state` are preserved only if `t`
succeeds.
-/
/--
`iterate_at_most n t` iterates `t` `n` times or until `t` fails, returning the
result of each successful iteration.
-/
/--
`iterate_at_most' n t` repeats `t` `n` times or until `t` fails.
-/
/--
`iterate_exactly n t` iterates `t` `n` times, returning the result of
each iteration. If any iteration fails, the whole tactic fails.
-/
/--
`iterate_exactly' n t` executes `t` `n` times. If any iteration fails, the whole
tactic fails.
-/
/--
`iterate t` repeats `t` 100.000 times or until `t` fails, returning the
result of each iteration.
-/
/--
`iterate' t` repeats `t` 100.000 times or until `t` fails.
-/
/-- Decorate t's exceptions with msg. -/
/-- Set the tactic_state. -/
/-- Get the tactic_state. -/
/--
`capture t` acts like `t`, but succeeds with a result containing either the returned value
or the exception.
Changes made by `t` to the `tactic_state` are preserved in both cases.

The result can be used to inspect the error message, or passed to `unwrap` to rethrow the
failure later.
-/
/--
`unwrap r` unwraps a result previously obtained using `capture`.

If the previous result was a success, this produces its wrapped value.
If the previous result was an exception, this "rethrows" the exception as if it came
from where it originated.

`do r ← capture t, unwrap r` is identical to `t`, but allows for intermediate tactics to be inserted.
-/
/--
`resume r` continues execution from a result previously obtained using `capture`.

This is like `unwrap`, but the `tactic_state` is rolled back to point of capture even upon success.
-/
end tactic


namespace tactic


/-- A parameter representing how aggressively definitions should be unfolded when trying to decide if two terms match, unify or are definitionally equal.
By default, theorem declarations are never unfolded.
- `all` will unfold everything, including macros and theorems. Except projection macros.
- `semireducible` will unfold everything except theorems and definitions tagged as irreducible.
- `instances` will unfold all class instance definitions and definitions tagged with reducible.
- `reducible` will only unfold definitions tagged with the `reducible` attribute.
- `none` will never unfold anything.
[NOTE] You are not allowed to tag a definition with more than one of `reducible`, `irreducible`, `semireducible` attributes.
[NOTE] there is a config flag `m_unfold_lemmas`that will make it unfold theorems.
 -/
inductive transparency 
where
| all : transparency
| semireducible : transparency
| instances : transparency
| reducible : transparency
| none : transparency

/-- (eval_expr α e) evaluates 'e' IF 'e' has type 'α'. -/
/-- Return the partial term/proof constructed so far. Note that the resultant expression
   may contain variables that are not declarate in the current main goal. -/
/-- Display the partial term/proof constructed so far. This tactic is *not* equivalent to
   `do { r ← result, s ← read, return (format_expr s r) }` because this one will format the result with respect
   to the current goal, and trace_result will do it with respect to the initial goal. -/
/-- Return target type of the main goal. Fail if tactic_state does not have any goal left. -/
/-- Clear the given local constant. The tactic fails if the given expression is not a local constant. -/
/-- `revert_lst : list expr → tactic nat` is the reverse of `intron`. It takes a local constant `c` and puts it back as bound by a `pi` or `elet` of the main target.
If there are other local constants that depend on `c`, these are also reverted. Because of this, the `nat` that is returned is the actual number of reverted local constants.
Example: with `x : ℕ, h : P(x) ⊢ T(x)`, `revert_lst [x]` returns `2` and produces the state ` ⊢ Π x, P(x) → T(x)`.
 -/
/-- Return `e` in weak head normal form with respect to the given transparency setting.
    If `unfold_ginductive` is `tt`, then nested and/or mutually recursive inductive datatype constructors
    and types are unfolded. Recall that nested and mutually recursive inductive datatype declarations
    are compiled into primitive datatypes accepted by the Kernel. -/
/-- (head) eta expand the given expression. `f : α → β` head-eta-expands to `λ a, f a`. If `f` isn't a function then it just returns `f`.  -/
/-- (head) beta reduction. `(λ x, B) c` reduces to `B[x/c]`. -/
/-- (head) zeta reduction. Reduction of let bindings at the head of the expression. `let x : a := b in c` reduces to `c[x/b]`. -/
/-- Zeta reduction. Reduction of let bindings. `let x : a := b in c` reduces to `c[x/b]`. -/
/-- (head) eta reduction. `(λ x, f x)` reduces to `f`. -/
/-- Succeeds if `t` and `s` can be unified using the given transparency setting. -/
/-- Similar to `unify`, but it treats metavariables as constants. -/
/-- Infer the type of the given expression.
   Remark: transparency does not affect type inference -/
/-- Get the `local_const` expr for the given `name`. -/
/-- Resolve a name using the current local context, environment, aliases, etc. -/
/-- Return the hypothesis in the main goal. Fail if tactic_state does not have any goal left. -/
/-- Get a fresh name that is guaranteed to not be in use in the local context.
    If `n` is provided and `n` is not in use, then `n` is returned.
    Otherwise a number `i` is appended to give `"n_i"`.
-/
/--  Helper tactic for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
    ```
        rel.{l_1 l_2} : Pi (α : Type.{l_1}) (β : α -> Type.{l_2}), (Pi x : α, β x) -> (Pi x : α, β x) -> , Prop
        nat     : Type
        real    : Type
        vec.{l} : Pi (α : Type l) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    ```
    then
    ```
    mk_app_core semireducible "rel" [f, g]
    ```
    returns the application
    ```
    rel.{1 2} nat (fun n : nat, vec real n) f g
    ```

    The unification constraints due to type inference are solved using the transparency `md`.
-/
/-- Similar to `mk_app`, but allows to specify which arguments are explicit/implicit.
   Example, given `(a b : nat)` then
   ```
   mk_mapp "ite" [some (a > b), none, none, some a, some b]
   ```
   returns the application
   ```
   @ite.{1} (a > b) (nat.decidable_gt a b) nat a b
   ```
-/
/-- (mk_congr_arg h₁ h₂) is a more efficient version of (mk_app `congr_arg [h₁, h₂]) -/
/-- (mk_congr_fun h₁ h₂) is a more efficient version of (mk_app `congr_fun [h₁, h₂]) -/
/-- (mk_congr h₁ h₂) is a more efficient version of (mk_app `congr [h₁, h₂]) -/
/-- (mk_eq_refl h) is a more efficient version of (mk_app `eq.refl [h]) -/
/-- (mk_eq_symm h) is a more efficient version of (mk_app `eq.symm [h]) -/
/-- (mk_eq_trans h₁ h₂) is a more efficient version of (mk_app `eq.trans [h₁, h₂]) -/
/-- (mk_eq_mp h₁ h₂) is a more efficient version of (mk_app `eq.mp [h₁, h₂]) -/
/-- (mk_eq_mpr h₁ h₂) is a more efficient version of (mk_app `eq.mpr [h₁, h₂]) -/
/- Given a local constant t, if t has type (lhs = rhs) apply substitution.
   Otherwise, try to find a local constant that has type of the form (t = t') or (t' = t).
   The tactic fails if the given expression is not a local constant. -/

/-- Close the current goal using `e`. Fail if the type of `e` is not definitionally equal to
    the target type. -/
/-- Elaborate the given quoted expression with respect to the current main goal.
    Note that this means that any implicit arguments for the given `pexpr` will be applied with fresh metavariables.
    If `allow_mvars` is tt, then metavariables are tolerated and become new goals if `subgoals` is tt. -/
/-- Return true if the given expression is a type class. -/
/-- Try to create an instance of the given type class. -/
/-- Change the target of the main goal.
   The input expression must be definitionally equal to the current target.
   If `check` is `ff`, then the tactic does not check whether `e`
   is definitionally equal to the current target. If it is not,
   then the error will only be detected by the kernel type checker. -/
/-- `assert_core H T`, adds a new goal for T, and change target to `T -> target`. -/
/-- `assertv_core H T P`, change target to (T -> target) if P has type T. -/
/-- `define_core H T`, adds a new goal for T, and change target to  `let H : T := ?M in target` in the current goal. -/
/-- `definev_core H T P`, change target to `let H : T := P in target` if P has type T. -/
/-- Rotate goals to the left. That is, `rotate_left 1` takes the main goal and puts it to the back of the subgoal list. -/
/-- Gets a list of metavariables, one for each goal. -/
/-- Replace the current list of goals with the given one. Each expr in the list should be a metavariable. Any assigned metavariables will be ignored.-/
/-- How to order the new goals made from an `apply` tactic.
Supposing we were applying `e : ∀ (a:α) (p : P(a)), Q`
- `non_dep_first` would produce goals `⊢ P(?m)`, `⊢ α`. It puts the P goal at the front because none of the arguments after `p` in `e` depend on `p`. It doesn't matter what the result `Q` depends on.
- `non_dep_only` would produce goal `⊢ P(?m)`.
- `all` would produce goals `⊢ α`, `⊢ P(?m)`.
-/
inductive new_goals 
where
| non_dep_first : new_goals
| non_dep_only : new_goals
| all : new_goals

/-- Configuration options for the `apply` tactic.
- `md` sets how aggressively definitions are unfolded.
- `new_goals` is the strategy for ordering new goals.
- `instances` if `tt`, then `apply` tries to synthesize unresolved `[...]` arguments using type class resolution.
- `auto_param` if `tt`, then `apply` tries to synthesize unresolved `(h : p . tac_id)` arguments using tactic `tac_id`.
- `opt_param` if `tt`, then `apply` tries to synthesize unresolved `(a : t := v)` arguments by setting them to `v`.
- `unify` if `tt`, then `apply` is free to assign existing metavariables in the goal when solving unification constraints.
   For example, in the goal `|- ?x < succ 0`, the tactic `apply succ_lt_succ` succeeds with the default configuration,
   but `apply_with succ_lt_succ {unify := ff}` doesn't since it would require Lean to assign `?x` to `succ ?y` where
   `?y` is a fresh metavariable.
-/
structure apply_cfg 
where
  md : transparency
  approx : Bool
  new_goals : new_goals
  instances : Bool
  auto_param : Bool
  opt_param : Bool
  unify : Bool

/-- Apply the expression `e` to the main goal, the unification is performed using the transparency mode in `cfg`.
    Supposing `e : Π (a₁:α₁) ... (aₙ:αₙ), P(a₁,...,aₙ)` and the target is `Q`, `apply` will attempt to unify `Q` with `P(?a₁,...?aₙ)`.
    All of the metavariables that are not assigned are added as new metavariables.
    If `cfg.approx` is `tt`, then fallback to first-order unification, and approximate context during unification.
    `cfg.new_goals` specifies which unassigned metavariables become new goals, and their order.
    If `cfg.instances` is `tt`, then use type class resolution to instantiate unassigned meta-variables.
    The fields `cfg.auto_param` and `cfg.opt_param` are ignored by this tactic (See `tactic.apply`).
    It returns a list of all introduced meta variables and the parameter name associated with them, even the assigned ones. -/
/- Create a fresh meta universe variable. -/

/- Create a fresh meta-variable with the given type.
   The scope of the new meta-variable is the local context of the main goal. -/

/-- Return the value assigned to the given universe meta-variable.
   Fail if argument is not an universe meta-variable or if it is not assigned. -/
/-- Return the value assigned to the given meta-variable.
   Fail if argument is not a meta-variable or if it is not assigned. -/
/-- Return true if the given meta-variable is assigned.
    Fail if argument is not a meta-variable. -/
/-- Make a name that is guaranteed to be unique. Eg `_fresh.1001.4667`. These will be different for each run of the tactic.  -/
/-- Induction on `h` using recursor `rec`, names for the new hypotheses
   are retrieved from `ns`. If `ns` does not have sufficient names, then use the internal binder names
   in the recursor.
   It returns for each new goal the name of the constructor (if `rec_name` is a builtin recursor),
   a list of new hypotheses, and a list of substitutions for hypotheses
   depending on `h`. The substitutions map internal names to their replacement terms. If the
   replacement is again a hypothesis the user name stays the same. The internal names are only valid
   in the original goal, not in the type context of the new goal.
   Remark: if `rec_name` is not a builtin recursor, we use parameter names of `rec_name` instead of
   constructor names.

   If `rec` is none, then the type of `h` is inferred, if it is of the form `C ...`, tactic uses `C.rec` -/
/-- Apply `cases_on` recursor, names for the new hypotheses are retrieved from `ns`.
   `h` must be a local constant. It returns for each new goal the name of the constructor, a list of new hypotheses, and a list of
   substitutions for hypotheses depending on `h`. The number of new goals may be smaller than the
   number of constructors. Some goals may be discarded when the indices to not match.
   See `induction` for information on the list of substitutions.

   The `cases` tactic is implemented using this one, and it relaxes the restriction of `h`.

   Note: There is one "new hypothesis" for every constructor argument. These are
   usually local constants, but due to dependent pattern matching, they can also
   be arbitrary terms. -/
/-- Similar to cases tactic, but does not revert/intro/clear hypotheses. -/
/-- Generalizes the target with respect to `e`.  -/
/-- instantiate assigned metavariables in the given expression -/
/-- Add the given declaration to the environment -/
/--
Changes the environment to the `new_env`.
The new environment does not need to be a descendant of the old one.
Use with care.
-/
/-- Changes the environment to the `new_env`. `new_env` needs to be a descendant from the current environment. -/
/-- `doc_string env d k` returns the doc string for `d` (if available) -/
/-- Set the docstring for the given declaration. -/
/--
Create an auxiliary definition with name `c` where `type` and `value` may contain local constants and
meta-variables. This function collects all dependencies (universe parameters, universe metavariables,
local constants (aka hypotheses) and metavariables).
It updates the environment in the tactic_state, and returns an expression of the form

          (c.{l_1 ... l_n} a_1 ... a_m)

where l_i's and a_j's are the collected dependencies.
-/
/-- Returns a list of all top-level (`/-! ... -/`) docstrings in the active module and imported ones.
The returned object is a list of modules, indexed by `(some filename)` for imported modules
and `none` for the active one, where each module in the list is paired with a list
of `(position_in_file, docstring)` pairs. -/
/-- Returns a list of docstrings in the active module. An entry in the list can be either:
- a top-level (`/-! ... -/`) docstring, represented as `(none, docstring)`
- a declaration-specific (`/-- ... -/`) docstring, represented as `(some decl_name, docstring)` -/
/-- Set attribute `attr_name` for constant `c_name` with the given priority.
   If the priority is none, then use default -/
/-- `unset_attribute attr_name c_name` -/
/-- `has_attribute attr_name c_name` succeeds if the declaration `decl_name`
   has the attribute `attr_name`. The result is the priority and whether or not
   the attribute is persistent. -/
/-- `copy_attribute attr_name c_name p d_name` copy attribute `attr_name` from
   `src` to `tgt` if it is defined for `src`; make it persistent if `p` is `tt`;
   if `p` is `none`, the copied attribute is made persistent iff it is persistent on `src`  -/
/-- Name of the declaration currently being elaborated. -/
/-- `save_type_info e ref` save (typeof e) at position associated with ref -/
/-- Return list of currently open namespaces -/
/-- Return tt iff `t` "occurs" in `e`. The occurrence checking is performed using
    keyed matching with the given transparency setting.

    We say `t` occurs in `e` by keyed matching iff there is a subterm `s`
    s.t. `t` and `s` have the same head, and `is_def_eq t s md`

    The main idea is to minimize the number of `is_def_eq` checks
    performed. -/
/-- Abstracts all occurrences of the term `t` in `e` using keyed matching.
    If `unify` is `ff`, then matching is used instead of unification.
    That is, metavariables occurring in `e` are not assigned. -/
/-- Blocks the execution of the current thread for at least `msecs` milliseconds.
    This tactic is used mainly for debugging purposes. -/
/-- Type check `e` with respect to the current goal.
    Fails if `e` is not type correct. -/
/-- A `tag` is a list of `names`. These are attached to goals to help tactics track them.-/
def tag  :=
  List name

