/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.type_context
import Mathlib.Lean3Lib.init.meta.rewrite_tactic
import Mathlib.Lean3Lib.init.meta.simp_tactic
import Mathlib.Lean3Lib.init.meta.smt.congruence_closure
import Mathlib.Lean3Lib.init.control.combinators
import Mathlib.Lean3Lib.init.meta.interactive_base
import Mathlib.Lean3Lib.init.meta.derive
import Mathlib.Lean3Lib.init.meta.match_tactic
import Mathlib.Lean3Lib.init.meta.congr_tactic
import Mathlib.Lean3Lib.init.meta.case_tag
 

universes l u v 

namespace Mathlib

namespace tactic


/- allows metavars -/

/- allow metavars and no subgoals -/

/- doesn't allows metavars -/

/- Auxiliary version of i_to_expr for apply-like tactics.
   This is a workaround for comment
      https://github.com/leanprover/lean/issues/1342#issuecomment-307912291
   at issue #1342.

   In interactive mode, given a tactic

        apply f

   we want the apply tactic to create all metavariables. The following
   definition will return `@f` for `f`. That is, it will **not** create
   metavariables for implicit arguments.

   Before we added `i_to_expr_for_apply`, the tactic

       apply le_antisymm

   would first elaborate `le_antisymm`, and create

       @le_antisymm ?m_1 ?m_2 ?m_3 ?m_4

   The type class resolution problem
        ?m_2 : weak_order ?m_1
   by the elaborator since ?m_1 is not assigned yet, and the problem is
   discarded.

   Then, we would invoke `apply_core`, which would create two
   new metavariables for the explicit arguments, and try to unify the resulting
   type with the current target. After the unification,
   the metavariables ?m_1, ?m_3 and ?m_4 are assigned, but we lost
   the information about the pending type class resolution problem.

   With `i_to_expr_for_apply`, `le_antisymm` is elaborate into `@le_antisymm`,
   the apply_core tactic creates all metavariables, and solves the ones that
   can be solved by type class resolution.

   Another possible fix: we modify the elaborator to return pending
   type class resolution problems, and store them in the tactic_state.
-/

namespace interactive


/--
itactic: parse a nested "interactive" tactic. That is, parse
  `{` tactic `}`
-/
/--
If the current goal is a Pi/forall `??? x : t, u` (resp. `let x := t in u`) then `intro` puts `x : t` (resp. `x := t`) in the local context. The new subgoal target is `u`.

If the goal is an arrow `t ??? u`, then it puts `h : t` in the local context and the new goal target is `u`.

If the goal is neither a Pi/forall nor begins with a let binder, the tactic `intro` applies the tactic `whnf` until an introduction can be applied or the goal is not head reducible. In the latter case, the tactic fails.
-/
/--
Similar to `intro` tactic. The tactic `intros` will keep introducing new hypotheses until the goal target is not a Pi/forall or let binder.

The variant `intros h??? ... h???` introduces `n` new hypotheses using the given identifiers to name them.
-/
/--
The tactic `introv` allows the user to automatically introduce the variables of a theorem and explicitly name the hypotheses involved. The given names are used to name non-dependent hypotheses.

Examples:
```
example : ??? a b : nat, a = b ??? b = a :=
begin
  introv h,
  exact h.symm
end
```
The state after `introv h` is
```
a b : ???,
h : a = b
??? b = a
```

```
example : ??? a b : nat, a = b ??? ??? c, b = c ??? a = c :=
begin
  introv h??? h???,
  exact h???.trans h???
end
```
The state after `introv h??? h???` is
```
a b : ???,
h??? : a = b,
c : ???,
h??? : b = c
??? a = c
```
-/
/-- Parse a current name and new name for `rename`. -/
/-- Parse the arguments of `rename`. -/
/--
Rename one or more local hypotheses. The renamings are given as follows:

```
rename x y             -- rename x to y
rename x ??? y           -- ditto
rename [x y, a b]      -- rename x to y and a to b
rename [x ??? y, a ??? b]  -- ditto
```

Note that if there are multiple hypotheses called `x` in the context, then
`rename x y` will rename *all* of them. If you want to rename only one, use
`dedup` first.
-/
/--
The `apply` tactic tries to match the current goal against the conclusion of the type of term. The argument term should be a term well-formed in the local context of the main goal. If it succeeds, then the tactic returns as many subgoals as the number of premises that have not been fixed by type inference or type class resolution. Non-dependent premises are added before dependent ones.

The `apply` tactic uses higher-order pattern matching, type class resolution, and first-order unification with dependent types.
-/
/--
Similar to the `apply` tactic, but does not reorder goals.
-/
/--
Similar to the `apply` tactic, but only creates subgoals for non-dependent premises that have not been fixed by type inference or type class resolution.
-/
/--
Similar to the `apply` tactic, but allows the user to provide a `apply_cfg` configuration object.
-/
/--
Similar to the `apply` tactic, but uses matching instead of unification.
`apply_match t` is equivalent to `apply_with t {unify := ff}`
-/
/--
This tactic tries to close the main goal `... ??? t` by generating a term of type `t` using type class resolution.
-/
/--
This tactic behaves like `exact`, but with a big difference: the user can put underscores `_` in the expression as placeholders for holes that need to be filled, and `refine` will generate as many subgoals as there are holes.

Note that some holes may be implicit. The type of each hole must either be synthesized by the system or declared by an explicit type ascription like `(_ : nat ??? Prop)`.
-/
/--
This tactic looks in the local context for a hypothesis whose type is equal to the goal target. If it finds one, it uses it to prove the goal, and otherwise it fails.
-/
/-- Try to apply `assumption` to all goals. -/
/--
`change u` replaces the target `t` of the main goal to `u` provided that `t` is well formed with respect to the local context of the main goal and `t` and `u` are definitionally equal.

`change u at h` will change a local hypothesis to `u`.

`change t with u at h1 h2 ...` will replace `t` with `u` in all the supplied hypotheses (or `*`), or in the goal if no `at` clause is specified, provided that `t` and `u` are definitionally equal.
-/
/--
This tactic provides an exact proof term to solve the main goal. If `t` is the goal and `p` is a term of type `u` then `exact p` succeeds if and only if `t` and `u` can be unified.
-/
/--
Like `exact`, but takes a list of terms and checks that all goals are discharged after the tactic.
-/
/--
A synonym for `exact` that allows writing `have/suffices/show ..., from ...` in tactic mode.
-/
/--
`revert h??? ... h???` applies to any goal with hypotheses `h???` ... `h???`. It moves the hypotheses and their dependencies to the target of the goal. This tactic is the inverse of `intro`.
-/
/- Version of to_expr that tries to bypass the elaborator if `p` is just a constant or local constant.
   This is not an optimization, by skipping the elaborator we make sure that no unwanted resolution is used.
   Example: the elaborator will force any unassigned ?A that must have be an instance of (has_one ?A) to nat.
   Remark: another benefit is that auxiliary temporary metavariables do not appear in error messages. -/

-- accepts the same content as `pexpr_list_or_texpr`, but with correct goal info pos annotations

/--
`rewrite e` applies identity `e` as a rewrite rule to the target of the main goal. If `e` is preceded by left arrow (`???` or `<-`), the rewrite is applied in the reverse direction. If `e` is a defined constant, then the equational lemmas associated with `e` are used. This provides a convenient way to unfold `e`.

`rewrite [e???, ..., e???]` applies the given rules sequentially.

`rewrite e at l` rewrites `e` at location(s) `l`, where `l` is either `*` or a list of hypotheses in the local context. In the latter case, a turnstile `???` or `|-` can also be used, to signify the target of the goal.
-/
/--
An abbreviation for `rewrite`.
-/
/--
`rewrite` followed by `assumption`.
-/
/--
A variant of `rewrite` that uses the unifier more aggressively, unfolding semireducible definitions.
-/
/--
An abbreviation for `erewrite`.
-/
/--
Returns the unique names of all hypotheses (local constants) in the context.
-/
/--
Returns all hypotheses (local constants) from the context except those whose
unique names are in `hyp_uids`.
-/
/--
Apply `t` to the main goal and revert any new hypothesis in the generated goals.
If `t` is a supported tactic or chain of supported tactics (e.g. `induction`,
`cases`, `apply`, `constructor`), the generated goals are also tagged with case
tags. You can then use `case` to focus such tagged goals.

Two typical uses of `with_cases`:

1. Applying a custom eliminator:

   ```
   lemma my_nat_rec :
     ??? n {P : ??? ??? Prop} (zero : P 0) (succ : ??? n, P n ??? P (n + 1)), P n := ...

   example (n : ???) : n = n :=
   begin
     with_cases { apply my_nat_rec n },
     case zero { refl },
     case succ : m ih { refl }
   end
   ```

2. Enabling the use of `case` after a chain of case-splitting tactics:

   ```
   example (n m : ???) : unit :=
   begin
     with_cases { cases n; induction m },
     case nat.zero nat.zero { exact () },
     case nat.zero nat.succ : k { exact () },
     case nat.succ nat.zero : i { exact () },
     case nat.succ nat.succ : k i ih_i { exact () }
   end
   ```
-/
/--
`generalize : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of the same type.

`generalize h : e = x` in addition registers the hypothesis `h : e = x`.
-/
/--
  Updates the tags of new subgoals produced by `cases` or `induction`. `in_tag`
  is the initial tag, i.e. the tag of the goal on which `cases`/`induction` was
  applied. `rs` should contain, for each subgoal, the constructor name
  associated with that goal and the hypotheses that were introduced.
-/
/--
Assuming `x` is a variable in the local context with an inductive type, `induction x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an inductive hypothesis is added for each recursive argument to the constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis incorporates that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `induction n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypotheses `h : P (nat.succ a)` and `ih??? : P a ??? Q a` and target `Q (nat.succ a)`. Here the names `a` and `ih???` ire chosen automatically.

`induction e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then performs induction on the resulting variable.

`induction e with y??? ... y???`, where `e` is a variable or an expression, specifies that the sequence of names `y??? ... y???` should be used for the arguments to the constructors and inductive hypotheses, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically. Note that for long sequences of names, the `case` tactic provides a more convenient naming mechanism.

`induction e using r` allows the user to specify the principle of induction that should be used. Here `r` should be a theorem whose result type must be of the form `C t`, where `C` is a bound variable and `t` is a (possibly empty) sequence of bound variables

`induction e generalizing z??? ... z???`, where `z??? ... z???` are variables in the local context, generalizes over `z??? ... z???` before applying the induction but then introduces them in each goal. In other words, the net effect is that each inductive hypothesis is generalized.

`induction h : t` will introduce an equality of the form `h : t = C x y`, asserting that the input term is equal to the current constructor case, to the context.
-/
/--
Focuses on a goal ('case') generated by `induction`, `cases` or `with_cases`.

The goal is selected by giving one or more names which must match exactly one
goal. A goal is matched if the given names are a suffix of its goal tag.
Additionally, each name in the sequence can be abbreviated to a suffix of the
corresponding name in the goal tag. Thus, a goal with tag
```
nat.zero, list.nil
```
can be selected with any of these invocations (among others):
```
case nat.zero list.nil {...}
case nat.zero nil      {...}
case zero     nil      {...}
case          nil      {...}
```

Additionally, the form
```
case C : N??? ... N??? {...}
```
can be used to rename hypotheses introduced by the preceding
`cases`/`induction`/`with_cases`, using the names `N???`. For example:
```
example (xs : list ???) : xs = xs :=
begin
  induction xs,
  case nil { reflexivity },
  case cons : x xs ih {
    -- x : ???, xs : list ???, ih : xs = xs
    reflexivity }
end
```

Note that this renaming functionality only work reliably *directly after* an
`induction`/`cases`/`with_cases`. If you need to perform additional work after
an `induction` or `cases` (e.g. introduce hypotheses in all goals), use
`with_cases`.
-/
/-
TODO `case` could be generalised to work with zero names as well. The form

  case : x y z { ... }

would select the first goal (or the first goal with a case tag), renaming
hypotheses to `x, y, z`. The renaming functionality would be available only if
the goal has a case tag.
-/

/--
Assuming `x` is a variable in the local context with an inductive type, `destruct x` splits the main goal, producing one goal for each constructor of the inductive type, in which `x` is assumed to be a general instance of that constructor. In contrast to `cases`, the local context is unchanged, i.e. no elements are reverted or introduced.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `destruct n` produces one goal with target `n = 0 ??? Q n`, and one goal with target `??? (a : ???), (?? (w : ???), n = w ??? Q n) (nat.succ a)`. Here the name `a` is chosen automatically.
-/
/--
Assuming `x` is a variable in the local context with an inductive type, `cases x` splits the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the case split affects that hypothesis as well.

For example, given `n : nat` and a goal with a hypothesis `h : P n` and target `Q n`, `cases n` produces one goal with hypothesis `h : P 0` and target `Q 0`, and one goal with hypothesis `h : P (nat.succ a)` and target `Q (nat.succ a)`. Here the name `a` is chosen automatically.

`cases e`, where `e` is an expression instead of a variable, generalizes `e` in the goal, and then cases on the resulting variable.

`cases e with y??? ... y???`, where `e` is a variable or an expression, specifies that the sequence of names `y??? ... y???` should be used for the arguments to the constructors, including implicit arguments. If the list does not include enough names for all of the arguments, additional names are generated automatically. If too many names are given, the extra ones are ignored. Underscores can be used in the list, in which case the corresponding names are generated automatically.

`cases h : e`, where `e` is a variable or an expression, performs cases on `e` as above, but also adds a hypothesis `h : e = ...` to each hypothesis, where `...` is the constructor instance for that particular case.
-/
/--
`cases_matching p` applies the `cases` tactic to a hypothesis `h : type` if `type` matches the pattern `p`.
`cases_matching [p_1, ..., p_n]` applies the `cases` tactic to a hypothesis `h : type` if `type` matches one of the given patterns.
`cases_matching* p` more efficient and compact version of `focus1 { repeat { cases_matching p } }`. It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_matching* [_ ??? _, _ ??? _]
```
-/
/-- Shorthand for `cases_matching` -/
/--
`cases_type I` applies the `cases` tactic to a hypothesis `h : (I ...)`
`cases_type I_1 ... I_n` applies the `cases` tactic to a hypothesis `h : (I_1 ...)` or ... or `h : (I_n ...)`
`cases_type* I` is shorthand for `focus1 { repeat { cases_type I } }`
`cases_type! I` only applies `cases` if the number of resulting subgoals is <= 1.

Example: The following tactic destructs all conjunctions and disjunctions in the current goal.
```
cases_type* or and
```
-/
/--
Tries to solve the current goal using a canonical proof of `true`, or the `reflexivity` tactic, or the `contradiction` tactic.
-/
/--
Closes the main goal using `sorry`.
-/
/--
Closes the main goal using `sorry`.
-/
/--
The contradiction tactic attempts to find in the current local context a hypothesis that is equivalent to an empty inductive type (e.g. `false`), a hypothesis of the form `c_1 ... = c_2 ...` where `c_1` and `c_2` are distinct constructors, or two contradictory hypotheses.
-/
/--
`iterate { t }` repeatedly applies tactic `t` until `t` fails. `iterate { t }` always succeeds.

`iterate n { t }` applies `t` `n` times.
-/
/--
`repeat { t }` applies `t` to each goal. If the application succeeds,
the tactic is applied recursively to all the generated subgoals until it eventually fails.
The recursion stops in a subgoal when the tactic has failed to make progress.
The tactic `repeat { t }` never fails.
-/
/--
`try { t }` tries to apply tactic `t`, but succeeds whether or not `t` succeeds.
-/
/--
A do-nothing tactic that always succeeds.
-/
/--
`solve1 { t }` applies the tactic `t` to the main goal and fails if it is not solved.
-/
/--
`abstract id { t }` tries to use tactic `t` to solve the main goal. If it succeeds, it abstracts the goal as an independent definition or theorem with name `id`. If `id` is omitted, a name is generated automatically.
-/
/--
`all_goals { t }` applies the tactic `t` to every goal, and succeeds if each application succeeds.
-/
/--
`any_goals { t }` applies the tactic `t` to every goal, and succeeds if at least one application succeeds.
-/
/--
`focus { t }` temporarily hides all goals other than the first, applies `t`, and then restores the other goals. It fails if there are no goals.
-/
/--
Assuming the target of the goal is a Pi or a let, `assume h : t` unifies the type of the binder with `t` and introduces it with name `h`, just like `intro h`. If `h` is absent, the tactic uses the name `this`. If `t` is omitted, it will be inferred.

`assume (h??? : t???) ... (h??? : t???)` introduces multiple hypotheses. Any of the types may be omitted, but the names must be present.
-/
/--
`have h : t := p` adds the hypothesis `h : t` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.

`have h : t` adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.

If `h` is omitted, the name `this` is used.
-/
/--
`let h : t := p` adds the hypothesis `h : t := p` to the current goal if `p` a term of type `t`. If `t` is omitted, it will be inferred.

`let h : t` adds the hypothesis `h : t := ?M` to the current goal and opens a new subgoal `?M : t`. The new subgoal becomes the main goal. If `t` is omitted, it will be replaced by a fresh metavariable.

If `h` is omitted, the name `this` is used.
-/
/--
`suffices h : t` is the same as `have h : t, tactic.swap`. In other words, it adds the hypothesis `h : t` to the current goal and opens a new subgoal with target `t`.
-/
/--
This tactic displays the current state in the tracing buffer.
-/
/--
`trace a` displays `a` in the tracing buffer.
-/
/--
`existsi e` will instantiate an existential quantifier in the target with `e` and leave the instantiated body as the new target. More generally, it applies to any inductive type with one constructor and at least two arguments, applying the constructor with `e` as the first argument and leaving the remaining arguments as goals.

`existsi [e???, ..., e???]` iteratively does the same for each expression in the list.
-/
/--
This tactic applies to a goal such that its conclusion is an inductive type (say `I`). It tries to apply each constructor of `I` until it succeeds.
-/
/--
Similar to `constructor`, but only non-dependent premises are added as new goals.
-/
/--
Applies the first constructor when the type of the target is an inductive data type with two constructors.
-/
/--
Applies the second constructor when the type of the target is an inductive data type with two constructors.
-/
/--
Applies the constructor when the type of the target is an inductive data type with one constructor.
-/
/--
Replaces the target of the main goal by `false`.
-/
/--
The `injection` tactic is based on the fact that constructors of inductive data types are injections. That means that if `c` is a constructor of an inductive datatype, and if `(c t???)` and `(c t???)` are two terms that are equal then  `t???` and `t???` are equal too.

If `q` is a proof of a statement of conclusion `t??? = t???`, then injection applies injectivity to derive the equality of all arguments of `t???` and `t???` placed in the same positions. For example, from `(a::b) = (c::d)` we derive `a=c` and `b=d`. To use this tactic `t???` and `t???` should be constructor applications of the same constructor.

Given `h : a::b = c::d`, the tactic `injection h` adds two new hypothesis with types `a = c` and `b = d` to the main goal. The tactic `injection h with h??? h???` uses the names `h???` and `h???` to name the new hypotheses.
-/
/--
`injections with h??? ... h???` iteratively applies `injection` to hypotheses using the names `h??? ... h???`.
-/
end interactive


/-- Decode a list of `simp_arg_type` into lists for each type.

  This is a backwards-compatibility version of `decode_simp_arg_list_with_symm`.
  This version fails when an argument of the form `simp_arg_type.symm_expr`
  is included, so that `simp`-like tactics that do not (yet) support backwards rewriting
  should properly report an error but function normally on other inputs.
-/
/-- Decode a list of `simp_arg_type` into lists for each type.

  This is the newer version of `decode_simp_arg_list`,
  and has a new name for backwards compatibility.
  This version indicates the direction of a `simp` lemma by including a `bool` with the `pexpr`.
-/
namespace interactive


/--
The `simp` tactic uses lemmas and hypotheses to simplify the main goal target or non-dependent hypotheses. It has many variants.

`simp` simplifies the main goal target using lemmas tagged with the attribute `[simp]`.

`simp [h??? h??? ... h???]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and the given `h???`'s, where the `h???`'s are expressions. If `h???` is preceded by left arrow (`???` or `<-`), the simplification is performed in the reverse direction. If an `h???` is a defined constant `f`, then the equational lemmas associated with `f` are used. This provides a convenient way to unfold `f`.

`simp [*]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]` and all hypotheses.

`simp *` is a shorthand for `simp [*]`.

`simp only [h??? h??? ... h???]` is like `simp [h??? h??? ... h???]` but does not use `[simp]` lemmas

`simp [-id_1, ... -id_n]` simplifies the main goal target using the lemmas tagged with the attribute `[simp]`, but removes the ones named `id???`.

`simp at h??? h??? ... h???` simplifies the non-dependent hypotheses `h??? : T???` ... `h??? : T???`. The tactic fails if the target or another hypothesis depends on one of them. The token `???` or `|-` can be added to the list to include the target.

`simp at *` simplifies all the hypotheses and the target.

`simp * at *` simplifies target and all (non-dependent propositional) hypotheses using the other hypotheses.

`simp with attr??? ... attr???` simplifies the main goal target using the lemmas tagged with any of the attributes `[attr???]`, ..., `[attr???]` or `[simp]`.
-/
/--
Just construct the simp set and trace it. Used for debugging.
-/
/--
`simp_intros h??? h??? ... h???` is similar to `intros h??? h??? ... h???` except that each hypothesis is simplified as it is introduced, and each introduced hypothesis is used to simplify later ones and the final target.

As with `simp`, a list of simplification lemmas can be provided. The modifiers `only` and `with` behave as with `simp`.
-/
/--
`dsimp` is similar to `simp`, except that it only uses definitional equalities.
-/
/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a reflexive relation, that is, a relation which has a reflexivity lemma tagged with the attribute `[refl]`. The tactic checks whether `t` and `u` are definitionally equal and then solves the goal.
-/
/--
Shorter name for the tactic `reflexivity`.
-/
/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation, that is, a relation which has a symmetry lemma tagged with the attribute `[symm]`. It replaces the target with `u ~ t`.
-/
/--
This tactic applies to a goal whose target has the form `t ~ u` where `~` is a transitive relation, that is, a relation which has a transitivity lemma tagged with the attribute `[trans]`.

`transitivity s` replaces the goal with the two subgoals `t ~ s` and `s ~ u`. If `s` is omitted, then a metavariable is used instead.
-/
/--
Proves a goal with target `s = t` when `s` and `t` are equal up to the associativity and commutativity of their binary operations.
-/
/--
An abbreviation for `ac_reflexivity`.
-/
/--
Tries to prove the main goal using congruence closure.
-/
/--
Given hypothesis `h : x = t` or `h : t = x`, where `x` is a local constant, `subst h` substitutes `x` by `t` everywhere in the main goal and then clears `h`.
-/
/--
Apply `subst` to all hypotheses of the form `h : x = t` or `h : t = x`.
-/
/--
`clear h??? ... h???` tries to clear each hypothesis `h???` from the local context.
-/
/--
Similar to `unfold`, but only uses definitional equalities.
-/
/--
Similar to `dunfold`, but performs a raw delta reduction, rather than using an equation associated with the defined constants.
-/
/--
This tactic unfolds all structure projections.
-/
end interactive


structure unfold_config 
extends simp_config
where

namespace interactive


/--
Given defined constants `e??? ... e???`, `unfold e??? ... e???` iteratively unfolds all occurrences in the target of the main goal, using equational lemmas associated with the definitions.

As with `simp`, the `at` modifier can be used to specify locations for the unfolding.
-/
/--
Similar to `unfold`, but does not iterate the unfolding.
-/
/--
If the target of the main goal is an `opt_param`, assigns the default value.
-/
/--
If the target of the main goal is an `auto_param`, executes the associated tactic.
-/
/--
Fails if the given tactic succeeds.
-/
/--
Succeeds if the given tactic fails.
-/
/--
`guard_target t` fails if the target of the main goal is not `t`.
We use this tactic for writing tests.
-/
/--
`guard_hyp h : t` fails if the hypothesis `h` does not have type `t`.
We use this tactic for writing tests.
-/
/--
`match_target t` fails if target does not match pattern `t`.
-/
/--
`by_cases p` splits the main goal into two cases, assuming `h : p` in the first branch, and
`h : ?? p` in the second branch. You can specify the name of the new hypothesis using the syntax
`by_cases h : p`.
-/
/--
Apply function extensionality and introduce new hypotheses.
The tactic `funext` will keep applying new the `funext` lemma until the goal target is not reducible to
```
  |-  ((fun x, ...) = (fun x, ...))
```
The variant `funext h??? ... h???` applies `funext` `n` times, and uses the given identifiers to name the new hypotheses.
-/
/--
If the target of the main goal is a proposition `p`, `by_contradiction` reduces the goal to proving `false` using the additional hypothesis `h : ?? p`. `by_contradiction h` can be used to name the hypothesis `h : ?? p`.

This tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.
-/
/--
If the target of the main goal is a proposition `p`, `by_contra` reduces the goal to proving `false` using the additional hypothesis `h : ?? p`. `by_contra h` can be used to name the hypothesis `h : ?? p`.

This tactic will attempt to use decidability of `p` if available, and will otherwise fall back on classical reasoning.
-/
/--
Type check the given expression, and trace its type.
-/
/--
Fail if there are unsolved goals.
-/
/--
`show t` finds the first goal whose target unifies with `t`. It makes that the main goal, performs the unification, and replaces the target with the unified version of `t`.
-/
/--
The tactic `specialize h a??? ... a???` works on local hypothesis `h`. The premises of this hypothesis, either universal quantifications or non-dependent implications, are instantiated by concrete terms coming either from arguments `a???` ... `a???`. The tactic adds a new hypothesis with the same name `h := h a??? ... a???` and tries to clear the previous one.
-/
end interactive


end tactic


/- See add_interactive -/

/--
Copy a list of meta definitions in the current namespace to tactic.interactive.

This command is useful when we want to update tactic.interactive without closing the current namespace.
-/
/--
Renames hypotheses with the same name.
-/
namespace tactic


/- Helper tactic for `mk_inj_eq -/

/- Auxiliary tactic for proving `I.C.inj_eq` lemmas.
   These lemmas are automatically generated by the equation compiler.
   Example:
   ```
   list.cons.inj_eq : forall h1 h2 t1 t2, (h1::t1 = h2::t2) = (h1 = h2 ??? t1 = t2) :=
   by mk_inj_eq
   ```
-/

end tactic


/- Define inj_eq lemmas for inductive datatypes that were declared before `mk_inj_eq` -/

theorem sum.inl.inj_eq {?? : Type u} (?? : Type v) (a??? : ??) (a??? : ??) : sum.inl a??? = sum.inl a??? = (a??? = a???) :=
  propext
    { mp := fun (h : sum.inl a??? = sum.inl a???) => sum.inl.inj h,
      mpr := fun (??? : a??? = a???) => (fun (val val_1 : ??) (e_2 : val = val_1) => congr_arg sum.inl e_2) a??? a??? ??? }

theorem sum.inr.inj_eq (?? : Type u) {?? : Type v} (b??? : ??) (b??? : ??) : sum.inr b??? = sum.inr b??? = (b??? = b???) := sorry

theorem psum.inl.inj_eq {?? : Sort u} (?? : Sort v) (a??? : ??) (a??? : ??) : psum.inl a??? = psum.inl a??? = (a??? = a???) :=
  propext
    { mp := fun (h : psum.inl a??? = psum.inl a???) => psum.inl.inj h,
      mpr := fun (??? : a??? = a???) => (fun (val val_1 : ??) (e_2 : val = val_1) => congr_arg psum.inl e_2) a??? a??? ??? }

theorem psum.inr.inj_eq (?? : Sort u) {?? : Sort v} (b??? : ??) (b??? : ??) : psum.inr b??? = psum.inr b??? = (b??? = b???) := sorry

theorem sigma.mk.inj_eq {?? : Type u} {?? : ?? ??? Type v} (a??? : ??) (b??? : ?? a???) (a??? : ??) (b??? : ?? a???) : sigma.mk a??? b??? = sigma.mk a??? b??? = (a??? = a??? ??? b??? == b???) := sorry

theorem psigma.mk.inj_eq {?? : Sort u} {?? : ?? ??? Sort v} (a??? : ??) (b??? : ?? a???) (a??? : ??) (b??? : ?? a???) : psigma.mk a??? b??? = psigma.mk a??? b??? = (a??? = a??? ??? b??? == b???) := sorry

theorem subtype.mk.inj_eq {?? : Sort u} {p : ?? ??? Prop} (a??? : ??) (h??? : p a???) (a??? : ??) (h??? : p a???) : { val := a???, property := h??? } = { val := a???, property := h??? } = (a??? = a???) := sorry

theorem option.some.inj_eq {?? : Type u} (a??? : ??) (a??? : ??) : some a??? = some a??? = (a??? = a???) :=
  propext
    { mp := fun (h : some a??? = some a???) => option.some.inj h,
      mpr := fun (??? : a??? = a???) => (fun (val val_1 : ??) (e_1 : val = val_1) => congr_arg some e_1) a??? a??? ??? }

theorem list.cons.inj_eq {?? : Type u} (h??? : ??) (t??? : List ??) (h??? : ??) (t??? : List ??) : h??? :: t??? = h??? :: t??? = (h??? = h??? ??? t??? = t???) := sorry

theorem nat.succ.inj_eq (n??? : ???) (n??? : ???) : Nat.succ n??? = Nat.succ n??? = (n??? = n???) :=
  propext
    { mp := fun (h : Nat.succ n??? = Nat.succ n???) => nat.succ.inj h,
      mpr := fun (??? : n??? = n???) => (fun (n n_1 : ???) (e_1 : n = n_1) => congr_arg Nat.succ e_1) n??? n??? ??? }

