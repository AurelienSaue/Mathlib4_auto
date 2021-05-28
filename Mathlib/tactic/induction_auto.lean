/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.dependencies
import Mathlib.tactic.fresh_names
import Mathlib.tactic.generalizes
import Mathlib.tactic.has_variable_names
import Mathlib.tactic.unify_equations
import PostPort

universes l 

namespace Mathlib

/-!
# A better tactic for induction and case analysis

This module defines the tactics `tactic.interactive.induction'` and
`tactic.interactive.cases'`, which are variations on Lean's builtin `induction`
and `cases`. The primed variants feature various improvements over the builtin
tactics; in particular, they generate more human-friendly names and `induction'`
deals much better with indexed inductive types. See the tactics' documentation
for more details. We also provide corresponding non-interactive induction
tactics `tactic.eliminate_hyp` and `tactic.eliminate_expr`.

The design and implementation of these tactics is described in a
[draft paper](https://limperg.de/paper/cpp2021-induction/).
-/

namespace tactic


namespace eliminate


/-!
## Tracing

We set up two tracing functions to be used by `eliminate_hyp` and its supporting
tactics. Their output is enabled by setting `trace.eliminate_hyp` to `true`.
-/

/--
`trace_eliminate_hyp msg` traces `msg` if the option `trace.eliminate_hyp` is
`true`.
-/
/--
`trace_state_eliminate_hyp msg` traces `msg` followed by the tactic state if the
option `trace.eliminate_hyp` is `true`.
-/
/-!
## Information Gathering

We define data structures for information relevant to the induction, and
functions to collect this information for a specific goal.
-/

/--
Information about a constructor argument. E.g. given the declaration

```
induction ℕ : Type
| zero : ℕ
| suc (n : ℕ) : ℕ
```

the `zero` constructor has no arguments and the `suc` constructor has one
argument, `n`.

We record the following information:

- `aname`: the argument's name. If the argument was not explicitly named in the
  declaration, the elaborator generates a name for it.
- `type` : the argument's type.
- `dependent`: whether the argument is dependent, i.e. whether it occurs in the
  remainder of the constructor type.
- `index_occurrences`: the index arguments of the constructor's return type
  in which this argument occurs. If the constructor return type is
  `I i₀ ... iₙ` and the argument under consideration is `a`, and `a` occurs in
  `i₁` and `i₂`, then the `index_occurrences` are `1, 2`. As an additional
  requirement, for `iⱼ` to be considered an index occurrences,
  the type of `iⱼ` must match that of `a` according to
  `index_occurrence_type_match`.
- `is_recursive`: whether this is a recursive constructor argument.
-/
/--
Information about a constructor. Contains:

- `cname`: the constructor's name.
- `non_param_args`: information about the arguments of the constructor,
  excluding the arguments induced by the parameters of the inductive type.
- `num_non_param_args`: the length of `non_param_args`.
- `rec_args`: the subset of `non_param_args` which are recursive constructor
  arguments.
- `num_rec_args`: the length of `rec_args`.

For example, take the constructor
```
list.cons : ∀ {α} (x : α) (xs : list α), list α
```
`α` is a parameter of `list`, so `non_param_args` contains information about `x`
and `xs`. `rec_args` contains information about `xs`.
-/
/--
When we construct the goal for the minor premise of a given constructor, this is
the number of hypotheses we must name.
-/
/--
Information about an inductive type. Contains:

- `iname`: the type's name.
- `constructors`: information about the type's constructors.
- `num_constructors`: the length of `constructors`.
- `type`: the type's type.
- `num_param`: the type's number of parameters.
- `num_indices`: the type's number of indices.
-/
/--
Information about a major premise (i.e. the hypothesis on which we are
performing induction). Contains:

- `mpname`: the major premise's name.
- `mpexpr`: the major premise itself.
- `type`: the type of `mpexpr`.
- `args`: the arguments of the major premise. The major premise has type
  `I x₀ ... xₙ`, where `I` is an inductive type. `args` is the map
  `[0 → x₀, ..., n → xₙ]`.
-/
/--
`index_occurrence_type_match t s` is true iff `t` and `s` are definitionally
equal.
-/
-- We could extend this check to be more permissive. E.g. if a constructor

-- argument has type `list α` and the index has type `list β`, we may want to

-- consider these types sufficiently similar to inherit the name. Same (but even

-- more obvious) with `vec α n` and `vec α (n + 1)`.

/--
From the return type of a constructor `C` of an inductive type `I`, determine
the index occurrences of the constructor arguments of `C`.

Input:

- `num_params:` the number of parameters of `I`.
- `ret_type`: the return type of `C`. `e` must be of the form `I x₁ ... xₙ`.

Output: A map associating each local constant `c` that appears in any of the `xᵢ`
with the set of indexes `j` such that `c` appears in `xⱼ` and `xⱼ`'s type
matches that of `c` according to `tactic.index_occurrence_type_match`.
-/
/--
Returns true iff `arg_type` is the local constant named `type_name`
(possibly applied to some arguments). If `arg_type` is the type of an argument
of one of `type_name`'s constructors and this function returns true, then the
constructor argument is a recursive occurrence.
-/
/--
Get information about the arguments of a constructor `C` of an inductive type
`I`.

Input:

- `inductive_name`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `T`: the type of `C`.

Output: a `constructor_argument_info` structure for each argument of `C`.
-/
/--
Get information about a constructor `C` of an inductive type `I`.

Input:

- `iname`: the name of `I`.
- `num_params`: the number of parameters of `I`.
- `c` : the name of `C`.

Output:

A `constructor_info` structure for `C`.
-/
/--
Get information about an inductive type `I`, given `I`'s name.
-/
/--
Get information about a major premise. The given `expr` must be a local
hypothesis.
-/
/-!
## Constructor Argument Naming

We define the algorithm for naming constructor arguments (which is a remarkably
big part of the tactic).
-/

/--
Information used when naming a constructor argument.
-/
/--
A constructor argument naming rule takes a `constructor_argument_naming_info`
structure and returns a list of suitable names for the argument. If the rule is
not applicable to the given constructor argument, the returned list is empty.
-/
/--
Naming rule for recursive constructor arguments.
-/
/--
Naming rule for constructor arguments associated with an index.
-/
/-
Right now, this rule only triggers if the major premise arg is exactly a
local const. We could consider a more permissive rule where the major premise
arg can be an arbitrary term as long as that term *contains* only a single local
const.
-/

/--
Naming rule for constructor arguments which are named in the constructor
declaration.
-/
/--
Naming rule for constructor arguments whose type is associated with a list of
typical variable names. See `tactic.typical_variable_names`.
-/
/--
Naming rule for constructor arguments whose type is in `Prop`.
-/
/--
Fallback constructor argument naming rule. This rule never fails.
-/
/--
`apply_constructor_argument_naming_rules info rules` applies the constructor
argument naming rules in `rules` to the constructor argument given by `info`.
Returns the result of the first applicable rule. Fails if no rule is applicable.
-/
/--
Get possible names for a constructor argument. This tactic applies all the
previously defined rules in order. It cannot fail and always returns a nonempty
list.
-/
/--
`intron_fresh n` introduces `n` hypotheses with names generated by
`tactic.mk_fresh_name`.
-/
/--
Introduce the new hypotheses generated by the minor premise for a given
constructor. The new hypotheses are given fresh (unique, non-human-friendly)
names. They are later renamed by `constructor_renames`. We delay the generation
of the human-friendly names because when `constructor_renames` is called, more
names may have become unused.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `cinfo`: information about the constructor.

Output:

- For each constructor argument, the pretty name of the newly introduced
  hypothesis corresponding to the argument and its `constructor_argument_info`.
- For each newly introduced induction hypothesis, its pretty name and the name
  of the recursive constructor argument from which it was derived.
-/
/--
`ih_name arg_name` is the name `ih_<arg_name>`.
-/
/--
Rename the new hypotheses in the goal for a minor premise.

Input:

- `generate_induction_hyps`: whether we generate induction hypotheses (i.e.
  whether `eliminate_hyp` is in `induction` or `cases` mode).
- `mpinfo`: information about the major premise.
- `iinfo`: information about the inductive type.
- `cinfo`: information about the constructor whose minor premise we are
  processing.
- `with_names`: a list of names given by the user. These are used to name
  constructor arguments and induction hypotheses. Our own naming logic only
  kicks in if this list does not contain enough names.
- `args` and `ihs`: the output of `constructor_intros`.

Output:

- The newly introduced hypotheses corresponding to constructor arguments.
- The newly introduced induction hypotheses.
-/
/-!
## Generalisation

`induction'` can generalise the goal before performing an induction, which gives
us a more general induction hypothesis. We call this 'auto-generalisation'.
-/

/--
A value of `generalization_mode` describes the behaviour of the
auto-generalisation functionality:

- `generalize_all_except hs` means that the `hs` remain fixed and all other
  hypotheses are generalised. However, there are three exceptions:

  * Hypotheses depending on any `h` in `hs` also remain fixed. If we were to
    generalise them, we would have to generalise `h` as well.
  * Hypotheses which do not occur in the target and which do not mention the
    major premise or its dependencies are never generalised. Generalising them
    would not lead to a more general induction hypothesis.
  * Frozen local instances and their dependencies are never generalised.

- `generalize_only hs` means that only the `hs` are generalised. Exception:
  hypotheses which depend on the major premise are generalised even if they do
  not appear in `hs`.
-/
inductive generalization_mode 
where
| generalize_all_except : List name → generalization_mode
| generalize_only : List name → generalization_mode

protected instance generalization_mode.inhabited : Inhabited generalization_mode :=
  { default := generalization_mode.generalize_all_except [] }

