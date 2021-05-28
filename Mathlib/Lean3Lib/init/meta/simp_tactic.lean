/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.attribute
import Mathlib.Lean3Lib.init.meta.constructor_tactic
import Mathlib.Lean3Lib.init.meta.relation_tactics
import Mathlib.Lean3Lib.init.meta.occurrences
import Mathlib.Lean3Lib.init.data.option.basic
import PostPort

universes l 

namespace Mathlib

def simp.default_max_steps : ℕ :=
  bit0
    (bit0
      (bit0
        (bit0
          (bit0
            (bit0
              (bit0
                (bit1
                  (bit0
                    (bit1
                      (bit1
                        (bit0 (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit0 (bit1 (bit1 (bit0 (bit0 1))))))))))))))))))))))

/-- Prefix the given `attr_name` with `"simp_attr"`. -/
/-- Simp lemmas are used by the "simplifier" family of tactics.
`simp_lemmas` is essentially a pair of tables `rb_map (expr_type × name) (priority_list simp_lemma)`.
One of the tables is for congruences and one is for everything else.
An individual simp lemma is:
- A kind which can be `Refl`, `Simp` or `Congr`.
- A pair of `expr`s `l ~> r`. The rb map is indexed by the name of `get_app_fn(l)`.
- A proof that `l = r` or `l ↔ r`.
- A list of the metavariables that must be filled before the proof can be applied.
- A priority number
-/
/-- Make a new table of simp lemmas -/
/-- Merge the simp_lemma tables. -/
/-- Remove the given lemmas from the table. Use the names of the lemmas. -/
/-- Makes the default simp_lemmas table which is composed of all lemmas tagged with `simp`. -/
/-- Add a simplification lemma by an expression `p`. Some conditions on `p` must hold for it to be added, see list below.
If your lemma is not being added, you can see the reasons by setting `set_option trace.simp_lemmas true`.

- `p` must have the type `Π (h₁ : _) ... (hₙ : _), LHS ~ RHS` for some reflexive, transitive relation (usually `=`).
- Any of the hypotheses `hᵢ` should either be present in `LHS` or otherwise a `Prop` or a typeclass instance.
- `LHS` should not occur within `RHS`.
- `LHS` should not occur within a hypothesis `hᵢ`.

 -/
/-- Add a simplification lemma by it's declaration name. See `simp_lemmas.add` for more information.-/
/-- Adds a congruence simp lemma to simp_lemmas.
A congruence simp lemma is a lemma that breaks the simplification down into separate problems.
For example, to simplify `a ∧ b` to `c ∧ d`, we should try to simp `a` to `c` and `b` to `d`.
For examples of congruence simp lemmas look for lemmas with the `@[congr]` attribute.
```lean
lemma if_simp_congr ... (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v := ...
lemma imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) := ...
lemma and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∧ b) ↔ (c ∧ d) := ...
```
-/
/-- Add expressions to a set of simp lemmas using `simp_lemmas.add`.

  This is the new version of `simp_lemmas.append`,
  which also allows you to set the `symm` flag.
-/
/-- Add expressions to a set of simp lemmas using `simp_lemmas.add`.

  This is the backwards-compatibility version of `simp_lemmas.append_with_symm`,
  and sets all `symm` flags to `ff`.
-/
/-- `simp_lemmas.rewrite s e prove R` apply a simplification lemma from 's'

   - 'e'     is the expression to be "simplified"
   - 'prove' is used to discharge proof obligations.
   - 'r'     is the equivalence relation being used (e.g., 'eq', 'iff')
   - 'md'    is the transparency; how aggresively should the simplifier perform reductions.

   Result (new_e, pr) is the new expression 'new_e' and a proof (pr : e R new_e) -/
/-- `simp_lemmas.drewrite s e` tries to rewrite 'e' using only refl lemmas in 's' -/
namespace tactic


/- Remark: `transform` should not change the target. -/

/-- Revert a local constant, change its type using `transform`.  -/
/-- `get_eqn_lemmas_for deps d` returns the automatically generated equational lemmas for definition d.
   If deps is tt, then lemmas for automatically generated auxiliary declarations used to define d are also included. -/
structure dsimp_config 
where
  md : transparency
  max_steps : ℕ
  canonize_instances : Bool
  single_pass : Bool
  fail_if_unchanged : Bool
  eta : Bool
  zeta : Bool
  beta : Bool
  proj : Bool
  iota : Bool
  unfold_reducible : Bool
  memoize : Bool

end tactic


/-- (Definitional) Simplify the given expression using *only* reflexivity equality lemmas from the given set of lemmas.
   The resulting expression is definitionally equal to the input.

   The list `u` contains defintions to be delta-reduced, and projections to be reduced.-/
namespace tactic


/- Remark: the configuration parameters `cfg.md` and `cfg.eta` are ignored by this tactic. -/

/- Remark: we use transparency.instances by default to make sure that we
   can unfold projections of type classes. Example:

          (@has_add.add nat nat.has_add a b)
-/

/-- Tries to unfold `e` if it is a constant or a constant application.
    Remark: this is not a recursive procedure. -/
structure dunfold_config 
extends dsimp_config
where

/- Remark: in principle, dunfold can be implemented on top of dsimp. We don't do it for
   performance reasons. -/

structure delta_config 
where
  max_steps : ℕ
  visit_instances : Bool

/-- Delta reduce the given constant names -/
structure unfold_proj_config 
extends dsimp_config
where

/-- If `e` is a projection application, try to unfold it, otherwise fail. -/
structure simp_config 
where
  max_steps : ℕ
  contextual : Bool
  lift_eq : Bool
  canonize_instances : Bool
  canonize_proofs : Bool
  use_axioms : Bool
  zeta : Bool
  beta : Bool
  eta : Bool
  proj : Bool
  iota : Bool
  iota_eqn : Bool
  constructor_eq : Bool
  single_pass : Bool
  fail_if_unchanged : Bool
  memoize : Bool
  trace_lemmas : Bool

/--
  `simplify s e cfg r prove` simplify `e` using `s` using bottom-up traversal.
  `discharger` is a tactic for dischaging new subgoals created by the simplifier.
   If it fails, the simplifier tries to discharge the subgoal by simplifying it to `true`.

   The parameter `to_unfold` specifies definitions that should be delta-reduced,
   and projection applications that should be unfolded.
-/
/--
`ext_simplify_core a c s discharger pre post r e`:

- `a : α` - initial user data
- `c : simp_config` - simp configuration options
- `s : simp_lemmas` - the set of simp_lemmas to use. Remark: the simplification lemmas are not applied automatically like in the simplify tactic. The caller must use them at pre/post.
- `discharger : α → tactic α` - tactic for dischaging hypothesis in conditional rewriting rules. The argument 'α' is the current user data.
- `pre a s r p e` is invoked before visiting the children of subterm 'e'.
  + arguments:
    - `a` is the current user data
    - `s` is the updated set of lemmas if 'contextual' is `tt`,
    - `r` is the simplification relation being used,
    - `p` is the "parent" expression (if there is one).
    - `e` is the current subexpression in question.
  + if it succeeds the result is `(new_a, new_e, new_pr, flag)` where
    - `new_a` is the new value for the user data
    - `new_e` is a new expression s.t. `r e new_e`
    - `new_pr` is a proof for `r e new_e`, If it is none, the proof is assumed to be by reflexivity
    - `flag`  if tt `new_e` children should be visited, and `post` invoked.
- `(post a s r p e)` is invoked after visiting the children of subterm `e`,
  The output is similar to `(pre a r s p e)`, but the 'flag' indicates whether the new expression should be revisited or not.
- `r` is the simplification relation. Usually `=` or `↔`.
- `e` is the input expression to be simplified.

The method returns `(a,e,pr)` where

 - `a` is the final user data
 - `e` is the new expression
 - `pr` is the proof that the given expression equals the input expression.

Note that `ext_simplify_core` will succeed even if `pre` and `post` fail, as failures are used to indicate that the method should move on to the next subterm.
If it is desirable to propagate errors from `pre`, they can be propagated through the "user data".
An easy way to do this is to call `tactic.capture (do ...)` in the parts of `pre`/`post` where errors matter, and then use `tactic.unwrap a` on the result.

Additionally, `ext_simplify_core` does not propagate changes made to the tactic state by `pre` and `post.
If it is desirable to propagate changes to the tactic state in addition to errors, use `tactic.resume` instead of `tactic.unwrap`.
-/
structure simp_intros_config 
extends simp_config
where
  use_hyps : Bool

