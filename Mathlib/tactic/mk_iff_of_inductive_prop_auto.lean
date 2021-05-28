/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.tactic.lint.default
import PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# mk_iff_of_inductive_prop

This file defines a tactic `tactic.mk_iff_of_inductive_prop` that generates `iff` rules for
inductive `Prop`s. For example, when applied to `list.chain`, it creates a declaration with
the following type:

```lean
∀{α : Type*} (R : α → α → Prop) (a : α) (l : list α),
  chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'
```

This tactic can be called using either the `mk_iff_of_inductive_prop` user command or
the `mk_iff` attribute.
-/

namespace mk_iff


/-- `select m n` runs `tactic.right` `m` times, and then `tactic.left` `(n-m)` times.
Fails if `n < m`. -/
/-- `compact_relation bs as_ps`: Produce a relation of the form:
```lean
R as := ∃ bs, Λ_i a_i = p_i[bs]
```
This relation is user-visible, so we compact it by removing each `b_j` where a `p_i = b_j`, and
hence `a_i = b_j`. We need to take care when there are `p_i` and `p_j` with `p_i = p_j = b_k`.

TODO: this is a variant of `compact_relation` in `coinductive_predicates.lean`, export it there.
-/
/--
Iterate over two lists, if the first element of the first list is `none`, insert `none` into the
result and continue with the tail of first list. Otherwise, wrap the first element of the second
list with `some` and continue with the tails of both lists. Return when either list is empty.

Example:
```
list_option_merge [none, some (), none, some ()] [0, 1, 2, 3, 4] = [none, (some 0), none, (some 1)]
```
-/
def list_option_merge {α : Type u_1} {β : Type u_2} : List (Option α) → List β → List (Option β) :=
  sorry

end mk_iff


namespace tactic


/--
`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
parameters for each of the constructors, and the equalities `is = cs` are the instantiations for
each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `list.chain` produces:

```lean
∀ {α : Type*} (R : α → α → Prop) (a : α) (l : list α),
  chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'
```
-/
end tactic


/--
`mk_iff_of_inductive_prop i r` makes an `iff` rule for the inductively-defined proposition `i`.
The new rule `r` has the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type
parameters, `is` are the indices, `j` ranges over all possible constructors, the `cs` are the
parameters for each of the constructors, and the equalities `is = cs` are the instantiations for
each constructor for each of the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, `mk_iff_of_inductive_prop` on `list.chain` produces:

```lean
∀ {α : Type*} (R : α → α → Prop) (a : α) (l : list α),
  chain R a l ↔ l = [] ∨ ∃{b : α} {l' : list α}, R a b ∧ chain R b l ∧ l = b :: l'
```

See also the `mk_iff` user attribute.
-/
/--
Applying the `mk_iff` attribute to an inductively-defined proposition `mk_iff` makes an `iff` rule
`r` with the shape `∀ps is, i as ↔ ⋁_j, ∃cs, is = cs`, where `ps` are the type parameters, `is` are
the indices, `j` ranges over all possible constructors, the `cs` are the parameters for each of the
constructors, and the equalities `is = cs` are the instantiations for each constructor for each of
the indices to the inductive type `i`.

In each case, we remove constructor parameters (i.e. `cs`) when the corresponding equality would
be just `c = i` for some index `i`.

For example, if we try the following:
```lean
@[mk_iff] structure foo (m n : ℕ) : Prop :=
(equal : m = n)
(sum_eq_two : m + n = 2)
```

Then `#check foo_iff` returns:
```lean
foo_iff : ∀ (m n : ℕ), foo m n ↔ m = n ∧ m + n = 2
```

You can add an optional string after `mk_iff` to change the name of the generated lemma.
For example, if we try the following:
```lean
@[mk_iff bar] structure foo (m n : ℕ) : Prop :=
(equal : m = n)
(sum_eq_two : m + n = 2)
```

Then `#check bar` returns:
```lean
bar : ∀ (m n : ℕ), foo m n ↔ m = n ∧ m + n = 2
```

See also the user command `mk_iff_of_inductive_prop`.
-/
