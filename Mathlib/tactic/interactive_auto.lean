/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Sebastien Gouezel, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.lint.default
import Mathlib.tactic.dependencies
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace tactic


namespace interactive


/-- Similar to `constructor`, but does not reorder goals. -/
/-- `try_for n { tac }` executes `tac` for `n` ticks, otherwise uses `sorry` to close the goal.
Never fails. Useful for debugging. -/
/-- Multiple `subst`. `substs x y z` is the same as `subst x, subst y, subst z`. -/
/-- Unfold coercion-related definitions -/
/-- Unfold `has_well_founded.r`, `sizeof` and other such definitions. -/
/-- Unfold auxiliary definitions associated with the current declaration. -/
/-- For debugging only. This tactic checks the current state for any
missing dropped goals and restores them. Useful when there are no
goals to solve but "result contains meta-variables". -/
/-- Like `try { tac }`, but in the case of failure it continues
from the failure state instead of reverting to the original state. -/
/-- `id { tac }` is the same as `tac`, but it is useful for creating a block scope without
requiring the goal to be solved at the end like `{ tac }`. It can also be used to enclose a
non-interactive tactic for patterns like `tac1; id {tac2}` where `tac2` is non-interactive. -/
/--
`work_on_goal n { tac }` creates a block scope for the `n`-goal (indexed from zero),
and does not require that the goal be solved at the end
(any remaining subgoals are inserted back into the list of goals).

Typically usage might look like:
````
intros,
simp,
apply lemma_1,
work_on_goal 2 {
  dsimp,
  simp
},
refl
````

See also `id { tac }`, which is equivalent to `work_on_goal 0 { tac }`.
-/
/--
`swap n` will move the `n`th goal to the front.
`swap` defaults to `swap 2`, and so interchanges the first and second goals.
-/
/-- `rotate` moves the first goal to the back. `rotate n` will do this `n` times. -/
/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
/--
Acts like `have`, but removes a hypothesis with the same name as
this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
then after `replace h := f h` the goal will be `h : q ⊢ goal`,
where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
This can be used to simulate the `specialize` and `apply at` tactics
of Coq. -/
/-- Make every proposition in the context decidable. -/
theorem generalize_a_aux {α : Sort u} (h : (x : Sort u) → (α → x) → x) : α := h α id

/--
Like `generalize` but also considers assumptions
specified by the user. The user can also specify to
omit the goal.
-/
/-- go from (x₀ : t₀) (x₁ : t₀) (x₂ : t₀) to (x₀ x₁ x₂ : t₀) -/
/--
Remove identity functions from a term. These are normally
automatically generated with terms like `show t, from p` or
`(p : t)` which translate to some variant on `@id t p` in
order to retain the type.
-/
/--
`refine_struct { .. }` acts like `refine` but works only with structure instance
literals. It creates a goal for each missing field and tags it with the name of the
field so that `have_field` can be used to generically refer to the field currently
being refined.

As an example, we can use `refine_struct` to automate the construction semigroup
instances:

```lean
refine_struct ( { .. } : semigroup α ),
-- case semigroup, mul

-- case semigroup, mul
-- α : Type u,

-- α : Type u,
-- ⊢ α → α → α

-- ⊢ α → α → α

-- case semigroup, mul_assoc

-- case semigroup, mul_assoc
-- α : Type u,

-- α : Type u,
-- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)

-- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)
```

`have_field`, used after `refine_struct _`, poses `field` as a local constant
with the type of the field of the current goal:

```lean
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```lean
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```
-/
/--
`guard_hyp' h : t` fails if the hypothesis `h` does not have type `t`.
We use this tactic for writing tests.
Fixes `guard_hyp` by instantiating meta variables
-/
/--
`match_hyp h : t` fails if the hypothesis `h` does not match the type `t` (which may be a pattern).
We use this tactic for writing tests.
-/
/--
`guard_expr_strict t := e` fails if the expr `t` is not equal to `e`. By contrast
to `guard_expr`, this tests strict (syntactic) equality.
We use this tactic for writing tests.
-/
/--
`guard_target_strict t` fails if the target of the main goal is not syntactically `t`.
We use this tactic for writing tests.
-/
/--
`guard_hyp_strict h : t` fails if the hypothesis `h` does not have type syntactically equal
to `t`.
We use this tactic for writing tests.
-/
/-- Tests that there are `n` hypotheses in the current context. -/
/-- Test that `t` is the tag of the main goal. -/
/-- `guard_proof_term { t } e` applies tactic `t` and tests whether the resulting proof term
  unifies with `p`. -/
/-- `success_if_fail_with_msg { tac } msg` succeeds if the interactive tactic `tac` fails with
error message `msg` (for test writing purposes). -/
/-- Get the field of the current goal. -/
/--
`have_field`, used after `refine_struct _` poses `field` as a local constant
with the type of the field of the current goal:

```lean
refine_struct ({ .. } : semigroup α),
{ have_field, ... },
{ have_field, ... },
```
behaves like
```lean
refine_struct ({ .. } : semigroup α),
{ have field := @semigroup.mul, ... },
{ have field := @semigroup.mul_assoc, ... },
```
-/
/-- `apply_field` functions as `have_field, apply field, clear field` -/
/--
`apply_rules hs n` applies the list of lemmas `hs` and `assumption` on the
first goal and the resulting subgoals, iteratively, at most `n` times.
`n` is optional, equal to 50 by default.
You can pass an `apply_cfg` option argument as `apply_rules hs n opt`.
(A typical usage would be with `apply_rules hs n { md := reducible })`,
which asks `apply_rules` to not unfold `semireducible` definitions (i.e. most)
when checking if a lemma matches the goal.)

`hs` can contain user attributes: in this case all theorems with this
attribute are added to the list of rules.

For instance:

```lean
@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }

attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

lemma my_test {a b c d e : real} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
-- any of the following lines solve the goal:

-- any of the following lines solve the goal:
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3
by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]
by apply_rules [mono_rules]
by apply_rules mono_rules
```
-/
/--
`h_generalize Hx : e == x` matches on `cast _ e` in the goal and replaces it with
`x`. It also adds `Hx : e == x` as an assumption. If `cast _ e` appears multiple
times (not necessarily with the same proof), they are all replaced by `x`. `cast`
`eq.mp`, `eq.mpr`, `eq.subst`, `eq.substr`, `eq.rec` and `eq.rec_on` are all treated
as casts.

- `h_generalize Hx : e == x with h` adds hypothesis `α = β` with `e : α, x : β`;
- `h_generalize Hx : e == x with _` chooses automatically chooses the name of
  assumption `α = β`;
- `h_generalize! Hx : e == x` reverts `Hx`;
- when `Hx` is omitted, assumption `Hx : e == x` is not added.
-/
/-- Tests whether `t` is definitionally equal to `p`. The difference with `guard_expr_eq` is that
  this uses definitional equality instead of alpha-equivalence. -/
/--
`guard_target' t` fails if the target of the main goal is not definitionally equal to `t`.
We use this tactic for writing tests.
The difference with `guard_target` is that this uses definitional equality instead of
alpha-equivalence.
-/
/--
a weaker version of `trivial` that tries to solve the goal by reflexivity or by reducing it to true,
unfolding only `reducible` constants. -/
/--
Similar to `existsi`. `use x` will instantiate the first term of an `∃` or `Σ` goal with `x`.
It will then try to close the new goal using `triv`, or try to simplify it by applying `exists_prop`.
Unlike `existsi`, `x` is elaborated with respect to the expected type.
`use` will alternatively take a list of terms `[x0, ..., xn]`.

`use` will work with constructors of arbitrary inductive types.

Examples:
```lean
example (α : Type) : ∃ S : set α, S = S :=
by use ∅

example : ∃ x : ℤ, x = x :=
by use 42

example : ∃ n > 0, n = n :=
begin
  use 1,
  -- goal is now 1 > 0 ∧ 1 = 1, whereas it would be ∃ (H : 1 > 0), 1 = 1 after existsi 1.
  exact ⟨zero_lt_one, rfl⟩,
end

example : ∃ a b c : ℤ, a + b + c = 6 :=
by use [1, 2, 3]

example : ∃ p : ℤ × ℤ, p.1 = 1 :=
by use ⟨1, 42⟩

example : Σ x y : ℤ, (ℤ × ℤ) × ℤ :=
by use [1, 2, 3, 4, 5]

inductive foo
| mk : ℕ → bool × ℕ → ℕ → foo

example : foo :=
by use [100, tt, 4, 3]
```
-/
/--
`clear_aux_decl` clears every `aux_decl` in the local context for the current goal.
This includes the induction hypothesis when using the equation compiler and
`_let_match` and `_fun_match`.

It is useful when using a tactic such as `finish`, `simp *` or `subst` that may use these
auxiliary declarations, and produce an error saying the recursion is not well founded.

```lean
example (n m : ℕ) (h₁ : n = m) (h₂ : ∃ a : ℕ, a = n ∧ a = m) : 2 * m = 2 * n :=
let ⟨a, ha⟩ := h₂ in
begin
  clear_aux_decl, -- subst will fail without this line
  subst h₁
end

example (x y : ℕ) (h₁ : ∃ n : ℕ, n * 1 = 2) (h₂ : 1 + 1 = 2 → x * 1 = y) : x = y :=
let ⟨n, hn⟩ := h₁ in
begin
  clear_aux_decl, -- finish produces an error without this line
  finish
end
```
-/
/--
The logic of `change x with y at l` fails when there are dependencies.
`change'` mimics the behavior of `change`, except in the case of `change x with y at l`.
In this case, it will correctly replace occurences of `x` with `y` at all possible hypotheses
in `l`. As long as `x` and `y` are defeq, it should never fail.
-/
/--
`set a := t with h` is a variant of `let a := t`. It adds the hypothesis `h : a = t` to
the local context and replaces `t` with `a` everywhere it can.

`set a := t with ←h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.

```lean
example (x : ℕ) (h : x = 3)  : x + x + x = 9 :=
begin
  set y := x with ←h_xy,
/-
x : ℕ,
y : ℕ := x,
h_xy : x = y,
h : y = 3
⊢ y + y + y = 9
-/
/--
`clear_except h₀ h₁` deletes all the assumptions it can except for `h₀` and `h₁`.
-/
/--
Format the current goal as a stand-alone example. Useful for testing tactics
or creating [minimal working examples](https://leanprover-community.github.io/mwe.html).

* `extract_goal`: formats the statement as an `example` declaration
* `extract_goal my_decl`: formats the statement as a `lemma` or `def` declaration
  called `my_decl`
* `extract_goal with i j k:` only use local constants `i`, `j`, `k` in the declaration

Examples:

```lean
example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
begin
  extract_goal,
     -- prints:
     -- example (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
     -- begin
     --   admit,
     -- end
  extract_goal my_lemma
     -- prints:
     -- lemma my_lemma (i j k : ℕ) (h₀ : i ≤ j) (h₁ : j ≤ k) : i ≤ k :=
     -- begin
     --   admit,
     -- end
end

example {i j k x y z w p q r m n : ℕ} (h₀ : i ≤ j) (h₁ : j ≤ k) (h₁ : k ≤ p) (h₁ : p ≤ q) : i ≤ k :=
begin
  extract_goal my_lemma,
    -- prints:
    -- lemma my_lemma {i j k x y z w p q r m n : ℕ}
    --   (h₀ : i ≤ j)
    --   (h₁ : j ≤ k)
    --   (h₁ : k ≤ p)
    --   (h₁ : p ≤ q) :
    --   i ≤ k :=
    -- begin
    --   admit,
    -- end

  extract_goal my_lemma with i j k
    -- prints:
    -- lemma my_lemma {p i j k : ℕ}
    --   (h₀ : i ≤ j)
    --   (h₁ : j ≤ k)
    --   (h₁ : k ≤ p) :
    --   i ≤ k :=
    -- begin
    --   admit,
    -- end
end

example : true :=
begin
  let n := 0,
  have m : ℕ, admit,
  have k : fin n, admit,
  have : n + m + k.1 = 0, extract_goal,
    -- prints:
    -- example (m : ℕ)  : let n : ℕ := 0 in ∀ (k : fin n), n + m + k.val = 0 :=
    -- begin
    --   intros n k,
    --   admit,
    -- end
end
```

-/
/--
`inhabit α` tries to derive a `nonempty α` instance and then upgrades this
to an `inhabited α` instance.
If the target is a `Prop`, this is done constructively;
otherwise, it uses `classical.choice`.

```lean
example (α) [nonempty α] : ∃ a : α, true :=
begin
  inhabit α,
  existsi default α,
  trivial
end
```
-/
/-- `revert_deps n₁ n₂ ...` reverts all the hypotheses that depend on one of `n₁, n₂, ...`
It does not revert `n₁, n₂, ...` themselves (unless they depend on another `nᵢ`). -/
/-- `revert_after n` reverts all the hypotheses after `n`. -/
/-- Reverts all local constants on which the target depends (recursively). -/
/-- `clear_value n₁ n₂ ...` clears the bodies of the local definitions `n₁, n₂ ...`, changing them
into regular hypotheses. A hypothesis `n : α := t` is changed to `n : α`. -/
/--
`generalize' : e = x` replaces all occurrences of `e` in the target with a new hypothesis `x` of
the same type.

`generalize' h : e = x` in addition registers the hypothesis `h : e = x`.

`generalize'` is similar to `generalize`. The difference is that `generalize' : e = x` also
succeeds when `e` does not occur in the goal. It is similar to `set`, but the resulting hypothesis
`x` is not a local definition.
-/
end Mathlib