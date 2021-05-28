/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Jesse Michael Han
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.rcases
import Mathlib.data.sum
import Mathlib.logic.function.basic
import Mathlib.PostPort

universes r s u u_1 

namespace Mathlib

/--
`derive_struct_ext_lemma n` generates two extensionality lemmas based on
the equality of all non-propositional projections.

On the following:

```lean
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

`derive_struct_lemma` generates:

```lean
lemma foo.ext : ∀ {α : Type u_1} (x y : foo α),
  x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α),
  x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
```

-/
def ext_param_type  :=
  Option name ⊕ Option name

/--
For performance reasons, it is inadvisable to use `user_attribute.get_param`.
The parameter is stored as a reflected expression.  When calling `get_param`,
the stored parameter is evaluated using `eval_expr`, which first compiles the
expression into VM bytecode. The unevaluated expression is available using
`user_attribute.get_param_untyped`.

In particular, `user_attribute.get_param` MUST NEVER BE USED in the
implementation of an attribute cache. This is because calling `eval_expr`
disables the attribute cache.

There are several possible workarounds:
 1. Set a different attribute depending on the parameter.
 2. Use your own evaluation function instead of `eval_expr`, such as e.g. `expr.to_nat`.
 3. Write your own `has_reflect Param` instance (using a more efficient serialization format).
   The `user_attribute` code unfortunately checks whether the expression has the correct type,
   but you can use `` `(id %%e : Param) `` to pretend that your expression `e` has type `Param`.
-/
/-!
For performance reasons, the parameters of the `@[ext]` attribute are stored
in two auxiliary attributes:
```lean
attribute [ext [thunk]] funext

-- is turned into

-- is turned into
attribute [_ext_core (@id name @funext)] thunk
attribute [_ext_lemma_core] funext
```

see Note [user attribute parameters]
-/

/-- Private attribute used to tag extensionality lemmas. -/
/--
Returns the extensionality lemmas in the environment, as a map from structure
name to lemma name.
-/
/--
Returns the extensionality lemmas in the environment, as a list of lemma names.
-/
/--
Tag lemmas of the form:

```lean
@[ext]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

The attribute indexes extensionality lemma using the type of the
objects (i.e. `my_collection`) which it gets from the statement of
the lemma.  In some cases, the same lemma can be used to state the
extensionality of multiple types that are definitionally equivalent.

```lean
attribute [ext [(→),thunk,stream]] funext
```

Those parameters are cumulative. The following are equivalent:

```lean
attribute [ext [(→),thunk]] funext
attribute [ext [stream]] funext
```
and
```lean
attribute [ext [(→),thunk,stream]] funext
```

One removes type names from the list for one lemma with:
```lean
attribute [ext [-stream,-thunk]] funext
```

Also, the following:

```lean
@[ext]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

is equivalent to

```lean
@[ext *]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

This allows us specify type synonyms along with the type
that is referred to in the lemma statement.

```lean
@[ext [*,my_type_synonym]]
lemma my_collection.ext (a b : my_collection)
  (h : ∀ x, a.lookup x = b.lookup y) :
  a = b := ...
```

The `ext` attribute can be applied to a structure to generate its extensionality lemmas:

```lean
@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)
```

will generate:

```lean
@[ext] lemma foo.ext : ∀ {α : Type u_1} (x y : foo α),
x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y
lemma foo.ext_iff : ∀ {α : Type u_1} (x y : foo α),
x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k
```

-/
/--
When possible, `ext` lemmas are stated without a full set of arguments. As an example, for bundled
homs `f`, `g`, and `of`, `f.comp of = g.comp of → f = g` is a better `ext` lemma than
`(∀ x, f (of x) = g (of x)) → f = g`, as the former allows a second type-specific extensionality
lemmas to be applied to `f.comp of = g.comp of`.
If the domain of `of` is `ℕ` or `ℤ` and `of` is a `ring_hom`, such a lemma could then make the goal
`f (of 1) = g (of 1)`.

For bundled morphisms, there is a `ext` lemma that always applies of the form
`(∀ x, ⇑f x = ⇑g x) → f = g`. When adding type-specific `ext` lemmas like the one above, we want
these to be tried first. This happens automatically since the type-specific lemmas are inevitably
defined later.
-/
-- We mark some existing extensionality lemmas.

-- We create some extensionality lemmas for existing structures.

theorem ulift.ext {α : Type s} (x : ulift α) (y : ulift α) (h : ulift.down x = ulift.down y) : x = y := sorry

namespace plift


-- This is stronger than the one generated automatically.

theorem ext {P : Prop} (a : plift P) (b : plift P) : a = b :=
  cases_on a fun (a : P) => cases_on b fun (b : P) => Eq.refl (up a)

end plift


-- Conservatively, we'll only add extensionality lemmas for `has_*` structures

-- as they become useful.

theorem has_zero.ext_iff {α : Type u} (x : HasZero α) (y : HasZero α) : x = y ↔ 0 = 0 := sorry

theorem unit.ext {x : Unit} {y : Unit} : x = y :=
  punit.cases_on x (punit.cases_on y (Eq.refl PUnit.unit))

theorem punit.ext {x : PUnit} {y : PUnit} : x = y :=
  punit.cases_on x (punit.cases_on y (Eq.refl PUnit.unit))

namespace tactic


/-- Helper structure for `ext` and `ext1`. `lemmas` keeps track of extensionality lemmas
  applied so far. -/
/-- Helper function for `try_intros`. Additionally populates the `trace_msg` field
  of `ext_state`. -/
/-- Try to introduce as many arguments as possible, using the given patterns to destruct the
  introduced variables. Returns the unused patterns. -/
/-- Apply one extensionality lemma, and destruct the arguments using the patterns
  in the ext_state. -/
/-- Apply multiple extensionality lemmas, destructing the arguments using the given patterns. -/
/-- Apply one extensionality lemma, and destruct the arguments using the given patterns.
  Returns the unused patterns. -/
/-- Apply multiple extensionality lemmas, destructing the arguments using the given patterns.
  `ext ps (some n)` applies at most `n` extensionality lemmas. Returns the unused patterns. -/
/--
`ext1 id` selects and apply one extensionality lemma (with attribute
`ext`), using `id`, if provided, to name a local constant
introduced by the lemma. If `id` is omitted, the local constant is
named automatically, as per `intro`. Placing a `?` after `ext1`
 (e.g. `ext1? i ⟨a,b⟩ : 3`) will display a sequence of tactic
applications that can replace the call to `ext1`.
-/
/--
- `ext` applies as many extensionality lemmas as possible;
- `ext ids`, with `ids` a list of identifiers, finds extentionality and applies them
  until it runs out of identifiers in `ids` to name the local constants.
- `ext` can also be given an `rcases` pattern in place of an identifier.
  This will destruct the introduced local constant.
- Placing a `?` after `ext` (e.g. `ext? i ⟨a,b⟩ : 3`) will display
  a sequence of tactic applications that can replace the call to `ext`.

When trying to prove:

```lean
α β : Type,
f g : α → set β
⊢ f = g
```

applying `ext x y` yields:

```lean
α β : Type,
f g : α → set β,
x : α,
y : β
⊢ y ∈ f x ↔ y ∈ f x
```

by applying functional extensionality and set extensionality.

When trying to prove:

```lean
α β γ : Type
f g : α × β → γ
⊢ f = g
```

applying `ext ⟨a, b⟩` yields:

```lean
α β γ : Type,
f g : α × β → γ,
a : α,
b : β
⊢ f (a, b) = g (a, b)
```

by applying functional extensionality and destructing the introduced pair.

In the previous example, applying `ext? ⟨a,b⟩` will produce the trace message:

```lean
Try this: apply funext, rintro ⟨a, b⟩
```

A maximum depth can be provided with `ext x y z : 3`.
-/
/--
* `ext1 id` selects and apply one extensionality lemma (with
