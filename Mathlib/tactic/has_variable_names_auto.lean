/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.core
import Mathlib.PostPort

universes u l v u_1 u_2 

namespace Mathlib

/-!
# A tactic for type-based naming of variables

When we name hypotheses or variables, we often do so in a type-directed fashion:
a hypothesis of type `ℕ` is called `n` or `m`; a hypothesis of type `list ℕ` is
called `ns`; etc. This module provides a tactic,
`tactic.typical_variable_names`, which looks up typical variable names for a
given type.

Typical variable names are registered by giving an instance of the type class
`has_variable_names`. This file provides `has_variable_names` instances for many
of the core Lean types. If you want to override these, you can declare a
high-priority instance (perhaps localised) of `has_variable_names`. E.g. to
change the names given to natural numbers:

```lean
def foo : has_variable_names ℕ :=
⟨[`i, `j, `k]⟩

local attribute [instance, priority 1000] foo
```
-/

/--
Type class for associating a type `α` with typical variable names for elements
of `α`. See `tactic.typical_variable_names`.
-/
class has_variable_names (α : Sort u) where
  names : List name
  names_nonempty :
    autoParam (0 < list.length names)
      (Lean.Syntax.ident Lean.SourceInfo.none
        (String.toSubstring "Mathlib.tactic.exact_dec_trivial")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "exact_dec_trivial")
        [])

namespace tactic


/--
`typical_variable_names t` obtains typical names for variables of type `t`.
The returned list is guaranteed to be nonempty. Fails if there is no instance
`has_typical_variable_names t`.

```
typical_variable_names `(ℕ) = [`n, `m, `o]
```
-/
end tactic


namespace has_variable_names


/--
`@make_listlike_instance α _ β` creates an instance `has_variable_names β` from
an instance `has_variable_names α`. If `α` has associated names `a`, `b`, ...,
the generated instance for `β` has names `as`, `bs`, ... This can be used to
create instances for 'containers' such as lists or sets.
-/
def make_listlike_instance (α : Sort u) [has_variable_names α] {β : Sort v} :
    has_variable_names β :=
  mk
    (list.map
      (fun (n : name) =>
        name.append_suffix n
          (string.str string.empty (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1)))))))))
      (names α))

/--
`@make_inheriting_instance α _ β` creates an instance `has_variable_names β`
from an instance `has_variable_names α`. The generated instance contains the
same variable names as that of `α`. This can be used to create instances for
'wrapper' types like `option` and `subtype`.
-/
def make_inheriting_instance (α : Sort u) [has_variable_names α] {β : Sort v} :
    has_variable_names β :=
  mk (names α)

end has_variable_names


protected instance d_array.has_variable_names {n : ℕ} {α : Type u_1} [has_variable_names α] :
    has_variable_names (d_array n fun (_x : fin n) => α) :=
  has_variable_names.make_listlike_instance α

protected instance bool.has_variable_names : has_variable_names Bool :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance char.has_variable_names : has_variable_names char :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance fin.has_variable_names {n : ℕ} : has_variable_names (fin n) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance int.has_variable_names : has_variable_names ℤ :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance list.has_variable_names {α : Type u_1} [has_variable_names α] :
    has_variable_names (List α) :=
  has_variable_names.make_listlike_instance α

protected instance nat.has_variable_names : has_variable_names ℕ :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance sort.has_variable_names : has_variable_names Prop :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 (bit0 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit1 (bit0 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit0 1))))))))
        name.anonymous]

protected instance thunk.has_variable_names {α : Type u_1} [has_variable_names α] :
    has_variable_names (thunk α) :=
  has_variable_names.make_inheriting_instance α

protected instance prod.has_variable_names {α : Type u_1} {β : Type u_2} :
    has_variable_names (α × β) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 1))))))))
        name.anonymous]

protected instance pprod.has_variable_names {α : Sort u_1} {β : Sort u_2} :
    has_variable_names (PProd α β) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 1))))))))
        name.anonymous]

protected instance sigma.has_variable_names {α : Type u_1} {β : α → Type u_2} :
    has_variable_names (sigma β) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 1))))))))
        name.anonymous]

protected instance psigma.has_variable_names {α : Sort u_1} {β : α → Sort u_2} :
    has_variable_names (psigma β) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit1 (bit1 1))))))))
        name.anonymous]

protected instance subtype.has_variable_names {α : Sort u_1} [has_variable_names α] {p : α → Prop} :
    has_variable_names (Subtype p) :=
  has_variable_names.make_inheriting_instance α

protected instance option.has_variable_names {α : Type u_1} [has_variable_names α] :
    has_variable_names (Option α) :=
  has_variable_names.make_inheriting_instance α

protected instance bin_tree.has_variable_names {α : Type u_1} : has_variable_names (bin_tree α) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit1 (bit1 1))))))))
        name.anonymous]

protected instance rbtree.has_variable_names {α : Type u_1} [has_variable_names α]
    {lt : α → α → Prop} : has_variable_names (rbtree α) :=
  has_variable_names.make_listlike_instance α

protected instance set.has_variable_names {α : Type u_1} [has_variable_names α] :
    has_variable_names (set α) :=
  has_variable_names.make_listlike_instance α

protected instance string.has_variable_names : has_variable_names string :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
        name.anonymous]

protected instance unsigned.has_variable_names : has_variable_names unsigned :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance pi.has_variable_names {α : Sort u_1} {β : α → Sort u_2} :
    has_variable_names ((a : α) → β a) :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit1 (bit1 (bit1 (bit0 (bit0 (bit1 1))))))))
        name.anonymous,
      name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit0 (bit0 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance name.has_variable_names : has_variable_names name :=
  has_variable_names.mk
    [name.mk_string
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

protected instance binder_info.has_variable_names : has_variable_names binder_info :=
  has_variable_names.mk
    [name.mk_string
        (string.str
          (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit0 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 (bit1 1))))))))
        name.anonymous]

end Mathlib