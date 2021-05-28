/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.fix_reflect_string
import Mathlib.PostPort

universes l 

namespace Mathlib

/-!
# Documentation commands

We generate html documentation from mathlib. It is convenient to collect lists of tactics, commands,
notes, etc. To facilitate this, we declare these documentation entries in the library
using special commands.

* `library_note` adds a note describing a certain feature or design decision. These can be
  referenced in doc strings with the text `note [name of note]`.
* `add_tactic_doc` adds an entry documenting an interactive tactic, command, hole command, or
  attribute.

Since these commands are used in files imported by `tactic.core`, this file has no imports.

## Implementation details

`library_note note_id note_msg` creates a declaration `` `library_note.i `` for some `i`.
This declaration is a pair of strings `note_id` and `note_msg`, and it gets tagged with the
`library_note` attribute.

Similarly, `add_tactic_doc` creates a declaration `` `tactic_doc.i `` that stores the provided
information.
-/

/-- A rudimentary hash function on strings. -/
def string.hash (s : string) : ℕ :=
  string.fold 1 (fun (h : ℕ) (c : char) => (bit1 (bit0 (bit0 (bit0 (bit0 1)))) * h + char.val c) % unsigned_sz) s

/-- `mk_hashed_name nspace id` hashes the string `id` to a value `i` and returns the name
`nspace._i` -/
/--
`copy_doc_string fr to` copies the docstring from the declaration named `fr`
to each declaration named in the list `to`. -/
/--
`copy_doc_string source → target_1 target_2 ... target_n` copies the doc string of the
declaration named `source` to each of `target_1`, `target_2`, ..., `target_n`.
 -/
/-! ### The `library_note` command -/

/-- A user attribute `library_note` for tagging decls of type `string × string` for use in note
output. -/
/--
`mk_reflected_definition name val` constructs a definition declaration by reflection.

Example: ``mk_reflected_definition `foo 17`` constructs the definition
declaration corresponding to `def foo : ℕ := 17`
-/
/-- If `note_name` and `note` are `pexpr`s representing strings,
`add_library_note note_name note` adds a declaration of type `string × string` and tags it with
the `library_note` attribute. -/
/--
A command to add library notes. Syntax:
```
/--
note message
-/
/-- Collects all notes in the current environment.
Returns a list of pairs `(note_id, note_content)` -/
/-! ### The `add_tactic_doc_entry` command -/

/-- The categories of tactic doc entry. -/
inductive doc_category 
where
| tactic : doc_category
| cmd : doc_category
| hole_cmd : doc_category
| attr : doc_category

/-- Format a `doc_category` -/
/-- The information used to generate a tactic doc entry -/
structure tactic_doc_entry 
where
  name : string
  category : doc_category
  decl_names : List name
  tags : List string
  description : string
  inherit_description_from : Option name

/-- Turns a `tactic_doc_entry` into a JSON representation. -/
/-- `update_description_from tde inh_id` replaces the `description` field of `tde` with the
    doc string of the declaration named `inh_id`. -/
/--
`update_description tde` replaces the `description` field of `tde` with:

* the doc string of `tde.inherit_description_from`, if this field has a value
* the doc string of the entry in `tde.decl_names`, if this field has length 1

If neither of these conditions are met, it returns `tde`. -/
/-- A user attribute `tactic_doc` for tagging decls of type `tactic_doc_entry`
for use in doc output -/
/-- Collects everything in the environment tagged with the attribute `tactic_doc`. -/
/-- `add_tactic_doc tde` adds a declaration to the environment
with `tde` as its body and tags it with the `tactic_doc`
attribute. If `tde.decl_names` has exactly one entry `` `decl`` and
if `tde.description` is the empty string, `add_tactic_doc` uses the doc
string of `decl` as the description. -/
/--
A command used to add documentation for a tactic, command, hole command, or attribute.

Usage: after defining an interactive tactic, command, or attribute,
add its documentation as follows.
```lean
/--
describe what the command does here
-/
/--
At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Syntax:
```
/--
note message
-/
/--
Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x).
-/
-- See Note [open expressions]

/-- behavior of f -/
-- add docs to core tactics

/--
The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
  (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
  f x = x :=
by cc
```

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.

The `cc` implementation in Lean does a few more tricks: for example it
derives `a=b` from `nat.succ a = nat.succ b`, and `nat.succ a !=
nat.zero` for any `a`.

* The starting reference point is Nelson, Oppen, [Fast decision procedures based on congruence
closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf),
Journal of the ACM (1980)

* The congruence lemmas for dependent type theory as used in Lean are described in
[Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf)
(de Moura, Selsam IJCAR 2016).
-/
/--
`conv {...}` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://leanprover-community.github.io/extras/conv.html> for more details.

Inside `conv` blocks, mathlib currently additionally provides
* `erw`,
* `ring`, `ring2` and `ring_exp`,
* `norm_num`,
* `norm_cast`,
* `apply_congr`, and
* `conv` (within another `conv`).

`apply_congr` applies congruence lemmas to step further inside expressions,
and sometimes gives between results than the automatically generated
congruence lemmas used by `congr`.

Using `conv` inside a `conv` block allows the user to return to the previous
state of the outer `conv` block after it is finished. Thus you can continue
editing an expression without having to start a new `conv` block and re-scoping
everything. For example:
```lean
example (a b c d : ℕ) (h₁ : b = c) (h₂ : a + c = a + d) : a + b = a + d :=
by conv {
  to_lhs,
  conv {
    congr, skip,
    rw h₁,
  },
  rw h₂,
}
```
Without `conv`, the above example would need to be proved using two successive
`conv` blocks, each beginning with `to_lhs`.

Also, as a shorthand, `conv_lhs` and `conv_rhs` are provided, so that
```lean
example : 0 + 0 = 0 :=
begin
  conv_lhs { simp }
end
```
just means
```lean
example : 0 + 0 = 0 :=
begin
  conv { to_lhs, simp }
end
```
and likewise for `to_rhs`.
-/
/--
Accepts terms with the type `component tactic_state string` or `html empty` and
renders them interactively.
Requires a compatible version of the vscode extension to view the resulting widget.

### Example:

```lean
/-- A simple counter that can be incremented or decremented with some buttons. -/
/--
The `add_decl_doc` command is used to add a doc string to an existing declaration.

```lean
def foo := 5

/--
Doc string for foo.
-/
