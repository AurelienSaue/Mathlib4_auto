/-
Copyright (c) 2019 Patrick Massot All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot, Simon Hudon

A tactic pushing negations into an expression
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.logic.basic
import Mathlib.algebra.order
import PostPort

universes u 

namespace Mathlib

namespace push_neg


theorem not_not_eq (p : Prop) : (¬¬p) = p :=
  propext not_not

theorem not_and_eq (p : Prop) (q : Prop) : (¬(p ∧ q)) = (p → ¬q) :=
  propext not_and

theorem not_or_eq (p : Prop) (q : Prop) : (¬(p ∨ q)) = (¬p ∧ ¬q) :=
  propext not_or_distrib

theorem not_forall_eq {α : Sort u} (s : α → Prop) : (¬∀ (x : α), s x) = ∃ (x : α), ¬s x :=
  propext not_forall

theorem not_exists_eq {α : Sort u} (s : α → Prop) : (¬∃ (x : α), s x) = ∀ (x : α), ¬s x :=
  propext not_exists

theorem not_implies_eq (p : Prop) (q : Prop) : (¬(p → q)) = (p ∧ ¬q) :=
  propext not_imp

theorem classical.implies_iff_not_or (p : Prop) (q : Prop) : p → q ↔ ¬p ∨ q :=
  imp_iff_not_or

theorem not_eq {α : Sort u} (a : α) (b : α) : ¬a = b ↔ a ≠ b :=
  iff.rfl

theorem not_le_eq {β : Type u} [linear_order β] (a : β) (b : β) : (¬a ≤ b) = (b < a) :=
  propext not_le

theorem not_lt_eq {β : Type u} [linear_order β] (a : β) (b : β) : (¬a < b) = (b ≤ a) :=
  propext not_lt

end push_neg


/--
Push negations in the goal of some assumption.

For instance, a hypothesis `h : ¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg at h` into
`h : ∃ x, ∀ y, y < x`. Variables names are conserved.

This tactic pushes negations inside expressions. For instance, given an assumption
```lean
h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε)
```
writing `push_neg at h` will turn `h` into
```lean
h : ∃ ε, ε > 0 ∧ ∀ δ, δ > 0 → (∃ x, |x - x₀| ≤ δ ∧ ε < |f x - y₀|),
```

(the pretty printer does *not* use the abreviations `∀ δ > 0` and `∃ ε > 0` but this issue
has nothing to do with `push_neg`).
Note that names are conserved by this tactic, contrary to what would happen with `simp`
using the relevant lemmas. One can also use this tactic at the goal using `push_neg`,
at every assumption and the goal using `push_neg at *` or at selected assumptions and the goal
using say `push_neg at h h' ⊢` as usual.
-/
theorem imp_of_not_imp_not (P : Prop) (Q : Prop) : (¬Q → ¬P) → P → Q :=
  fun (h : ¬Q → ¬P) (hP : P) => classical.by_contradiction fun (h' : ¬Q) => h h' hP

/-- Matches either an identifier "h" or a pair of identifiers "h with k" -/
/--
Transforms the goal into its contrapositive.

* `contrapose`     turns a goal `P → Q` into `¬ Q → ¬ P`
* `contrapose!`    turns a goal `P → Q` into `¬ Q → ¬ P` and pushes negations inside `P` and `Q`
  using `push_neg`
* `contrapose h`   first reverts the local assumption `h`, and then uses `contrapose` and `intro h`
* `contrapose! h`  first reverts the local assumption `h`, and then uses `contrapose!` and `intro h`
* `contrapose h with new_h` uses the name `new_h` for the introduced hypothesis
-/
