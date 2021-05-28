/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.set.basic
import PostPort

universes u_1 

namespace Mathlib

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`.
-/

namespace well_founded


/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α : Type u_1} {r : α → α → Prop} (H : well_founded r) (s : set α) : set.nonempty s → ∃ (a : α), ∃ (H : a ∈ s), ∀ (x : α), x ∈ s → ¬r x a := sorry

/-- A minimal element of a nonempty set in a well-founded order -/
def min {α : Type u_1} {r : α → α → Prop} (H : well_founded r) (p : set α) (h : set.nonempty p) : α :=
  classical.some (has_min H p h)

theorem min_mem {α : Type u_1} {r : α → α → Prop} (H : well_founded r) (p : set α) (h : set.nonempty p) : min H p h ∈ p := sorry

theorem not_lt_min {α : Type u_1} {r : α → α → Prop} (H : well_founded r) (p : set α) (h : set.nonempty p) {x : α} (xp : x ∈ p) : ¬r x (min H p h) := sorry

theorem well_founded_iff_has_min {α : Type u_1} {r : α → α → Prop} : well_founded r ↔ ∀ (p : set α), set.nonempty p → ∃ (m : α), ∃ (H : m ∈ p), ∀ (x : α), x ∈ p → ¬r x m := sorry

theorem eq_iff_not_lt_of_le {α : Type u_1} [partial_order α] {x : α} {y : α} : x ≤ y → y = x ↔ ¬x < y := sorry

theorem well_founded_iff_has_max' {α : Type u_1} [partial_order α] : well_founded gt ↔ ∀ (p : set α), set.nonempty p → ∃ (m : α), ∃ (H : m ∈ p), ∀ (x : α), x ∈ p → m ≤ x → x = m := sorry

theorem well_founded_iff_has_min' {α : Type u_1} [partial_order α] : well_founded Less ↔ ∀ (p : set α), set.nonempty p → ∃ (m : α), ∃ (H : m ∈ p), ∀ (x : α), x ∈ p → x ≤ m → x = m :=
  well_founded_iff_has_max'

/-- The supremum of a bounded, well-founded order -/
protected def sup {α : Type u_1} {r : α → α → Prop} (wf : well_founded r) (s : set α) (h : bounded r s) : α :=
  min wf (set_of fun (x : α) => ∀ (a : α), a ∈ s → r a x) h

protected theorem lt_sup {α : Type u_1} {r : α → α → Prop} (wf : well_founded r) {s : set α} (h : bounded r s) {x : α} (hx : x ∈ s) : r x (well_founded.sup wf s h) :=
  min_mem wf (set_of fun (x : α) => ∀ (a : α), a ∈ s → r a x) h x hx

/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected def succ {α : Type u_1} {r : α → α → Prop} (wf : well_founded r) (x : α) : α :=
  dite (∃ (y : α), r x y) (fun (h : ∃ (y : α), r x y) => min wf (set_of fun (y : α) => r x y) h)
    fun (h : ¬∃ (y : α), r x y) => x

protected theorem lt_succ {α : Type u_1} {r : α → α → Prop} (wf : well_founded r) {x : α} (h : ∃ (y : α), r x y) : r x (well_founded.succ wf x) := sorry

protected theorem lt_succ_iff {α : Type u_1} {r : α → α → Prop} [wo : is_well_order α r] {x : α} (h : ∃ (y : α), r x y) (y : α) : r y (well_founded.succ is_well_order.wf x) ↔ r y x ∨ y = x := sorry

