/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Simon Hudon, Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.basic
import PostPort

universes u v 

namespace Mathlib

/-!
# Opposites

In this file we define a type synonym `opposite α := α`, denoted by `αᵒᵖ` and two synonyms for the
identity map, `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. The type tag `αᵒᵖ` is used with two different
meanings:

- if `α` is a category, then `αᵒᵖ` is the opposite category, with all arrows reversed;

- if `α` is a monoid (group, etc), then `αᵒᵖ` is the opposite monoid (group, etc) with
  `op (x * y) = op x * op y`.
-/

/-- The type of objects of the opposite of `α`; used to define the opposite category or group.

  In order to avoid confusion between `α` and its opposite type, we
  set up the type of objects `opposite α` using the following pattern,
  which will be repeated later for the morphisms.

  1. Define `opposite α := α`.
  2. Define the isomorphisms `op : α → opposite α`, `unop : opposite α → α`.
  3. Make the definition `opposite` irreducible.

  This has the following consequences.

  * `opposite α` and `α` are distinct types in the elaborator, so you
    must use `op` and `unop` explicitly to convert between them.
  * Both `unop (op X) = X` and `op (unop X) = X` are definitional
    equalities. Notably, every object of the opposite category is
    definitionally of the form `op X`, which greatly simplifies the
    definition of the structure of the opposite category, for example.

  (If Lean supported definitional eta equality for records, we could
  achieve the same goals using a structure with one field.)
-/
def opposite (α : Sort u)  :=
  α

postfix:0 "ᵒᵖ" => Mathlib.opposite

-- Use a high right binding power (like that of postfix ⁻¹) so that, for example,

-- `presheaf Cᵒᵖ` parses as `presheaf (Cᵒᵖ)` and not `(presheaf C)ᵒᵖ`.

namespace opposite


/-- The canonical map `α → αᵒᵖ`. -/
/-- The canonical map `αᵒᵖ → α`. -/
def op {α : Sort u} : α → (αᵒᵖ) :=
  id

def unop {α : Sort u} : αᵒᵖ → α :=
  id

theorem op_injective {α : Sort u} : function.injective op :=
  fun (_x _x_1 : α) => id

theorem unop_injective {α : Sort u} : function.injective unop :=
  fun (_x _x_1 : αᵒᵖ) => id

@[simp] theorem op_inj_iff {α : Sort u} (x : α) (y : α) : op x = op y ↔ x = y :=
  iff.rfl

@[simp] theorem unop_inj_iff {α : Sort u} (x : αᵒᵖ) (y : αᵒᵖ) : unop x = unop y ↔ x = y :=
  iff.rfl

@[simp] theorem op_unop {α : Sort u} (x : αᵒᵖ) : op (unop x) = x :=
  rfl

@[simp] theorem unop_op {α : Sort u} (x : α) : unop (op x) = x :=
  rfl

/-- The type-level equivalence between a type and its opposite. -/
def equiv_to_opposite {α : Sort u} : α ≃ (αᵒᵖ) :=
  equiv.mk op unop unop_op op_unop

@[simp] theorem equiv_to_opposite_apply {α : Sort u} (a : α) : coe_fn equiv_to_opposite a = op a :=
  rfl

@[simp] theorem equiv_to_opposite_symm_apply {α : Sort u} (a : αᵒᵖ) : coe_fn (equiv.symm equiv_to_opposite) a = unop a :=
  rfl

theorem op_eq_iff_eq_unop {α : Sort u} {x : α} {y : αᵒᵖ} : op x = y ↔ x = unop y :=
  equiv.apply_eq_iff_eq_symm_apply equiv_to_opposite

theorem unop_eq_iff_eq_op {α : Sort u} {x : αᵒᵖ} {y : α} : unop x = y ↔ x = op y :=
  equiv.apply_eq_iff_eq_symm_apply (equiv.symm equiv_to_opposite)

protected instance inhabited {α : Sort u} [Inhabited α] : Inhabited (αᵒᵖ) :=
  { default := op Inhabited.default }

@[simp] def op_induction {α : Sort u} {F : αᵒᵖ → Sort v} (h : (X : α) → F (op X)) (X : αᵒᵖ) : F X :=
  h (unop X)

