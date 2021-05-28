/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.data.bool.default
import PostPort

namespace Mathlib

/-
Simplification lemmas for ite.

We don't prove them at logic.lean because it is easier to prove them using
the tactic framework.
-/

@[simp] theorem if_true_right_eq_or (p : Prop) [h : Decidable p] (q : Prop) : ite p q True = (¬p ∨ q) := sorry

@[simp] theorem if_true_left_eq_or (p : Prop) [h : Decidable p] (q : Prop) : ite p True q = (p ∨ q) := sorry

@[simp] theorem if_false_right_eq_and (p : Prop) [h : Decidable p] (q : Prop) : ite p q False = (p ∧ q) := sorry

@[simp] theorem if_false_left_eq_and (p : Prop) [h : Decidable p] (q : Prop) : ite p False q = (¬p ∧ q) := sorry

