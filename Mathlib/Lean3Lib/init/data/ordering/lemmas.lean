/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.ordering.basic
import Mathlib.Lean3Lib.init.meta.default
import Mathlib.Lean3Lib.init.algebra.classes
import Mathlib.Lean3Lib.init.ite_simp
 

universes u 

namespace Mathlib

namespace ordering


@[simp] theorem ite_eq_lt_distrib (c : Prop) [Decidable c] (a : ordering) (b : ordering) : ite c a b = lt = ite c (a = lt) (b = lt) := sorry

@[simp] theorem ite_eq_eq_distrib (c : Prop) [Decidable c] (a : ordering) (b : ordering) : ite c a b = eq = ite c (a = eq) (b = eq) := sorry

@[simp] theorem ite_eq_gt_distrib (c : Prop) [Decidable c] (a : ordering) (b : ordering) : ite c a b = gt = ite c (a = gt) (b = gt) := sorry

/- ------------------------------------------------------------------ -/

end ordering


@[simp] theorem cmp_using_eq_lt {α : Type u} {lt : α → α → Prop} [DecidableRel lt] (a : α) (b : α) : cmp_using lt a b = ordering.lt = lt a b := sorry

@[simp] theorem cmp_using_eq_gt {α : Type u} {lt : α → α → Prop} [DecidableRel lt] [is_strict_order α lt] (a : α) (b : α) : cmp_using lt a b = ordering.gt = lt b a := sorry

@[simp] theorem cmp_using_eq_eq {α : Type u} {lt : α → α → Prop} [DecidableRel lt] (a : α) (b : α) : cmp_using lt a b = ordering.eq = (¬lt a b ∧ ¬lt b a) := sorry

