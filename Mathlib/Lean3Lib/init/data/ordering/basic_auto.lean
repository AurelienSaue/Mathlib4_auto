/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.repr
import Mathlib.Lean3Lib.init.data.prod
import Mathlib.Lean3Lib.init.data.sum.basic

universes l u 

namespace Mathlib

inductive ordering where
| lt : ordering
| eq : ordering
| gt : ordering

protected instance ordering.has_repr : has_repr ordering := has_repr.mk fun (s : ordering) => sorry

namespace ordering


def swap : ordering → ordering := sorry

def or_else : ordering → ordering → ordering := sorry

theorem swap_swap (o : ordering) : swap (swap o) = o :=
  ordering.cases_on o (idRhs (swap (swap lt) = swap (swap lt)) rfl)
    (idRhs (swap (swap eq) = swap (swap eq)) rfl) (idRhs (swap (swap gt) = swap (swap gt)) rfl)

end ordering


def cmp_using {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a : α) (b : α) : ordering :=
  ite (lt a b) ordering.lt (ite (lt b a) ordering.gt ordering.eq)

def cmp {α : Type u} [HasLess α] [DecidableRel Less] (a : α) (b : α) : ordering :=
  cmp_using Less a b

protected instance ordering.decidable_eq : DecidableEq ordering := fun (a b : ordering) => sorry

end Mathlib