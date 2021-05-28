/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.pi
import Mathlib.algebra.ordered_group
import Mathlib.tactic.pi_instances
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

namespace pi


protected instance ordered_cancel_comm_monoid {I : Type u} {f : I → Type v} [(i : I) → ordered_cancel_comm_monoid (f i)] : ordered_cancel_comm_monoid ((i : I) → f i) :=
  ordered_cancel_comm_monoid.mk Mul.mul sorry sorry 1 sorry sorry sorry sorry LessEq Less sorry sorry sorry sorry sorry

protected instance ordered_add_comm_group {I : Type u} {f : I → Type v} [(i : I) → ordered_add_comm_group (f i)] : ordered_add_comm_group ((i : I) → f i) :=
  ordered_add_comm_group.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub
    sorry sorry partial_order.le partial_order.lt sorry sorry sorry sorry

