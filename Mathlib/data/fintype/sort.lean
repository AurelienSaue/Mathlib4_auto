/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.finset.sort
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-- Given a linearly ordered fintype `α` of cardinal `k`, the order isomorphism
`mono_equiv_of_fin α h` is the increasing bijection between `fin k` and `α`. Here, `h` is a proof
that the cardinality of `s` is `k`. We use this instead of an isomorphism `fin s.card ≃o α` to avoid
casting issues in further uses of this function. -/
def mono_equiv_of_fin (α : Type u_1) [fintype α] [linear_order α] {k : ℕ} (h : fintype.card α = k) : fin k ≃o α :=
  order_iso.trans (finset.order_iso_of_fin finset.univ h)
    (order_iso.trans (order_iso.set_congr (↑finset.univ) set.univ finset.coe_univ) order_iso.set.univ)

