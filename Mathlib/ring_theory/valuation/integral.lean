/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.integral_closure
import Mathlib.ring_theory.valuation.integers
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
# Integral elements over the ring of integers of a valution

The ring of integers is integrally closed inside the original ring.
-/

namespace valuation


namespace integers


theorem mem_of_integral {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation R Γ₀} {O : Type w} [comm_ring O] [algebra O R] (hv : integers v O) {x : R} (hx : is_integral O x) : x ∈ integer v := sorry

protected theorem integral_closure {R : Type u} {Γ₀ : Type v} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] {v : valuation R Γ₀} {O : Type w} [comm_ring O] [algebra O R] (hv : integers v O) : integral_closure O R = ⊥ := sorry

