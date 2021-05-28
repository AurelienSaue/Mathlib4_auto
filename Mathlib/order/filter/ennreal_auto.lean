/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.real.ennreal
import Mathlib.order.filter.countable_Inter
import Mathlib.order.liminf_limsup
import PostPort

universes u_1 

namespace Mathlib

/-!
# Order properties of extended non-negative reals

This file compiles filter-related results about `ennreal` (see data/real/ennreal.lean).
-/

namespace ennreal


theorem eventually_le_limsup {α : Type u_1} {f : filter α} [countable_Inter_filter f] (u : α → ennreal) : filter.eventually (fun (y : α) => u y ≤ filter.limsup f u) f := sorry

theorem limsup_eq_zero_iff {α : Type u_1} {f : filter α} [countable_Inter_filter f] {u : α → ennreal} : filter.limsup f u = 0 ↔ filter.eventually_eq f u 0 := sorry

theorem limsup_const_mul_of_ne_top {α : Type u_1} {f : filter α} {u : α → ennreal} {a : ennreal} (ha_top : a ≠ ⊤) : (filter.limsup f fun (x : α) => a * u x) = a * filter.limsup f u := sorry

theorem limsup_const_mul {α : Type u_1} {f : filter α} [countable_Inter_filter f] {u : α → ennreal} {a : ennreal} : (filter.limsup f fun (x : α) => a * u x) = a * filter.limsup f u := sorry

theorem limsup_add_le {α : Type u_1} {f : filter α} [countable_Inter_filter f] (u : α → ennreal) (v : α → ennreal) : filter.limsup f (u + v) ≤ filter.limsup f u + filter.limsup f v := sorry

