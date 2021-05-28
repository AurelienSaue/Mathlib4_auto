/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.measure_theory.measure_space
import Mathlib.order.filter.ennreal
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ennreal` is used in particular to define the norm in
the `L∞` space (see measure_theory/lp_space.lean).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see measure_theory/ae_eq_fun.lean).

## Main definitions

* `ess_sup f μ := μ.ae.limsup f`
* `ess_inf f μ := μ.ae.liminf f`
-/

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def ess_sup {α : Type u_1} {β : Type u_2} [measurable_space α] [conditionally_complete_lattice β] (f : α → β) (μ : measure_theory.measure α) : β :=
  filter.limsup (measure_theory.measure.ae μ) f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def ess_inf {α : Type u_1} {β : Type u_2} [measurable_space α] [conditionally_complete_lattice β] (f : α → β) (μ : measure_theory.measure α) : β :=
  filter.liminf (measure_theory.measure.ae μ) f

theorem ess_sup_congr_ae {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [conditionally_complete_lattice β] {f : α → β} {g : α → β} (hfg : filter.eventually_eq (measure_theory.measure.ae μ) f g) : ess_sup f μ = ess_sup g μ :=
  filter.limsup_congr hfg

theorem ess_inf_congr_ae {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [conditionally_complete_lattice β] {f : α → β} {g : α → β} (hfg : filter.eventually_eq (measure_theory.measure.ae μ) f g) : ess_inf f μ = ess_inf g μ :=
  ess_sup_congr_ae hfg

@[simp] theorem ess_sup_measure_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [complete_lattice β] {f : α → β} : ess_sup f 0 = ⊥ := sorry

@[simp] theorem ess_inf_measure_zero {α : Type u_1} {β : Type u_2} [measurable_space α] [complete_lattice β] {f : α → β} : ess_inf f 0 = ⊤ :=
  ess_sup_measure_zero

theorem ess_sup_mono_ae {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_lattice β] {f : α → β} {g : α → β} (hfg : filter.eventually_le (measure_theory.measure.ae μ) f g) : ess_sup f μ ≤ ess_sup g μ :=
  filter.limsup_le_limsup hfg

theorem ess_inf_mono_ae {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_lattice β] {f : α → β} {g : α → β} (hfg : filter.eventually_le (measure_theory.measure.ae μ) f g) : ess_inf f μ ≤ ess_inf g μ :=
  filter.liminf_le_liminf hfg

theorem ess_sup_const {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_lattice β] (c : β) (hμ : μ ≠ 0) : ess_sup (fun (x : α) => c) μ = c :=
  filter.limsup_const c

theorem ess_inf_const {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_lattice β] (c : β) (hμ : μ ≠ 0) : ess_inf (fun (x : α) => c) μ = c :=
  ess_sup_const c hμ

theorem ess_sup_const_bot {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_lattice β] : ess_sup (fun (x : α) => ⊥) μ = ⊥ :=
  filter.limsup_const_bot

theorem ess_inf_const_top {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_lattice β] : ess_inf (fun (x : α) => ⊤) μ = ⊤ :=
  filter.liminf_const_top

theorem order_iso.ess_sup_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [complete_lattice β] {γ : Type u_3} [complete_lattice γ] (f : α → β) (μ : measure_theory.measure α) (g : β ≃o γ) : coe_fn g (ess_sup f μ) = ess_sup (fun (x : α) => coe_fn g (f x)) μ :=
  order_iso.limsup_apply g

theorem order_iso.ess_inf_apply {α : Type u_1} {β : Type u_2} [measurable_space α] [complete_lattice β] {γ : Type u_3} [complete_lattice γ] (f : α → β) (μ : measure_theory.measure α) (g : β ≃o γ) : coe_fn g (ess_inf f μ) = ess_inf (fun (x : α) => coe_fn g (f x)) μ :=
  order_iso.ess_sup_apply f μ (order_iso.dual g)

theorem ae_lt_of_ess_sup_lt {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_linear_order β] {f : α → β} {x : β} (hf : ess_sup f μ < x) : filter.eventually (fun (y : α) => f y < x) (measure_theory.measure.ae μ) :=
  filter.eventually_lt_of_limsup_lt hf

theorem ae_lt_of_lt_ess_inf {α : Type u_1} {β : Type u_2} [measurable_space α] {μ : measure_theory.measure α} [complete_linear_order β] {f : α → β} {x : β} (hf : x < ess_inf f μ) : filter.eventually (fun (y : α) => x < f y) (measure_theory.measure.ae μ) :=
  ae_lt_of_ess_sup_lt hf

namespace ennreal


theorem ae_le_ess_sup {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α} (f : α → ennreal) : filter.eventually (fun (y : α) => f y ≤ ess_sup f μ) (measure_theory.measure.ae μ) :=
  eventually_le_limsup f

theorem ess_sup_eq_zero_iff {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α} {f : α → ennreal} : ess_sup f μ = 0 ↔ filter.eventually_eq (measure_theory.measure.ae μ) f 0 :=
  limsup_eq_zero_iff

theorem ess_sup_const_mul {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α} {f : α → ennreal} {a : ennreal} : ess_sup (fun (x : α) => a * f x) μ = a * ess_sup f μ :=
  limsup_const_mul

theorem ess_sup_add_le {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α} (f : α → ennreal) (g : α → ennreal) : ess_sup (f + g) μ ≤ ess_sup f μ + ess_sup g μ :=
  limsup_add_le f g

