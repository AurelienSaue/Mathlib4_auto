/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

Basic topological facts (limits and continuity) about `floor`,
`ceil` and `fract` in a `floor_ring`.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.algebra.ordered
import Mathlib.algebra.floor
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

theorem tendsto_floor_at_top {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : filter.tendsto floor filter.at_top filter.at_top := sorry

theorem tendsto_floor_at_bot {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : filter.tendsto floor filter.at_bot filter.at_bot :=
  monotone.tendsto_at_bot_at_bot (fun (a b : α) (hab : a ≤ b) => floor_mono hab)
    fun (b : ℤ) => Exists.intro (↑b) (eq.mpr (id (Eq._oldrec (Eq.refl (floor ↑b ≤ b)) (floor_coe b))) (le_refl b))

theorem tendsto_ceil_at_top {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : filter.tendsto ceil filter.at_top filter.at_top :=
  filter.tendsto.comp filter.tendsto_neg_at_bot_at_top
    (filter.tendsto.comp tendsto_floor_at_bot filter.tendsto_neg_at_top_at_bot)

theorem tendsto_ceil_at_bot {α : Type u_1} [linear_ordered_ring α] [floor_ring α] : filter.tendsto ceil filter.at_bot filter.at_bot :=
  filter.tendsto.comp filter.tendsto_neg_at_top_at_bot
    (filter.tendsto.comp tendsto_floor_at_top filter.tendsto_neg_at_bot_at_top)

theorem continuous_on_floor {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] (n : ℤ) : continuous_on (fun (x : α) => ↑(floor x)) (set.Ico (↑n) (↑n + 1)) :=
  iff.mpr (continuous_on_congr (floor_eq_on_Ico' n)) continuous_on_const

theorem continuous_on_ceil {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] (n : ℤ) : continuous_on (fun (x : α) => ↑(ceil x)) (set.Ioc (↑n - 1) ↑n) :=
  iff.mpr (continuous_on_congr (ceil_eq_on_Ioc' n)) continuous_on_const

theorem tendsto_floor_right' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(floor x)) (nhds_within (↑n) (set.Ici ↑n)) (nhds ↑n) := sorry

theorem tendsto_ceil_left' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(ceil x)) (nhds_within (↑n) (set.Iic ↑n)) (nhds ↑n) := sorry

theorem tendsto_floor_right {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(floor x)) (nhds_within (↑n) (set.Ici ↑n)) (nhds_within (↑n) (set.Ici ↑n)) := sorry

theorem tendsto_ceil_left {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(ceil x)) (nhds_within (↑n) (set.Iic ↑n)) (nhds_within (↑n) (set.Iic ↑n)) := sorry

theorem tendsto_floor_left {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(floor x)) (nhds_within (↑n) (set.Iio ↑n)) (nhds_within (↑n - 1) (set.Iic (↑n - 1))) := sorry

theorem tendsto_ceil_right {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(ceil x)) (nhds_within (↑n) (set.Ioi ↑n)) (nhds_within (↑n + 1) (set.Ici (↑n + 1))) := sorry

theorem tendsto_floor_left' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(floor x)) (nhds_within (↑n) (set.Iio ↑n)) (nhds (↑n - 1)) := sorry

theorem tendsto_ceil_right' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] (n : ℤ) : filter.tendsto (fun (x : α) => ↑(ceil x)) (nhds_within (↑n) (set.Ioi ↑n)) (nhds (↑n + 1)) := sorry

theorem continuous_on_fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [topological_add_group α] (n : ℤ) : continuous_on fract (set.Ico (↑n) (↑n + 1)) :=
  continuous_on.sub continuous_on_id (continuous_on_floor n)

theorem tendsto_fract_left' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] [topological_add_group α] (n : ℤ) : filter.tendsto fract (nhds_within (↑n) (set.Iio ↑n)) (nhds 1) := sorry

theorem tendsto_fract_left {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] [topological_add_group α] (n : ℤ) : filter.tendsto fract (nhds_within (↑n) (set.Iio ↑n)) (nhds_within 1 (set.Iio 1)) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within fract (tendsto_fract_left' n)
    (filter.eventually_of_forall fract_lt_one)

theorem tendsto_fract_right' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] [topological_add_group α] (n : ℤ) : filter.tendsto fract (nhds_within (↑n) (set.Ici ↑n)) (nhds 0) := sorry

theorem tendsto_fract_right {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] [order_closed_topology α] [topological_add_group α] (n : ℤ) : filter.tendsto fract (nhds_within (↑n) (set.Ici ↑n)) (nhds_within 0 (set.Ici 0)) :=
  tendsto_nhds_within_of_tendsto_nhds_of_eventually_within fract (tendsto_fract_right' n)
    (filter.eventually_of_forall fract_nonneg)

theorem continuous_on.comp_fract' {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] {β : Type u_2} {γ : Type u_3} [order_topology α] [topological_add_group α] [topological_space β] [topological_space γ] {f : β → α → γ} (h : continuous_on (function.uncurry f) (set.prod set.univ (set.Icc 0 1))) (hf : ∀ (s : β), f s 0 = f s 1) : continuous fun (st : β × α) => f (prod.fst st) (fract (prod.snd st)) := sorry

theorem continuous_on.comp_fract {α : Type u_1} [linear_ordered_ring α] [floor_ring α] [topological_space α] {β : Type u_2} [order_topology α] [topological_add_group α] [topological_space β] {f : α → β} (h : continuous_on f (set.Icc 0 1)) (hf : f 0 = f 1) : continuous (f ∘ fract) := sorry

