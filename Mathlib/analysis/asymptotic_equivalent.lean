/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.asymptotics
import Mathlib.analysis.normed_space.ordered
import Mathlib.analysis.normed_space.bounded_linear_maps
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Asymptotic equivalence

In this file, we define the relation `is_equivalent u v l`, which means that `u-v` is little o of
`v` along the filter `l`.

Unlike `is_[oO]` relations, this one requires `u` and `v` to have the same codomaine `β`. While the
definition only requires `β` to be a `normed_group`, most interesting properties require it to be a
`normed_field`.

## Notations

We introduce the notation `u ~[l] v := is_equivalent u v l`, which you can use by opening the
`asymptotics` locale.

## Main results

If `β` is a `normed_group` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `tendsto u l (𝓝 c)` (see `is_equivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `is_equivalent_zero_iff_eventually_zero`)

If `β` is a `normed_field` :

- Alternative characterization of the relation (see `is_equivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ tendsto (u/v) l (𝓝 1)`
  (see `is_equivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c)`
  (see `is_equivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `is_equivalent.mul` and `is_equivalent.div`)

If `β` is a `normed_linear_ordered_field` :

- If `u ~[l] v`, we have `tendsto u l at_top ↔ tendsto v l at_top`
  (see `is_equivalent.tendsto_at_top_iff`)

-/

namespace asymptotics


/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as x converges along `l`. -/
def is_equivalent {α : Type u_1} {β : Type u_2} [normed_group β] (u : α → β) (v : α → β) (l : filter α)  :=
  is_o (u - v) v l

theorem is_equivalent.is_o {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {l : filter α} (h : is_equivalent u v l) : is_o (u - v) v l :=
  h

theorem is_equivalent.is_O {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {l : filter α} (h : is_equivalent u v l) : is_O u v l :=
  iff.mp (is_O.congr_of_sub (is_O.symm (is_o.is_O h))) (is_O_refl (fun (x : α) => v x) l)

theorem is_equivalent.is_O_symm {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {l : filter α} (h : is_equivalent u v l) : is_O v u l := sorry

theorem is_equivalent.refl {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {l : filter α} : is_equivalent u u l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_equivalent u u l)) (is_equivalent.equations._eqn_1 u u l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_o (u - u) u l)) (sub_self u))) (is_o_zero u l))

theorem is_equivalent.symm {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {l : filter α} (h : is_equivalent u v l) : is_equivalent v u l :=
  is_o.symm (is_o.trans_is_O (is_equivalent.is_o h) (is_equivalent.is_O_symm h))

theorem is_equivalent.trans {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {w : α → β} {l : filter α} (huv : is_equivalent u v l) (hvw : is_equivalent v w l) : is_equivalent u w l :=
  is_o.triangle (is_o.trans_is_O (is_equivalent.is_o huv) (is_equivalent.is_O hvw)) (is_equivalent.is_o hvw)

theorem is_equivalent_zero_iff_eventually_zero {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {l : filter α} : is_equivalent u 0 l ↔ filter.eventually_eq l u 0 :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (is_equivalent u 0 l ↔ filter.eventually_eq l u 0)) (is_equivalent.equations._eqn_1 u 0 l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_o (u - 0) 0 l ↔ filter.eventually_eq l u 0)) (sub_zero u))) is_o_zero_right_iff)

theorem is_equivalent_const_iff_tendsto {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {l : filter α} {c : β} (h : c ≠ 0) : is_equivalent u (function.const α c) l ↔ filter.tendsto u l (nhds c) := sorry

theorem is_equivalent.tendsto_const {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {l : filter α} {c : β} (hu : is_equivalent u (function.const α c) l) : filter.tendsto u l (nhds c) := sorry

theorem is_equivalent.tendsto_nhds {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {l : filter α} {c : β} (huv : is_equivalent u v l) (hu : filter.tendsto u l (nhds c)) : filter.tendsto v l (nhds c) := sorry

theorem is_equivalent.tendsto_nhds_iff {α : Type u_1} {β : Type u_2} [normed_group β] {u : α → β} {v : α → β} {l : filter α} {c : β} (huv : is_equivalent u v l) : filter.tendsto u l (nhds c) ↔ filter.tendsto v l (nhds c) :=
  { mp := is_equivalent.tendsto_nhds huv, mpr := is_equivalent.tendsto_nhds (is_equivalent.symm huv) }

theorem is_equivalent_iff_exists_eq_mul {α : Type u_1} {β : Type u_2} [normed_field β] {u : α → β} {v : α → β} {l : filter α} : is_equivalent u v l ↔ ∃ (φ : α → β), ∃ (hφ : filter.tendsto φ l (nhds 1)), filter.eventually_eq l u (φ * v) := sorry

theorem is_equivalent.exists_eq_mul {α : Type u_1} {β : Type u_2} [normed_field β] {u : α → β} {v : α → β} {l : filter α} (huv : is_equivalent u v l) : ∃ (φ : α → β), ∃ (hφ : filter.tendsto φ l (nhds 1)), filter.eventually_eq l u (φ * v) :=
  iff.mp is_equivalent_iff_exists_eq_mul huv

theorem is_equivalent_of_tendsto_one {α : Type u_1} {β : Type u_2} [normed_field β] {u : α → β} {v : α → β} {l : filter α} (hz : filter.eventually (fun (x : α) => v x = 0 → u x = 0) l) (huv : filter.tendsto (u / v) l (nhds 1)) : is_equivalent u v l := sorry

theorem is_equivalent_of_tendsto_one' {α : Type u_1} {β : Type u_2} [normed_field β] {u : α → β} {v : α → β} {l : filter α} (hz : ∀ (x : α), v x = 0 → u x = 0) (huv : filter.tendsto (u / v) l (nhds 1)) : is_equivalent u v l :=
  is_equivalent_of_tendsto_one (filter.eventually_of_forall hz) huv

theorem is_equivalent_iff_tendsto_one {α : Type u_1} {β : Type u_2} [normed_field β] {u : α → β} {v : α → β} {l : filter α} (hz : filter.eventually (fun (x : α) => v x ≠ 0) l) : is_equivalent u v l ↔ filter.tendsto (u / v) l (nhds 1) := sorry

theorem is_equivalent.smul {α : Type u_1} {E : Type u_2} {𝕜 : Type u_3} [normed_field 𝕜] [normed_group E] [normed_space 𝕜 E] {a : α → 𝕜} {b : α → 𝕜} {u : α → E} {v : α → E} {l : filter α} (hab : is_equivalent a b l) (huv : is_equivalent u v l) : is_equivalent (fun (x : α) => a x • u x) (fun (x : α) => b x • v x) l := sorry

theorem is_equivalent.mul {α : Type u_1} {β : Type u_2} [normed_field β] {t : α → β} {u : α → β} {v : α → β} {w : α → β} {l : filter α} (htu : is_equivalent t u l) (hvw : is_equivalent v w l) : is_equivalent (t * v) (u * w) l :=
  is_equivalent.smul htu hvw

theorem is_equivalent.inv {α : Type u_1} {β : Type u_2} [normed_field β] {u : α → β} {v : α → β} {l : filter α} (huv : is_equivalent u v l) : is_equivalent (fun (x : α) => u x⁻¹) (fun (x : α) => v x⁻¹) l := sorry

theorem is_equivalent.div {α : Type u_1} {β : Type u_2} [normed_field β] {t : α → β} {u : α → β} {v : α → β} {w : α → β} {l : filter α} (htu : is_equivalent t u l) (hvw : is_equivalent v w l) : is_equivalent (fun (x : α) => t x / v x) (fun (x : α) => u x / w x) l :=
  is_equivalent.mul htu (is_equivalent.inv hvw)

theorem is_equivalent.tendsto_at_top {α : Type u_1} {β : Type u_2} [normed_linear_ordered_field β] {u : α → β} {v : α → β} {l : filter α} [order_topology β] (huv : is_equivalent u v l) (hu : filter.tendsto u l filter.at_top) : filter.tendsto v l filter.at_top := sorry

theorem is_equivalent.tendsto_at_top_iff {α : Type u_1} {β : Type u_2} [normed_linear_ordered_field β] {u : α → β} {v : α → β} {l : filter α} [order_topology β] (huv : is_equivalent u v l) : filter.tendsto u l filter.at_top ↔ filter.tendsto v l filter.at_top :=
  { mp := is_equivalent.tendsto_at_top huv, mpr := is_equivalent.tendsto_at_top (is_equivalent.symm huv) }

