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

Unlike `is_[oO]` relations, this one requires `u` and `v` to have the same codomaine `ฮฒ`. While the
definition only requires `ฮฒ` to be a `normed_group`, most interesting properties require it to be a
`normed_field`.

## Notations

We introduce the notation `u ~[l] v := is_equivalent u v l`, which you can use by opening the
`asymptotics` locale.

## Main results

If `ฮฒ` is a `normed_group` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c โ  0`, this is true iff `tendsto u l (๐ c)` (see `is_equivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =แถ [l] 0` (see `is_equivalent_zero_iff_eventually_zero`)

If `ฮฒ` is a `normed_field` :

- Alternative characterization of the relation (see `is_equivalent_iff_exists_eq_mul`) :

  `u ~[l] v โ โ (ฯ : ฮฑ โ ฮฒ) (hฯ : tendsto ฯ l (๐ 1)), u =แถ [l] ฯ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v โ tendsto (u/v) l (๐ 1)`
  (see `is_equivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `tendsto u l (๐ c) โ tendsto v l (๐ c)`
  (see `is_equivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `is_equivalent.mul` and `is_equivalent.div`)

If `ฮฒ` is a `normed_linear_ordered_field` :

- If `u ~[l] v`, we have `tendsto u l at_top โ tendsto v l at_top`
  (see `is_equivalent.tendsto_at_top_iff`)

-/

namespace asymptotics


/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as x converges along `l`. -/
def is_equivalent {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] (u : ฮฑ โ ฮฒ) (v : ฮฑ โ ฮฒ) (l : filter ฮฑ) :=
  is_o (u - v) v l

theorem is_equivalent.is_o {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (h : is_equivalent u v l) : is_o (u - v) v l :=
  h

theorem is_equivalent.is_O {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (h : is_equivalent u v l) : is_O u v l :=
  iff.mp (is_O.congr_of_sub (is_O.symm (is_o.is_O h))) (is_O_refl (fun (x : ฮฑ) => v x) l)

theorem is_equivalent.is_O_symm {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (h : is_equivalent u v l) : is_O v u l := sorry

theorem is_equivalent.refl {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {l : filter ฮฑ} : is_equivalent u u l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_equivalent u u l)) (is_equivalent.equations._eqn_1 u u l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_o (u - u) u l)) (sub_self u))) (is_o_zero u l))

theorem is_equivalent.symm {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (h : is_equivalent u v l) : is_equivalent v u l :=
  is_o.symm (is_o.trans_is_O (is_equivalent.is_o h) (is_equivalent.is_O_symm h))

theorem is_equivalent.trans {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {w : ฮฑ โ ฮฒ} {l : filter ฮฑ} (huv : is_equivalent u v l) (hvw : is_equivalent v w l) : is_equivalent u w l :=
  is_o.triangle (is_o.trans_is_O (is_equivalent.is_o huv) (is_equivalent.is_O hvw)) (is_equivalent.is_o hvw)

theorem is_equivalent_zero_iff_eventually_zero {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {l : filter ฮฑ} : is_equivalent u 0 l โ filter.eventually_eq l u 0 :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (is_equivalent u 0 l โ filter.eventually_eq l u 0)) (is_equivalent.equations._eqn_1 u 0 l)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_o (u - 0) 0 l โ filter.eventually_eq l u 0)) (sub_zero u))) is_o_zero_right_iff)

theorem is_equivalent_const_iff_tendsto {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {l : filter ฮฑ} {c : ฮฒ} (h : c โ  0) : is_equivalent u (function.const ฮฑ c) l โ filter.tendsto u l (nhds c) := sorry

theorem is_equivalent.tendsto_const {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {l : filter ฮฑ} {c : ฮฒ} (hu : is_equivalent u (function.const ฮฑ c) l) : filter.tendsto u l (nhds c) := sorry

theorem is_equivalent.tendsto_nhds {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} {c : ฮฒ} (huv : is_equivalent u v l) (hu : filter.tendsto u l (nhds c)) : filter.tendsto v l (nhds c) := sorry

theorem is_equivalent.tendsto_nhds_iff {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_group ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} {c : ฮฒ} (huv : is_equivalent u v l) : filter.tendsto u l (nhds c) โ filter.tendsto v l (nhds c) :=
  { mp := is_equivalent.tendsto_nhds huv, mpr := is_equivalent.tendsto_nhds (is_equivalent.symm huv) }

theorem is_equivalent_iff_exists_eq_mul {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} : is_equivalent u v l โ โ (ฯ : ฮฑ โ ฮฒ), โ (hฯ : filter.tendsto ฯ l (nhds 1)), filter.eventually_eq l u (ฯ * v) := sorry

theorem is_equivalent.exists_eq_mul {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (huv : is_equivalent u v l) : โ (ฯ : ฮฑ โ ฮฒ), โ (hฯ : filter.tendsto ฯ l (nhds 1)), filter.eventually_eq l u (ฯ * v) :=
  iff.mp is_equivalent_iff_exists_eq_mul huv

theorem is_equivalent_of_tendsto_one {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (hz : filter.eventually (fun (x : ฮฑ) => v x = 0 โ u x = 0) l) (huv : filter.tendsto (u / v) l (nhds 1)) : is_equivalent u v l := sorry

theorem is_equivalent_of_tendsto_one' {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (hz : โ (x : ฮฑ), v x = 0 โ u x = 0) (huv : filter.tendsto (u / v) l (nhds 1)) : is_equivalent u v l :=
  is_equivalent_of_tendsto_one (filter.eventually_of_forall hz) huv

theorem is_equivalent_iff_tendsto_one {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (hz : filter.eventually (fun (x : ฮฑ) => v x โ  0) l) : is_equivalent u v l โ filter.tendsto (u / v) l (nhds 1) := sorry

theorem is_equivalent.smul {ฮฑ : Type u_1} {E : Type u_2} {๐ : Type u_3} [normed_field ๐] [normed_group E] [normed_space ๐ E] {a : ฮฑ โ ๐} {b : ฮฑ โ ๐} {u : ฮฑ โ E} {v : ฮฑ โ E} {l : filter ฮฑ} (hab : is_equivalent a b l) (huv : is_equivalent u v l) : is_equivalent (fun (x : ฮฑ) => a x โข u x) (fun (x : ฮฑ) => b x โข v x) l := sorry

theorem is_equivalent.mul {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {t : ฮฑ โ ฮฒ} {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {w : ฮฑ โ ฮฒ} {l : filter ฮฑ} (htu : is_equivalent t u l) (hvw : is_equivalent v w l) : is_equivalent (t * v) (u * w) l :=
  is_equivalent.smul htu hvw

theorem is_equivalent.inv {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} (huv : is_equivalent u v l) : is_equivalent (fun (x : ฮฑ) => u xโปยน) (fun (x : ฮฑ) => v xโปยน) l := sorry

theorem is_equivalent.div {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_field ฮฒ] {t : ฮฑ โ ฮฒ} {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {w : ฮฑ โ ฮฒ} {l : filter ฮฑ} (htu : is_equivalent t u l) (hvw : is_equivalent v w l) : is_equivalent (fun (x : ฮฑ) => t x / v x) (fun (x : ฮฑ) => u x / w x) l :=
  is_equivalent.mul htu (is_equivalent.inv hvw)

theorem is_equivalent.tendsto_at_top {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_linear_ordered_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} [order_topology ฮฒ] (huv : is_equivalent u v l) (hu : filter.tendsto u l filter.at_top) : filter.tendsto v l filter.at_top := sorry

theorem is_equivalent.tendsto_at_top_iff {ฮฑ : Type u_1} {ฮฒ : Type u_2} [normed_linear_ordered_field ฮฒ] {u : ฮฑ โ ฮฒ} {v : ฮฑ โ ฮฒ} {l : filter ฮฑ} [order_topology ฮฒ] (huv : is_equivalent u v l) : filter.tendsto u l filter.at_top โ filter.tendsto v l filter.at_top :=
  { mp := is_equivalent.tendsto_at_top huv, mpr := is_equivalent.tendsto_at_top (is_equivalent.symm huv) }

