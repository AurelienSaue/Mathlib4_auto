/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.specific_limits
import Mathlib.data.setoid.basic
import Mathlib.dynamics.fixed_points.topology
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.

## Main definitions

* `contracting_with K f` : a Lipschitz continuous self-map with `K < 1`;
* `efixed_point` : given a contracting map `f` on a complete emetric space and a point `x`
  such that `edist x (f x) < ∞`, `efixed_point f hf x hx` is the unique fixed point of `f`
  in `emetric.ball x ∞`;
* `fixed_point` : the unique fixed point of a contracting map on a complete nonempty metric space.

## Tags

contracting map, fixed point, Banach fixed point theorem
-/

/-- A map is said to be `contracting_with K`, if `K < 1` and `f` is `lipschitz_with K`. -/
def contracting_with {α : Type u_1} [emetric_space α] (K : nnreal) (f : α → α) :=
  K < 1 ∧ lipschitz_with K f

namespace contracting_with


theorem to_lipschitz_with {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) : lipschitz_with K f :=
  and.right hf

theorem one_sub_K_pos' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) : 0 < 1 - ↑K :=
  sorry

theorem one_sub_K_ne_zero {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) : 1 - ↑K ≠ 0 :=
  ne_of_gt (one_sub_K_pos' hf)

theorem one_sub_K_ne_top {K : nnreal} : 1 - ↑K ≠ ⊤ := sorry

theorem edist_inequality {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) {x : α} {y : α} (h : edist x y < ⊤) :
    edist x y ≤ (edist x (f x) + edist y (f y)) / (1 - ↑K) :=
  sorry

theorem edist_le_of_fixed_point {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) {x : α} {y : α} (h : edist x y < ⊤)
    (hy : function.is_fixed_pt f y) : edist x y ≤ edist x (f x) / (1 - ↑K) :=
  sorry

theorem eq_or_edist_eq_top_of_fixed_points {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) {x : α} {y : α} (hx : function.is_fixed_pt f x)
    (hy : function.is_fixed_pt f y) : x = y ∨ edist x y = ⊤ :=
  sorry

/-- If a map `f` is `contracting_with K`, and `s` is a forward-invariant set, then
restriction of `f` to `s` is `contracting_with K` as well. -/
theorem restrict {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) {s : set α} (hs : set.maps_to f s s) :
    contracting_with K (set.maps_to.restrict f s s hs) :=
  { left := and.left hf, right := fun (x y : ↥s) => and.right hf ↑x ↑y }

/-- Banach fixed-point theorem, contraction mapping theorem, `emetric_space` version.
A contracting map on a complete metric space has a fixed point.
We include more conclusions in this theorem to avoid proving them again later.

The main API for this theorem are the functions `efixed_point` and `fixed_point`,
and lemmas about these functions. -/
theorem exists_fixed_point {α : Type u_1} [emetric_space α] [cs : complete_space α] {K : nnreal}
    {f : α → α} (hf : contracting_with K f) (x : α) (hx : edist x (f x) < ⊤) :
    ∃ (y : α),
        function.is_fixed_pt f y ∧
          filter.tendsto (fun (n : ℕ) => nat.iterate f n x) filter.at_top (nhds y) ∧
            ∀ (n : ℕ), edist (nat.iterate f n x) y ≤ edist x (f x) * ↑K ^ n / (1 - ↑K) :=
  sorry

/-- Let `x` be a point of a complete emetric space. Suppose that `f` is a contracting map,
and `edist x (f x) < ∞`. Then `efixed_point` is the unique fixed point of `f`
in `emetric.ball x ∞`. -/
def efixed_point {α : Type u_1} [emetric_space α] [cs : complete_space α] {K : nnreal} (f : α → α)
    (hf : contracting_with K f) (x : α) (hx : edist x (f x) < ⊤) : α :=
  classical.some (exists_fixed_point hf x hx)

theorem efixed_point_is_fixed_pt {α : Type u_1} [emetric_space α] [cs : complete_space α]
    {K : nnreal} {f : α → α} (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
    function.is_fixed_pt f (efixed_point f hf x hx) :=
  and.left (classical.some_spec (exists_fixed_point hf x hx))

theorem tendsto_iterate_efixed_point {α : Type u_1} [emetric_space α] [cs : complete_space α]
    {K : nnreal} {f : α → α} (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
    filter.tendsto (fun (n : ℕ) => nat.iterate f n x) filter.at_top
        (nhds (efixed_point f hf x hx)) :=
  and.left (and.right (classical.some_spec (exists_fixed_point hf x hx)))

theorem apriori_edist_iterate_efixed_point_le {α : Type u_1} [emetric_space α]
    [cs : complete_space α] {K : nnreal} {f : α → α} (hf : contracting_with K f) {x : α}
    (hx : edist x (f x) < ⊤) (n : ℕ) :
    edist (nat.iterate f n x) (efixed_point f hf x hx) ≤ edist x (f x) * ↑K ^ n / (1 - ↑K) :=
  and.right (and.right (classical.some_spec (exists_fixed_point hf x hx))) n

theorem edist_efixed_point_le {α : Type u_1} [emetric_space α] [cs : complete_space α] {K : nnreal}
    {f : α → α} (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
    edist x (efixed_point f hf x hx) ≤ edist x (f x) / (1 - ↑K) :=
  sorry

theorem edist_efixed_point_lt_top {α : Type u_1} [emetric_space α] [cs : complete_space α]
    {K : nnreal} {f : α → α} (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) :
    edist x (efixed_point f hf x hx) < ⊤ :=
  lt_of_le_of_lt (edist_efixed_point_le hf hx)
    (ennreal.mul_lt_top hx
      (iff.mpr ennreal.lt_top_iff_ne_top (iff.mpr ennreal.inv_ne_top (one_sub_K_ne_zero hf))))

theorem efixed_point_eq_of_edist_lt_top {α : Type u_1} [emetric_space α] [cs : complete_space α]
    {K : nnreal} {f : α → α} (hf : contracting_with K f) {x : α} (hx : edist x (f x) < ⊤) {y : α}
    (hy : edist y (f y) < ⊤) (h : edist x y < ⊤) :
    efixed_point f hf x hx = efixed_point f hf y hy :=
  sorry

/-- Banach fixed-point theorem for maps contracting on a complete subset. -/
theorem exists_fixed_point' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α} {s : set α}
    (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) :
    ∃ (y : α),
        ∃ (H : y ∈ s),
          function.is_fixed_pt f y ∧
            filter.tendsto (fun (n : ℕ) => nat.iterate f n x) filter.at_top (nhds y) ∧
              ∀ (n : ℕ), edist (nat.iterate f n x) y ≤ edist x (f x) * ↑K ^ n / (1 - ↑K) :=
  sorry

/-- Let `s` be a complete forward-invariant set of a self-map `f`. If `f` contracts on `s`
and `x ∈ s` satisfies `edist x (f x) < ⊤`, then `efixed_point'` is the unique fixed point
of the restriction of `f` to `s ∩ emetric.ball x ⊤`. -/
def efixed_point' {α : Type u_1} [emetric_space α] {K : nnreal} (f : α → α) {s : set α}
    (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) (x : α) (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) : α :=
  classical.some (exists_fixed_point' hsc hsf hf hxs hx)

theorem efixed_point_mem' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α} {s : set α}
    (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) : efixed_point' f hsc hsf hf x hxs hx ∈ s :=
  Exists.fst (classical.some_spec (exists_fixed_point' hsc hsf hf hxs hx))

theorem efixed_point_is_fixed_pt' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    {s : set α} (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) : function.is_fixed_pt f (efixed_point' f hsc hsf hf x hxs hx) :=
  and.left (Exists.snd (classical.some_spec (exists_fixed_point' hsc hsf hf hxs hx)))

theorem tendsto_iterate_efixed_point' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    {s : set α} (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) :
    filter.tendsto (fun (n : ℕ) => nat.iterate f n x) filter.at_top
        (nhds (efixed_point' f hsc hsf hf x hxs hx)) :=
  and.left (and.right (Exists.snd (classical.some_spec (exists_fixed_point' hsc hsf hf hxs hx))))

theorem apriori_edist_iterate_efixed_point_le' {α : Type u_1} [emetric_space α] {K : nnreal}
    {f : α → α} {s : set α} (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) (n : ℕ) :
    edist (nat.iterate f n x) (efixed_point' f hsc hsf hf x hxs hx) ≤
        edist x (f x) * ↑K ^ n / (1 - ↑K) :=
  and.right (and.right (Exists.snd (classical.some_spec (exists_fixed_point' hsc hsf hf hxs hx)))) n

theorem edist_efixed_point_le' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α} {s : set α}
    (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) :
    edist x (efixed_point' f hsc hsf hf x hxs hx) ≤ edist x (f x) / (1 - ↑K) :=
  sorry

theorem edist_efixed_point_lt_top' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    {s : set α} (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hf : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) : edist x (efixed_point' f hsc hsf hf x hxs hx) < ⊤ :=
  lt_of_le_of_lt (edist_efixed_point_le' hsc hsf hf hxs hx)
    (ennreal.mul_lt_top hx
      (iff.mpr ennreal.lt_top_iff_ne_top (iff.mpr ennreal.inv_ne_top (one_sub_K_ne_zero hf))))

/-- If a globally contracting map `f` has two complete forward-invariant sets `s`, `t`,
and `x ∈ s` is at a finite distance from `y ∈ t`, then the `efixed_point'` constructed by `x`
is the same as the `efixed_point'` constructed by `y`.

This lemma takes additional arguments stating that `f` contracts on `s` and `t` because this way
it can be used to prove the desired equality with non-trivial proofs of these facts. -/
theorem efixed_point_eq_of_edist_lt_top' {α : Type u_1} [emetric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) {s : set α} (hsc : is_complete s) (hsf : set.maps_to f s s)
    (hfs : contracting_with K (set.maps_to.restrict f s s hsf)) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) < ⊤) {t : set α} (htc : is_complete t) (htf : set.maps_to f t t)
    (hft : contracting_with K (set.maps_to.restrict f t t htf)) {y : α} (hyt : y ∈ t)
    (hy : edist y (f y) < ⊤) (hxy : edist x y < ⊤) :
    efixed_point' f hsc hsf hfs x hxs hx = efixed_point' f htc htf hft y hyt hy :=
  sorry

end contracting_with


namespace contracting_with


theorem one_sub_K_pos {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) : 0 < 1 - ↑K :=
  iff.mpr sub_pos (and.left hf)

theorem dist_le_mul {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) (x : α) (y : α) : dist (f x) (f y) ≤ ↑K * dist x y :=
  lipschitz_with.dist_le_mul (to_lipschitz_with hf) x y

theorem dist_inequality {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) (x : α) (y : α) :
    dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - ↑K) :=
  sorry

theorem dist_le_of_fixed_point {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) (x : α) {y : α} (hy : function.is_fixed_pt f y) :
    dist x y ≤ dist x (f x) / (1 - ↑K) :=
  sorry

theorem fixed_point_unique' {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) {x : α} {y : α} (hx : function.is_fixed_pt f x)
    (hy : function.is_fixed_pt f y) : x = y :=
  or.resolve_right (eq_or_edist_eq_top_of_fixed_points hf hx hy) (edist_ne_top x y)

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
theorem dist_fixed_point_fixed_point_of_dist_le' {α : Type u_1} [metric_space α] {K : nnreal}
    {f : α → α} (hf : contracting_with K f) (g : α → α) {x : α} {y : α}
    (hx : function.is_fixed_pt f x) (hy : function.is_fixed_pt g y) {C : ℝ}
    (hfg : ∀ (z : α), dist (f z) (g z) ≤ C) : dist x y ≤ C / (1 - ↑K) :=
  sorry

/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
def fixed_point {α : Type u_1} [metric_space α] {K : nnreal} (f : α → α) (hf : contracting_with K f)
    [Nonempty α] [complete_space α] : α :=
  efixed_point f hf (Classical.choice _inst_2) sorry

/-- The point provided by `contracting_with.fixed_point` is actually a fixed point. -/
theorem fixed_point_is_fixed_pt {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) [Nonempty α] [complete_space α] :
    function.is_fixed_pt f (fixed_point f hf) :=
  efixed_point_is_fixed_pt hf (fixed_point._proof_1 f)

theorem fixed_point_unique {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) [Nonempty α] [complete_space α] {x : α}
    (hx : function.is_fixed_pt f x) : x = fixed_point f hf :=
  fixed_point_unique' hf hx (fixed_point_is_fixed_pt hf)

theorem dist_fixed_point_le {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) [Nonempty α] [complete_space α] (x : α) :
    dist x (fixed_point f hf) ≤ dist x (f x) / (1 - ↑K) :=
  dist_le_of_fixed_point hf x (fixed_point_is_fixed_pt hf)

/-- Aposteriori estimates on the convergence of iterates to the fixed point. -/
theorem aposteriori_dist_iterate_fixed_point_le {α : Type u_1} [metric_space α] {K : nnreal}
    {f : α → α} (hf : contracting_with K f) [Nonempty α] [complete_space α] (x : α) (n : ℕ) :
    dist (nat.iterate f n x) (fixed_point f hf) ≤
        dist (nat.iterate f n x) (nat.iterate f (n + 1) x) / (1 - ↑K) :=
  sorry

theorem apriori_dist_iterate_fixed_point_le {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) [Nonempty α] [complete_space α] (x : α) (n : ℕ) :
    dist (nat.iterate f n x) (fixed_point f hf) ≤ dist x (f x) * ↑K ^ n / (1 - ↑K) :=
  le_trans (aposteriori_dist_iterate_fixed_point_le hf x n)
    (iff.mpr (div_le_div_right (one_sub_K_pos hf))
      (lipschitz_with.dist_iterate_succ_le_geometric (to_lipschitz_with hf) x n))

theorem tendsto_iterate_fixed_point {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) [Nonempty α] [complete_space α] (x : α) :
    filter.tendsto (fun (n : ℕ) => nat.iterate f n x) filter.at_top (nhds (fixed_point f hf)) :=
  sorry

theorem fixed_point_lipschitz_in_map {α : Type u_1} [metric_space α] {K : nnreal} {f : α → α}
    (hf : contracting_with K f) [Nonempty α] [complete_space α] {g : α → α}
    (hg : contracting_with K g) {C : ℝ} (hfg : ∀ (z : α), dist (f z) (g z) ≤ C) :
    dist (fixed_point f hf) (fixed_point g hg) ≤ C / (1 - ↑K) :=
  dist_fixed_point_fixed_point_of_dist_le' hf g (fixed_point_is_fixed_pt hf)
    (fixed_point_is_fixed_pt hg) hfg

end Mathlib