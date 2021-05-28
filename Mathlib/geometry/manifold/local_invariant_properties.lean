/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.smooth_manifold_with_corners
import Mathlib.PostPort

universes u_1 u_3 l u_2 u_4 

namespace Mathlib

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `local_invariant_prop G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `charted_space.lift_prop_within_at` (resp. `lift_prop_at`, `lift_prop_on` and `lift_prop`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : local_invariant_prop G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.lift_prop_within_at_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.lift_prop_within_at_congr` saying that if `lift_prop_within_at P g s x` holds, and `g` and `g'`
coincide on `s`, then `lift_prop_within_at P g' s x` holds. We can't call it
`lift_prop_within_at.congr` as it is in the namespace associated to `local_invariant_prop`, not
in the one for `lift_prop_within_at`.
-/

namespace structure_groupoid


/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
structure local_invariant_prop {H : Type u_1} [topological_space H] {H' : Type u_3} [topological_space H'] (G : structure_groupoid H) (G' : structure_groupoid H') (P : (H → H') → set H → H → Prop) 
where
  is_local : ∀ {s : set H} {x : H} {u : set H} {f : H → H'}, is_open u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance : ∀ {s : set H} {x : H} {f : H → H'} {e : local_homeomorph H H},
  e ∈ G →
    x ∈ local_equiv.source (local_homeomorph.to_local_equiv e) →
      P f s x →
        P (f ∘ ⇑(local_homeomorph.symm e))
          (local_equiv.target (local_homeomorph.to_local_equiv e) ∩ ⇑(local_homeomorph.symm e) ⁻¹' s) (coe_fn e x)
  congr : ∀ {s : set H} {x : H} {f g : H → H'}, (∀ (y : H), y ∈ s → f y = g y) → f x = g x → P f s x → P g s x
  left_invariance : ∀ {s : set H} {x : H} {f : H → H'} {e' : local_homeomorph H' H'},
  e' ∈ G' →
    s ⊆ f ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv e') →
      f x ∈ local_equiv.source (local_homeomorph.to_local_equiv e') → P f s x → P (⇑e' ∘ f) s x

end structure_groupoid


/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`lift_prop_within_at_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
def charted_space.lift_prop_within_at {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] (P : (H → H') → set H → H → Prop) (f : M → M') (s : set M) (x : M)  :=
  continuous_within_at f s x ∧
    P (⇑(charted_space.chart_at H' (f x)) ∘ f ∘ ⇑(local_homeomorph.symm (charted_space.chart_at H x)))
      (local_equiv.target (local_homeomorph.to_local_equiv (charted_space.chart_at H x)) ∩
        ⇑(local_homeomorph.symm (charted_space.chart_at H x)) ⁻¹'
          (s ∩ f ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv (charted_space.chart_at H' (f x)))))
      (coe_fn (charted_space.chart_at H x) x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def charted_space.lift_prop_on {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] (P : (H → H') → set H → H → Prop) (f : M → M') (s : set M)  :=
  ∀ (x : M), x ∈ s → charted_space.lift_prop_within_at P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def charted_space.lift_prop_at {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] (P : (H → H') → set H → H → Prop) (f : M → M') (x : M)  :=
  charted_space.lift_prop_within_at P f set.univ x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
def charted_space.lift_prop {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] (P : (H → H') → set H → H → Prop) (f : M → M')  :=
  ∀ (x : M), charted_space.lift_prop_at P f x

namespace structure_groupoid


theorem lift_prop_within_at_univ {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {P : (H → H') → set H → H → Prop} {g : M → M'} {x : M} : charted_space.lift_prop_within_at P g set.univ x ↔ charted_space.lift_prop_at P g x :=
  iff.rfl

theorem lift_prop_on_univ {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {P : (H → H') → set H → H → Prop} {g : M → M'} : charted_space.lift_prop_on P g set.univ ↔ charted_space.lift_prop P g := sorry

namespace local_invariant_prop


/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
theorem lift_prop_within_at_indep_chart_aux {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {e : local_homeomorph M H} {e' : local_homeomorph M H} {f : local_homeomorph M' H'} {f' : local_homeomorph M' H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (he : e ∈ maximal_atlas M G) (xe : x ∈ local_equiv.source (local_homeomorph.to_local_equiv e)) (he' : e' ∈ maximal_atlas M G) (xe' : x ∈ local_equiv.source (local_homeomorph.to_local_equiv e')) (hf : f ∈ maximal_atlas M' G') (xf : g x ∈ local_equiv.source (local_homeomorph.to_local_equiv f)) (hf' : f' ∈ maximal_atlas M' G') (xf' : g x ∈ local_equiv.source (local_homeomorph.to_local_equiv f')) (hgs : continuous_within_at g s x) (h : P (⇑f ∘ g ∘ ⇑(local_homeomorph.symm e))
  (local_equiv.target (local_homeomorph.to_local_equiv e) ∩
    ⇑(local_homeomorph.symm e) ⁻¹' (s ∩ g ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv f)))
  (coe_fn e x)) : P (⇑f' ∘ g ∘ ⇑(local_homeomorph.symm e'))
  (local_equiv.target (local_homeomorph.to_local_equiv e') ∩
    ⇑(local_homeomorph.symm e') ⁻¹' (s ∩ g ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv f')))
  (coe_fn e' x) := sorry

theorem lift_prop_within_at_indep_chart {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {e : local_homeomorph M H} {f : local_homeomorph M' H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) [has_groupoid M G] [has_groupoid M' G'] (he : e ∈ maximal_atlas M G) (xe : x ∈ local_equiv.source (local_homeomorph.to_local_equiv e)) (hf : f ∈ maximal_atlas M' G') (xf : g x ∈ local_equiv.source (local_homeomorph.to_local_equiv f)) : charted_space.lift_prop_within_at P g s x ↔
  continuous_within_at g s x ∧
    P (⇑f ∘ g ∘ ⇑(local_homeomorph.symm e))
      (local_equiv.target (local_homeomorph.to_local_equiv e) ∩
        ⇑(local_homeomorph.symm e) ⁻¹' (s ∩ g ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv f)))
      (coe_fn e x) := sorry

theorem lift_prop_on_indep_chart {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {e : local_homeomorph M H} {f : local_homeomorph M' H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} (hG : local_invariant_prop G G' P) [has_groupoid M G] [has_groupoid M' G'] (he : e ∈ maximal_atlas M G) (hf : f ∈ maximal_atlas M' G') (h : charted_space.lift_prop_on P g s) (y : H) : y ∈
    local_equiv.target (local_homeomorph.to_local_equiv e) ∩
      ⇑(local_homeomorph.symm e) ⁻¹' (s ∩ g ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv f)) →
  P (⇑f ∘ g ∘ ⇑(local_homeomorph.symm e))
    (local_equiv.target (local_homeomorph.to_local_equiv e) ∩
      ⇑(local_homeomorph.symm e) ⁻¹' (s ∩ g ⁻¹' local_equiv.source (local_homeomorph.to_local_equiv f)))
    y := sorry

theorem lift_prop_within_at_inter' {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {t : set M} {x : M} (hG : local_invariant_prop G G' P) (ht : t ∈ nhds_within x s) : charted_space.lift_prop_within_at P g (s ∩ t) x ↔ charted_space.lift_prop_within_at P g s x := sorry

theorem lift_prop_within_at_inter {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {t : set M} {x : M} (hG : local_invariant_prop G G' P) (ht : t ∈ nhds x) : charted_space.lift_prop_within_at P g (s ∩ t) x ↔ charted_space.lift_prop_within_at P g s x :=
  lift_prop_within_at_inter' hG (mem_nhds_within_of_mem_nhds ht)

theorem lift_prop_at_of_lift_prop_within_at {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (h : charted_space.lift_prop_within_at P g s x) (hs : s ∈ nhds x) : charted_space.lift_prop_at P g x := sorry

theorem lift_prop_within_at_of_lift_prop_at_of_mem_nhds {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (h : charted_space.lift_prop_at P g x) (hs : s ∈ nhds x) : charted_space.lift_prop_within_at P g s x := sorry

theorem lift_prop_on_of_locally_lift_prop_on {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} (hG : local_invariant_prop G G' P) (h : ∀ (x : M), x ∈ s → ∃ (u : set M), is_open u ∧ x ∈ u ∧ charted_space.lift_prop_on P g (s ∩ u)) : charted_space.lift_prop_on P g s := sorry

theorem lift_prop_of_locally_lift_prop_on {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} (hG : local_invariant_prop G G' P) (h : ∀ (x : M), ∃ (u : set M), is_open u ∧ x ∈ u ∧ charted_space.lift_prop_on P g u) : charted_space.lift_prop P g := sorry

theorem lift_prop_within_at_congr {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (h : charted_space.lift_prop_within_at P g s x) (h₁ : ∀ (y : M), y ∈ s → g' y = g y) (hx : g' x = g x) : charted_space.lift_prop_within_at P g' s x := sorry

theorem lift_prop_within_at_congr_iff {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (h₁ : ∀ (y : M), y ∈ s → g' y = g y) (hx : g' x = g x) : charted_space.lift_prop_within_at P g' s x ↔ charted_space.lift_prop_within_at P g s x := sorry

theorem lift_prop_within_at_congr_of_eventually_eq {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (h : charted_space.lift_prop_within_at P g s x) (h₁ : filter.eventually_eq (nhds_within x s) g' g) (hx : g' x = g x) : charted_space.lift_prop_within_at P g' s x := sorry

theorem lift_prop_within_at_congr_iff_of_eventually_eq {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {s : set M} {x : M} (hG : local_invariant_prop G G' P) (h₁ : filter.eventually_eq (nhds_within x s) g' g) (hx : g' x = g x) : charted_space.lift_prop_within_at P g' s x ↔ charted_space.lift_prop_within_at P g s x := sorry

theorem lift_prop_at_congr_of_eventually_eq {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {x : M} (hG : local_invariant_prop G G' P) (h : charted_space.lift_prop_at P g x) (h₁ : filter.eventually_eq (nhds x) g' g) : charted_space.lift_prop_at P g' x := sorry

theorem lift_prop_at_congr_iff_of_eventually_eq {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {x : M} (hG : local_invariant_prop G G' P) (h₁ : filter.eventually_eq (nhds x) g' g) : charted_space.lift_prop_at P g' x ↔ charted_space.lift_prop_at P g x := sorry

theorem lift_prop_on_congr {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {s : set M} (hG : local_invariant_prop G G' P) (h : charted_space.lift_prop_on P g s) (h₁ : ∀ (y : M), y ∈ s → g' y = g y) : charted_space.lift_prop_on P g' s :=
  fun (x : M) (hx : x ∈ s) => lift_prop_within_at_congr hG (h x hx) h₁ (h₁ x hx)

theorem lift_prop_on_congr_iff {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {G : structure_groupoid H} {G' : structure_groupoid H'} {P : (H → H') → set H → H → Prop} {g : M → M'} {g' : M → M'} {s : set M} (hG : local_invariant_prop G G' P) (h₁ : ∀ (y : M), y ∈ s → g' y = g y) : charted_space.lift_prop_on P g' s ↔ charted_space.lift_prop_on P g s := sorry

theorem lift_prop_within_at_mono {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {t : set M} {x : M} (mono : ∀ {s : set H} {x : H} {t : set H} {f : H → H'}, t ⊆ s → P f s x → P f t x) (h : charted_space.lift_prop_within_at P g t x) (hst : s ⊆ t) : charted_space.lift_prop_within_at P g s x := sorry

theorem lift_prop_within_at_of_lift_prop_at {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {x : M} (mono : ∀ {s : set H} {x : H} {t : set H} {f : H → H'}, t ⊆ s → P f s x → P f t x) (h : charted_space.lift_prop_at P g x) : charted_space.lift_prop_within_at P g s x :=
  lift_prop_within_at_mono mono
    (eq.mp (Eq._oldrec (Eq.refl (charted_space.lift_prop_at P g x)) (Eq.symm (propext lift_prop_within_at_univ))) h)
    (set.subset_univ s)

theorem lift_prop_on_mono {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} {t : set M} (mono : ∀ {s : set H} {x : H} {t : set H} {f : H → H'}, t ⊆ s → P f s x → P f t x) (h : charted_space.lift_prop_on P g t) (hst : s ⊆ t) : charted_space.lift_prop_on P g s :=
  fun (x : M) (hx : x ∈ s) => lift_prop_within_at_mono mono (h x (hst hx)) hst

theorem lift_prop_on_of_lift_prop {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {H' : Type u_3} {M' : Type u_4} [topological_space H'] [topological_space M'] [charted_space H' M'] {P : (H → H') → set H → H → Prop} {g : M → M'} {s : set M} (mono : ∀ {s : set H} {x : H} {t : set H} {f : H → H'}, t ⊆ s → P f s x → P f t x) (h : charted_space.lift_prop P g) : charted_space.lift_prop_on P g s :=
  lift_prop_on_mono mono
    (eq.mp (Eq._oldrec (Eq.refl (charted_space.lift_prop P g)) (Eq.symm (propext lift_prop_on_univ))) h)
    (set.subset_univ s)

theorem lift_prop_at_of_mem_maximal_atlas {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {e : local_homeomorph M H} {x : M} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) (he : e ∈ maximal_atlas M G) (hx : x ∈ local_equiv.source (local_homeomorph.to_local_equiv e)) : charted_space.lift_prop_at Q (⇑e) x := sorry

theorem lift_prop_on_of_mem_maximal_atlas {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {e : local_homeomorph M H} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) (he : e ∈ maximal_atlas M G) : charted_space.lift_prop_on Q (⇑e) (local_equiv.source (local_homeomorph.to_local_equiv e)) := sorry

theorem lift_prop_at_symm_of_mem_maximal_atlas {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {e : local_homeomorph M H} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] {x : H} (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) (he : e ∈ maximal_atlas M G) (hx : x ∈ local_equiv.target (local_homeomorph.to_local_equiv e)) : charted_space.lift_prop_at Q (⇑(local_homeomorph.symm e)) x := sorry

theorem lift_prop_on_symm_of_mem_maximal_atlas {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {e : local_homeomorph M H} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) (he : e ∈ maximal_atlas M G) : charted_space.lift_prop_on Q (⇑(local_homeomorph.symm e)) (local_equiv.target (local_homeomorph.to_local_equiv e)) := sorry

theorem lift_prop_at_chart {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {x : M} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) : charted_space.lift_prop_at Q (⇑(charted_space.chart_at H x)) x :=
  lift_prop_at_of_mem_maximal_atlas hG hQ (chart_mem_maximal_atlas G x) (charted_space.mem_chart_source H x)

theorem lift_prop_on_chart {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {x : M} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) : charted_space.lift_prop_on Q (⇑(charted_space.chart_at H x))
  (local_equiv.source (local_homeomorph.to_local_equiv (charted_space.chart_at H x))) :=
  lift_prop_on_of_mem_maximal_atlas hG hQ (chart_mem_maximal_atlas G x)

theorem lift_prop_at_chart_symm {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {x : M} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) : charted_space.lift_prop_at Q (⇑(local_homeomorph.symm (charted_space.chart_at H x)))
  (coe_fn (charted_space.chart_at H x) x) := sorry

theorem lift_prop_on_chart_symm {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {x : M} {Q : (H → H) → set H → H → Prop} [has_groupoid M G] (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) : charted_space.lift_prop_on Q (⇑(local_homeomorph.symm (charted_space.chart_at H x)))
  (local_equiv.target (local_homeomorph.to_local_equiv (charted_space.chart_at H x))) :=
  lift_prop_on_symm_of_mem_maximal_atlas hG hQ (chart_mem_maximal_atlas G x)

theorem lift_prop_id {H : Type u_1} {M : Type u_2} [topological_space H] [topological_space M] [charted_space H M] {G : structure_groupoid H} {Q : (H → H) → set H → H → Prop} (hG : local_invariant_prop G G Q) (hQ : ∀ (y : H), Q id set.univ y) : charted_space.lift_prop Q id := sorry

end local_invariant_prop


/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def is_local_structomorph_within_at {H : Type u_1} [topological_space H] (G : structure_groupoid H) (f : H → H) (s : set H) (x : H)  :=
  x ∈ s →
    ∃ (e : local_homeomorph H H),
      e ∈ G ∧
        set.eq_on f (local_equiv.to_fun (local_homeomorph.to_local_equiv e))
            (s ∩ local_equiv.source (local_homeomorph.to_local_equiv e)) ∧
          x ∈ local_equiv.source (local_homeomorph.to_local_equiv e)

/-- For a groupoid `G` which is `closed_under_restriction`, being a local structomorphism is a local
invariant property. -/
theorem is_local_structomorph_within_at_local_invariant_prop {H : Type u_1} [topological_space H] (G : structure_groupoid H) [closed_under_restriction G] : local_invariant_prop G G (is_local_structomorph_within_at G) := sorry

