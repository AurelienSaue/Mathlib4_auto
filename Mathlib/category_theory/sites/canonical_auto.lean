/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.sites.sheaf_of_types
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# The canonical topology on a category

We define the finest (largest) Grothendieck topology for which a given presheaf `P` is a sheaf.
This is well defined since if `P` is a sheaf for a topology `J`, then it is a sheaf for any
coarser (smaller) topology. Nonetheless we define the topology explicitly by specifying its sieves:
A sieve `S` on `X` is covering for `finest_topology_single P` iff
  for any `f : Y ⟶ X`, `P` satisfies the sheaf axiom for `S.pullback f`.
Showing that this is a genuine Grothendieck topology (namely that it satisfies the transitivity
axiom) forms the bulk of this file.

This generalises to a set of presheaves, giving the topology `finest_topology Ps` which is the
finest topology for which every presheaf in `Ps` is a sheaf.
Using `Ps` as the set of representable presheaves defines the `canonical_topology`: the finest
topology for which every representable is a sheaf.

A Grothendieck topology is called `subcanonical` if it is smaller than the canonical topology,
equivalently it is subcanonical iff every representable presheaf is a sheaf.

## References
* https://ncatlab.org/nlab/show/canonical+topology
* https://ncatlab.org/nlab/show/subcanonical+coverage
* https://stacks.math.columbia.edu/tag/00Z9
* https://math.stackexchange.com/a/358709/
-/

namespace category_theory


namespace sheaf


/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `is_sheaf_for_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
theorem is_sheaf_for_bind {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) (U : sieve X)
    (B : {Y : C} → {f : Y ⟶ X} → coe_fn U Y f → sieve Y) (hU : presieve.is_sheaf_for P ⇑U)
    (hB : ∀ {Y : C} {f : Y ⟶ X} (hf : coe_fn U Y f), presieve.is_sheaf_for P ⇑(B hf))
    (hB' :
      ∀ {Y : C} {f : Y ⟶ X} (h : coe_fn U Y f) {Z : C} (g : Z ⟶ Y),
        presieve.is_separated_for P ⇑(sieve.pullback g (B h))) :
    presieve.is_sheaf_for P ⇑(sieve.bind (⇑U) B) :=
  sorry

/--
Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `finest_topology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
theorem is_sheaf_for_trans {C : Type u} [category C] {X : C} (P : Cᵒᵖ ⥤ Type v) (R : sieve X)
    (S : sieve X) (hR : presieve.is_sheaf_for P ⇑R)
    (hR' : ∀ {Y : C} {f : Y ⟶ X}, coe_fn S Y f → presieve.is_separated_for P ⇑(sieve.pullback f R))
    (hS : ∀ {Y : C} {f : Y ⟶ X}, coe_fn R Y f → presieve.is_sheaf_for P ⇑(sieve.pullback f S)) :
    presieve.is_sheaf_for P ⇑S :=
  sorry

/--
Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf.

This is a special case of https://stacks.math.columbia.edu/tag/00Z9, but following a different
proof (see the comments there).
-/
def finest_topology_single {C : Type u} [category C] (P : Cᵒᵖ ⥤ Type v) : grothendieck_topology C :=
  grothendieck_topology.mk
    (fun (X : C) (S : sieve X) =>
      ∀ (Y : C) (f : Y ⟶ X), presieve.is_sheaf_for P ⇑(sieve.pullback f S))
    sorry sorry sorry

/--
Construct the finest (largest) Grothendieck topology for which all the given presheaves are sheaves.

This is equal to the construction of https://stacks.math.columbia.edu/tag/00Z9.
-/
def finest_topology {C : Type u} [category C] (Ps : set (Cᵒᵖ ⥤ Type v)) : grothendieck_topology C :=
  Inf (finest_topology_single '' Ps)

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
theorem sheaf_for_finest_topology {C : Type u} [category C] {P : Cᵒᵖ ⥤ Type v}
    (Ps : set (Cᵒᵖ ⥤ Type v)) (h : P ∈ Ps) : presieve.is_sheaf (finest_topology Ps) P :=
  sorry

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finest_topology Ps`.
-/
theorem le_finest_topology {C : Type u} [category C] (Ps : set (Cᵒᵖ ⥤ Type v))
    (J : grothendieck_topology C) (hJ : ∀ (P : Cᵒᵖ ⥤ Type v), P ∈ Ps → presieve.is_sheaf J P) :
    J ≤ finest_topology Ps :=
  sorry

/--
The `canonical_topology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf.

See https://stacks.math.columbia.edu/tag/00ZA
-/
def canonical_topology (C : Type u) [category C] : grothendieck_topology C :=
  finest_topology (set.range (functor.obj yoneda))

/-- `yoneda.obj X` is a sheaf for the canonical topology. -/
theorem is_sheaf_yoneda_obj {C : Type u} [category C] (X : C) :
    presieve.is_sheaf (canonical_topology C) (functor.obj yoneda X) :=
  fun (Y : C) (S : sieve Y) (hS : S ∈ coe_fn (canonical_topology C) Y) =>
    sheaf_for_finest_topology (set.range (functor.obj yoneda)) (set.mem_range_self X) S hS

/-- A representable functor is a sheaf for the canonical topology. -/
theorem is_sheaf_of_representable {C : Type u} [category C] (P : Cᵒᵖ ⥤ Type v) [representable P] :
    presieve.is_sheaf (canonical_topology C) P :=
  presieve.is_sheaf_iso (canonical_topology C) representable.w
    (is_sheaf_yoneda_obj (representable.X P))

/--
A subcanonical topology is a topology which is smaller than the canonical topology.
Equivalently, a topology is subcanonical iff every representable is a sheaf.
-/
def subcanonical {C : Type u} [category C] (J : grothendieck_topology C) := J ≤ canonical_topology C

namespace subcanonical


/-- If every functor `yoneda.obj X` is a `J`-sheaf, then `J` is subcanonical. -/
theorem of_yoneda_is_sheaf {C : Type u} [category C] (J : grothendieck_topology C)
    (h : ∀ (X : C), presieve.is_sheaf J (functor.obj yoneda X)) : subcanonical J :=
  le_finest_topology (set.range (functor.obj yoneda)) J
    fun (P : Cᵒᵖ ⥤ Type v) (H : P ∈ set.range (functor.obj yoneda)) =>
      Exists.dcases_on H fun (X : C) (H_h : functor.obj yoneda X = P) => Eq._oldrec (h X) H_h

/-- If `J` is subcanonical, then any representable is a `J`-sheaf. -/
theorem is_sheaf_of_representable {C : Type u} [category C] {J : grothendieck_topology C}
    (hJ : subcanonical J) (P : Cᵒᵖ ⥤ Type v) [representable P] : presieve.is_sheaf J P :=
  presieve.is_sheaf_of_le P hJ (is_sheaf_of_representable P)

end Mathlib