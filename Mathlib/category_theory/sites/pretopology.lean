/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.sites.grothendieck
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Grothendieck pretopologies

Definition and lemmas about Grothendieck pretopologies.
A Grothendieck pretopology for a category `C` is a set of families of morphisms with fixed codomain,
satisfying certain closure conditions.

We show that a pretopology generates a genuine Grothendieck topology, and every topology has
a maximal pretopology which generates it.

The pretopology associated to a topological space is defined in `spaces.lean`.

## Tags

coverage, pretopology, site

## References

* [https://ncatlab.org/nlab/show/Grothendieck+pretopology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [https://stacks.math.columbia.edu/tag/00VG][Stacks]
-/

namespace category_theory


/--
Pullback a set of arrows with given codomain along a fixed map, by taking the pullback in the
category.
This is not the same as the arrow set of `sieve.pullback`, but there is a relation between them
in `pullback_arrows_comm`.
-/
inductive pullback_arrows {C : Type u} [category C] [limits.has_pullbacks C] {X : C} {Y : C} (f : Y ⟶ X) (S : presieve X) : presieve Y
where
| mk : ∀ (Z : C) (h : Z ⟶ X), S h → pullback_arrows f S limits.pullback.snd

theorem pullback_arrows_comm {C : Type u} [category C] [limits.has_pullbacks C] {X : C} {Y : C} (f : Y ⟶ X) (R : presieve X) : sieve.generate (pullback_arrows f R) = sieve.pullback f (sieve.generate R) := sorry

theorem pullback_singleton {C : Type u} [category C] [limits.has_pullbacks C] {X : C} {Y : C} {Z : C} (f : Y ⟶ X) (g : Z ⟶ X) : pullback_arrows f (presieve.singleton g) = presieve.singleton limits.pullback.snd := sorry

/--
A (Grothendieck) pretopology on `C` consists of a collection of families of morphisms with a fixed
target `X` for every object `X` in `C`, called "coverings" of `X`, which satisfies the following
three axioms:
1. Every family consisting of a single isomorphism is a covering family.
2. The collection of covering families is stable under pullback.
3. Given a covering family, and a covering family on each domain of the former, the composition
   is a covering family.

In some sense, a pretopology can be seen as Grothendieck topology with weaker saturation conditions,
in that each covering is not necessarily downward closed.

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology, or
https://stacks.math.columbia.edu/tag/00VH, or [MM92] Chapter III, Section 2, Definition 2.
Note that Stacks calls a category together with a pretopology a site, and [MM92] calls this
a basis for a topology.
-/
structure pretopology (C : Type u) [category C] [limits.has_pullbacks C] 
where
  coverings : (X : C) → set (presieve X)
  has_isos : ∀ {X Y : C} (f : Y ⟶ X) [_inst_3 : is_iso f], presieve.singleton f ∈ coverings X
  pullbacks : ∀ {X Y : C} (f : Y ⟶ X) (S : presieve X), S ∈ coverings X → pullback_arrows f S ∈ coverings Y
  transitive : ∀ {X : C} (S : presieve X) (Ti : {Y : C} → (f : Y ⟶ X) → S f → presieve Y),
  S ∈ coverings X → (∀ {Y : C} (f : Y ⟶ X) (H : S f), Ti f H ∈ coverings Y) → presieve.bind S Ti ∈ coverings X

namespace pretopology


protected instance has_coe_to_fun (C : Type u) [category C] [limits.has_pullbacks C] : has_coe_to_fun (pretopology C) :=
  has_coe_to_fun.mk (fun (J : pretopology C) => (X : C) → set (presieve X)) fun (J : pretopology C) => coverings J

protected instance partial_order (C : Type u) [category C] [limits.has_pullbacks C] : partial_order (pretopology C) :=
  partial_order.mk (fun (K₁ K₂ : pretopology C) => ⇑K₁ ≤ ⇑K₂)
    (preorder.lt._default fun (K₁ K₂ : pretopology C) => ⇑K₁ ≤ ⇑K₂) sorry sorry sorry

protected instance order_top (C : Type u) [category C] [limits.has_pullbacks C] : order_top (pretopology C) :=
  order_top.mk (mk (fun (_x : C) => set.univ) sorry sorry sorry) partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance inhabited (C : Type u) [category C] [limits.has_pullbacks C] : Inhabited (pretopology C) :=
  { default := ⊤ }

/--
A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See https://stacks.math.columbia.edu/tag/00ZC, or [MM92] Chapter III, Section 2, Equation (2).
-/
def to_grothendieck (C : Type u) [category C] [limits.has_pullbacks C] (K : pretopology C) : grothendieck_topology C :=
  grothendieck_topology.mk (fun (X : C) (S : sieve X) => ∃ (R : presieve X), ∃ (H : R ∈ coe_fn K X), R ≤ ⇑S) sorry sorry
    sorry

theorem mem_to_grothendieck (C : Type u) [category C] [limits.has_pullbacks C] (K : pretopology C) (X : C) (S : sieve X) : S ∈ coe_fn (to_grothendieck C K) X ↔ ∃ (R : presieve X), ∃ (H : R ∈ coe_fn K X), R ≤ ⇑S :=
  iff.rfl

/--
The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def of_grothendieck (C : Type u) [category C] [limits.has_pullbacks C] (J : grothendieck_topology C) : pretopology C :=
  mk (fun (X : C) (R : presieve X) => sieve.generate R ∈ coe_fn J X) sorry sorry sorry

/-- We have a galois insertion from pretopologies to Grothendieck topologies. -/
def gi (C : Type u) [category C] [limits.has_pullbacks C] : galois_insertion (to_grothendieck C) (of_grothendieck C) :=
  galois_insertion.mk (fun (x : pretopology C) (hx : of_grothendieck C (to_grothendieck C x) ≤ x) => to_grothendieck C x)
    sorry sorry sorry

/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See https://stacks.math.columbia.edu/tag/07GE
-/
def trivial (C : Type u) [category C] [limits.has_pullbacks C] : pretopology C :=
  mk (fun (X : C) (S : presieve X) => ∃ (Y : C), ∃ (f : Y ⟶ X), ∃ (h : is_iso f), S = presieve.singleton f) sorry sorry
    sorry

protected instance order_bot (C : Type u) [category C] [limits.has_pullbacks C] : order_bot (pretopology C) :=
  order_bot.mk (trivial C) partial_order.le partial_order.lt sorry sorry sorry sorry

/-- The trivial pretopology induces the trivial grothendieck topology. -/
theorem to_grothendieck_bot (C : Type u) [category C] [limits.has_pullbacks C] : to_grothendieck C ⊥ = ⊥ :=
  galois_connection.l_bot (galois_insertion.gc (gi C))

