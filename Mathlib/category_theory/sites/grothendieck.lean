/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.sites.sieves
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.order.copy
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology
as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

A pretopology, or a basis for a topology is defined in `pretopology.lean`. The topology associated
to a topological space is defined in `spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [https://ncatlab.org/nlab/show/Grothendieck+topology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM91]

## Implementation notes

We use the definition of [nlab] and [MM91](Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/

namespace category_theory


/--
The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See https://stacks.math.columbia.edu/tag/00Z4, or [nlab], or [MM92] Chapter III, Section 2,
Definition 1.
-/
structure grothendieck_topology (C : Type u) [category C] 
where
  sieves : (X : C) → set (sieve X)
  top_mem' : ∀ (X : C), ⊤ ∈ sieves X
  pullback_stable' : ∀ {X Y : C} {S : sieve X} (f : Y ⟶ X), S ∈ sieves X → sieve.pullback f S ∈ sieves Y
  transitive' : ∀ {X : C} {S : sieve X},
  S ∈ sieves X → ∀ (R : sieve X), (∀ {Y : C} {f : Y ⟶ X}, coe_fn S Y f → sieve.pullback f R ∈ sieves Y) → R ∈ sieves X

namespace grothendieck_topology


protected instance has_coe_to_fun (C : Type u) [category C] : has_coe_to_fun (grothendieck_topology C) :=
  has_coe_to_fun.mk (fun (J : grothendieck_topology C) => (X : C) → set (sieve X))
    fun (J : grothendieck_topology C) => sieves J

/--
An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
theorem ext {C : Type u} [category C] {J₁ : grothendieck_topology C} {J₂ : grothendieck_topology C} (h : ⇑J₁ = ⇑J₂) : J₁ = J₂ := sorry

@[simp] theorem mem_sieves_iff_coe {C : Type u} [category C] {X : C} {S : sieve X} (J : grothendieck_topology C) : S ∈ sieves J X ↔ S ∈ coe_fn J X :=
  iff.rfl

-- Also known as the maximality axiom.

-- Also known as the stability axiom.

@[simp] theorem top_mem {C : Type u} [category C] (J : grothendieck_topology C) (X : C) : ⊤ ∈ coe_fn J X :=
  top_mem' J X

@[simp] theorem pullback_stable {C : Type u} [category C] {X : C} {Y : C} {S : sieve X} (J : grothendieck_topology C) (f : Y ⟶ X) (hS : S ∈ coe_fn J X) : sieve.pullback f S ∈ coe_fn J Y :=
  pullback_stable' J f hS

theorem transitive {C : Type u} [category C] {X : C} {S : sieve X} (J : grothendieck_topology C) (hS : S ∈ coe_fn J X) (R : sieve X) (h : ∀ {Y : C} {f : Y ⟶ X}, coe_fn S Y f → sieve.pullback f R ∈ coe_fn J Y) : R ∈ coe_fn J X :=
  transitive' J hS R h

theorem covering_of_eq_top {C : Type u} [category C] {X : C} {S : sieve X} (J : grothendieck_topology C) : S = ⊤ → S ∈ coe_fn J X :=
  fun (h : S = ⊤) => Eq.symm h ▸ top_mem J X

/--
If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See https://stacks.math.columbia.edu/tag/00Z5 (2), or discussion after [MM92] Chapter III,
Section 2, Definition 1.
-/
theorem superset_covering {C : Type u} [category C] {X : C} {S : sieve X} {R : sieve X} (J : grothendieck_topology C) (Hss : S ≤ R) (sjx : S ∈ coe_fn J X) : R ∈ coe_fn J X := sorry

/--
The intersection of two covering sieves is covering.

See https://stacks.math.columbia.edu/tag/00Z5 (1), or [MM92] Chapter III,
Section 2, Definition 1 (iv).
-/
theorem intersection_covering {C : Type u} [category C] {X : C} {S : sieve X} {R : sieve X} (J : grothendieck_topology C) (rj : R ∈ coe_fn J X) (sj : S ∈ coe_fn J X) : R ⊓ S ∈ coe_fn J X := sorry

@[simp] theorem intersection_covering_iff {C : Type u} [category C] {X : C} {S : sieve X} {R : sieve X} (J : grothendieck_topology C) : R ⊓ S ∈ coe_fn J X ↔ R ∈ coe_fn J X ∧ S ∈ coe_fn J X := sorry

theorem bind_covering {C : Type u} [category C] {X : C} (J : grothendieck_topology C) {S : sieve X} {R : {Y : C} → {f : Y ⟶ X} → coe_fn S Y f → sieve Y} (hS : S ∈ coe_fn J X) (hR : ∀ {Y : C} {f : Y ⟶ X} (H : coe_fn S Y f), R H ∈ coe_fn J Y) : sieve.bind (⇑S) R ∈ coe_fn J X :=
  transitive J hS (sieve.bind (⇑S) R)
    fun (Y : C) (f : Y ⟶ X) (hf : coe_fn S Y f) => superset_covering J (sieve.le_pullback_bind (⇑S) R f hf) (hR hf)

/--
The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
def covers {C : Type u} [category C] {X : C} {Y : C} (J : grothendieck_topology C) (S : sieve X) (f : Y ⟶ X)  :=
  sieve.pullback f S ∈ coe_fn J Y

theorem covers_iff {C : Type u} [category C] {X : C} {Y : C} (J : grothendieck_topology C) (S : sieve X) (f : Y ⟶ X) : covers J S f ↔ sieve.pullback f S ∈ coe_fn J Y :=
  iff.rfl

theorem covering_iff_covers_id {C : Type u} [category C] {X : C} (J : grothendieck_topology C) (S : sieve X) : S ∈ coe_fn J X ↔ covers J S 𝟙 := sorry

/-- The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`. -/
theorem arrow_max {C : Type u} [category C] {X : C} {Y : C} (J : grothendieck_topology C) (f : Y ⟶ X) (S : sieve X) (hf : coe_fn S Y f) : covers J S f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (covers J S f)) (covers.equations._eqn_1 J S f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sieve.pullback f S ∈ coe_fn J Y)) (iff.mp (sieve.pullback_eq_top_iff_mem f) hf)))
      (top_mem J Y))

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
theorem arrow_stable {C : Type u} [category C] {X : C} {Y : C} (J : grothendieck_topology C) (f : Y ⟶ X) (S : sieve X) (h : covers J S f) {Z : C} (g : Z ⟶ Y) : covers J S (g ≫ f) := sorry

/--
The transitivity axiom in 'arrow' form: If `S` covers `f` and every arrow in `S` is covered by
`R`, then `R` covers `f`.
-/
theorem arrow_trans {C : Type u} [category C] {X : C} {Y : C} (J : grothendieck_topology C) (f : Y ⟶ X) (S : sieve X) (R : sieve X) (h : covers J S f) : (∀ {Z : C} (g : Z ⟶ X), coe_fn S Z g → covers J R g) → covers J R f := sorry

theorem arrow_intersect {C : Type u} [category C] {X : C} {Y : C} (J : grothendieck_topology C) (f : Y ⟶ X) (S : sieve X) (R : sieve X) (hS : covers J S f) (hR : covers J R f) : covers J (S ⊓ R) f := sorry

/--
The trivial Grothendieck topology, in which only the maximal sieve is covering. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies
-/
def trivial (C : Type u) [category C] : grothendieck_topology C :=
  mk (fun (X : C) => singleton ⊤) sorry sorry sorry

/--
The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies.
-/
def discrete (C : Type u) [category C] : grothendieck_topology C :=
  mk (fun (X : C) => set.univ) sorry sorry sorry

theorem trivial_covering {C : Type u} [category C] {X : C} {S : sieve X} : S ∈ coe_fn (trivial C) X ↔ S = ⊤ :=
  set.mem_singleton_iff

/-- See https://stacks.math.columbia.edu/tag/00Z6 -/
protected instance partial_order {C : Type u} [category C] : partial_order (grothendieck_topology C) :=
  partial_order.mk (fun (J₁ J₂ : grothendieck_topology C) => ⇑J₁ ≤ ⇑J₂)
    (preorder.lt._default fun (J₁ J₂ : grothendieck_topology C) => ⇑J₁ ≤ ⇑J₂) sorry sorry sorry

/-- See https://stacks.math.columbia.edu/tag/00Z7 -/
protected instance has_Inf {C : Type u} [category C] : has_Inf (grothendieck_topology C) :=
  has_Inf.mk fun (T : set (grothendieck_topology C)) => mk (Inf (sieves '' T)) sorry sorry sorry

/-- See https://stacks.math.columbia.edu/tag/00Z7 -/
theorem is_glb_Inf {C : Type u} [category C] (s : set (grothendieck_topology C)) : is_glb s (Inf s) :=
  is_glb.of_image (fun (x y : grothendieck_topology C) => iff.refl (sieves x ≤ sieves y)) (is_glb_Inf (sieves '' s))

/--
Construct a complete lattice from the `Inf`, but make the trivial and discrete topologies
definitionally equal to the bottom and top respectively.
-/
protected instance complete_lattice {C : Type u} [category C] : complete_lattice (grothendieck_topology C) :=
  complete_lattice.copy (complete_lattice_of_Inf (grothendieck_topology C) is_glb_Inf) complete_lattice.le sorry
    (discrete C) sorry (trivial C) sorry complete_lattice.sup sorry complete_lattice.inf sorry complete_lattice.Sup sorry
    Inf sorry

protected instance inhabited {C : Type u} [category C] : Inhabited (grothendieck_topology C) :=
  { default := ⊤ }

@[simp] theorem trivial_eq_bot {C : Type u} [category C] : trivial C = ⊥ :=
  rfl

@[simp] theorem discrete_eq_top {C : Type u} [category C] : discrete C = ⊤ :=
  rfl

@[simp] theorem bot_covering {C : Type u} [category C] {X : C} {S : sieve X} : S ∈ coe_fn ⊥ X ↔ S = ⊤ :=
  trivial_covering

@[simp] theorem top_covering {C : Type u} [category C] {X : C} {S : sieve X} : S ∈ coe_fn ⊤ X :=
  True.intro

theorem bot_covers {C : Type u} [category C] {X : C} {Y : C} (S : sieve X) (f : Y ⟶ X) : covers ⊥ S f ↔ coe_fn S Y f := sorry

@[simp] theorem top_covers {C : Type u} [category C] {X : C} {Y : C} (S : sieve X) (f : Y ⟶ X) : covers ⊤ S f :=
  eq.mpr (id (Eq.trans (propext (covers_iff ⊤ S f)) (propext (iff_true_intro top_covering)))) trivial

/--
The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section 2, example (e).
-/
def dense {C : Type u} [category C] : grothendieck_topology C :=
  mk (fun (X : C) (S : sieve X) => ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : C), ∃ (g : Z ⟶ Y), coe_fn S Z (g ≫ f)) sorry sorry sorry

theorem dense_covering {C : Type u} [category C] {X : C} {S : sieve X} : S ∈ coe_fn dense X ↔ ∀ {Y : C} (f : Y ⟶ X), ∃ (Z : C), ∃ (g : Z ⟶ Y), coe_fn S Z (g ≫ f) :=
  iff.rfl

/--
A category satisfies the right Ore condition if any span can be completed to a commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
def right_ore_condition (C : Type u) [category C]  :=
  ∀ {X Y Z : C} (yx : Y ⟶ X) (zx : Z ⟶ X), ∃ (W : C), ∃ (wy : W ⟶ Y), ∃ (wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

theorem right_ore_of_pullbacks {C : Type u} [category C] [limits.has_pullbacks C] : right_ore_condition C :=
  fun (X Y Z : C) (yx : Y ⟶ X) (zx : Z ⟶ X) =>
    Exists.intro (limits.pullback yx zx)
      (Exists.intro limits.pullback.fst (Exists.intro limits.pullback.snd limits.pullback.condition))

/--
The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2, example (f).
-/
def atomic {C : Type u} [category C] (hro : right_ore_condition C) : grothendieck_topology C :=
  mk (fun (X : C) (S : sieve X) => ∃ (Y : C), ∃ (f : Y ⟶ X), coe_fn S Y f) sorry sorry sorry

