/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.opens
import Mathlib.category_theory.sites.grothendieck
import Mathlib.category_theory.sites.pretopology
import Mathlib.category_theory.limits.lattice
import PostPort

universes u 

namespace Mathlib

/-!
# Grothendieck topology on a topological space

Define the Grothendieck topology and the pretopology associated to a topological space, and show
that the pretopology induces the topology.

The covering (pre)sieves on `X` are those for which the union of domains contains `X`.

## Tags

site, Grothendieck topology, space

## References

* [https://ncatlab.org/nlab/show/Grothendieck+topology][nlab]
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We define the two separately, rather than defining the Grothendieck topology as that generated
by the pretopology for the purpose of having nice definitional properties for the sieves.
-/

namespace opens


/-- The Grothendieck topology associated to a topological space. -/
def grothendieck_topology (T : Type u) [topological_space T] : category_theory.grothendieck_topology (topological_space.opens T) :=
  category_theory.grothendieck_topology.mk
    (fun (X : topological_space.opens T) (S : category_theory.sieve X) =>
      ∀ (x : T), x ∈ X → ∃ (U : topological_space.opens T), ∃ (f : U ⟶ X), coe_fn S U f ∧ x ∈ U)
    sorry sorry sorry

/-- The Grothendieck pretopology associated to a topological space. -/
def pretopology (T : Type u) [topological_space T] : category_theory.pretopology (topological_space.opens T) :=
  category_theory.pretopology.mk
    (fun (X : topological_space.opens T) (R : category_theory.presieve X) =>
      ∀ (x : T), x ∈ X → ∃ (U : topological_space.opens T), ∃ (f : U ⟶ X), R f ∧ x ∈ U)
    sorry sorry sorry

/--
The pretopology associated to a space induces the Grothendieck topology associated to the space.
-/
@[simp] theorem pretopology_to_grothendieck (T : Type u) [topological_space T] : category_theory.pretopology.to_grothendieck (topological_space.opens T) (pretopology T) = grothendieck_topology T := sorry

