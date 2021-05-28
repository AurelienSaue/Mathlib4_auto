/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.local_predicate
import Mathlib.topology.sheaves.stalks
import Mathlib.PostPort

universes v 

namespace Mathlib

/-!
# Sheafification of `Type` valued presheaves

We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalk_to_fiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `to_sheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

## Future work
Show that the map induced on stalks by `to_sheafify` is the inverse of `stalk_to_fiber`.

Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor,
following https://stacks.math.columbia.edu/tag/007X.
-/

namespace Top.presheaf


namespace sheafify


/--
The prelocal predicate on functions into the stalks, asserting that the function is equal to a germ.
-/
def is_germ {X : Top} (F : presheaf (Type v) X) : prelocal_predicate fun (x : ↥X) => stalk F x :=
  prelocal_predicate.mk
    (fun (U : topological_space.opens ↥X) (f : (x : ↥U) → stalk F ↑x) =>
      ∃ (g : category_theory.functor.obj F (opposite.op U)), ∀ (x : ↥U), f x = germ F x g)
    sorry

/--
The local predicate on functions into the stalks,
asserting that the function is locally equal to a germ.
-/
def is_locally_germ {X : Top} (F : presheaf (Type v) X) : local_predicate fun (x : ↥X) => stalk F x :=
  prelocal_predicate.sheafify (is_germ F)

end sheafify


/--
The sheafification of a `Type` valued presheaf, defined as the functions into the stalks which
are locally equal to germs.
-/
def sheafify {X : Top} (F : presheaf (Type v) X) : sheaf (Type v) X :=
  subsheaf_to_Types sorry

/--
The morphism from a presheaf to its sheafification,
sending each section to its germs.
(This forms the unit of the adjunction.)
-/
def to_sheafify {X : Top} (F : presheaf (Type v) X) : F ⟶ sheaf.presheaf (sheafify F) :=
  category_theory.nat_trans.mk
    fun (U : topological_space.opens ↥Xᵒᵖ) (f : category_theory.functor.obj F U) =>
      { val := fun (x : ↥(opposite.unop U)) => germ F x f, property := sorry }

/--
The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafify_stalk_iso` we show this is an isomorphism.
-/
def stalk_to_fiber {X : Top} (F : presheaf (Type v) X) (x : ↥X) : stalk (sheaf.presheaf (sheafify F)) x ⟶ stalk F x :=
  stalk_to_fiber (sheafify.is_locally_germ F) x

theorem stalk_to_fiber_surjective {X : Top} (F : presheaf (Type v) X) (x : ↥X) : function.surjective (stalk_to_fiber F x) := sorry

theorem stalk_to_fiber_injective {X : Top} (F : presheaf (Type v) X) (x : ↥X) : function.injective (stalk_to_fiber F x) := sorry

/--
The isomorphism betweeen a stalk of the sheafification and the original stalk.
-/
def sheafify_stalk_iso {X : Top} (F : presheaf (Type v) X) (x : ↥X) : stalk (sheaf.presheaf (sheafify F)) x ≅ stalk F x :=
  equiv.to_iso (equiv.of_bijective (stalk_to_fiber F x) sorry)

