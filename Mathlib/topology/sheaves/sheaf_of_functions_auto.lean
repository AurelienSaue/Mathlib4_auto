/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.presheaf_of_functions
import Mathlib.topology.sheaves.sheaf
import Mathlib.category_theory.limits.shapes.types
import Mathlib.topology.local_homeomorph
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Sheaf conditions for presheaves of (continuous) functions.

We show that
* `Top.sheaf_condition.to_Type`: not-necessarily-continuous functions into a type form a sheaf
* `Top.sheaf_condition.to_Types`: in fact, these may be dependent functions into a type family

For
* `Top.sheaf_condition.to_Top`: continuous functions into a topological space form a sheaf
please see `topology/sheaves/local_predicate.lean`, where we set up a general framework
for constructing sub(pre)sheaves of the sheaf of dependent functions.

## Future work
Obviously there's more to do:
* sections of a fiber bundle
* various classes of smooth and structure preserving functions
* functions into spaces with algebraic structure, which the sections inherit
-/

namespace Top.presheaf


/--
We show that the presheaf of functions to a type `T`
(no continuity assumptions, just plain functions)
form a sheaf.

In fact, the proof is identical when we do this for dependent functions to a type family `T`,
so we do the more general case.
-/
def to_Types (X : Top) (T : ↥X → Type u) : sheaf_condition (presheaf_to_Types X T) := sorry

-- U is a family of open sets, indexed by `ι`.

-- In the informal comments below, I'll just write `U` to represent the union.

-- We verify that the non-dependent version is an immediate consequence:

/--
The presheaf of not-necessarily-continuous functions to
a target type `T` satsifies the sheaf condition.
-/
def to_Type (X : Top) (T : Type u) : sheaf_condition (presheaf_to_Type X T) :=
  to_Types X fun (_x : ↥X) => T

end Top.presheaf


namespace Top


/--
The sheaf of not-necessarily-continuous functions on `X` with values in type family `T : X → Type u`.
-/
def sheaf_to_Types (X : Top) (T : ↥X → Type u) : sheaf (Type u) X :=
  sheaf.mk (presheaf_to_Types X T) (presheaf.to_Types X T)

/--
The sheaf of not-necessarily-continuous functions on `X` with values in a type `T`.
-/
def sheaf_to_Type (X : Top) (T : Type u) : sheaf (Type u) X :=
  sheaf.mk (presheaf_to_Type X T) (presheaf.to_Type X T)

end Mathlib