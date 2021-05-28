/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.closed.cartesian
import Mathlib.category_theory.limits.shapes.zero
import Mathlib.category_theory.punit
import Mathlib.category_theory.conj
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# A cartesian closed category with zero object is trivial

A cartesian closed category with zero object is trivial: it is equivalent to the category with one
object and one morphism.

## References

* https://mathoverflow.net/a/136480

-/

namespace category_theory


/--
If a cartesian closed category has an initial object which is isomorphic to the terminal object,
then each homset has exactly one element.
-/
def unique_homset_of_initial_iso_terminal {C : Type u} [category C] [limits.has_finite_products C] [cartesian_closed C] [limits.has_initial C] (i : ⊥_C ≅ ⊤_C) (X : C) (Y : C) : unique (X ⟶ Y) :=
  equiv.unique
    (equiv.trans
      (equiv.trans (iso.hom_congr (iso.symm (limits.prod.right_unitor X)) (iso.refl Y))
        (iso.hom_congr (limits.prod.map_iso (iso.refl X) (iso.symm i)) (iso.refl Y)))
      (adjunction.hom_equiv (exp.adjunction X) (⊥_C) Y))

/-- If a cartesian closed category has a zero object, each homset has exactly one element. -/
def unique_homset_of_zero {C : Type u} [category C] [limits.has_finite_products C] [cartesian_closed C] [limits.has_zero_object C] (X : C) (Y : C) : unique (X ⟶ Y) :=
  unique_homset_of_initial_iso_terminal (iso.mk Inhabited.default (Inhabited.default ≫ Inhabited.default)) X Y

/--
A cartesian closed category with a zero object is equivalent to the category with one object and
one morphism.
-/
def equiv_punit {C : Type u} [category C] [limits.has_finite_products C] [cartesian_closed C] [limits.has_zero_object C] : C ≌ discrete PUnit :=
  equivalence.mk (functor.star C) (functor.from_punit 0)
    (nat_iso.of_components (fun (X : C) => iso.mk Inhabited.default Inhabited.default) sorry)
    (functor.punit_ext (functor.from_punit 0 ⋙ functor.star C) 𝟭)

