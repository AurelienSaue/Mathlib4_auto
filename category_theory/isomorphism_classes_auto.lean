/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.category.Cat
import Mathlib.category_theory.groupoid
import PostPort

universes v u 

namespace Mathlib

/-!
# Objects of a category up to an isomorphism

`is_isomorphic X Y := nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/

namespace category_theory


/-- An object `X` is isomorphic to an object `Y`, if `X ≅ Y` is not empty. -/
def is_isomorphic {C : Type u} [category C] : C → C → Prop :=
  fun (X Y : C) => Nonempty (X ≅ Y)

/-- `is_isomorphic` defines a setoid. -/
def is_isomorphic_setoid (C : Type u) [category C] : setoid C :=
  setoid.mk is_isomorphic sorry

/--
The functor that sends each category to the quotient space of its objects up to an isomorphism.
-/
def isomorphism_classes : Cat ⥤ Type u :=
  functor.mk (fun (C : Cat) => quotient (is_isomorphic_setoid (bundled.α C)))
    fun (C D : Cat) (F : C ⟶ D) => quot.map (functor.obj F) sorry

theorem groupoid.is_isomorphic_iff_nonempty_hom {C : Type u} [groupoid C] {X : C} {Y : C} : is_isomorphic X Y ↔ Nonempty (X ⟶ Y) :=
  equiv.nonempty_iff_nonempty (groupoid.iso_equiv_hom X Y)

