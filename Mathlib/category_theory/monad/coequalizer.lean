/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.reflexive
import Mathlib.category_theory.limits.preserves.shapes.equalizers
import Mathlib.category_theory.limits.preserves.limits
import Mathlib.category_theory.monad.adjunction
import Mathlib.PostPort

universes v₁ u₁ 

namespace Mathlib

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).
-/

namespace category_theory


namespace monad


/-!
Show that any algebra is a coequalizer of free algebras.
-/

/-- The top map in the coequalizer diagram we will construct. -/
@[simp] theorem free_coequalizer.top_map_f {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : algebra.hom.f (free_coequalizer.top_map X) = functor.map T (algebra.a X) :=
  Eq.refl (functor.map T (algebra.a X))

/-- The bottom map in the coequalizer diagram we will construct. -/
def free_coequalizer.bottom_map {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : functor.obj (free T) (functor.obj T (algebra.A X)) ⟶ functor.obj (free T) (algebra.A X) :=
  algebra.hom.mk (nat_trans.app μ_ (algebra.A X))

/-- The cofork map in the coequalizer diagram we will construct. -/
def free_coequalizer.π {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : functor.obj (free T) (algebra.A X) ⟶ X :=
  algebra.hom.mk (algebra.a X)

theorem free_coequalizer.condition {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : free_coequalizer.top_map X ≫ free_coequalizer.π X = free_coequalizer.bottom_map X ≫ free_coequalizer.π X :=
  algebra.hom.ext (free_coequalizer.top_map X ≫ free_coequalizer.π X)
    (free_coequalizer.bottom_map X ≫ free_coequalizer.π X) (Eq.symm (algebra.assoc X))

protected instance free_coequalizer.bottom_map.category_theory.is_reflexive_pair {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : is_reflexive_pair (free_coequalizer.top_map X) (free_coequalizer.bottom_map X) :=
  is_reflexive_pair.mk' (functor.map (free T) (nat_trans.app η_ (algebra.A X)))
    (algebra.hom.ext (functor.map (free T) (nat_trans.app η_ (algebra.A X)) ≫ free_coequalizer.top_map X) 𝟙
      (id
        (eq.mpr
          (id
            (Eq._oldrec (Eq.refl (functor.map T (nat_trans.app η_ (algebra.A X)) ≫ functor.map T (algebra.a X) = 𝟙))
              (Eq.symm (functor.map_comp T (nat_trans.app η_ (algebra.A X)) (algebra.a X)))))
          (eq.mpr
            (id
              (Eq._oldrec (Eq.refl (functor.map T (nat_trans.app η_ (algebra.A X) ≫ algebra.a X) = 𝟙)) (algebra.unit X)))
            (eq.mpr (id (Eq._oldrec (Eq.refl (functor.map T 𝟙 = 𝟙)) (functor.map_id T (algebra.A X)))) (Eq.refl 𝟙))))))
    (algebra.hom.ext (functor.map (free T) (nat_trans.app η_ (algebra.A X)) ≫ free_coequalizer.bottom_map X) 𝟙
      (right_unit (functor.obj 𝟭 (algebra.A X))))

/--
Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simp] theorem beck_algebra_cofork_X {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : limits.cocone.X (beck_algebra_cofork X) = X :=
  Eq.refl X

/--
The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/
def beck_algebra_coequalizer {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : limits.is_colimit (beck_algebra_cofork X) :=
  limits.cofork.is_colimit.mk' (beck_algebra_cofork X)
    fun (s : limits.cofork (free_coequalizer.top_map X) (free_coequalizer.bottom_map X)) =>
      { val :=
          algebra.hom.mk
            (nat_trans.app η_ (algebra.A (limits.cocone.X (beck_algebra_cofork X))) ≫ algebra.hom.f (limits.cofork.π s)),
        property := sorry }

/-- The Beck cofork is a split coequalizer. -/
def beck_split_coequalizer {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : is_split_coequalizer (functor.map T (algebra.a X)) (nat_trans.app μ_ (algebra.A X)) (algebra.a X) :=
  is_split_coequalizer.mk (nat_trans.app η_ (algebra.A X)) (nat_trans.app η_ (functor.obj T (algebra.A X))) sorry
    (algebra.unit X) sorry sorry

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simp] theorem beck_cofork_X {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : limits.cocone.X (beck_cofork X) = algebra.A X :=
  Eq.refl (algebra.A X)

/-- The Beck cofork is a coequalizer. -/
def beck_coequalizer {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (X : algebra T) : limits.is_colimit (beck_cofork X) :=
  is_split_coequalizer.is_coequalizer (beck_split_coequalizer X)

