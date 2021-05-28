/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monad.algebra
import Mathlib.category_theory.adjunction.default
import PostPort

universes u₁ u₂ v₁ v₂ l 

namespace Mathlib

namespace category_theory


namespace adjunction


@[simp] theorem monad_μ {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [is_right_adjoint R] : μ_ = whisker_right (whisker_left (left_adjoint R) (counit (of_right_adjoint R))) R :=
  Eq.refl μ_

@[simp] theorem comonad_ε {C : Type u₁} [category C] {D : Type u₂} [category D] (L : C ⥤ D) [is_left_adjoint L] : ε_ = counit (of_left_adjoint L) :=
  Eq.refl ε_

end adjunction


namespace monad


/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simp] theorem comparison_map_f {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [is_right_adjoint R] (X : D) (Y : D) (f : X ⟶ Y) : algebra.hom.f (functor.map (comparison R) f) = functor.map R f :=
  Eq.refl (algebra.hom.f (functor.map (comparison R) f))

/--
The underlying object of `(monad.comparison R).obj X` is just `R.obj X`.
-/
def comparison_forget {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [is_right_adjoint R] : comparison R ⋙ forget (left_adjoint R ⋙ R) ≅ R :=
  iso.mk (nat_trans.mk fun (X : D) => 𝟙) (nat_trans.mk fun (X : D) => 𝟙)

end monad


namespace comonad


/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object 
`L.obj X`.
-/
@[simp] theorem comparison_obj_a {C : Type u₁} [category C] {D : Type u₂} [category D] (L : C ⥤ D) [is_left_adjoint L] (X : C) : coalgebra.a (functor.obj (comparison L) X) =
  functor.map L (nat_trans.app (adjunction.unit (adjunction.of_left_adjoint L)) X) :=
  Eq.refl (coalgebra.a (functor.obj (comparison L) X))

/--
The underlying object of `(comonad.comparison L).obj X` is just `L.obj X`.
-/
def comparison_forget {C : Type u₁} [category C] {D : Type u₂} [category D] (L : C ⥤ D) [is_left_adjoint L] : comparison L ⋙ forget (right_adjoint L ⋙ L) ≅ L :=
  iso.mk (nat_trans.mk fun (X : C) => 𝟙) (nat_trans.mk fun (X : C) => 𝟙)

end comonad


/--
A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class monadic_right_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) 
extends is_right_adjoint R
where
  eqv : is_equivalence (monad.comparison R)

/--
A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class comonadic_left_adjoint {C : Type u₁} [category C] {D : Type u₂} [category D] (L : C ⥤ D) 
extends is_left_adjoint L
where
  eqv : is_equivalence (comonad.comparison L)

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.

protected instance μ_iso_of_reflective {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [reflective R] : is_iso μ_ :=
  id
    (category_theory.is_iso_whisker_right
      (whisker_left (left_adjoint R) (adjunction.counit (adjunction.of_right_adjoint R))) R)

namespace reflective


protected instance app.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [reflective R] (X : monad.algebra (left_adjoint R ⋙ R)) : is_iso (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint R)) (monad.algebra.A X)) :=
  is_iso.mk (monad.algebra.a X)

protected instance comparison_ess_surj {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [reflective R] : ess_surj (monad.comparison R) := sorry

protected instance comparison_full {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [full R] [is_right_adjoint R] : full (monad.comparison R) :=
  full.mk
    fun (X Y : D) (f : functor.obj (monad.comparison R) X ⟶ functor.obj (monad.comparison R) Y) =>
      functor.preimage R (monad.algebra.hom.f f)

protected instance comparison_faithful {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [faithful R] [is_right_adjoint R] : faithful (monad.comparison R) :=
  faithful.mk

end reflective


-- It is possible to do this computably since the construction gives the data of the inverse, not

-- just the existence of an inverse on each object.

/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
protected instance monadic_of_reflective {C : Type u₁} [category C] {D : Type u₂} [category D] (R : D ⥤ C) [reflective R] : monadic_right_adjoint R :=
  monadic_right_adjoint.mk (equivalence.equivalence_of_fully_faithfully_ess_surj (monad.comparison R))

