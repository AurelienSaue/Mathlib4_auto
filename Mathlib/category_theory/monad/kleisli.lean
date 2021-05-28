/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.default
import Mathlib.category_theory.monad.adjunction
import Mathlib.category_theory.monad.basic
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-! # Kleisli category on a monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)`. It also defines the Kleisli
adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/

namespace category_theory


/--
The objects for the Kleisli category of the functor (usually monad) `T : C ⥤ C`, which are the same
thing as objects of the base category `C`.
-/
def kleisli {C : Type u} [category C] (T : C ⥤ C)  :=
  C

namespace kleisli


protected instance inhabited {C : Type u} [category C] (T : C ⥤ C) [Inhabited C] : Inhabited (kleisli T) :=
  { default := Inhabited.default }

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
protected instance kleisli.category {C : Type u} [category C] (T : C ⥤ C) [monad T] : category (kleisli T) :=
  category.mk

namespace adjunction


/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
def to_kleisli {C : Type u} [category C] (T : C ⥤ C) [monad T] : C ⥤ kleisli T :=
  functor.mk (fun (X : C) => X) fun (X Y : C) (f : X ⟶ Y) => f ≫ nat_trans.app η_ Y

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
def from_kleisli {C : Type u} [category C] (T : C ⥤ C) [monad T] : kleisli T ⥤ C :=
  functor.mk (fun (X : kleisli T) => functor.obj T X)
    fun (X Y : kleisli T) (f : X ⟶ Y) => functor.map T f ≫ nat_trans.app μ_ Y

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj {C : Type u} [category C] (T : C ⥤ C) [monad T] : to_kleisli T ⊣ from_kleisli T :=
  adjunction.mk_of_hom_equiv
    (adjunction.core_hom_equiv.mk fun (X : C) (Y : kleisli T) => equiv.refl (X ⟶ functor.obj T Y))

/-- The composition of the adjunction gives the original functor. -/
def to_kleisli_comp_from_kleisli_iso_self {C : Type u} [category C] (T : C ⥤ C) [monad T] : to_kleisli T ⋙ from_kleisli T ≅ T :=
  nat_iso.of_components (fun (X : C) => iso.refl (functor.obj (to_kleisli T ⋙ from_kleisli T) X)) sorry

