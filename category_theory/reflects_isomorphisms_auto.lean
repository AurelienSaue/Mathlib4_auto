/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.fully_faithful
import PostPort

universes v₁ v₂ u₁ u₂ l 

namespace Mathlib

namespace category_theory


/--
Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  reflects : {A B : C} → (f : A ⟶ B) → [_inst_3 : is_iso (functor.map F f)] → is_iso f

/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
def is_iso_of_reflects_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {A : C} {B : C} (f : A ⟶ B) (F : C ⥤ D) [is_iso (functor.map F f)] [reflects_isomorphisms F] : is_iso f :=
  reflects_isomorphisms.reflects F f

protected instance of_full_and_faithful {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [full F] [faithful F] : reflects_isomorphisms F :=
  reflects_isomorphisms.mk
    fun (X Y : C) (f : X ⟶ Y) (i : is_iso (functor.map F f)) => is_iso.mk (functor.preimage F (inv (functor.map F f)))

