/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.concrete_category.basic
import Mathlib.category_theory.reflects_isomorphisms
import Mathlib.PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/

protected instance category_theory.forget.category_theory.reflects_isomorphisms : category_theory.reflects_isomorphisms (category_theory.forget (Type u)) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : Type u) (f : X ⟶ Y)
      (i : category_theory.is_iso (category_theory.functor.map (category_theory.forget (Type u)) f)) => i

/--
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
protected instance category_theory.forget₂.category_theory.reflects_isomorphisms (C : Type (u + 1)) [category_theory.category C] [category_theory.concrete_category C] (D : Type (u + 1)) [category_theory.category D] [category_theory.concrete_category D] [category_theory.has_forget₂ C D] [category_theory.reflects_isomorphisms (category_theory.forget C)] : category_theory.reflects_isomorphisms (category_theory.forget₂ C D) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : C) (f : X ⟶ Y)
      (i : category_theory.is_iso (category_theory.functor.map (category_theory.forget₂ C D) f)) =>
      category_theory.is_iso_of_reflects_iso f (category_theory.forget C)

