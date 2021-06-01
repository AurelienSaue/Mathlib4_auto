/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.products.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
The hom functor, sending `(X, Y)` to the type `X ⟶ Y`.
-/

namespace category_theory.functor


/-- `functor.hom` is the hom-pairing, sending (X,Y) to X → Y, contravariant in X and covariant in Y. -/
def hom (C : Type u) [category C] : Cᵒᵖ × C ⥤ Type v :=
  mk (fun (p : Cᵒᵖ × C) => opposite.unop (prod.fst p) ⟶ prod.snd p)
    fun (X Y : Cᵒᵖ × C) (f : X ⟶ Y) (h : opposite.unop (prod.fst X) ⟶ prod.snd X) =>
      has_hom.hom.unop (prod.fst f) ≫ h ≫ prod.snd f

@[simp] theorem hom_obj (C : Type u) [category C] (X : Cᵒᵖ × C) :
    obj (hom C) X = (opposite.unop (prod.fst X) ⟶ prod.snd X) :=
  rfl

@[simp] theorem hom_pairing_map (C : Type u) [category C] {X : Cᵒᵖ × C} {Y : Cᵒᵖ × C} (f : X ⟶ Y) :
    map (hom C) f = fun (h : obj (hom C) X) => has_hom.hom.unop (prod.fst f) ≫ h ≫ prod.snd f :=
  rfl

end Mathlib