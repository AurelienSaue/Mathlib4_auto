/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.category
import Mathlib.category_theory.adjunction.basic
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some of the theorems proved about cartesian closed categories
should be generalised and moved to this file.
-/

namespace category_theory


/-- An object `X` is (right) closed if `(X ⊗ -)` is a left adjoint. -/
class closed {C : Type u} [category C] [monoidal_category C] (X : C) 
where
  is_adj : is_left_adjoint (monoidal_category.tensor_left X)

/-- A monoidal category `C` is (right) monoidal closed if every object is (right) closed. -/
class monoidal_closed (C : Type u) [category C] [monoidal_category C] 
where
  closed : (X : C) → closed X

/--
The unit object is always closed.
This isn't an instance because most of the time we'll prove closedness for all objects at once,
rather than just for this one.
-/
def unit_closed {C : Type u} [category C] [monoidal_category C] : closed 𝟙_ :=
  closed.mk
    (is_left_adjoint.mk 𝟭
      (adjunction.mk_of_hom_equiv
        (adjunction.core_hom_equiv.mk
          fun (X _x : C) =>
            equiv.mk (fun (a : functor.obj (monoidal_category.tensor_left 𝟙_) X ⟶ _x) => iso.inv λ_ ≫ a)
              (fun (a : X ⟶ functor.obj 𝟭 _x) => iso.hom λ_ ≫ a) sorry sorry)))

