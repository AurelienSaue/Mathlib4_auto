/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.category.Top.basic
import Mathlib.category_theory.adjunction.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace Top


/-- Equipping a type with the discrete topology is left adjoint to the forgetful functor `Top ⥤ Type`. -/
def adj₁ : discrete ⊣ category_theory.forget Top :=
  category_theory.adjunction.mk
    (fun (X : Type u) (Y : Top) =>
      equiv.mk (fun (f : category_theory.functor.obj discrete X ⟶ Y) => ⇑f)
        (fun (f : X ⟶ category_theory.functor.obj (category_theory.forget Top) Y) =>
          continuous_map.mk f)
        sorry sorry)
    (category_theory.nat_trans.mk fun (X : Type u) => id)
    (category_theory.nat_trans.mk fun (X : Top) => continuous_map.mk id)

/-- Equipping a type with the trivial topology is right adjoint to the forgetful functor `Top ⥤ Type`. -/
def adj₂ : category_theory.forget Top ⊣ trivial :=
  category_theory.adjunction.mk
    (fun (X : Top) (Y : Type u) =>
      equiv.mk
        (fun (f : category_theory.functor.obj (category_theory.forget Top) X ⟶ Y) =>
          continuous_map.mk f)
        (fun (f : X ⟶ category_theory.functor.obj trivial Y) => ⇑f) sorry sorry)
    (category_theory.nat_trans.mk fun (X : Top) => continuous_map.mk id)
    (category_theory.nat_trans.mk fun (X : Type u) => id)

end Mathlib