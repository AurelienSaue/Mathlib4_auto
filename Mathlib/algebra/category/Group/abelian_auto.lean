/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Group.Z_Module_equivalence
import Mathlib.algebra.category.Group.limits
import Mathlib.algebra.category.Group.colimits
import Mathlib.algebra.category.Module.abelian
import Mathlib.category_theory.abelian.basic
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# The category of abelian groups is abelian
-/

namespace AddCommGroup


/-- In the category of abelian groups, every monomorphism is normal. -/
def normal_mono {X : AddCommGroup} {Y : AddCommGroup} (f : X ⟶ Y) (hf : category_theory.mono f) :
    category_theory.normal_mono f :=
  category_theory.equivalence_reflects_normal_mono
    (category_theory.functor.inv (category_theory.forget₂ (Module ℤ) AddCommGroup))
    (Module.normal_mono
      (category_theory.functor.map
        (category_theory.functor.inv (category_theory.forget₂ (Module ℤ) AddCommGroup)) f)
      sorry)

/-- In the category of abelian groups, every epimorphism is normal. -/
def normal_epi {X : AddCommGroup} {Y : AddCommGroup} (f : X ⟶ Y) (hf : category_theory.epi f) :
    category_theory.normal_epi f :=
  category_theory.equivalence_reflects_normal_epi
    (category_theory.functor.inv (category_theory.forget₂ (Module ℤ) AddCommGroup))
    (Module.normal_epi
      (category_theory.functor.map
        (category_theory.functor.inv (category_theory.forget₂ (Module ℤ) AddCommGroup)) f)
      sorry)

/-- The category of abelian groups is abelian. -/
protected instance category_theory.abelian : category_theory.abelian AddCommGroup :=
  category_theory.abelian.mk (fun (X Y : AddCommGroup) => normal_mono)
    fun (X Y : AddCommGroup) => normal_epi

end Mathlib