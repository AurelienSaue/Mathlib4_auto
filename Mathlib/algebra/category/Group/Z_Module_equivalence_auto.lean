/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Module.basic
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.

TODO:
either use this equivalence to transport the monoidal structure from `Module ℤ` to `Ab`,
or, having constructed that monoidal structure directly, show this functor is monoidal.
-/

/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is full. -/
protected instance category_theory.forget₂.category_theory.full :
    category_theory.full (category_theory.forget₂ (Module ℤ) AddCommGroup) :=
  category_theory.full.mk
    fun (A B : Module ℤ)
      (f :
      category_theory.functor.obj (category_theory.forget₂ (Module ℤ) AddCommGroup) A ⟶
        category_theory.functor.obj (category_theory.forget₂ (Module ℤ) AddCommGroup) B) =>
      linear_map.mk ⇑f sorry sorry

/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is essentially surjective. -/
protected instance category_theory.forget₂.category_theory.ess_surj :
    category_theory.ess_surj (category_theory.forget₂ (Module ℤ) AddCommGroup) :=
  category_theory.ess_surj.mk
    fun (A : AddCommGroup) =>
      Exists.intro (Module.of ℤ ↥A) (Nonempty.intro (category_theory.iso.mk 𝟙 𝟙))

protected instance category_theory.forget₂.category_theory.is_equivalence :
    category_theory.is_equivalence (category_theory.forget₂ (Module ℤ) AddCommGroup) :=
  category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj
    (category_theory.forget₂ (Module ℤ) AddCommGroup)

end Mathlib