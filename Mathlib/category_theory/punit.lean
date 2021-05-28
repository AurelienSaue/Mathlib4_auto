/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.const
import Mathlib.category_theory.discrete_category
import Mathlib.PostPort

universes v u u_1 

namespace Mathlib

namespace category_theory


namespace functor


/-- The constant functor sending everything to `punit.star`. -/
def star (C : Type u) [category C] : C ⥤ discrete PUnit :=
  obj (const C) PUnit.unit

/-- Any two functors to `discrete punit` are isomorphic. -/
def punit_ext {C : Type u} [category C] (F : C ⥤ discrete PUnit) (G : C ⥤ discrete PUnit) : F ≅ G :=
  nat_iso.of_components (fun (_x : C) => eq_to_iso sorry) sorry

/--
Any two functors to `discrete punit` are *equal*.
You probably want to use `punit_ext` instead of this.
-/
theorem punit_ext' {C : Type u} [category C] (F : C ⥤ discrete PUnit) (G : C ⥤ discrete PUnit) : F = G :=
  ext (fun (_x : C) => of_as_true trivial) fun (_x _x_1 : C) (_x_2 : _x ⟶ _x_1) => of_as_true trivial

/-- The functor from `discrete punit` sending everything to the given object. -/
def from_punit {C : Type u} [category C] (X : C) : discrete PUnit ⥤ C :=
  obj (const (discrete PUnit)) X

/-- Functors from `discrete punit` are equivalent to the category itself. -/
@[simp] theorem equiv_functor_obj {C : Type u} [category C] (F : discrete PUnit ⥤ C) : obj (equivalence.functor equiv) F = obj F PUnit.unit :=
  Eq.refl (obj (equivalence.functor equiv) F)

