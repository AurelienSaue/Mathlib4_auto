/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.category.default
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
The category of types with binary relations as morphisms.
-/

namespace category_theory


/-- A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def Rel := Type u

protected instance Rel.inhabited : Inhabited Rel := eq.mpr sorry sort.inhabited

/-- The category of types with binary relations as morphisms. -/
protected instance rel : large_category Rel := category.mk

end Mathlib