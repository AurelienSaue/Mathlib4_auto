/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.presheaf
import Mathlib.category_theory.limits.functor_category
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/

namespace Top


protected instance presheaf.category_theory.limits.has_limits {C : Type u}
    [category_theory.category C] [category_theory.limits.has_limits C] (X : Top) :
    category_theory.limits.has_limits (presheaf C X) :=
  id category_theory.limits.functor_category_has_limits

protected instance presheaf.category_theory.limits.has_colimits {C : Type u}
    [category_theory.category C] [category_theory.limits.has_colimits C] (X : Top) :
    category_theory.limits.has_colimits (presheaf C X) :=
  id category_theory.limits.functor_category_has_colimits

end Mathlib