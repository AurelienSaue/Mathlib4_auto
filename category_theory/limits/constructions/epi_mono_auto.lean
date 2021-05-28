/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.preserves.shapes.pullbacks
import PostPort

universes v u₁ u₂ 

namespace Mathlib

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

## TODO

Dualise and apply to functor categories.

-/

namespace category_theory


/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
protected instance preserves_mono {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) [limits.preserves_limit (limits.cospan f f) F] [mono f] : mono (functor.map F f) := sorry

/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
theorem reflects_mono {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) [limits.reflects_limit (limits.cospan f f) F] [mono (functor.map F f)] : mono f := sorry

