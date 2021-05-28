/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.shapes.binary_products
import Mathlib.category_theory.limits.preserves.shapes.terminal
import Mathlib.category_theory.adjunction.fully_faithful
import PostPort

universes v₁ v₂ u₁ u₂ l 

namespace Mathlib

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`category_theory.monad.limits`.
-/

namespace category_theory


/--
A functor is *reflective*, or *a reflective inclusion*, if it is fully faithful and right adjoint.
-/
class reflective {C : Type u₁} {D : Type u₂} [category C] [category D] (R : D ⥤ C) 
extends full R, faithful R, is_right_adjoint R
where

/--
For a reflective functor `i` (with left adjoint `L`), with unit `η`, we have `η_iL = iL η`.
-/
-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.

theorem unit_obj_eq_map_unit {C : Type u₁} {D : Type u₂} [category C] [category D] {i : D ⥤ C} [reflective i] (X : C) : nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) (functor.obj i (functor.obj (left_adjoint i) X)) =
  functor.map i (functor.map (left_adjoint i) (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) X)) := sorry

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism.
More generally this applies to objects essentially in the reflective subcategory, see
`functor.ess_image.unit_iso`.
-/
protected instance functor.ess_image.unit_iso_restrict {C : Type u₁} {D : Type u₂} [category C] [category D] {i : D ⥤ C} [reflective i] {B : D} : is_iso (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) (functor.obj i B)) :=
  eq.mpr sorry is_iso.inv_is_iso

/--
If `A` is essentially in the image of a reflective functor `i`, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the essential image can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
def functor.ess_image.unit_is_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {i : D ⥤ C} [reflective i] {A : C} (h : A ∈ functor.ess_image i) : is_iso (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) A) :=
  eq.mpr sorry is_iso.comp_is_iso

/-- If `η_A` is an isomorphism, then `A` is in the essential image of `i`. -/
theorem mem_ess_image_of_unit_is_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {i : D ⥤ C} [is_right_adjoint i] (A : C) [is_iso (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) A)] : A ∈ functor.ess_image i :=
  Exists.intro (functor.obj (left_adjoint i) A)
    (Nonempty.intro (iso.symm (as_iso (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) A))))

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
theorem mem_ess_image_of_unit_split_mono {C : Type u₁} {D : Type u₂} [category C] [category D] {i : D ⥤ C} [reflective i] {A : C} [split_mono (nat_trans.app (adjunction.unit (adjunction.of_right_adjoint i)) A)] : A ∈ functor.ess_image i :=
  let η : 𝟭 ⟶ left_adjoint i ⋙ i := adjunction.unit (adjunction.of_right_adjoint i);
  mem_ess_image_of_unit_is_iso A

