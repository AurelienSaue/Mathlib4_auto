/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.over
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.shapes.wide_pullbacks
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_wide_pullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `over B` has `J`-indexed products.
-/

namespace category_theory.over


namespace construct_products


/--
(Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
def wide_pullback_diagram_of_diagram_over {C : Type u} [category C] (B : C) {J : Type v} (F : discrete J ⥤ over B) : limits.wide_pullback_shape J ⥤ C :=
  limits.wide_pullback_shape.wide_cospan B (fun (j : J) => comma.left (functor.obj F j))
    fun (j : J) => comma.hom (functor.obj F j)

/-- (Impl) A preliminary definition to avoid timeouts. -/
def cones_equiv_inverse_obj {C : Type u} [category C] (B : C) {J : Type v} (F : discrete J ⥤ over B) (c : limits.cone F) : limits.cone (wide_pullback_diagram_of_diagram_over B F) :=
  limits.cone.mk (comma.left (limits.cone.X c))
    (nat_trans.mk
      fun (X : limits.wide_pullback_shape J) =>
        option.cases_on X (comma.hom (limits.cone.X c))
          fun (j : J) => comma_morphism.left (nat_trans.app (limits.cone.π c) j))

/-- (Impl) A preliminary definition to avoid timeouts. -/
def cones_equiv_inverse {C : Type u} [category C] (B : C) {J : Type v} (F : discrete J ⥤ over B) : limits.cone F ⥤ limits.cone (wide_pullback_diagram_of_diagram_over B F) :=
  functor.mk (cones_equiv_inverse_obj B F)
    fun (c₁ c₂ : limits.cone F) (f : c₁ ⟶ c₂) =>
      limits.cone_morphism.mk (comma_morphism.left (limits.cone_morphism.hom f))

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp] theorem cones_equiv_functor_map_hom {C : Type u} [category C] (B : C) {J : Type v} (F : discrete J ⥤ over B) (c₁ : limits.cone (wide_pullback_diagram_of_diagram_over B F)) (c₂ : limits.cone (wide_pullback_diagram_of_diagram_over B F)) (f : c₁ ⟶ c₂) : limits.cone_morphism.hom (functor.map (cones_equiv_functor B F) f) = hom_mk (limits.cone_morphism.hom f) :=
  Eq.refl (limits.cone_morphism.hom (functor.map (cones_equiv_functor B F) f))

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp] def cones_equiv_unit_iso {J : Type v} {C : Type u} [category C] (B : C) (F : discrete J ⥤ over B) : 𝟭 ≅ cones_equiv_functor B F ⋙ cones_equiv_inverse B F :=
  nat_iso.of_components
    (fun (_x : limits.cone (wide_pullback_diagram_of_diagram_over B F)) => limits.cones.ext (iso.mk 𝟙 𝟙) sorry) sorry

/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simp] def cones_equiv_counit_iso {J : Type v} {C : Type u} [category C] (B : C) (F : discrete J ⥤ over B) : cones_equiv_inverse B F ⋙ cones_equiv_functor B F ≅ 𝟭 :=
  nat_iso.of_components (fun (_x : limits.cone F) => limits.cones.ext (iso.mk (hom_mk 𝟙) (hom_mk 𝟙)) sorry) sorry

-- TODO: Can we add `. obviously` to the second arguments of `nat_iso.of_components` and

--       `cones.ext`?

/--
(Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simp] theorem cones_equiv_unit_iso_2 {J : Type v} {C : Type u} [category C] (B : C) (F : discrete J ⥤ over B) : equivalence.unit_iso (cones_equiv B F) = cones_equiv_unit_iso B F :=
  Eq.refl (equivalence.unit_iso (cones_equiv B F))

/-- Use the above equivalence to prove we have a limit. -/
theorem has_over_limit_discrete_of_wide_pullback_limit {J : Type v} {C : Type u} [category C] {B : C} (F : discrete J ⥤ over B) [limits.has_limit (wide_pullback_diagram_of_diagram_over B F)] : limits.has_limit F := sorry

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
theorem over_product_of_wide_pullback {J : Type v} {C : Type u} [category C] [limits.has_limits_of_shape (limits.wide_pullback_shape J) C] {B : C} : limits.has_limits_of_shape (discrete J) (over B) :=
  limits.has_limits_of_shape.mk fun (F : discrete J ⥤ over B) => has_over_limit_discrete_of_wide_pullback_limit F

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
theorem over_binary_product_of_pullback {C : Type u} [category C] [limits.has_pullbacks C] {B : C} : limits.has_binary_products (over B) :=
  over_product_of_wide_pullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
theorem over_products_of_wide_pullbacks {C : Type u} [category C] [limits.has_wide_pullbacks C] {B : C} : limits.has_products (over B) :=
  fun (J : Type v) => over_product_of_wide_pullback

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
theorem over_finite_products_of_finite_wide_pullbacks {C : Type u} [category C] [limits.has_finite_wide_pullbacks C] {B : C} : limits.has_finite_products (over B) :=
  fun (J : Type v) (𝒥₁ : DecidableEq J) (𝒥₂ : fintype J) => over_product_of_wide_pullback

end construct_products


/--
Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_wide_pullback` above.)
-/
theorem over_has_terminal {C : Type u} [category C] (B : C) : limits.has_terminal (over B) := sorry

