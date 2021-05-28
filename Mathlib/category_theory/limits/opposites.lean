/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.discrete_category
import Mathlib.PostPort

universes v u 

namespace Mathlib

namespace category_theory.limits


/--
If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_limit_of_has_colimit_left_op {C : Type u} [category C] {J : Type v} [small_category J] (F : J ⥤ (Cᵒᵖ)) [has_colimit (functor.left_op F)] : has_limit F :=
  has_limit.mk
    (limit_cone.mk (cone_of_cocone_left_op (colimit.cocone (functor.left_op F)))
      (is_limit.mk fun (s : cone F) => has_hom.hom.op (colimit.desc (functor.left_op F) (cocone_left_op_of_cone s))))

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_limits_of_shape_op_of_has_colimits_of_shape {C : Type u} [category C] {J : Type v} [small_category J] [has_colimits_of_shape (Jᵒᵖ) C] : has_limits_of_shape J (Cᵒᵖ) :=
  has_limits_of_shape.mk fun (F : J ⥤ (Cᵒᵖ)) => has_limit_of_has_colimit_left_op F

/--
If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
theorem has_limits_op_of_has_colimits {C : Type u} [category C] [has_colimits C] : has_limits (Cᵒᵖ) :=
  has_limits.mk fun (J : Type v) (𝒥 : small_category J) => has_limits_of_shape_op_of_has_colimits_of_shape

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_colimit_of_has_limit_left_op {C : Type u} [category C] {J : Type v} [small_category J] (F : J ⥤ (Cᵒᵖ)) [has_limit (functor.left_op F)] : has_colimit F :=
  has_colimit.mk
    (colimit_cocone.mk (cocone_of_cone_left_op (limit.cone (functor.left_op F)))
      (is_colimit.mk fun (s : cocone F) => has_hom.hom.op (limit.lift (functor.left_op F) (cone_left_op_of_cocone s))))

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_colimits_of_shape_op_of_has_limits_of_shape {C : Type u} [category C] {J : Type v} [small_category J] [has_limits_of_shape (Jᵒᵖ) C] : has_colimits_of_shape J (Cᵒᵖ) :=
  has_colimits_of_shape.mk fun (F : J ⥤ (Cᵒᵖ)) => has_colimit_of_has_limit_left_op F

/--
If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
theorem has_colimits_op_of_has_limits {C : Type u} [category C] [has_limits C] : has_colimits (Cᵒᵖ) :=
  has_colimits.mk fun (J : Type v) (𝒥 : small_category J) => has_colimits_of_shape_op_of_has_limits_of_shape

/--
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
theorem has_coproducts_opposite {C : Type u} [category C] (X : Type v) [has_products_of_shape X C] : has_coproducts_of_shape X (Cᵒᵖ) :=
  has_colimits_of_shape_op_of_has_limits_of_shape

/--
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
theorem has_products_opposite {C : Type u} [category C] (X : Type v) [has_coproducts_of_shape X C] : has_products_of_shape X (Cᵒᵖ) :=
  has_limits_of_shape_op_of_has_colimits_of_shape

