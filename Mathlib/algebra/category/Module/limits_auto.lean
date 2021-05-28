/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.category.Module.basic
import Mathlib.algebra.category.Group.limits
import Mathlib.algebra.direct_limit
import PostPort

universes u v u_1 

namespace Mathlib

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

namespace Module


protected instance add_comm_group_obj {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) (j : J) : add_comm_group (category_theory.functor.obj (F ⋙ category_theory.forget (Module R)) j) :=
  id (is_add_comm_group (category_theory.functor.obj F j))

protected instance module_obj {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) (j : J) : module R (category_theory.functor.obj (F ⋙ category_theory.forget (Module R)) j) :=
  id (is_module (category_theory.functor.obj F j))

/--
The flat sections of a functor into `Module R` form a submodule of all sections.
-/
def sections_submodule {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) : submodule R ((j : J) → ↥(category_theory.functor.obj F j)) :=
  submodule.mk (category_theory.functor.sections (F ⋙ category_theory.forget (Module R))) sorry sorry sorry

protected instance limit_add_comm_group {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) : add_comm_group
  (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Module R)))) :=
  id (submodule.add_comm_group (sections_submodule F))

protected instance limit_module {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) : module R
  (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Module R)))) :=
  id (submodule.semimodule (sections_submodule F))

/-- `limit.π (F ⋙ forget Ring) j` as a `ring_hom`. -/
def limit_π_linear_map {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) (j : J) : linear_map R
  (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Module R))))
  (category_theory.functor.obj (F ⋙ category_theory.forget (Module R)) j) :=
  linear_map.mk
    (category_theory.nat_trans.app
      (category_theory.limits.cone.π (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Module R)))) j)
    sorry sorry

namespace has_limits


-- The next two definitions are used in the construction of `has_limits (Module R)`.

-- After that, the limits should be constructed using the generic limits API,

-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Module R`.
(Internal use only; use the limits API.)
-/
def limit_cone {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) : category_theory.limits.cone F :=
  category_theory.limits.cone.mk
    (of R
      (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Module R)))))
    (category_theory.nat_trans.mk (limit_π_linear_map F))

/--
Witness that the limit cone in `Module R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) : category_theory.limits.is_limit (limit_cone F) :=
  category_theory.limits.is_limit.of_faithful (category_theory.forget (Module R))
    (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget (Module R)))
    (fun (s : category_theory.limits.cone F) =>
      linear_map.mk
        (fun
          (v : category_theory.limits.cone.X (category_theory.functor.map_cone (category_theory.forget (Module R)) s)) =>
          { val :=
              fun (j : J) =>
                category_theory.nat_trans.app
                  (category_theory.limits.cone.π (category_theory.functor.map_cone (category_theory.forget (Module R)) s))
                  j v,
            property := sorry })
        sorry sorry)
    sorry

end has_limits


/-- The category of R-modules has all limits. -/
protected instance has_limits {R : Type u} [ring R] : category_theory.limits.has_limits (Module R) :=
  category_theory.limits.has_limits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ Module R) => category_theory.limits.has_limit.mk (category_theory.limits.limit_cone.mk sorry sorry)

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_AddCommGroup_preserves_limits_aux {R : Type u} [ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Module R) : category_theory.limits.is_limit
  (category_theory.functor.map_cone (category_theory.forget₂ (Module R) AddCommGroup) (has_limits.limit_cone F)) :=
  AddCommGroup.limit_cone_is_limit (F ⋙ category_theory.forget₂ (Module R) AddCommGroup)

/--
The forgetful functor from R-modules to abelian groups preserves all limits.
-/
protected instance forget₂_AddCommGroup_preserves_limits {R : Type u} [ring R] : category_theory.limits.preserves_limits (category_theory.forget₂ (Module R) AddCommGroup) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Module R) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
            (forget₂_AddCommGroup_preserves_limits_aux F)

/--
The forgetful functor from R-modules to types preserves all limits.
-/
protected instance forget_preserves_limits {R : Type u} [ring R] : category_theory.limits.preserves_limits (category_theory.forget (Module R)) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Module R) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
            (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget (Module R)))

/-- The diagram (in the sense of `category_theory`)
 of an unbundled `direct_limit` of modules. -/
@[simp] theorem direct_limit_diagram_map {R : Type u} [ring R] {ι : Type v} [directed_order ι] (G : ι → Type v) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) [module.directed_system G f] (i : ι) (j : ι) (hij : i ⟶ j) : category_theory.functor.map (direct_limit_diagram G f) hij = f i j (direct_limit_diagram._proof_1 i j hij) :=
  Eq.refl (category_theory.functor.map (direct_limit_diagram G f) hij)

/-- The `cocone` on `direct_limit_diagram` corresponding to
the unbundled `direct_limit` of modules.

In `direct_limit_is_colimit` we show that it is a colimit cocone. -/
@[simp] theorem direct_limit_cocone_ι_app {R : Type u} [ring R] {ι : Type v} [directed_order ι] (G : ι → Type v) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) [module.directed_system G f] [DecidableEq ι] (i : ι) : category_theory.nat_trans.app (category_theory.limits.cocone.ι (direct_limit_cocone G f)) i =
  module.direct_limit.of R ι G f i :=
  Eq.refl (category_theory.nat_trans.app (category_theory.limits.cocone.ι (direct_limit_cocone G f)) i)

/-- The unbundled `direct_limit` of modules is a colimit
in the sense of `category_theory`. -/
def direct_limit_is_colimit {R : Type u} [ring R] {ι : Type v} [directed_order ι] (G : ι → Type v) [(i : ι) → add_comm_group (G i)] [(i : ι) → module R (G i)] (f : (i j : ι) → i ≤ j → linear_map R (G i) (G j)) [module.directed_system G f] [DecidableEq ι] [Nonempty ι] : category_theory.limits.is_colimit (direct_limit_cocone G f) :=
  category_theory.limits.is_colimit.mk
    fun (s : category_theory.limits.cocone (direct_limit_diagram G f)) =>
      module.direct_limit.lift R ι G f (category_theory.nat_trans.app (category_theory.limits.cocone.ι s)) sorry

