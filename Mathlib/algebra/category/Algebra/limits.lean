/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Algebra.basic
import Mathlib.algebra.category.Module.limits
import Mathlib.algebra.category.CommRing.limits
import Mathlib.PostPort

universes v u u_1 

namespace Mathlib

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

namespace Algebra


protected instance semiring_obj {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) (j : J) : semiring (category_theory.functor.obj (F ⋙ category_theory.forget (Algebra R)) j) :=
  id ring.to_semiring

protected instance algebra_obj {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) (j : J) : algebra R (category_theory.functor.obj (F ⋙ category_theory.forget (Algebra R)) j) :=
  id (is_algebra (category_theory.functor.obj F j))

/--
The flat sections of a functor into `Algebra R` form a submodule of all sections.
-/
def sections_subalgebra {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : subalgebra R ((j : J) → ↥(category_theory.functor.obj F j)) :=
  subalgebra.mk
    (subsemiring.carrier
      (SemiRing.sections_subsemiring
        (F ⋙ category_theory.forget₂ (Algebra R) Ring ⋙ category_theory.forget₂ Ring SemiRing)))
    sorry sorry sorry sorry sorry

protected instance limit_semiring {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : ring (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Algebra R)))) :=
  id (subalgebra.ring R ((j : J) → ↥(category_theory.functor.obj F j)) (sections_subalgebra F))

protected instance limit_algebra {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : algebra R
  (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Algebra R)))) :=
  id (subalgebra.algebra (sections_subalgebra F))

/-- `limit.π (F ⋙ forget (Algebra R)) j` as a `alg_hom`. -/
def limit_π_alg_hom {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) (j : J) : alg_hom R
  (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Algebra R))))
  (category_theory.functor.obj (F ⋙ category_theory.forget (Algebra R)) j) :=
  alg_hom.mk
    (ring_hom.to_fun
      (SemiRing.limit_π_ring_hom (F ⋙ category_theory.forget₂ (Algebra R) Ring ⋙ category_theory.forget₂ Ring SemiRing)
        j))
    sorry sorry sorry sorry sorry

namespace has_limits


-- The next two definitions are used in the construction of `has_limits (Algebra R)`.

-- After that, the limits should be constructed using the generic limits API,

-- e.g. `limit F`, `limit.cone F`, and `limit.is_limit F`.

/--
Construction of a limit cone in `Algebra R`.
(Internal use only; use the limits API.)
-/
def limit_cone {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : category_theory.limits.cone F :=
  category_theory.limits.cone.mk
    (of R
      (category_theory.limits.cone.X (category_theory.limits.types.limit_cone (F ⋙ category_theory.forget (Algebra R)))))
    (category_theory.nat_trans.mk (limit_π_alg_hom F))

/--
Witness that the limit cone in `Algebra R` is a limit cone.
(Internal use only; use the limits API.)
-/
def limit_cone_is_limit {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : category_theory.limits.is_limit (limit_cone F) :=
  category_theory.limits.is_limit.of_faithful (category_theory.forget (Algebra R))
    (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget (Algebra R)))
    (fun (s : category_theory.limits.cone F) =>
      alg_hom.mk
        (fun
          (v : category_theory.limits.cone.X (category_theory.functor.map_cone (category_theory.forget (Algebra R)) s)) =>
          { val :=
              fun (j : J) =>
                category_theory.nat_trans.app
                  (category_theory.limits.cone.π
                    (category_theory.functor.map_cone (category_theory.forget (Algebra R)) s))
                  j v,
            property := sorry })
        sorry sorry sorry sorry sorry)
    sorry

end has_limits


/-- The category of R-algebras has all limits. -/
protected instance has_limits {R : Type u} [comm_ring R] : category_theory.limits.has_limits (Algebra R) :=
  category_theory.limits.has_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.has_limits_of_shape.mk
        fun (F : J ⥤ Algebra R) => category_theory.limits.has_limit.mk (category_theory.limits.limit_cone.mk sorry sorry)

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_Ring_preserves_limits_aux {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : category_theory.limits.is_limit
  (category_theory.functor.map_cone (category_theory.forget₂ (Algebra R) Ring) (has_limits.limit_cone F)) :=
  Ring.limit_cone_is_limit (F ⋙ category_theory.forget₂ (Algebra R) Ring)

/--
The forgetful functor from R-algebras to rings preserves all limits.
-/
protected instance forget₂_Ring_preserves_limits {R : Type u} [comm_ring R] : category_theory.limits.preserves_limits (category_theory.forget₂ (Algebra R) Ring) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Algebra R) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
            (forget₂_Ring_preserves_limits_aux F)

/--
An auxiliary declaration to speed up typechecking.
-/
def forget₂_Module_preserves_limits_aux {R : Type u} [comm_ring R] {J : Type v} [category_theory.small_category J] (F : J ⥤ Algebra R) : category_theory.limits.is_limit
  (category_theory.functor.map_cone (category_theory.forget₂ (Algebra R) (Module R)) (has_limits.limit_cone F)) :=
  Module.has_limits.limit_cone_is_limit (F ⋙ category_theory.forget₂ (Algebra R) (Module R))

/--
The forgetful functor from R-algebras to R-modules preserves all limits.
-/
protected instance forget₂_Module_preserves_limits {R : Type u} [comm_ring R] : category_theory.limits.preserves_limits (category_theory.forget₂ (Algebra R) (Module R)) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Algebra R) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
            (forget₂_Module_preserves_limits_aux F)

/--
The forgetful functor from R-algebras to types preserves all limits.
-/
protected instance forget_preserves_limits {R : Type u} [comm_ring R] : category_theory.limits.preserves_limits (category_theory.forget (Algebra R)) :=
  category_theory.limits.preserves_limits.mk
    fun (J : Type u_1) (𝒥 : category_theory.small_category J) =>
      category_theory.limits.preserves_limits_of_shape.mk
        fun (F : J ⥤ Algebra R) =>
          category_theory.limits.preserves_limit_of_preserves_limit_cone (has_limits.limit_cone_is_limit F)
            (category_theory.limits.types.limit_cone_is_limit (F ⋙ category_theory.forget (Algebra R)))

