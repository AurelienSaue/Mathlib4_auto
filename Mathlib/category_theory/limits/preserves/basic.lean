/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.PostPort

universes v u₁ u₂ l u₃ 

namespace Mathlib

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C → D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/

namespace category_theory.limits


/--
A functor `F` preserves limits of `K` (written as `preserves_limit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) 
where
  preserves : {c : cone K} → is_limit c → is_limit (functor.map_cone F c)

/--
A functor `F` preserves colimits of `K` (written as `preserves_colimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class preserves_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) 
where
  preserves : {c : cocone K} → is_colimit c → is_colimit (functor.map_cocone F c)

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
    `K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class preserves_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) 
where
  preserves_limit : {K : J ⥤ C} → preserves_limit K F

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
    `K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
class preserves_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) 
where
  preserves_colimit : {K : J ⥤ C} → preserves_colimit K F

/-- We say that `F` preserves limits if it sends limit cones over any diagram to limit cones. -/
class preserves_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  preserves_limits_of_shape : {J : Type v} → [𝒥 : small_category J] → preserves_limits_of_shape J F

/-- We say that `F` preserves colimits if it sends colimit cocones over any diagram to colimit
    cocones.-/
class preserves_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  preserves_colimits_of_shape : {J : Type v} → [𝒥 : small_category J] → preserves_colimits_of_shape J F

/--
A convenience function for `preserves_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_limit_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} (F : C ⥤ D) {c : cone K} (t : is_limit c) [preserves_limit K F] : is_limit (functor.map_cone F c) :=
  preserves_limit.preserves t

/--
A convenience function for `preserves_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_colimit_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} (F : C ⥤ D) {c : cocone K} (t : is_colimit c) [preserves_colimit K F] : is_colimit (functor.map_cocone F c) :=
  preserves_colimit.preserves t

protected instance preserves_limit_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) : subsingleton (preserves_limit K F) :=
  subsingleton.intro
    fun (a b : preserves_limit K F) =>
      preserves_limit.cases_on a
        fun (a : {c : cone K} → is_limit c → is_limit (functor.map_cone F c)) =>
          preserves_limit.cases_on b
            fun (b : {c : cone K} → is_limit c → is_limit (functor.map_cone F c)) =>
              (fun {K : J ⥤ C} {F : C ⥤ D}
                  (preserves preserves_1 : {c : cone K} → is_limit c → is_limit (functor.map_cone F c)) =>
                  Eq.trans
                    ((fun {K : J ⥤ C} {F : C ⥤ D}
                        (preserves : {c : cone K} → is_limit c → is_limit (functor.map_cone F c)) =>
                        Eq.refl (preserves_limit.mk preserves))
                      preserves)
                    (congr (Eq.refl preserves_limit.mk) (subsingleton.elim preserves preserves_1)))
                a b

protected instance preserves_colimit_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) : subsingleton (preserves_colimit K F) :=
  subsingleton.intro
    fun (a b : preserves_colimit K F) =>
      preserves_colimit.cases_on a
        fun (a : {c : cocone K} → is_colimit c → is_colimit (functor.map_cocone F c)) =>
          preserves_colimit.cases_on b
            fun (b : {c : cocone K} → is_colimit c → is_colimit (functor.map_cocone F c)) =>
              (fun {K : J ⥤ C} {F : C ⥤ D}
                  (preserves preserves_1 : {c : cocone K} → is_colimit c → is_colimit (functor.map_cocone F c)) =>
                  Eq.trans
                    ((fun {K : J ⥤ C} {F : C ⥤ D}
                        (preserves : {c : cocone K} → is_colimit c → is_colimit (functor.map_cocone F c)) =>
                        Eq.refl (preserves_colimit.mk preserves))
                      preserves)
                    (congr (Eq.refl preserves_colimit.mk) (subsingleton.elim preserves preserves_1)))
                a b

protected instance preserves_limits_of_shape_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) : subsingleton (preserves_limits_of_shape J F) :=
  subsingleton.intro
    fun (a b : preserves_limits_of_shape J F) =>
      preserves_limits_of_shape.cases_on a
        fun (a : {K : J ⥤ C} → preserves_limit K F) =>
          preserves_limits_of_shape.cases_on b
            fun (b : {K : J ⥤ C} → preserves_limit K F) =>
              (fun [_inst_4 : small_category J] {F : C ⥤ D}
                  (preserves_limit preserves_limit_1 : {K : J ⥤ C} → preserves_limit K F) =>
                  Eq.trans
                    ((fun [_inst_4 : small_category J] {F : C ⥤ D}
                        (preserves_limit : {K : J ⥤ C} → preserves_limit K F) =>
                        Eq.refl (preserves_limits_of_shape.mk preserves_limit))
                      preserves_limit)
                    (congr (Eq.refl preserves_limits_of_shape.mk) (subsingleton.elim preserves_limit preserves_limit_1)))
                a b

protected instance preserves_colimits_of_shape_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) : subsingleton (preserves_colimits_of_shape J F) :=
  subsingleton.intro
    fun (a b : preserves_colimits_of_shape J F) =>
      preserves_colimits_of_shape.cases_on a
        fun (a : {K : J ⥤ C} → preserves_colimit K F) =>
          preserves_colimits_of_shape.cases_on b
            fun (b : {K : J ⥤ C} → preserves_colimit K F) =>
              (fun [_inst_4 : small_category J] {F : C ⥤ D}
                  (preserves_colimit preserves_colimit_1 : {K : J ⥤ C} → preserves_colimit K F) =>
                  Eq.trans
                    ((fun [_inst_4 : small_category J] {F : C ⥤ D}
                        (preserves_colimit : {K : J ⥤ C} → preserves_colimit K F) =>
                        Eq.refl (preserves_colimits_of_shape.mk preserves_colimit))
                      preserves_colimit)
                    (congr (Eq.refl preserves_colimits_of_shape.mk)
                      (subsingleton.elim preserves_colimit preserves_colimit_1)))
                a b

protected instance preserves_limits_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : subsingleton (preserves_limits F) :=
  subsingleton.intro
    fun (a b : preserves_limits F) =>
      preserves_limits.cases_on a
        fun (a : {J : Type v} → [𝒥 : small_category J] → preserves_limits_of_shape J F) =>
          preserves_limits.cases_on b
            fun (b : {J : Type v} → [𝒥 : small_category J] → preserves_limits_of_shape J F) =>
              of_eq_true
                (eq_true_intro
                  (eq_of_heq
                    ((fun
                        (preserves_limits_of_shape preserves_limits_of_shape' :
                        {J : Type v} → [𝒥 : small_category J] → preserves_limits_of_shape J F)
                        (e_0 : preserves_limits_of_shape = preserves_limits_of_shape') =>
                        Eq._oldrec (HEq.refl (preserves_limits.mk preserves_limits_of_shape)) e_0)
                      a b (Eq.symm (subsingleton.elim b a)))))

protected instance preserves_colimits_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : subsingleton (preserves_colimits F) :=
  subsingleton.intro
    fun (a b : preserves_colimits F) =>
      preserves_colimits.cases_on a
        fun (a : {J : Type v} → [𝒥 : small_category J] → preserves_colimits_of_shape J F) =>
          preserves_colimits.cases_on b
            fun (b : {J : Type v} → [𝒥 : small_category J] → preserves_colimits_of_shape J F) =>
              of_eq_true
                (eq_true_intro
                  (eq_of_heq
                    ((fun
                        (preserves_colimits_of_shape preserves_colimits_of_shape' :
                        {J : Type v} → [𝒥 : small_category J] → preserves_colimits_of_shape J F)
                        (e_0 : preserves_colimits_of_shape = preserves_colimits_of_shape') =>
                        Eq._oldrec (HEq.refl (preserves_colimits.mk preserves_colimits_of_shape)) e_0)
                      a b (Eq.symm (subsingleton.elim b a)))))

protected instance id_preserves_limits {C : Type u₁} [category C] : preserves_limits 𝟭 :=
  preserves_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      preserves_limits_of_shape.mk
        fun (K : J ⥤ C) =>
          preserves_limit.mk
            fun (c : cone K) (h : is_limit c) =>
              is_limit.mk
                fun (s : cone (K ⋙ 𝟭)) =>
                  is_limit.lift h (cone.mk (cone.X s) (nat_trans.mk fun (j : J) => nat_trans.app (cone.π s) j))

protected instance id_preserves_colimits {C : Type u₁} [category C] : preserves_colimits 𝟭 :=
  preserves_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      preserves_colimits_of_shape.mk
        fun (K : J ⥤ C) =>
          preserves_colimit.mk
            fun (c : cocone K) (h : is_colimit c) =>
              is_colimit.mk
                fun (s : cocone (K ⋙ 𝟭)) =>
                  is_colimit.desc h (cocone.mk (cocone.X s) (nat_trans.mk fun (j : J) => nat_trans.app (cocone.ι s) j))

protected instance comp_preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_limit K F] [preserves_limit (K ⋙ F) G] : preserves_limit K (F ⋙ G) :=
  preserves_limit.mk fun (c : cone K) (h : is_limit c) => preserves_limit.preserves (preserves_limit.preserves h)

protected instance comp_preserves_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_limits_of_shape J F] [preserves_limits_of_shape J G] : preserves_limits_of_shape J (F ⋙ G) :=
  preserves_limits_of_shape.mk fun (K : J ⥤ C) => infer_instance

protected instance comp_preserves_limits {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_limits F] [preserves_limits G] : preserves_limits (F ⋙ G) :=
  preserves_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => infer_instance

protected instance comp_preserves_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_colimit K F] [preserves_colimit (K ⋙ F) G] : preserves_colimit K (F ⋙ G) :=
  preserves_colimit.mk
    fun (c : cocone K) (h : is_colimit c) => preserves_colimit.preserves (preserves_colimit.preserves h)

protected instance comp_preserves_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_colimits_of_shape J F] [preserves_colimits_of_shape J G] : preserves_colimits_of_shape J (F ⋙ G) :=
  preserves_colimits_of_shape.mk fun (K : J ⥤ C) => infer_instance

protected instance comp_preserves_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_colimits F] [preserves_colimits G] : preserves_colimits (F ⋙ G) :=
  preserves_colimits.mk fun (J : Type v) (𝒥₁ : small_category J) => infer_instance

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preserves_limit_of_preserves_limit_cone {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} {t : cone K} (h : is_limit t) (hF : is_limit (functor.map_cone F t)) : preserves_limit K F :=
  preserves_limit.mk
    fun (t' : cone K) (h' : is_limit t') =>
      is_limit.of_iso_limit hF (functor.map_iso (cones.functoriality K F) (is_limit.unique_up_to_iso h h'))

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
def preserves_limit_of_iso_diagram {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K₁ : J ⥤ C} {K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [preserves_limit K₁ F] : preserves_limit K₂ F :=
  preserves_limit.mk
    fun (c : cone K₂) (t : is_limit c) =>
      coe_fn (is_limit.postcompose_inv_equiv (iso_whisker_right h F) (functor.map_cone F c))
        (is_limit.of_iso_limit (is_limit_of_preserves F (coe_fn (equiv.symm (is_limit.postcompose_inv_equiv h c)) t))
          (cones.ext (iso.refl (cone.X (functor.map_cone F (functor.obj (cones.postcompose (iso.inv h)) c)))) sorry))

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
def preserves_limit_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [preserves_limit K F] : preserves_limit K G :=
  preserves_limit.mk fun (c : cone K) (t : is_limit c) => is_limit.map_cone_equiv h (preserves_limit.preserves t)

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
def preserves_limits_of_shape_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [preserves_limits_of_shape J F] : preserves_limits_of_shape J G :=
  preserves_limits_of_shape.mk fun (K : J ⥤ C) => preserves_limit_of_nat_iso K h

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
def preserves_limits_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [preserves_limits F] : preserves_limits G :=
  preserves_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => preserves_limits_of_shape_of_nat_iso h

/-- Transfer preservation of limits along a equivalence in the shape. -/
def preserves_limits_of_shape_of_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {J' : Type v} [small_category J'] (e : J ≌ J') (F : C ⥤ D) [preserves_limits_of_shape J F] : preserves_limits_of_shape J' F :=
  preserves_limits_of_shape.mk
    fun (K : J' ⥤ C) =>
      preserves_limit.mk
        fun (c : cone K) (t : is_limit c) =>
          let equ : equivalence.inverse e ⋙ equivalence.functor e ⋙ K ⋙ F ≅ K ⋙ F :=
            equivalence.inv_fun_id_assoc e (K ⋙ F);
          is_limit.of_iso_limit
            (coe_fn
              (equiv.symm
                (is_limit.postcompose_hom_equiv equ
                  (cone.whisker (equivalence.functor (equivalence.symm e))
                    (functor.map_cone F (cone.whisker (equivalence.functor e) c)))))
              (is_limit.whisker_equivalence (is_limit_of_preserves F (is_limit.whisker_equivalence t e))
                (equivalence.symm e)))
            (cones.ext
              (iso.refl
                (cone.X
                  (functor.obj (cones.postcompose (iso.hom equ))
                    (cone.whisker (equivalence.functor (equivalence.symm e))
                      (functor.map_cone F (cone.whisker (equivalence.functor e) c))))))
              sorry)

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
def preserves_colimit_of_preserves_colimit_cocone {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} {t : cocone K} (h : is_colimit t) (hF : is_colimit (functor.map_cocone F t)) : preserves_colimit K F :=
  preserves_colimit.mk
    fun (t' : cocone K) (h' : is_colimit t') =>
      is_colimit.of_iso_colimit hF (functor.map_iso (cocones.functoriality K F) (is_colimit.unique_up_to_iso h h'))

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
def preserves_colimit_of_iso_diagram {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K₁ : J ⥤ C} {K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [preserves_colimit K₁ F] : preserves_colimit K₂ F :=
  preserves_colimit.mk
    fun (c : cocone K₂) (t : is_colimit c) =>
      coe_fn (is_colimit.precompose_hom_equiv (iso_whisker_right h F) (functor.map_cocone F c))
        (is_colimit.of_iso_colimit
          (is_colimit_of_preserves F (coe_fn (equiv.symm (is_colimit.precompose_hom_equiv h c)) t))
          (cocones.ext (iso.refl (cocone.X (functor.map_cocone F (functor.obj (cocones.precompose (iso.hom h)) c))))
            sorry))

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
def preserves_colimit_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [preserves_colimit K F] : preserves_colimit K G :=
  preserves_colimit.mk
    fun (c : cocone K) (t : is_colimit c) => is_colimit.map_cocone_equiv h (preserves_colimit.preserves t)

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
def preserves_colimits_of_shape_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [preserves_colimits_of_shape J F] : preserves_colimits_of_shape J G :=
  preserves_colimits_of_shape.mk fun (K : J ⥤ C) => preserves_colimit_of_nat_iso K h

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
def preserves_colimits_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [preserves_colimits F] : preserves_colimits G :=
  preserves_colimits.mk fun (J : Type v) (𝒥₁ : small_category J) => preserves_colimits_of_shape_of_nat_iso h

/-- Transfer preservation of colimits along a equivalence in the shape. -/
def preserves_colimits_of_shape_of_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {J' : Type v} [small_category J'] (e : J ≌ J') (F : C ⥤ D) [preserves_colimits_of_shape J F] : preserves_colimits_of_shape J' F := sorry

/--
A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class reflects_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) 
where
  reflects : {c : cone K} → is_limit (functor.map_cone F c) → is_limit c

/--
A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class reflects_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) 
where
  reflects : {c : cocone K} → is_colimit (functor.map_cocone F c) → is_colimit c

/--
A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class reflects_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) 
where
  reflects_limit : {K : J ⥤ C} → reflects_limit K F

/--
A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class reflects_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) 
where
  reflects_colimit : {K : J ⥤ C} → reflects_colimit K F

/--
A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class reflects_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  reflects_limits_of_shape : {J : Type v} → {𝒥 : small_category J} → reflects_limits_of_shape J F

/--
A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class reflects_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  reflects_colimits_of_shape : {J : Type v} → {𝒥 : small_category J} → reflects_colimits_of_shape J F

/--
A convenience function for `reflects_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_limit_of_reflects {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} (F : C ⥤ D) {c : cone K} (t : is_limit (functor.map_cone F c)) [reflects_limit K F] : is_limit c :=
  reflects_limit.reflects t

/--
A convenience function for `reflects_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_colimit_of_reflects {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} (F : C ⥤ D) {c : cocone K} (t : is_colimit (functor.map_cocone F c)) [reflects_colimit K F] : is_colimit c :=
  reflects_colimit.reflects t

protected instance reflects_limit_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) : subsingleton (reflects_limit K F) :=
  subsingleton.intro
    fun (a b : reflects_limit K F) =>
      reflects_limit.cases_on a
        fun (a : {c : cone K} → is_limit (functor.map_cone F c) → is_limit c) =>
          reflects_limit.cases_on b
            fun (b : {c : cone K} → is_limit (functor.map_cone F c) → is_limit c) =>
              (fun {K : J ⥤ C} {F : C ⥤ D}
                  (reflects reflects_1 : {c : cone K} → is_limit (functor.map_cone F c) → is_limit c) =>
                  Eq.trans
                    ((fun {K : J ⥤ C} {F : C ⥤ D}
                        (reflects : {c : cone K} → is_limit (functor.map_cone F c) → is_limit c) =>
                        Eq.refl (reflects_limit.mk reflects))
                      reflects)
                    (congr (Eq.refl reflects_limit.mk) (subsingleton.elim reflects reflects_1)))
                a b

protected instance reflects_colimit_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) : subsingleton (reflects_colimit K F) :=
  subsingleton.intro
    fun (a b : reflects_colimit K F) =>
      reflects_colimit.cases_on a
        fun (a : {c : cocone K} → is_colimit (functor.map_cocone F c) → is_colimit c) =>
          reflects_colimit.cases_on b
            fun (b : {c : cocone K} → is_colimit (functor.map_cocone F c) → is_colimit c) =>
              (fun {K : J ⥤ C} {F : C ⥤ D}
                  (reflects reflects_1 : {c : cocone K} → is_colimit (functor.map_cocone F c) → is_colimit c) =>
                  Eq.trans
                    ((fun {K : J ⥤ C} {F : C ⥤ D}
                        (reflects : {c : cocone K} → is_colimit (functor.map_cocone F c) → is_colimit c) =>
                        Eq.refl (reflects_colimit.mk reflects))
                      reflects)
                    (congr (Eq.refl reflects_colimit.mk) (subsingleton.elim reflects reflects_1)))
                a b

protected instance reflects_limits_of_shape_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) : subsingleton (reflects_limits_of_shape J F) :=
  subsingleton.intro
    fun (a b : reflects_limits_of_shape J F) =>
      reflects_limits_of_shape.cases_on a
        fun (a : {K : J ⥤ C} → reflects_limit K F) =>
          reflects_limits_of_shape.cases_on b
            fun (b : {K : J ⥤ C} → reflects_limit K F) =>
              (fun [_inst_4 : small_category J] {F : C ⥤ D}
                  (reflects_limit reflects_limit_1 : {K : J ⥤ C} → reflects_limit K F) =>
                  Eq.trans
                    ((fun [_inst_4 : small_category J] {F : C ⥤ D} (reflects_limit : {K : J ⥤ C} → reflects_limit K F) =>
                        Eq.refl (reflects_limits_of_shape.mk reflects_limit))
                      reflects_limit)
                    (congr (Eq.refl reflects_limits_of_shape.mk) (subsingleton.elim reflects_limit reflects_limit_1)))
                a b

protected instance reflects_colimits_of_shape_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) : subsingleton (reflects_colimits_of_shape J F) :=
  subsingleton.intro
    fun (a b : reflects_colimits_of_shape J F) =>
      reflects_colimits_of_shape.cases_on a
        fun (a : {K : J ⥤ C} → reflects_colimit K F) =>
          reflects_colimits_of_shape.cases_on b
            fun (b : {K : J ⥤ C} → reflects_colimit K F) =>
              (fun [_inst_4 : small_category J] {F : C ⥤ D}
                  (reflects_colimit reflects_colimit_1 : {K : J ⥤ C} → reflects_colimit K F) =>
                  Eq.trans
                    ((fun [_inst_4 : small_category J] {F : C ⥤ D}
                        (reflects_colimit : {K : J ⥤ C} → reflects_colimit K F) =>
                        Eq.refl (reflects_colimits_of_shape.mk reflects_colimit))
                      reflects_colimit)
                    (congr (Eq.refl reflects_colimits_of_shape.mk)
                      (subsingleton.elim reflects_colimit reflects_colimit_1)))
                a b

protected instance reflects_limits_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : subsingleton (reflects_limits F) :=
  subsingleton.intro
    fun (a b : reflects_limits F) =>
      reflects_limits.cases_on a
        fun (a : {J : Type v} → {𝒥 : small_category J} → reflects_limits_of_shape J F) =>
          reflects_limits.cases_on b
            fun (b : {J : Type v} → {𝒥 : small_category J} → reflects_limits_of_shape J F) =>
              of_eq_true
                (eq_true_intro
                  (eq_of_heq
                    ((fun
                        (reflects_limits_of_shape reflects_limits_of_shape' :
                        {J : Type v} → {𝒥 : small_category J} → reflects_limits_of_shape J F)
                        (e_0 : reflects_limits_of_shape = reflects_limits_of_shape') =>
                        Eq._oldrec (HEq.refl (reflects_limits.mk reflects_limits_of_shape)) e_0)
                      a b (Eq.symm (subsingleton.elim b a)))))

protected instance reflects_colimits_subsingleton {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : subsingleton (reflects_colimits F) :=
  subsingleton.intro
    fun (a b : reflects_colimits F) =>
      reflects_colimits.cases_on a
        fun (a : {J : Type v} → {𝒥 : small_category J} → reflects_colimits_of_shape J F) =>
          reflects_colimits.cases_on b
            fun (b : {J : Type v} → {𝒥 : small_category J} → reflects_colimits_of_shape J F) =>
              of_eq_true
                (eq_true_intro
                  (eq_of_heq
                    ((fun
                        (reflects_colimits_of_shape reflects_colimits_of_shape' :
                        {J : Type v} → {𝒥 : small_category J} → reflects_colimits_of_shape J F)
                        (e_0 : reflects_colimits_of_shape = reflects_colimits_of_shape') =>
                        Eq._oldrec (HEq.refl (reflects_colimits.mk reflects_colimits_of_shape)) e_0)
                      a b (Eq.symm (subsingleton.elim b a)))))

protected instance reflects_limit_of_reflects_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [H : reflects_limits_of_shape J F] : reflects_limit K F :=
  reflects_limits_of_shape.reflects_limit

protected instance reflects_colimit_of_reflects_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [H : reflects_colimits_of_shape J F] : reflects_colimit K F :=
  reflects_colimits_of_shape.reflects_colimit

protected instance reflects_limits_of_shape_of_reflects_limits {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : C ⥤ D) [H : reflects_limits F] : reflects_limits_of_shape J F :=
  reflects_limits.reflects_limits_of_shape

protected instance reflects_colimits_of_shape_of_reflects_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : C ⥤ D) [H : reflects_colimits F] : reflects_colimits_of_shape J F :=
  reflects_colimits.reflects_colimits_of_shape

protected instance id_reflects_limits {C : Type u₁} [category C] : reflects_limits 𝟭 :=
  reflects_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      reflects_limits_of_shape.mk
        fun (K : J ⥤ C) =>
          reflects_limit.mk
            fun (c : cone K) (h : is_limit (functor.map_cone 𝟭 c)) =>
              is_limit.mk
                fun (s : cone K) =>
                  is_limit.lift h (cone.mk (cone.X s) (nat_trans.mk fun (j : J) => nat_trans.app (cone.π s) j))

protected instance id_reflects_colimits {C : Type u₁} [category C] : reflects_colimits 𝟭 :=
  reflects_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      reflects_colimits_of_shape.mk
        fun (K : J ⥤ C) =>
          reflects_colimit.mk
            fun (c : cocone K) (h : is_colimit (functor.map_cocone 𝟭 c)) =>
              is_colimit.mk
                fun (s : cocone K) =>
                  is_colimit.desc h (cocone.mk (cocone.X s) (nat_trans.mk fun (j : J) => nat_trans.app (cocone.ι s) j))

protected instance comp_reflects_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [reflects_limit K F] [reflects_limit (K ⋙ F) G] : reflects_limit K (F ⋙ G) :=
  reflects_limit.mk
    fun (c : cone K) (h : is_limit (functor.map_cone (F ⋙ G) c)) => reflects_limit.reflects (reflects_limit.reflects h)

protected instance comp_reflects_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [reflects_limits_of_shape J F] [reflects_limits_of_shape J G] : reflects_limits_of_shape J (F ⋙ G) :=
  reflects_limits_of_shape.mk fun (K : J ⥤ C) => infer_instance

protected instance comp_reflects_limits {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [reflects_limits F] [reflects_limits G] : reflects_limits (F ⋙ G) :=
  reflects_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => infer_instance

protected instance comp_reflects_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [reflects_colimit K F] [reflects_colimit (K ⋙ F) G] : reflects_colimit K (F ⋙ G) :=
  reflects_colimit.mk
    fun (c : cocone K) (h : is_colimit (functor.map_cocone (F ⋙ G) c)) =>
      reflects_colimit.reflects (reflects_colimit.reflects h)

protected instance comp_reflects_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [reflects_colimits_of_shape J F] [reflects_colimits_of_shape J G] : reflects_colimits_of_shape J (F ⋙ G) :=
  reflects_colimits_of_shape.mk fun (K : J ⥤ C) => infer_instance

protected instance comp_reflects_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [reflects_colimits F] [reflects_colimits G] : reflects_colimits (F ⋙ G) :=
  reflects_colimits.mk fun (J : Type v) (𝒥₁ : small_category J) => infer_instance

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
def preserves_limit_of_reflects_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_limit K (F ⋙ G)] [reflects_limit (K ⋙ F) G] : preserves_limit K F :=
  preserves_limit.mk fun (c : cone K) (h : is_limit c) => is_limit_of_reflects G (is_limit_of_preserves (F ⋙ G) h)

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
def preserves_limits_of_shape_of_reflects_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_limits_of_shape J (F ⋙ G)] [reflects_limits_of_shape J G] : preserves_limits_of_shape J F :=
  preserves_limits_of_shape.mk fun (K : J ⥤ C) => preserves_limit_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
def preserves_limits_of_reflects_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_limits (F ⋙ G)] [reflects_limits G] : preserves_limits F :=
  preserves_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => preserves_limits_of_shape_of_reflects_of_preserves F G

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
def reflects_limit_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [reflects_limit K F] : reflects_limit K G :=
  reflects_limit.mk
    fun (c : cone K) (t : is_limit (functor.map_cone G c)) =>
      reflects_limit.reflects (is_limit.map_cone_equiv (iso.symm h) t)

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
def reflects_limits_of_shape_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [reflects_limits_of_shape J F] : reflects_limits_of_shape J G :=
  reflects_limits_of_shape.mk fun (K : J ⥤ C) => reflects_limit_of_nat_iso K h

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
def reflects_limits_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [reflects_limits F] : reflects_limits G :=
  reflects_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => reflects_limits_of_shape_of_nat_iso h

/--
If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F`.
-/
def reflects_limit_of_reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : J ⥤ C) (G : C ⥤ D) [reflects_isomorphisms G] [has_limit F] [preserves_limit F G] : reflects_limit F G :=
  reflects_limit.mk fun (c : cone F) (t : is_limit (functor.map_cone G c)) => is_limit.of_point_iso (limit.is_limit F)

/--
If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
def reflects_limits_of_shape_of_reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {G : C ⥤ D} [reflects_isomorphisms G] [has_limits_of_shape J C] [preserves_limits_of_shape J G] : reflects_limits_of_shape J G :=
  reflects_limits_of_shape.mk fun (F : J ⥤ C) => reflects_limit_of_reflects_isomorphisms F G

/--
If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
def reflects_limits_of_reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] {G : C ⥤ D} [reflects_isomorphisms G] [has_limits C] [preserves_limits G] : reflects_limits G :=
  reflects_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => reflects_limits_of_shape_of_reflects_isomorphisms

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
def preserves_colimit_of_reflects_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_colimit K (F ⋙ G)] [reflects_colimit (K ⋙ F) G] : preserves_colimit K F :=
  preserves_colimit.mk
    fun (c : cocone K) (h : is_colimit c) => is_colimit_of_reflects G (is_colimit_of_preserves (F ⋙ G) h)

/--
If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
def preserves_colimits_of_shape_of_reflects_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_colimits_of_shape J (F ⋙ G)] [reflects_colimits_of_shape J G] : preserves_colimits_of_shape J F :=
  preserves_colimits_of_shape.mk fun (K : J ⥤ C) => preserves_colimit_of_reflects_of_preserves F G

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
def preserves_colimits_of_reflects_of_preserves {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [preserves_colimits (F ⋙ G)] [reflects_colimits G] : preserves_colimits F :=
  preserves_colimits.mk
    fun (J : Type v) (𝒥₁ : small_category J) => preserves_colimits_of_shape_of_reflects_of_preserves F G

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
def reflects_colimit_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [reflects_colimit K F] : reflects_colimit K G :=
  reflects_colimit.mk
    fun (c : cocone K) (t : is_colimit (functor.map_cocone G c)) =>
      reflects_colimit.reflects (is_colimit.map_cocone_equiv (iso.symm h) t)

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
def reflects_colimits_of_shape_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [reflects_colimits_of_shape J F] : reflects_colimits_of_shape J G :=
  reflects_colimits_of_shape.mk fun (K : J ⥤ C) => reflects_colimit_of_nat_iso K h

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
def reflects_colimits_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [reflects_colimits F] : reflects_colimits G :=
  reflects_colimits.mk fun (J : Type v) (𝒥₁ : small_category J) => reflects_colimits_of_shape_of_nat_iso h

/--
If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F`.
-/
def reflects_colimit_of_reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : J ⥤ C) (G : C ⥤ D) [reflects_isomorphisms G] [has_colimit F] [preserves_colimit F G] : reflects_colimit F G :=
  reflects_colimit.mk
    fun (c : cocone F) (t : is_colimit (functor.map_cocone G c)) => is_colimit.of_point_iso (colimit.is_colimit F)

/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
def reflects_colimits_of_shape_of_reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {G : C ⥤ D} [reflects_isomorphisms G] [has_colimits_of_shape J C] [preserves_colimits_of_shape J G] : reflects_colimits_of_shape J G :=
  reflects_colimits_of_shape.mk fun (F : J ⥤ C) => reflects_colimit_of_reflects_isomorphisms F G

/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
def reflects_colimits_of_reflects_isomorphisms {C : Type u₁} [category C] {D : Type u₂} [category D] {G : C ⥤ D} [reflects_isomorphisms G] [has_colimits C] [preserves_colimits G] : reflects_colimits G :=
  reflects_colimits.mk fun (J : Type v) (𝒥₁ : small_category J) => reflects_colimits_of_shape_of_reflects_isomorphisms

/-- A fully faithful functor reflects limits. -/
def fully_faithful_reflects_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [full F] [faithful F] : reflects_limits F :=
  reflects_limits.mk
    fun (J : Type v) (𝒥₁ : small_category J) =>
      reflects_limits_of_shape.mk
        fun (K : J ⥤ C) =>
          reflects_limit.mk
            fun (c : cone K) (t : is_limit (functor.map_cone F c)) =>
              is_limit.mk_cone_morphism
                (fun (s : cone K) =>
                  functor.preimage (cones.functoriality K F)
                    (is_limit.lift_cone_morphism t (functor.obj (cones.functoriality K F) s)))
                sorry

/-- A fully faithful functor reflects colimits. -/
def fully_faithful_reflects_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [full F] [faithful F] : reflects_colimits F :=
  reflects_colimits.mk
    fun (J : Type v) (𝒥₁ : small_category J) =>
      reflects_colimits_of_shape.mk
        fun (K : J ⥤ C) =>
          reflects_colimit.mk
            fun (c : cocone K) (t : is_colimit (functor.map_cocone F c)) =>
              is_colimit.mk_cocone_morphism
                (fun (s : cocone K) =>
                  functor.preimage (cocones.functoriality K F)
                    (is_colimit.desc_cocone_morphism t (functor.obj (cocones.functoriality K F) s)))
                sorry

