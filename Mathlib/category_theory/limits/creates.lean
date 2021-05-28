/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.PostPort

universes v u₁ u₂ l u₃ 

namespace Mathlib

namespace category_theory


/--
Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure liftable_cone {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) (c : limits.cone (K ⋙ F)) 
where
  lifted_cone : limits.cone K
  valid_lift : functor.map_cone F lifted_cone ≅ c

/--
Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
structure liftable_cocone {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) (c : limits.cocone (K ⋙ F)) 
where
  lifted_cocone : limits.cocone K
  valid_lift : functor.map_cocone F lifted_cocone ≅ c

/--
Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class creates_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) 
extends limits.reflects_limit K F
where
  lifts : (c : limits.cone (K ⋙ F)) → limits.is_limit c → liftable_cone K F c

/--
`F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class creates_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) 
where
  creates_limit : {K : J ⥤ C} → creates_limit K F

/-- `F` creates limits if it creates limits of shape `J` for any small `J`. -/
class creates_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  creates_limits_of_shape : {J : Type v} → {𝒥 : small_category J} → creates_limits_of_shape J F

/--
Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class creates_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) 
extends limits.reflects_colimit K F
where
  lifts : (c : limits.cocone (K ⋙ F)) → limits.is_colimit c → liftable_cocone K F c

/--
`F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class creates_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] (J : Type v) [small_category J] (F : C ⥤ D) 
where
  creates_colimit : {K : J ⥤ C} → creates_colimit K F

/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
class creates_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) 
where
  creates_colimits_of_shape : {J : Type v} → {𝒥 : small_category J} → creates_colimits_of_shape J F

/- Interface to the `creates_limit` class. -/

/-- `lift_limit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
def lift_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [creates_limit K F] {c : limits.cone (K ⋙ F)} (t : limits.is_limit c) : limits.cone K :=
  liftable_cone.lifted_cone (creates_limit.lifts c t)

/-- The lifted cone has an image isomorphic to the original cone. -/
def lifted_limit_maps_to_original {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [creates_limit K F] {c : limits.cone (K ⋙ F)} (t : limits.is_limit c) : functor.map_cone F (lift_limit t) ≅ c :=
  liftable_cone.valid_lift (creates_limit.lifts c t)

/-- The lifted cone is a limit. -/
def lifted_limit_is_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [creates_limit K F] {c : limits.cone (K ⋙ F)} (t : limits.is_limit c) : limits.is_limit (lift_limit t) :=
  limits.reflects_limit.reflects (limits.is_limit.of_iso_limit t (iso.symm (lifted_limit_maps_to_original t)))

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem has_limit_of_created {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [limits.has_limit (K ⋙ F)] [creates_limit K F] : limits.has_limit K :=
  limits.has_limit.mk
    (limits.limit_cone.mk (lift_limit (limits.limit.is_limit (K ⋙ F)))
      (lifted_limit_is_limit (limits.limit.is_limit (K ⋙ F))))

/--
If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : C ⥤ D) [limits.has_limits_of_shape J D] [creates_limits_of_shape J F] : limits.has_limits_of_shape J C :=
  limits.has_limits_of_shape.mk fun (G : J ⥤ C) => has_limit_of_created G F

/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
theorem has_limits_of_has_limits_creates_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [limits.has_limits D] [creates_limits F] : limits.has_limits C :=
  limits.has_limits.mk
    fun (J : Type v) (I : small_category J) => has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape F

/- Interface to the `creates_colimit` class. -/

/-- `lift_colimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
def lift_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [creates_colimit K F] {c : limits.cocone (K ⋙ F)} (t : limits.is_colimit c) : limits.cocone K :=
  liftable_cocone.lifted_cocone (creates_colimit.lifts c t)

/-- The lifted cocone has an image isomorphic to the original cocone. -/
def lifted_colimit_maps_to_original {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [creates_colimit K F] {c : limits.cocone (K ⋙ F)} (t : limits.is_colimit c) : functor.map_cocone F (lift_colimit t) ≅ c :=
  liftable_cocone.valid_lift (creates_colimit.lifts c t)

/-- The lifted cocone is a colimit. -/
def lifted_colimit_is_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [creates_colimit K F] {c : limits.cocone (K ⋙ F)} (t : limits.is_colimit c) : limits.is_colimit (lift_colimit t) :=
  limits.reflects_colimit.reflects (limits.is_colimit.of_iso_colimit t (iso.symm (lifted_colimit_maps_to_original t)))

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem has_colimit_of_created {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [limits.has_colimit (K ⋙ F)] [creates_colimit K F] : limits.has_colimit K :=
  limits.has_colimit.mk
    (limits.colimit_cocone.mk (lift_colimit (limits.colimit.is_colimit (K ⋙ F)))
      (lifted_colimit_is_colimit (limits.colimit.is_colimit (K ⋙ F))))

/--
If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : C ⥤ D) [limits.has_colimits_of_shape J D] [creates_colimits_of_shape J F] : limits.has_colimits_of_shape J C :=
  limits.has_colimits_of_shape.mk fun (G : J ⥤ C) => has_colimit_of_created G F

/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
theorem has_colimits_of_has_colimits_creates_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [limits.has_colimits D] [creates_colimits F] : limits.has_colimits C :=
  limits.has_colimits.mk
    fun (J : Type v) (I : small_category J) => has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape F

/--
A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure lifts_to_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) (c : limits.cone (K ⋙ F)) (t : limits.is_limit c) 
extends liftable_cone K F c
where
  makes_limit : limits.is_limit (liftable_cone.lifted_cone _to_liftable_cone)

/--
A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
structure lifts_to_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) (c : limits.cocone (K ⋙ F)) (t : limits.is_colimit c) 
extends liftable_cocone K F c
where
  makes_colimit : limits.is_colimit (liftable_cocone.lifted_cocone _to_liftable_cocone)

/--
If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def creates_limit_of_reflects_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F] (h : (c : limits.cone (K ⋙ F)) → (t : limits.is_limit c) → lifts_to_limit K F c t) : creates_limit K F :=
  creates_limit.mk fun (c : limits.cone (K ⋙ F)) (t : limits.is_limit c) => lifts_to_limit.to_liftable_cone (h c t)

/--
When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
-- Notice however that even if the isomorphism is `iso.refl _`,

-- this construction will insert additional identity morphisms in the cone maps,

-- so the constructed limits may not be ideal, definitionally.

def creates_limit_of_fully_faithful_of_lift {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [full F] [faithful F] [limits.has_limit (K ⋙ F)] (c : limits.cone K) (i : functor.map_cone F c ≅ limits.limit.cone (K ⋙ F)) : creates_limit K F :=
  creates_limit_of_reflects_iso
    fun (c' : limits.cone (K ⋙ F)) (t : limits.is_limit c') =>
      lifts_to_limit.mk (liftable_cone.mk c (i ≪≫ limits.is_limit.unique_up_to_iso (limits.limit.is_limit (K ⋙ F)) t))
        (limits.is_limit.of_faithful F (limits.is_limit.of_iso_limit (limits.limit.is_limit (K ⋙ F)) (iso.symm i))
          (fun (s : limits.cone K) =>
            functor.preimage F
              (limits.is_limit.lift (limits.is_limit.of_iso_limit (limits.limit.is_limit (K ⋙ F)) (iso.symm i))
                (functor.map_cone F s)))
          sorry)

/--
When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
-- Notice however that even if the isomorphism is `iso.refl _`,

-- this construction will insert additional identity morphisms in the cone maps,

-- so the constructed limits may not be ideal, definitionally.

def creates_limit_of_fully_faithful_of_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [full F] [faithful F] [limits.has_limit (K ⋙ F)] (X : C) (i : functor.obj F X ≅ limits.limit (K ⋙ F)) : creates_limit K F :=
  creates_limit_of_fully_faithful_of_lift
    (limits.cone.mk X (nat_trans.mk fun (j : J) => functor.preimage F (iso.hom i ≫ limits.limit.π (K ⋙ F) j)))
    (limits.cones.ext i sorry)

/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
protected instance preserves_limit_of_creates_limit_and_has_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [creates_limit K F] [limits.has_limit (K ⋙ F)] : limits.preserves_limit K F :=
  limits.preserves_limit.mk
    fun (c : limits.cone K) (t : limits.is_limit c) =>
      limits.is_limit.of_iso_limit (limits.limit.is_limit (K ⋙ F))
        (iso.symm (lifted_limit_maps_to_original (limits.limit.is_limit (K ⋙ F))) ≪≫
          functor.map_iso (limits.cones.functoriality K F)
            (limits.is_limit.unique_up_to_iso (lifted_limit_is_limit (limits.limit.is_limit (K ⋙ F))) t))

/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
protected instance preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : C ⥤ D) [creates_limits_of_shape J F] [limits.has_limits_of_shape J D] : limits.preserves_limits_of_shape J F :=
  limits.preserves_limits_of_shape.mk
    fun (K : J ⥤ C) => category_theory.preserves_limit_of_creates_limit_and_has_limit K F

/-- `F` preserves limits if it creates limits and `D` has limits. -/
protected instance preserves_limits_of_creates_limits_and_has_limits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [creates_limits F] [limits.has_limits D] : limits.preserves_limits F :=
  limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      category_theory.preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape F

/--
If `F` reflects isomorphisms and we can lift any limit cocone to a limit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def creates_colimit_of_reflects_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F] (h : (c : limits.cocone (K ⋙ F)) → (t : limits.is_colimit c) → lifts_to_colimit K F c t) : creates_colimit K F :=
  creates_colimit.mk
    fun (c : limits.cocone (K ⋙ F)) (t : limits.is_colimit c) => lifts_to_colimit.to_liftable_cocone (h c t)

/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
protected instance preserves_colimit_of_creates_colimit_and_has_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [creates_colimit K F] [limits.has_colimit (K ⋙ F)] : limits.preserves_colimit K F :=
  limits.preserves_colimit.mk
    fun (c : limits.cocone K) (t : limits.is_colimit c) =>
      limits.is_colimit.of_iso_colimit (limits.colimit.is_colimit (K ⋙ F))
        (iso.symm (lifted_colimit_maps_to_original (limits.colimit.is_colimit (K ⋙ F))) ≪≫
          functor.map_iso (limits.cocones.functoriality K F)
            (limits.is_colimit.unique_up_to_iso (lifted_colimit_is_colimit (limits.colimit.is_colimit (K ⋙ F))) t))

/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
protected instance preserves_colimit_of_shape_of_creates_colimits_of_shape_and_has_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (F : C ⥤ D) [creates_colimits_of_shape J F] [limits.has_colimits_of_shape J D] : limits.preserves_colimits_of_shape J F :=
  limits.preserves_colimits_of_shape.mk
    fun (K : J ⥤ C) => category_theory.preserves_colimit_of_creates_colimit_and_has_colimit K F

/-- `F` preserves limits if it creates limits and `D` has limits. -/
protected instance preserves_colimits_of_creates_colimits_and_has_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [creates_colimits F] [limits.has_colimits D] : limits.preserves_colimits F :=
  limits.preserves_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      category_theory.preserves_colimit_of_shape_of_creates_colimits_of_shape_and_has_colimits_of_shape F

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
def creates_limit_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [creates_limit K F] : creates_limit K G :=
  creates_limit.mk
    fun (c : limits.cone (K ⋙ G)) (t : limits.is_limit c) =>
      liftable_cone.mk
        (lift_limit (coe_fn (equiv.symm (limits.is_limit.postcompose_inv_equiv (iso_whisker_left K h) c)) t))
        (limits.is_limit.unique_up_to_iso
          (limits.is_limit.map_cone_equiv h
            (limits.is_limit.of_iso_limit
              (coe_fn (equiv.symm (limits.is_limit.postcompose_inv_equiv (iso_whisker_left K h) c)) t)
              (iso.symm
                (lifted_limit_maps_to_original
                  (coe_fn (equiv.symm (limits.is_limit.postcompose_inv_equiv (iso_whisker_left K h) c)) t)))))
          t)

/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
def creates_limits_of_shape_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [creates_limits_of_shape J F] : creates_limits_of_shape J G :=
  creates_limits_of_shape.mk fun (K : J ⥤ C) => creates_limit_of_nat_iso h

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
def creates_limits_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [creates_limits F] : creates_limits G :=
  creates_limits.mk fun (J : Type v) (𝒥₁ : small_category J) => creates_limits_of_shape_of_nat_iso h

/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
def creates_colimit_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [creates_colimit K F] : creates_colimit K G :=
  creates_colimit.mk
    fun (c : limits.cocone (K ⋙ G)) (t : limits.is_colimit c) =>
      liftable_cocone.mk
        (lift_colimit (coe_fn (equiv.symm (limits.is_colimit.precompose_hom_equiv (iso_whisker_left K h) c)) t))
        (limits.is_colimit.unique_up_to_iso
          (limits.is_colimit.map_cocone_equiv h
            (limits.is_colimit.of_iso_colimit
              (coe_fn (equiv.symm (limits.is_colimit.precompose_hom_equiv (iso_whisker_left K h) c)) t)
              (iso.symm
                (lifted_colimit_maps_to_original
                  (coe_fn (equiv.symm (limits.is_colimit.precompose_hom_equiv (iso_whisker_left K h) c)) t)))))
          t)

/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
def creates_colimits_of_shape_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [creates_colimits_of_shape J F] : creates_colimits_of_shape J G :=
  creates_colimits_of_shape.mk fun (K : J ⥤ C) => creates_colimit_of_nat_iso h

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
def creates_colimits_of_nat_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) [creates_colimits F] : creates_colimits G :=
  creates_colimits.mk fun (J : Type v) (𝒥₁ : small_category J) => creates_colimits_of_shape_of_nat_iso h

-- For the inhabited linter later.

/-- If F creates the limit of K, any cone lifts to a limit. -/
def lifts_to_limit_of_creates {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [creates_limit K F] (c : limits.cone (K ⋙ F)) (t : limits.is_limit c) : lifts_to_limit K F c t :=
  lifts_to_limit.mk (liftable_cone.mk (lift_limit t) (lifted_limit_maps_to_original t)) (lifted_limit_is_limit t)

-- For the inhabited linter later.

/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
def lifts_to_colimit_of_creates {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [creates_colimit K F] (c : limits.cocone (K ⋙ F)) (t : limits.is_colimit c) : lifts_to_colimit K F c t :=
  lifts_to_colimit.mk (liftable_cocone.mk (lift_colimit t) (lifted_colimit_maps_to_original t))
    (lifted_colimit_is_colimit t)

/-- Any cone lifts through the identity functor. -/
def id_lifts_cone {C : Type u₁} [category C] {J : Type v} [small_category J] {K : J ⥤ C} (c : limits.cone (K ⋙ 𝟭)) : liftable_cone K 𝟭 c :=
  liftable_cone.mk (limits.cone.mk (limits.cone.X c) (limits.cone.π c ≫ iso.hom (functor.right_unitor K)))
    (limits.cones.ext
      (iso.refl
        (limits.cone.X
          (functor.map_cone 𝟭 (limits.cone.mk (limits.cone.X c) (limits.cone.π c ≫ iso.hom (functor.right_unitor K))))))
      sorry)

/-- The identity functor creates all limits. -/
protected instance id_creates_limits {C : Type u₁} [category C] : creates_limits 𝟭 :=
  creates_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      creates_limits_of_shape.mk
        fun (F : J ⥤ C) => creates_limit.mk fun (c : limits.cone (F ⋙ 𝟭)) (t : limits.is_limit c) => id_lifts_cone c

/-- Any cocone lifts through the identity functor. -/
def id_lifts_cocone {C : Type u₁} [category C] {J : Type v} [small_category J] {K : J ⥤ C} (c : limits.cocone (K ⋙ 𝟭)) : liftable_cocone K 𝟭 c :=
  liftable_cocone.mk (limits.cocone.mk (limits.cocone.X c) (iso.inv (functor.right_unitor K) ≫ limits.cocone.ι c))
    (limits.cocones.ext
      (iso.refl
        (limits.cocone.X
          (functor.map_cocone 𝟭
            (limits.cocone.mk (limits.cocone.X c) (iso.inv (functor.right_unitor K) ≫ limits.cocone.ι c)))))
      sorry)

/-- The identity functor creates all colimits. -/
protected instance id_creates_colimits {C : Type u₁} [category C] : creates_colimits 𝟭 :=
  creates_colimits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      creates_colimits_of_shape.mk
        fun (F : J ⥤ C) =>
          creates_colimit.mk fun (c : limits.cocone (F ⋙ 𝟭)) (t : limits.is_colimit c) => id_lifts_cocone c

/-- Satisfy the inhabited linter -/
protected instance inhabited_liftable_cone {C : Type u₁} [category C] {J : Type v} [small_category J] {K : J ⥤ C} (c : limits.cone (K ⋙ 𝟭)) : Inhabited (liftable_cone K 𝟭 c) :=
  { default := id_lifts_cone c }

protected instance inhabited_liftable_cocone {C : Type u₁} [category C] {J : Type v} [small_category J] {K : J ⥤ C} (c : limits.cocone (K ⋙ 𝟭)) : Inhabited (liftable_cocone K 𝟭 c) :=
  { default := id_lifts_cocone c }

/-- Satisfy the inhabited linter -/
protected instance inhabited_lifts_to_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [creates_limit K F] (c : limits.cone (K ⋙ F)) (t : limits.is_limit c) : Inhabited (lifts_to_limit K F c t) :=
  { default := lifts_to_limit_of_creates K F c t }

protected instance inhabited_lifts_to_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] (K : J ⥤ C) (F : C ⥤ D) [creates_colimit K F] (c : limits.cocone (K ⋙ F)) (t : limits.is_colimit c) : Inhabited (lifts_to_colimit K F c t) :=
  { default := lifts_to_colimit_of_creates K F c t }

protected instance comp_creates_limit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [creates_limit K F] [creates_limit (K ⋙ F) G] : creates_limit K (F ⋙ G) :=
  creates_limit.mk
    fun (c : limits.cone (K ⋙ F ⋙ G)) (t : limits.is_limit c) =>
      liftable_cone.mk (lift_limit (lifted_limit_is_limit t))
        (functor.map_iso (limits.cones.functoriality (K ⋙ F) G)
            (lifted_limit_maps_to_original (lifted_limit_is_limit t)) ≪≫
          lifted_limit_maps_to_original t)

protected instance comp_creates_limits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [creates_limits_of_shape J F] [creates_limits_of_shape J G] : creates_limits_of_shape J (F ⋙ G) :=
  creates_limits_of_shape.mk infer_instance

protected instance comp_creates_limits {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [creates_limits F] [creates_limits G] : creates_limits (F ⋙ G) :=
  creates_limits.mk infer_instance

protected instance comp_creates_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {K : J ⥤ C} {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [creates_colimit K F] [creates_colimit (K ⋙ F) G] : creates_colimit K (F ⋙ G) :=
  creates_colimit.mk
    fun (c : limits.cocone (K ⋙ F ⋙ G)) (t : limits.is_colimit c) =>
      liftable_cocone.mk (lift_colimit (lifted_colimit_is_colimit t))
        (functor.map_iso (limits.cocones.functoriality (K ⋙ F) G)
            (lifted_colimit_maps_to_original (lifted_colimit_is_colimit t)) ≪≫
          lifted_colimit_maps_to_original t)

protected instance comp_creates_colimits_of_shape {C : Type u₁} [category C] {D : Type u₂} [category D] {J : Type v} [small_category J] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [creates_colimits_of_shape J F] [creates_colimits_of_shape J G] : creates_colimits_of_shape J (F ⋙ G) :=
  creates_colimits_of_shape.mk infer_instance

protected instance comp_creates_colimits {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [ℰ : category E] (F : C ⥤ D) (G : D ⥤ E) [creates_colimits F] [creates_colimits G] : creates_colimits (F ⋙ G) :=
  creates_colimits.mk infer_instance

