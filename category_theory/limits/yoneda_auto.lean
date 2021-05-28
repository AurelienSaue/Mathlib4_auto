/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.limits.functor_category
import PostPort

universes v u 

namespace Mathlib

/-!
# Limit properties relating to the (co)yoneda embedding.

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `punit`.
(This is used in characterising cofinal functors.)

We also show the (co)yoneda embeddings preserve limits and jointly reflect them.
-/

namespace category_theory


namespace coyoneda


/--
The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simp] theorem colimit_cocone_ι_app {C : Type v} [small_category C] (X : Cᵒᵖ) (X_1 : C) : ∀ (ᾰ : functor.obj (functor.obj coyoneda X) X_1),
  nat_trans.app (limits.cocone.ι (colimit_cocone X)) X_1 ᾰ =
    id
      (fun (ᾰ : functor.obj (functor.obj coyoneda X) X_1) =>
        id (fun (X : Cᵒᵖ) (X_1 : C) (ᾰ : opposite.unop X ⟶ X_1) => PUnit.unit) X X_1 ᾰ)
      ᾰ :=
  fun (ᾰ : functor.obj (functor.obj coyoneda X) X_1) => Eq.refl (nat_trans.app (limits.cocone.ι (colimit_cocone X)) X_1 ᾰ)

/--
The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
def colimit_cocone_is_colimit {C : Type v} [small_category C] (X : Cᵒᵖ) : limits.is_colimit (colimit_cocone X) :=
  limits.is_colimit.mk
    fun (s : limits.cocone (functor.obj coyoneda X)) (x : limits.cocone.X (colimit_cocone X)) =>
      nat_trans.app (limits.cocone.ι s) (opposite.unop X) 𝟙

protected instance obj.category_theory.limits.has_colimit {C : Type v} [small_category C] (X : Cᵒᵖ) : limits.has_colimit (functor.obj coyoneda X) :=
  limits.has_colimit.mk (limits.colimit_cocone.mk (colimit_cocone X) (colimit_cocone_is_colimit X))

/--
The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
def colimit_coyoneda_iso {C : Type v} [small_category C] (X : Cᵒᵖ) : limits.colimit (functor.obj coyoneda X) ≅ PUnit :=
  limits.colimit.iso_colimit_cocone (limits.colimit_cocone.mk (colimit_cocone X) (colimit_cocone_is_colimit X))

end coyoneda


/-- The yoneda embedding `yoneda.obj X : Cᵒᵖ ⥤ Type v` for `X : C` preserves limits. -/
protected instance yoneda_preserves_limits {C : Type u} [category C] (X : C) : limits.preserves_limits (functor.obj yoneda X) :=
  limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      limits.preserves_limits_of_shape.mk
        fun (K : J ⥤ (Cᵒᵖ)) =>
          limits.preserves_limit.mk
            fun (c : limits.cone K) (t : limits.is_limit c) =>
              limits.is_limit.mk
                fun (s : limits.cone (K ⋙ functor.obj yoneda X)) (x : limits.cone.X s) =>
                  has_hom.hom.unop
                    (limits.is_limit.lift t
                      (limits.cone.mk (opposite.op X)
                        (nat_trans.mk fun (j : J) => has_hom.hom.op (nat_trans.app (limits.cone.π s) j x))))

/-- The coyoneda embedding `coyoneda.obj X : C ⥤ Type v` for `X : Cᵒᵖ` preserves limits. -/
protected instance coyoneda_preserves_limits {C : Type u} [category C] (X : Cᵒᵖ) : limits.preserves_limits (functor.obj coyoneda X) :=
  limits.preserves_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      limits.preserves_limits_of_shape.mk
        fun (K : J ⥤ C) =>
          limits.preserves_limit.mk
            fun (c : limits.cone K) (t : limits.is_limit c) =>
              limits.is_limit.mk
                fun (s : limits.cone (K ⋙ functor.obj coyoneda X)) (x : limits.cone.X s) =>
                  limits.is_limit.lift t
                    (limits.cone.mk (opposite.unop X) (nat_trans.mk fun (j : J) => nat_trans.app (limits.cone.π s) j x))

/-- The yoneda embeddings jointly reflect limits. -/
def yoneda_jointly_reflects_limits {C : Type u} [category C] (J : Type v) [small_category J] (K : J ⥤ (Cᵒᵖ)) (c : limits.cone K) (t : (X : C) → limits.is_limit (functor.map_cone (functor.obj yoneda X) c)) : limits.is_limit c :=
  let s' : (s : limits.cone K) → limits.cone (K ⋙ functor.obj yoneda (opposite.unop (limits.cone.X s))) :=
    fun (s : limits.cone K) =>
      limits.cone.mk PUnit
        (nat_trans.mk
          fun (j : J) (_x : functor.obj (functor.obj (functor.const J) PUnit) j) =>
            has_hom.hom.unop (nat_trans.app (limits.cone.π s) j));
  limits.is_limit.mk
    fun (s : limits.cone K) =>
      has_hom.hom.op (limits.is_limit.lift (t (opposite.unop (limits.cone.X s))) (s' s) PUnit.unit)

/-- The coyoneda embeddings jointly reflect limits. -/
def coyoneda_jointly_reflects_limits {C : Type u} [category C] (J : Type v) [small_category J] (K : J ⥤ C) (c : limits.cone K) (t : (X : Cᵒᵖ) → limits.is_limit (functor.map_cone (functor.obj coyoneda X) c)) : limits.is_limit c :=
  let s' : (s : limits.cone K) → limits.cone (K ⋙ functor.obj coyoneda (opposite.op (limits.cone.X s))) :=
    fun (s : limits.cone K) =>
      limits.cone.mk PUnit
        (nat_trans.mk
          fun (j : J) (_x : functor.obj (functor.obj (functor.const J) PUnit) j) => nat_trans.app (limits.cone.π s) j);
  limits.is_limit.mk fun (s : limits.cone K) => limits.is_limit.lift (t (opposite.op (limits.cone.X s))) (s' s) PUnit.unit

