/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.over
import Mathlib.category_theory.limits.connected
import Mathlib.category_theory.limits.creates
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Connected limits in the over category

Shows that the forgetful functor `over B ⥤ C` creates connected limits, in particular `over B` has
any connected limit which `C` has.
-/

namespace category_theory.over


namespace creates_connected


/--
(Impl) Given a diagram in the over category, produce a natural transformation from the
diagram legs to the specific object.
-/
def nat_trans_in_over {J : Type v} [small_category J] {C : Type u} [category C] {B : C} (F : J ⥤ over B) : F ⋙ forget B ⟶ functor.obj (functor.const J) B :=
  nat_trans.mk fun (j : J) => comma.hom (functor.obj F j)

/--
(Impl) Given a cone in the base category, raise it to a cone in the over category. Note this is
where the connected assumption is used.
-/
@[simp] theorem raise_cone_π_app {J : Type v} [small_category J] {C : Type u} [category C] [is_connected J] {B : C} {F : J ⥤ over B} (c : limits.cone (F ⋙ forget B)) (j : J) : nat_trans.app (limits.cone.π (raise_cone c)) j = hom_mk (nat_trans.app (limits.cone.π c) j) :=
  Eq.refl (nat_trans.app (limits.cone.π (raise_cone c)) j)

theorem raised_cone_lowers_to_original {J : Type v} [small_category J] {C : Type u} [category C] [is_connected J] {B : C} {F : J ⥤ over B} (c : limits.cone (F ⋙ forget B)) (t : limits.is_limit c) : functor.map_cone (forget B) (raise_cone c) = c := sorry

/-- (Impl) Show that the raised cone is a limit. -/
def raised_cone_is_limit {J : Type v} [small_category J] {C : Type u} [category C] [is_connected J] {B : C} {F : J ⥤ over B} {c : limits.cone (F ⋙ forget B)} (t : limits.is_limit c) : limits.is_limit (raise_cone c) :=
  limits.is_limit.mk fun (s : limits.cone F) => hom_mk (limits.is_limit.lift t (functor.map_cone (forget B) s))

end creates_connected


/-- The forgetful functor from the over category creates any connected limit. -/
protected instance forget_creates_connected_limits {J : Type v} [small_category J] {C : Type u} [category C] [is_connected J] {B : C} : creates_limits_of_shape J (forget B) :=
  creates_limits_of_shape.mk
    fun (K : J ⥤ over B) =>
      creates_limit_of_reflects_iso
        fun (c : limits.cone (K ⋙ forget B)) (t : limits.is_limit c) =>
          lifts_to_limit.mk
            (liftable_cone.mk (creates_connected.raise_cone c)
              (eq_to_iso (creates_connected.raised_cone_lowers_to_original c t)))
            (creates_connected.raised_cone_is_limit t)

/-- The over category has any connected limit which the original category has. -/
protected instance has_connected_limits {J : Type v} [small_category J] {C : Type u} [category C] {B : C} [is_connected J] [limits.has_limits_of_shape J C] : limits.has_limits_of_shape J (over B) :=
  limits.has_limits_of_shape.mk fun (F : J ⥤ over B) => has_limit_of_created F (forget B)

