/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.concrete_category.basic
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Facts about (co)limits of functors into concrete categories
-/

namespace category_theory.limits


-- We now prove a lemma about naturality of cones over functors into bundled categories.

namespace cone


/-- Naturality of a cone over functors to a concrete category. -/
@[simp] theorem w_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] {F : J ⥤ C} (s : cone F) {j : J} {j' : J} (f : j ⟶ j') (x : ↥(X s)) : coe_fn (functor.map F f) (coe_fn (nat_trans.app (π s) j) x) = coe_fn (nat_trans.app (π s) j') x := sorry

@[simp] theorem w_forget_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] (F : J ⥤ C) (s : cone (F ⋙ forget C)) {j : J} {j' : J} (f : j ⟶ j') (x : X s) : coe_fn (functor.map F f) (nat_trans.app (π s) j x) = nat_trans.app (π s) j' x :=
  congr_fun (w s f) x

end cone


namespace cocone


/-- Naturality of a cocone over functors into a concrete category. -/
@[simp] theorem w_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] {F : J ⥤ C} (s : cocone F) {j : J} {j' : J} (f : j ⟶ j') (x : ↥(functor.obj F j)) : coe_fn (nat_trans.app (ι s) j') (coe_fn (functor.map F f) x) = coe_fn (nat_trans.app (ι s) j) x := sorry

@[simp] theorem w_forget_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] (F : J ⥤ C) (s : cocone (F ⋙ forget C)) {j : J} {j' : J} (f : j ⟶ j') (x : ↥(functor.obj F j)) : nat_trans.app (ι s) j' (coe_fn (functor.map F f) x) = nat_trans.app (ι s) j x :=
  congr_fun (w s f) x

end cocone


@[simp] theorem limit.lift_π_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] (F : J ⥤ C) [has_limit F] (s : cone F) (j : J) (x : ↥(cone.X s)) : coe_fn (limit.π F j) (coe_fn (limit.lift F s) x) = coe_fn (nat_trans.app (cone.π s) j) x := sorry

@[simp] theorem limit.w_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] (F : J ⥤ C) [has_limit F] {j : J} {j' : J} (f : j ⟶ j') (x : ↥(limit F)) : coe_fn (functor.map F f) (coe_fn (limit.π F j) x) = coe_fn (limit.π F j') x := sorry

@[simp] theorem colimit.ι_desc_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] (F : J ⥤ C) [has_colimit F] (s : cocone F) (j : J) (x : ↥(functor.obj F j)) : coe_fn (colimit.desc F s) (coe_fn (colimit.ι F j) x) = coe_fn (nat_trans.app (cocone.ι s) j) x := sorry

@[simp] theorem colimit.w_apply {J : Type v} [small_category J] {C : Type u} [category C] [concrete_category C] (F : J ⥤ C) [has_colimit F] {j : J} {j' : J} (f : j ⟶ j') (x : ↥(functor.obj F j)) : coe_fn (colimit.ι F j') (coe_fn (functor.map F f) x) = coe_fn (colimit.ι F j) x := sorry

