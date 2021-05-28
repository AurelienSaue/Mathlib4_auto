/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.opposites
import PostPort

universes u₂ v₂ u₁ v₁ u₃ v₃ 

namespace Mathlib

namespace category_theory.functor


/--
The functor sending `X : C` to the constant functor `J ⥤ C` sending everything to `X`.
-/
def const (J : Type u₁) [category J] {C : Type u₂} [category C] : C ⥤ J ⥤ C :=
  mk (fun (X : C) => mk (fun (j : J) => X) fun (j j' : J) (f : j ⟶ j') => 𝟙)
    fun (X Y : C) (f : X ⟶ Y) => nat_trans.mk fun (j : J) => f

namespace const


@[simp] theorem obj_obj {J : Type u₁} [category J] {C : Type u₂} [category C] (X : C) (j : J) : obj (obj (const J) X) j = X :=
  rfl

@[simp] theorem obj_map {J : Type u₁} [category J] {C : Type u₂} [category C] (X : C) {j : J} {j' : J} (f : j ⟶ j') : map (obj (const J) X) f = 𝟙 :=
  rfl

@[simp] theorem map_app {J : Type u₁} [category J] {C : Type u₂} [category C] {X : C} {Y : C} (f : X ⟶ Y) (j : J) : nat_trans.app (map (const J) f) j = f :=
  rfl

/--
The contant functor `Jᵒᵖ ⥤ Cᵒᵖ` sending everything to `op X`
is (naturally isomorphic to) the opposite of the constant functor `J ⥤ C` sending everything to `X`.
-/
def op_obj_op {J : Type u₁} [category J] {C : Type u₂} [category C] (X : C) : obj (const (Jᵒᵖ)) (opposite.op X) ≅ functor.op (obj (const J) X) :=
  iso.mk (nat_trans.mk fun (j : Jᵒᵖ) => 𝟙) (nat_trans.mk fun (j : Jᵒᵖ) => 𝟙)

@[simp] theorem op_obj_op_hom_app {J : Type u₁} [category J] {C : Type u₂} [category C] (X : C) (j : Jᵒᵖ) : nat_trans.app (iso.hom (op_obj_op X)) j = 𝟙 :=
  rfl

@[simp] theorem op_obj_op_inv_app {J : Type u₁} [category J] {C : Type u₂} [category C] (X : C) (j : Jᵒᵖ) : nat_trans.app (iso.inv (op_obj_op X)) j = 𝟙 :=
  rfl

/--
The contant functor `Jᵒᵖ ⥤ C` sending everything to `unop X`
is (naturally isomorphic to) the opposite of
the constant functor `J ⥤ Cᵒᵖ` sending everything to `X`.
-/
def op_obj_unop {J : Type u₁} [category J] {C : Type u₂} [category C] (X : Cᵒᵖ) : obj (const (Jᵒᵖ)) (opposite.unop X) ≅ functor.left_op (obj (const J) X) :=
  iso.mk (nat_trans.mk fun (j : Jᵒᵖ) => 𝟙) (nat_trans.mk fun (j : Jᵒᵖ) => 𝟙)

-- Lean needs some help with universes here.

@[simp] theorem op_obj_unop_hom_app {J : Type u₁} [category J] {C : Type u₂} [category C] (X : Cᵒᵖ) (j : Jᵒᵖ) : nat_trans.app (iso.hom (op_obj_unop X)) j = 𝟙 :=
  rfl

@[simp] theorem op_obj_unop_inv_app {J : Type u₁} [category J] {C : Type u₂} [category C] (X : Cᵒᵖ) (j : Jᵒᵖ) : nat_trans.app (iso.inv (op_obj_unop X)) j = 𝟙 :=
  rfl

@[simp] theorem unop_functor_op_obj_map {J : Type u₁} [category J] {C : Type u₂} [category C] (X : Cᵒᵖ) {j₁ : J} {j₂ : J} (f : j₁ ⟶ j₂) : map (opposite.unop (obj (functor.op (const J)) X)) f = 𝟙 :=
  rfl

end const


/-- These are actually equal, of course, but not definitionally equal
  (the equality requires F.map (𝟙 _) = 𝟙 _). A natural isomorphism is
  more convenient than an equality between functors (compare id_to_iso). -/
def const_comp (J : Type u₁) [category J] {C : Type u₂} [category C] {D : Type u₃} [category D] (X : C) (F : C ⥤ D) : obj (const J) X ⋙ F ≅ obj (const J) (obj F X) :=
  iso.mk (nat_trans.mk fun (_x : J) => 𝟙) (nat_trans.mk fun (_x : J) => 𝟙)

/-- If `J` is nonempty, then the constant functor over `J` is faithful. -/
protected instance const.category_theory.faithful (J : Type u₁) [category J] {C : Type u₂} [category C] [Nonempty J] : faithful (const J) :=
  faithful.mk

