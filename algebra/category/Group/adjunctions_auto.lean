/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.category.Group.basic
import Mathlib.group_theory.free_abelian_group
import PostPort

universes u 

namespace Mathlib

/-!
The free abelian group on a type is the left adjoint of the
forgetful functor from abelian groups to types.
-/

namespace AddCommGroup


/--
The free functor `Type u ⥤ AddCommGroup` sending a type `X` to the
free abelian group with generators `x : X`.
-/
def free : Type u ⥤ AddCommGroup :=
  category_theory.functor.mk (fun (α : Type u) => of (free_abelian_group α)) fun (X Y : Type u) => free_abelian_group.map

@[simp] theorem free_obj_coe {α : Type u} : ↥(category_theory.functor.obj free α) = free_abelian_group α :=
  rfl

@[simp] theorem free_map_coe {α : Type u} {β : Type u} {f : α → β} (x : free_abelian_group α) : coe_fn (category_theory.functor.map free f) x = f <$> x :=
  rfl

/--
The free-forgetful adjunction for abelian groups.
-/
def adj : free ⊣ category_theory.forget AddCommGroup :=
  category_theory.adjunction.mk_of_hom_equiv
    (category_theory.adjunction.core_hom_equiv.mk
      fun (X : Type u) (G : AddCommGroup) => free_abelian_group.hom_equiv X ↥G)

