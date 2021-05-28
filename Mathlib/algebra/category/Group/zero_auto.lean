/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.category.Group.basic
import Mathlib.category_theory.limits.shapes.zero
import PostPort

universes u_1 

namespace Mathlib

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/

namespace Group


protected instance Mathlib.AddGroup.has_zero_object : category_theory.limits.has_zero_object AddGroup :=
  category_theory.limits.has_zero_object.mk 0 (fun (X : AddGroup) => unique.mk { default := 0 } sorry)
    fun (X : AddGroup) => unique.mk { default := 0 } sorry

end Group


namespace CommGroup


protected instance Mathlib.AddCommGroup.has_zero_object : category_theory.limits.has_zero_object AddCommGroup :=
  category_theory.limits.has_zero_object.mk 0 (fun (X : AddCommGroup) => unique.mk { default := 0 } sorry)
    fun (X : AddCommGroup) => unique.mk { default := 0 } sorry

