/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.category_theory.concrete_category.basic
import PostPort

universes u u_1 

namespace Mathlib

/-!
# Facts about limits of functors into concrete categories

This file doesn't yet attempt to be exhaustive;
it just contains lemmas that are useful
while comparing categorical limits with existing constructions in concrete categories.
-/

namespace category_theory.limits


@[simp] theorem kernel_condition_apply {C : Type (u + 1)} [large_category C] [concrete_category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y) [has_kernel f] (x : ↥(kernel f)) : coe_fn f (coe_fn (kernel.ι f) x) = coe_fn 0 x := sorry

@[simp] theorem cokernel_condition_apply {C : Type (u + 1)} [large_category C] [concrete_category C] [has_zero_morphisms C] {X : C} {Y : C} (f : X ⟶ Y) [has_cokernel f] (x : ↥X) : coe_fn (cokernel.π f) (coe_fn f x) = coe_fn 0 x := sorry

