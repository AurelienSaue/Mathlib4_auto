/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monoidal.of_chosen_finite_products
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.category_theory.limits.shapes.types
import PostPort

universes u 

namespace Mathlib

/-!
# The category of types is a symmetric monoidal category
-/

namespace category_theory.monoidal


protected instance types_monoidal : monoidal_category (Type u) :=
  monoidal_of_chosen_finite_products limits.types.terminal_limit_cone limits.types.binary_product_limit_cone

protected instance types_symmetric : symmetric_category (Type u) :=
  symmetric_of_chosen_finite_products limits.types.terminal_limit_cone limits.types.binary_product_limit_cone

@[simp] theorem tensor_apply {W : Type u} {X : Type u} {Y : Type u} {Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) : monoidal_category.tensor_hom f g p = (f (prod.fst p), g (prod.snd p)) :=
  rfl

@[simp] theorem left_unitor_hom_apply {X : Type u} {x : X} {p : PUnit} : iso.hom λ_ (p, x) = x :=
  rfl

@[simp] theorem left_unitor_inv_apply {X : Type u} {x : X} : iso.inv λ_ x = (PUnit.unit, x) :=
  rfl

@[simp] theorem right_unitor_hom_apply {X : Type u} {x : X} {p : PUnit} : iso.hom ρ_ (x, p) = x :=
  rfl

@[simp] theorem right_unitor_inv_apply {X : Type u} {x : X} : iso.inv ρ_ x = (x, PUnit.unit) :=
  rfl

@[simp] theorem associator_hom_apply {X : Type u} {Y : Type u} {Z : Type u} {x : X} {y : Y} {z : Z} : iso.hom α_ ((x, y), z) = (x, y, z) :=
  rfl

@[simp] theorem associator_inv_apply {X : Type u} {Y : Type u} {Z : Type u} {x : X} {y : Y} {z : Z} : iso.inv α_ (x, y, z) = ((x, y), z) :=
  rfl

@[simp] theorem braiding_hom_apply {X : Type u} {Y : Type u} {x : X} {y : Y} : iso.hom β_ (x, y) = (y, x) :=
  rfl

@[simp] theorem braiding_inv_apply {X : Type u} {Y : Type u} {x : X} {y : Y} : iso.inv β_ (y, x) = (x, y) :=
  rfl

