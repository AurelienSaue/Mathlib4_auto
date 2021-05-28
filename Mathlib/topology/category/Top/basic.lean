/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.concrete_category.unbundled_hom
import Mathlib.topology.continuous_map
import Mathlib.topology.opens
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-- The category of topological spaces and continuous maps. -/
def Top  :=
  category_theory.bundled topological_space

namespace Top


protected instance bundled_hom : category_theory.bundled_hom continuous_map :=
  category_theory.bundled_hom.mk continuous_map.to_fun continuous_map.id continuous_map.comp

protected instance has_coe_to_sort : has_coe_to_sort Top :=
  category_theory.bundled.has_coe_to_sort

protected instance topological_space_unbundled (x : Top) : topological_space ↥x :=
  category_theory.bundled.str x

@[simp] theorem id_app (X : Top) (x : ↥X) : coe_fn 𝟙 x = x :=
  rfl

@[simp] theorem comp_app {X : Top} {Y : Top} {Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) : coe_fn (f ≫ g) x = coe_fn g (coe_fn f x) :=
  rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [topological_space X] : Top :=
  category_theory.bundled.mk X

protected instance topological_space (X : Top) : topological_space ↥X :=
  category_theory.bundled.str X

@[simp] theorem coe_of (X : Type u) [topological_space X] : ↥(of X) = X :=
  rfl

protected instance inhabited : Inhabited Top :=
  { default := of empty }

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ Top :=
  category_theory.functor.mk (fun (X : Type u) => category_theory.bundled.mk X)
    fun (X Y : Type u) (f : X ⟶ Y) => continuous_map.mk f

/-- The trivial topology on any type. -/
def trivial : Type u ⥤ Top :=
  category_theory.functor.mk (fun (X : Type u) => category_theory.bundled.mk X)
    fun (X Y : Type u) (f : X ⟶ Y) => continuous_map.mk f

