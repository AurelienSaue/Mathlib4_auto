/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.zero
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.category_theory.abelian.basic
import Mathlib.PostPort

universes v u l 

namespace Mathlib

namespace category_theory


/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
-- This is a constructive definition, from which we can extract an inverse for `f` given `f ≠ 0`.

-- We show below that although it contains data, it is a subsingleton.

class simple {C : Type u} [category C] [limits.has_zero_morphisms C] (X : C) 
where
  mono_is_iso_equiv_nonzero : {Y : C} → (f : Y ⟶ X) → [_inst_3 : mono f] → is_iso f ≃ f ≠ 0

theorem simple.ext {C : Type u} [category C] [limits.has_zero_morphisms C] {X : C} {a : simple X} {b : simple X} : a = b := sorry

protected instance subsingleton_simple {C : Type u} [category C] [limits.has_zero_morphisms C] (X : C) : subsingleton (simple X) :=
  subsingleton.intro simple.ext

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
def is_iso_of_mono_of_nonzero {C : Type u} [category C] [limits.has_zero_morphisms C] {X : C} {Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : f ≠ 0) : is_iso f :=
  coe_fn (equiv.symm (simple.mono_is_iso_equiv_nonzero f)) w

theorem kernel_zero_of_nonzero_from_simple {C : Type u} [category C] [limits.has_zero_morphisms C] {X : C} {Y : C} [simple X] {f : X ⟶ Y} [limits.has_kernel f] (w : f ≠ 0) : limits.kernel.ι f = 0 :=
  decidable.by_contradiction fun (h : ¬limits.kernel.ι f = 0) => w (limits.eq_zero_of_epi_kernel f)

theorem mono_to_simple_zero_of_not_iso {C : Type u} [category C] [limits.has_zero_morphisms C] {X : C} {Y : C} [simple Y] {f : X ⟶ Y} [mono f] (w : is_iso f → False) : f = 0 :=
  decidable.by_contradiction fun (h : ¬f = 0) => w (is_iso_of_mono_of_nonzero h)

theorem id_nonzero {C : Type u} [category C] [limits.has_zero_morphisms C] (X : C) [simple X] : 𝟙 ≠ 0 :=
  coe_fn (simple.mono_is_iso_equiv_nonzero 𝟙) (is_iso.id X)

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
theorem zero_not_simple {C : Type u} [category C] [limits.has_zero_morphisms C] [limits.has_zero_object C] [simple 0] : False :=
  coe_fn (simple.mono_is_iso_equiv_nonzero 0) (is_iso.mk 0) rfl

-- We next make the dual arguments, but for this we must be in an abelian category.

/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
def simple_of_cosimple {C : Type u} [category C] [abelian C] (X : C) (h : {Z : C} → (f : X ⟶ Z) → [_inst_3 : epi f] → is_iso f ≃ f ≠ 0) : simple X :=
  simple.mk
    fun (Y : C) (f : Y ⟶ X) (I : mono f) =>
      equiv_of_subsingleton_of_subsingleton sorry fun (hf : f ≠ 0) => abelian.is_iso_of_mono_of_epi f

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
def is_iso_of_epi_of_nonzero {C : Type u} [category C] [abelian C] {X : C} {Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : f ≠ 0) : is_iso f :=
  abelian.is_iso_of_mono_of_epi f

theorem cokernel_zero_of_nonzero_to_simple {C : Type u} [category C] [abelian C] {X : C} {Y : C} [simple Y] {f : X ⟶ Y} [limits.has_cokernel f] (w : f ≠ 0) : limits.cokernel.π f = 0 :=
  decidable.by_contradiction fun (h : ¬limits.cokernel.π f = 0) => w (limits.eq_zero_of_mono_cokernel f)

theorem epi_from_simple_zero_of_not_iso {C : Type u} [category C] [abelian C] {X : C} {Y : C} [simple X] {f : X ⟶ Y} [epi f] (w : is_iso f → False) : f = 0 :=
  decidable.by_contradiction fun (h : ¬f = 0) => w (is_iso_of_epi_of_nonzero h)

