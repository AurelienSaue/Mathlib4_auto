/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison

Facts about epimorphisms and monomorphisms.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.opposites
import PostPort

universes v₁ v₂ u₁ u₂ l 

namespace Mathlib

namespace category_theory


theorem left_adjoint_preserves_epi {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : C} {Y : C} {f : X ⟶ Y} (hf : epi f) : epi (functor.map F f) := sorry

theorem right_adjoint_preserves_mono {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X : D} {Y : D} {f : X ⟶ Y} (hf : mono f) : mono (functor.map G f) := sorry

theorem faithful_reflects_epi {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [faithful F] {X : C} {Y : C} {f : X ⟶ Y} (hf : epi (functor.map F f)) : epi f := sorry

theorem faithful_reflects_mono {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [faithful F] {X : C} {Y : C} {f : X ⟶ Y} (hf : mono (functor.map F f)) : mono f := sorry

/--
A split monomorphism is a morphism `f : X ⟶ Y` admitting a retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
class split_mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) 
where
  retraction : Y ⟶ X
  id' : autoParam (f ≫ retraction = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/--
A split epimorphism is a morphism `f : X ⟶ Y` admitting a section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
class split_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) 
where
  section_ : Y ⟶ X
  id' : autoParam (section_ ≫ f = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/-- The chosen retraction of a split monomorphism. -/
def retraction {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] : Y ⟶ X :=
  split_mono.retraction f

@[simp] theorem split_mono.id_assoc {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] {X' : C} (f' : X ⟶ X') : f ≫ retraction f ≫ f' = f' := sorry

/-- The retraction of a split monomorphism is itself a split epimorphism. -/
protected instance retraction_split_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] : split_epi (retraction f) :=
  split_epi.mk f

/-- A split mono which is epi is an iso. -/
def is_iso_of_epi_of_split_mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] [epi f] : is_iso f :=
  is_iso.mk (retraction f)

/--
The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
def section_ {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] : Y ⟶ X :=
  split_epi.section_ f

@[simp] theorem split_epi.id_assoc {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] {X' : C} (f' : Y ⟶ X') : section_ f ≫ f ≫ f' = f' := sorry

/-- The section of a split epimorphism is itself a split monomorphism. -/
protected instance section_split_mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] : split_mono (section_ f) :=
  split_mono.mk f

/-- A split epi which is mono is an iso. -/
def is_iso_of_mono_of_split_epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] [split_epi f] : is_iso f :=
  is_iso.mk (section_ f)

/-- Every iso is a split mono. -/
protected instance split_mono.of_iso {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] : split_mono f :=
  split_mono.mk (inv f)

/-- Every iso is a split epi. -/
protected instance split_epi.of_iso {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso f] : split_epi f :=
  split_epi.mk (inv f)

/-- Every split mono is a mono. -/
protected instance split_mono.mono {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] : mono f := sorry

/-- Every split epi is an epi. -/
protected instance split_epi.epi {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] : epi f :=
  epi.mk
    fun (Z : C) (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h) =>
      eq.mpr (id (Eq.refl (g = h)))
        (eq.mp
          ((fun (a a_1 : Y ⟶ Z) (e_1 : a = a_1) (ᾰ ᾰ_1 : Y ⟶ Z) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
            (section_ f ≫ f ≫ g) g (split_epi.id_assoc f g) (section_ f ≫ f ≫ h) h (split_epi.id_assoc f h))
          (section_ f ≫= w))

/-- Every split mono whose retraction is mono is an iso. -/
def is_iso.of_mono_retraction {C : Type u₁} [category C] {X : C} {Y : C} {f : X ⟶ Y} [split_mono f] [mono (retraction f)] : is_iso f :=
  is_iso.mk (retraction f)

/-- Every split epi whose section is epi is an iso. -/
def is_iso.of_epi_section {C : Type u₁} [category C] {X : C} {Y : C} {f : X ⟶ Y} [split_epi f] [epi (section_ f)] : is_iso f :=
  is_iso.mk (section_ f)

protected instance unop_mono_of_epi {C : Type u₁} [category C] {A : Cᵒᵖ} {B : Cᵒᵖ} (f : A ⟶ B) [epi f] : mono (has_hom.hom.unop f) :=
  mono.mk
    fun (Z : C) (g h : Z ⟶ opposite.unop B) (eq : g ≫ has_hom.hom.unop f = h ≫ has_hom.hom.unop f) =>
      has_hom.hom.op_inj (iff.mp (cancel_epi f) (has_hom.hom.unop_inj eq))

protected instance unop_epi_of_mono {C : Type u₁} [category C] {A : Cᵒᵖ} {B : Cᵒᵖ} (f : A ⟶ B) [mono f] : epi (has_hom.hom.unop f) :=
  epi.mk
    fun (Z : C) (g h : opposite.unop A ⟶ Z) (eq : has_hom.hom.unop f ≫ g = has_hom.hom.unop f ≫ h) =>
      has_hom.hom.op_inj (iff.mp (cancel_mono f) (has_hom.hom.unop_inj eq))

protected instance op_mono_of_epi {C : Type u₁} [category C] {A : C} {B : C} (f : A ⟶ B) [epi f] : mono (has_hom.hom.op f) :=
  mono.mk
    fun (Z : Cᵒᵖ) (g h : Z ⟶ opposite.op B) (eq : g ≫ has_hom.hom.op f = h ≫ has_hom.hom.op f) =>
      has_hom.hom.unop_inj (iff.mp (cancel_epi f) (has_hom.hom.op_inj eq))

protected instance op_epi_of_mono {C : Type u₁} [category C] {A : C} {B : C} (f : A ⟶ B) [mono f] : epi (has_hom.hom.op f) :=
  epi.mk
    fun (Z : Cᵒᵖ) (g h : opposite.op A ⟶ Z) (eq : has_hom.hom.op f ≫ g = has_hom.hom.op f ≫ h) =>
      has_hom.hom.unop_inj (iff.mp (cancel_mono f) (has_hom.hom.op_inj eq))

/-- Split monomorphisms are also absolute monomorphisms. -/
protected instance functor.map.split_mono {C : Type u₁} [category C] {D : Type u₂} [category D] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] (F : C ⥤ D) : split_mono (functor.map F f) :=
  split_mono.mk (functor.map F (retraction f))

/-- Split epimorphisms are also absolute epimorphisms. -/
protected instance functor.map.split_epi {C : Type u₁} [category C] {D : Type u₂} [category D] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] (F : C ⥤ D) : split_epi (functor.map F f) :=
  split_epi.mk (functor.map F (section_ f))

