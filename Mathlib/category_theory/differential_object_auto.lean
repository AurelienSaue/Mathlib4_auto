/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.shift
import Mathlib.category_theory.concrete_category.default
import Mathlib.PostPort

universes v u l u_1 

namespace Mathlib

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, and zero morphisms and zero objects.
-/

namespace category_theory


/--
A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
structure differential_object (C : Type u) [category C] [limits.has_zero_morphisms C] [has_shift C]
    where
  X : C
  d : X ⟶ functor.obj (equivalence.functor (shift C ^ 1)) X
  d_squared' :
    autoParam (d ≫ functor.map (equivalence.functor (shift C ^ 1)) d = 0)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem differential_object.d_squared {C : Type u} [category C]
    [limits.has_zero_morphisms C] [has_shift C] (c : differential_object C) :
    differential_object.d c ≫
          functor.map (equivalence.functor (shift C)) (differential_object.d c) =
        0 :=
  sorry

namespace differential_object


/--
A morphism of differential objects is a morphism commuting with the differentials.
-/
structure hom {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    (X : differential_object C) (Y : differential_object C)
    where
  f : X X ⟶ X Y
  comm' :
    autoParam (d X ≫ functor.map (equivalence.functor (shift C ^ 1)) f = f ≫ d Y)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem hom.comm {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    {X : differential_object C} {Y : differential_object C} (c : hom X Y) :
    d X ≫ functor.map (equivalence.functor (shift C)) (hom.f c) = hom.f c ≫ d Y :=
  sorry

@[simp] theorem hom.comm_assoc {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    {X : differential_object C} {Y : differential_object C} (c : hom X Y) {X' : C}
    (f' : functor.obj (equivalence.functor (shift C)) (X Y) ⟶ X') :
    d X ≫ functor.map (equivalence.functor (shift C)) (hom.f c) ≫ f' = hom.f c ≫ d Y ≫ f' :=
  sorry

namespace hom


/-- The identity morphism of a differential object. -/
@[simp] theorem id_f {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    (X : differential_object C) : f (id X) = 𝟙 :=
  Eq.refl (f (id X))

/-- The composition of morphisms of differential objects. -/
@[simp] theorem comp_f {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    {X : differential_object C} {Y : differential_object C} {Z : differential_object C}
    (f : hom X Y) (g : hom Y Z) : f (comp f g) = f f ≫ f g :=
  Eq.refl (f (comp f g))

end hom


protected instance category_of_differential_objects {C : Type u} [category C]
    [limits.has_zero_morphisms C] [has_shift C] : category (differential_object C) :=
  category.mk

@[simp] theorem id_f {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    (X : differential_object C) : hom.f 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_f {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    {X : differential_object C} {Y : differential_object C} {Z : differential_object C} (f : X ⟶ Y)
    (g : Y ⟶ Z) : hom.f (f ≫ g) = hom.f f ≫ hom.f g :=
  rfl

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget (C : Type u) [category C] [limits.has_zero_morphisms C] [has_shift C] :
    differential_object C ⥤ C :=
  functor.mk (fun (X : differential_object C) => X X)
    fun (X Y : differential_object C) (f : X ⟶ Y) => hom.f f

protected instance forget_faithful (C : Type u) [category C] [limits.has_zero_morphisms C]
    [has_shift C] : faithful (forget C) :=
  faithful.mk

protected instance has_zero_morphisms (C : Type u) [category C] [limits.has_zero_morphisms C]
    [has_shift C] : limits.has_zero_morphisms (differential_object C) :=
  limits.has_zero_morphisms.mk

@[simp] theorem zero_f {C : Type u} [category C] [limits.has_zero_morphisms C] [has_shift C]
    (P : differential_object C) (Q : differential_object C) : hom.f 0 = 0 :=
  rfl

end differential_object


end category_theory


namespace category_theory


namespace differential_object


protected instance has_zero_object (C : Type u) [category C] [limits.has_zero_object C]
    [limits.has_zero_morphisms C] [has_shift C] : limits.has_zero_object (differential_object C) :=
  limits.has_zero_object.mk (mk 0 0)
    (fun (X : differential_object C) => unique.mk { default := hom.mk 0 } sorry)
    fun (X : differential_object C) => unique.mk { default := hom.mk 0 } sorry

end differential_object


namespace differential_object


protected instance concrete_category_of_differential_objects (C : Type (u + 1)) [large_category C]
    [concrete_category C] [limits.has_zero_morphisms C] [has_shift C] :
    concrete_category (differential_object C) :=
  concrete_category.mk (forget C ⋙ forget C)

protected instance category_theory.has_forget₂ (C : Type (u + 1)) [large_category C]
    [concrete_category C] [limits.has_zero_morphisms C] [has_shift C] :
    has_forget₂ (differential_object C) C :=
  has_forget₂.mk (forget C)

end Mathlib