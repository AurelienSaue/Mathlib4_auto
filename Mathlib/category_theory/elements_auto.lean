/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.comma
import Mathlib.category_theory.groupoid
import Mathlib.category_theory.punit
import PostPort

universes w v u 

namespace Mathlib

/-!
# The category of elements

This file defines the category of elements, also known as (a special case of) the Grothendieck construction.

Given a functor `F : C ⥤ Type`, an object of `F.elements` is a pair `(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.

## Implementation notes
This construction is equivalent to a special case of a comma construction, so this is mostly just
a more convenient API. We prove the equivalence in `category_theory.category_of_elements.comma_equivalence`.

## References
* [Emily Riehl, *Category Theory in Context*, Section 2.4][riehl2017]
* <https://en.wikipedia.org/wiki/Category_of_elements>
* <https://ncatlab.org/nlab/show/category+of+elements>

## Tags
category of elements, Grothendieck construction, comma category
-/

namespace category_theory


/--
The type of objects for the category of elements of a functor `F : C ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def functor.elements {C : Type u} [category C] (F : C ⥤ Type w)  :=
  sigma fun (c : C) => functor.obj F c

/-- The category structure on `F.elements`, for `F : C ⥤ Type`.
    A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, so `F.map f` takes `x` to `y`.
 -/
protected instance category_of_elements {C : Type u} [category C] (F : C ⥤ Type w) : category (functor.elements F) :=
  category.mk

namespace category_of_elements


theorem ext {C : Type u} [category C] (F : C ⥤ Type w) {x : functor.elements F} {y : functor.elements F} (f : x ⟶ y) (g : x ⟶ y) (w : subtype.val f = subtype.val g) : f = g :=
  subtype.ext_val w

@[simp] theorem comp_val {C : Type u} [category C] {F : C ⥤ Type w} {p : functor.elements F} {q : functor.elements F} {r : functor.elements F} {f : p ⟶ q} {g : q ⟶ r} : subtype.val (f ≫ g) = subtype.val f ≫ subtype.val g :=
  rfl

@[simp] theorem id_val {C : Type u} [category C] {F : C ⥤ Type w} {p : functor.elements F} : subtype.val 𝟙 = 𝟙 :=
  rfl

end category_of_elements


protected instance groupoid_of_elements {G : Type u} [groupoid G] (F : G ⥤ Type w) : groupoid (functor.elements F) :=
  groupoid.mk fun (p q : functor.elements F) (f : p ⟶ q) => { val := inv (subtype.val f), property := sorry }

namespace category_of_elements


/-- The functor out of the category of elements which forgets the element. -/
@[simp] theorem π_map {C : Type u} [category C] (F : C ⥤ Type w) (X : functor.elements F) (Y : functor.elements F) (f : X ⟶ Y) : functor.map (π F) f = subtype.val f :=
  Eq.refl (functor.map (π F) f)

/--
A natural transformation between functors induces a functor between the categories of elements.
-/
@[simp] theorem map_obj_fst {C : Type u} [category C] {F₁ : C ⥤ Type w} {F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) (t : functor.elements F₁) : sigma.fst (functor.obj (map α) t) = sigma.fst t :=
  Eq.refl (sigma.fst (functor.obj (map α) t))

@[simp] theorem map_π {C : Type u} [category C] {F₁ : C ⥤ Type w} {F₂ : C ⥤ Type w} (α : F₁ ⟶ F₂) : map α ⋙ π F₂ = π F₁ :=
  rfl

/-- The forward direction of the equivalence `F.elements ≅ (*, F)`. -/
def to_comma {C : Type u} [category C] (F : C ⥤ Type w) : functor.elements F ⥤ comma (functor.from_punit PUnit) F :=
  functor.mk
    (fun (X : functor.elements F) => comma.mk fun (_x : functor.obj (functor.from_punit PUnit) PUnit.unit) => sigma.snd X)
    fun (X Y : functor.elements F) (f : X ⟶ Y) => comma_morphism.mk

@[simp] theorem to_comma_obj {C : Type u} [category C] (F : C ⥤ Type w) (X : functor.elements F) : functor.obj (to_comma F) X = comma.mk fun (_x : functor.obj (functor.from_punit PUnit) PUnit.unit) => sigma.snd X :=
  rfl

@[simp] theorem to_comma_map {C : Type u} [category C] (F : C ⥤ Type w) {X : functor.elements F} {Y : functor.elements F} (f : X ⟶ Y) : functor.map (to_comma F) f = comma_morphism.mk :=
  rfl

/-- The reverse direction of the equivalence `F.elements ≅ (*, F)`. -/
def from_comma {C : Type u} [category C] (F : C ⥤ Type w) : comma (functor.from_punit PUnit) F ⥤ functor.elements F :=
  functor.mk (fun (X : comma (functor.from_punit PUnit) F) => sigma.mk (comma.right X) (comma.hom X PUnit.unit))
    fun (X Y : comma (functor.from_punit PUnit) F) (f : X ⟶ Y) => { val := comma_morphism.right f, property := sorry }

@[simp] theorem from_comma_obj {C : Type u} [category C] (F : C ⥤ Type w) (X : comma (functor.from_punit PUnit) F) : functor.obj (from_comma F) X = sigma.mk (comma.right X) (comma.hom X PUnit.unit) :=
  rfl

@[simp] theorem from_comma_map {C : Type u} [category C] (F : C ⥤ Type w) {X : comma (functor.from_punit PUnit) F} {Y : comma (functor.from_punit PUnit) F} (f : X ⟶ Y) : functor.map (from_comma F) f =
  { val := comma_morphism.right f, property := congr_fun (Eq.symm (comma_morphism.w' f)) PUnit.unit } :=
  rfl

/-- The equivalence between the category of elements `F.elements`
    and the comma category `(*, F)`. -/
def comma_equivalence {C : Type u} [category C] (F : C ⥤ Type w) : functor.elements F ≌ comma (functor.from_punit PUnit) F :=
  equivalence.mk (to_comma F) (from_comma F)
    (nat_iso.of_components (fun (X : functor.elements F) => eq_to_iso sorry) sorry)
    (nat_iso.of_components (fun (X : comma (functor.from_punit PUnit) F) => iso.mk comma_morphism.mk comma_morphism.mk)
      sorry)

@[simp] theorem comma_equivalence_functor {C : Type u} [category C] (F : C ⥤ Type w) : equivalence.functor (comma_equivalence F) = to_comma F :=
  rfl

@[simp] theorem comma_equivalence_inverse {C : Type u} [category C] (F : C ⥤ Type w) : equivalence.inverse (comma_equivalence F) = from_comma F :=
  rfl

