/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.category.Cat
import Mathlib.category_theory.elements
import Mathlib.PostPort

universes u_1 u_3 u_5 u_6 l w 

namespace Mathlib

/-!
# The Grothendieck construction

Given a functor `F : C ⥤ Cat`, the objects of `grothendieck F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj c`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : (F.map β).obj f ⟶ f'`

Categories such as `PresheafedSpace` are in fact examples of this construction,
and it may be interesting to try to generalize some of the development there.

## Implementation notes

Really we should treat `Cat` as a 2-category, and allow `F` to be a 2-functor.

There is also a closely related construction starting with `G : Cᵒᵖ ⥤ Cat`,
where morphisms consists again of `β : b ⟶ b'` and `φ : f ⟶ (F.map (op β)).obj f'`.

## References

See also `category_theory.functor.elements` for the category of elements of functor `F : C ⥤ Type`.

* https://stacks.math.columbia.edu/tag/02XV
* https://ncatlab.org/nlab/show/Grothendieck+construction

-/

namespace category_theory


/--
The Grothendieck construction (often written as `∫ F` in mathematics) for a functor `F : C ⥤ Cat`
gives a category whose
* objects `X` consist of `X.base : C` and `X.fiber : F.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`
-/
structure grothendieck {C : Type u_1} [category C] (F : C ⥤ Cat) 
where
  base : C
  fiber : ↥(functor.obj F base)

namespace grothendieck


/--
A morphism in the Grothendieck category `F : C ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : (F.map base).obj X.fiber ⟶ Y.fiber`.
-/
structure hom {C : Type u_1} [category C] {F : C ⥤ Cat} (X : grothendieck F) (Y : grothendieck F) 
where
  base : base X ⟶ base Y
  fiber : functor.obj (functor.map F base) (fiber X) ⟶ fiber Y

theorem ext {C : Type u_1} [category C] {F : C ⥤ Cat} {X : grothendieck F} {Y : grothendieck F} (f : hom X Y) (g : hom X Y) (w_base : hom.base f = hom.base g) (w_fiber : eq_to_hom
      (eq.mpr
        (id
          (Eq._oldrec
            (Eq.refl
              (functor.obj (functor.map F (hom.base g)) (fiber X) = functor.obj (functor.map F (hom.base f)) (fiber X)))
            w_base))
        (Eq.refl (functor.obj (functor.map F (hom.base g)) (fiber X)))) ≫
    hom.fiber f =
  hom.fiber g) : f = g := sorry

/--
The identity morphism in the Grothendieck category.
-/
@[simp] theorem id_fiber {C : Type u_1} [category C] {F : C ⥤ Cat} (X : grothendieck F) : hom.fiber (id X) = eq_to_hom (id._proof_1 X) :=
  Eq.refl (hom.fiber (id X))

protected instance hom.inhabited {C : Type u_1} [category C] {F : C ⥤ Cat} (X : grothendieck F) : Inhabited (hom X X) :=
  { default := id X }

/--
Composition of morphisms in the Grothendieck category.
-/
@[simp] theorem comp_fiber {C : Type u_1} [category C] {F : C ⥤ Cat} {X : grothendieck F} {Y : grothendieck F} {Z : grothendieck F} (f : hom X Y) (g : hom Y Z) : hom.fiber (comp f g) =
  eq_to_hom (comp._proof_1 f g) ≫ functor.map (functor.map F (hom.base g)) (hom.fiber f) ≫ hom.fiber g :=
  Eq.refl (hom.fiber (comp f g))

protected instance category_theory.category {C : Type u_1} [category C] {F : C ⥤ Cat} : category (grothendieck F) :=
  category.mk

@[simp] theorem id_fiber' {C : Type u_1} [category C] {F : C ⥤ Cat} (X : grothendieck F) : hom.fiber 𝟙 =
  eq_to_hom
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (functor.obj (functor.map F (hom.base 𝟙)) (fiber X) = fiber X))
          (functor.map_id F (base X))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (functor.obj 𝟙 (fiber X) = fiber X)) (functor.id_obj (fiber X))))
        (Eq.refl (fiber X)))) :=
  id_fiber X

theorem congr {C : Type u_1} [category C] {F : C ⥤ Cat} {X : grothendieck F} {Y : grothendieck F} {f : X ⟶ Y} {g : X ⟶ Y} (h : f = g) : hom.fiber f = eq_to_hom (Eq._oldrec (Eq.refl (functor.obj (functor.map F (hom.base f)) (fiber X))) h) ≫ hom.fiber g := sorry

/-- The forgetful functor from `grothendieck F` to the source category. -/
def forget {C : Type u_1} [category C] (F : C ⥤ Cat) : grothendieck F ⥤ C :=
  functor.mk (fun (X : grothendieck F) => base X) fun (X Y : grothendieck F) (f : X ⟶ Y) => hom.base f

/--
The Grothendieck construction applied to a functor to `Type`
(thought of as a functor to `Cat` by realising a type as a discrete category)
is the same as the 'category of elements' construction.
-/
def grothendieck_Type_to_Cat {C : Type u_1} [category C] (G : C ⥤ Type w) : grothendieck (G ⋙ Type_to_Cat) ≌ functor.elements G := sorry

