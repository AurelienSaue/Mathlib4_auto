/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Scott Morrison, Simon Hudon

Definition and basic properties of endomorphisms and automorphisms of an object in a category.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.groupoid
import Mathlib.data.equiv.mul_add
import PostPort

universes v u u' v' 

namespace Mathlib

namespace category_theory


/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`function.comp`, not with `category.comp`. -/
def End {C : Type u} [category_struct C] (X : C)  :=
  X ⟶ X

namespace End


protected instance has_one {C : Type u} [category_struct C] (X : C) : HasOne (End X) :=
  { one := 𝟙 }

protected instance inhabited {C : Type u} [category_struct C] (X : C) : Inhabited (End X) :=
  { default := 𝟙 }

/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
protected instance has_mul {C : Type u} [category_struct C] (X : C) : Mul (End X) :=
  { mul := fun (x y : End X) => y ≫ x }

@[simp] theorem one_def {C : Type u} [category_struct C] {X : C} : 1 = 𝟙 :=
  rfl

@[simp] theorem mul_def {C : Type u} [category_struct C] {X : C} (xs : End X) (ys : End X) : xs * ys = ys ≫ xs :=
  rfl

/-- Endomorphisms of an object form a monoid -/
protected instance monoid {C : Type u} [category C] {X : C} : monoid (End X) :=
  monoid.mk Mul.mul sorry 1 category.comp_id category.id_comp

/-- In a groupoid, endomorphisms form a group -/
protected instance group {C : Type u} [groupoid C] (X : C) : group (End X) :=
  group.mk monoid.mul sorry monoid.one sorry sorry groupoid.inv
    (div_inv_monoid.div._default monoid.mul sorry monoid.one sorry sorry groupoid.inv) groupoid.comp_inv

end End


/--
Automorphisms of an object in a category.

The order of arguments in multiplication agrees with
`function.comp`, not with `category.comp`.
-/
def Aut {C : Type u} [category C] (X : C)  :=
  X ≅ X

namespace Aut


protected instance inhabited {C : Type u} [category C] (X : C) : Inhabited (Aut X) :=
  { default := iso.refl X }

protected instance group {C : Type u} [category C] (X : C) : group (Aut X) :=
  group.mk (flip iso.trans) sorry (iso.refl X) sorry sorry iso.symm
    (div_inv_monoid.div._default (flip iso.trans) sorry (iso.refl X) sorry sorry iso.symm) sorry

/--
Units in the monoid of endomorphisms of an object
are (multiplicatively) equivalent to automorphisms of that object.
-/
def units_End_equiv_Aut {C : Type u} [category C] (X : C) : units (End X) ≃* Aut X :=
  mul_equiv.mk (fun (f : units (End X)) => iso.mk (units.val f) (units.inv f))
    (fun (f : Aut X) => units.mk (iso.hom f) (iso.inv f) (iso.inv_hom_id' f) (iso.hom_inv_id' f)) sorry sorry sorry

end Aut


namespace functor


/-- `f.map` as a monoid hom between endomorphism monoids. -/
def map_End {C : Type u} [category C] (X : C) {D : Type u'} [category D] (f : C ⥤ D) : End X →* End (obj f X) :=
  monoid_hom.mk (map f) (map_id f X) sorry

/-- `f.map_iso` as a group hom between automorphism groups. -/
def map_Aut {C : Type u} [category C] (X : C) {D : Type u'} [category D] (f : C ⥤ D) : Aut X →* Aut (obj f X) :=
  monoid_hom.mk (map_iso f) (map_iso_refl f X) sorry

