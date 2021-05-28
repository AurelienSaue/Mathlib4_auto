/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.concrete_category.default
import Mathlib.category_theory.discrete_category
import Mathlib.category_theory.eq_to_hom
import PostPort

universes v u u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Category of categories

This file contains the definition of the category `Cat` of all categories.
In this category objects are categories and
morphisms are functors between these categories.

## Implementation notes

Though `Cat` is not a concrete category, we use `bundled` to define
its carrier type.
-/

namespace category_theory


/-- Category of categories. -/
def Cat  :=
  bundled category

namespace Cat


protected instance inhabited : Inhabited Cat :=
  { default := bundled.mk (Type u) }

protected instance has_coe_to_sort : has_coe_to_sort Cat :=
  has_coe_to_sort.mk (Type u) bundled.α

protected instance str (C : Cat) : category ↥C :=
  bundled.str C

/-- Construct a bundled `Cat` from the underlying type and the typeclass. -/
def of (C : Type u) [category C] : Cat :=
  bundled.of C

/-- Category structure on `Cat` -/
protected instance category : large_category Cat :=
  category.mk

/-- Functor that gets the set of objects of a category. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Cat ⥤ Type u :=
  functor.mk (fun (C : Cat) => ↥C) fun (C D : Cat) (F : C ⟶ D) => functor.obj F

/-- Any isomorphism in `Cat` induces an equivalence of the underlying categories. -/
def equiv_of_iso {C : Cat} {D : Cat} (γ : C ≅ D) : ↥C ≌ ↥D :=
  equivalence.mk' (iso.hom γ) (iso.inv γ) (eq_to_iso sorry) (eq_to_iso (iso.inv_hom_id γ))

end Cat


/--
Embedding `Type` into `Cat` as discrete categories.

This ought to be modelled as a 2-functor!
-/
@[simp] theorem Type_to_Cat_obj (X : Type u) : functor.obj Type_to_Cat X = Cat.of (discrete X) :=
  Eq.refl (functor.obj Type_to_Cat X)

protected instance Type_to_Cat.faithful : faithful Type_to_Cat :=
  faithful.mk

protected instance Type_to_Cat.full : full Type_to_Cat :=
  full.mk
    fun (X Y : Type (max (max (max u_1 u_2 u_3 u_4) u_1 u_2 u_3) (max u_1 u_2 u_3 u_4) u_1 u_2))
      (F : functor.obj Type_to_Cat X ⟶ functor.obj Type_to_Cat Y) => functor.obj F

