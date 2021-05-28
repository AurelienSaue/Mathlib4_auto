/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.fully_faithful
import Mathlib.PostPort

universes v u₁ u₂ u_1 

namespace Mathlib

namespace category_theory


/- Induced categories.

  Given a category D and a function F : C → D from a type C to the
  objects of D, there is an essentially unique way to give C a
  category structure such that F becomes a fully faithful functor,
  namely by taking Hom_C(X, Y) = Hom_D(FX, FY). We call this the
  category induced from D along F.

  As a special case, if C is a subtype of D, this produces the full
  subcategory of D on the objects belonging to C. In general the
  induced category is equivalent to the full subcategory of D on the
  image of F.

-/

/-
It looks odd to make D an explicit argument of `induced_category`,
when it is determined by the argument F anyways. The reason to make D
explicit is in order to control its syntactic form, so that instances
like `induced_category.has_forget₂` (elsewhere) refer to the correct
form of D. This is used to set up several algebraic categories like

  def CommMon : Type (u+1) := induced_category Mon (bundled.map @comm_monoid.to_monoid)
  -- not `induced_category (bundled monoid) (bundled.map @comm_monoid.to_monoid)`,
  -- even though `Mon = bundled monoid`!
-/

/--
`induced_category D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
def induced_category {C : Type u₁} (D : Type u₂) [category D] (F : C → D)  :=
  C

protected instance induced_category.has_coe_to_sort {C : Type u₁} {D : Type u₂} [category D] (F : C → D) [has_coe_to_sort D] : has_coe_to_sort (induced_category D F) :=
  has_coe_to_sort.mk (has_coe_to_sort.S D) fun (c : induced_category D F) => ↥(F c)

protected instance induced_category.category {C : Type u₁} {D : Type u₂} [category D] (F : C → D) : category (induced_category D F) :=
  category.mk

/--
The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simp] theorem induced_functor_obj {C : Type u₁} {D : Type u₂} [category D] (F : C → D) : ∀ (ᾰ : C), functor.obj (induced_functor F) ᾰ = F ᾰ :=
  fun (ᾰ : C) => Eq.refl (functor.obj (induced_functor F) ᾰ)

protected instance induced_category.full {C : Type u₁} {D : Type u₂} [category D] (F : C → D) : full (induced_functor F) :=
  full.mk
    fun (x y : induced_category D F) (f : functor.obj (induced_functor F) x ⟶ functor.obj (induced_functor F) y) => f

protected instance induced_category.faithful {C : Type u₁} {D : Type u₂} [category D] (F : C → D) : faithful (induced_functor F) :=
  faithful.mk

/- A full subcategory is the special case of an induced category with F = subtype.val. -/

/--
The category structure on a subtype; morphisms just ignore the property.

See https://stacks.math.columbia.edu/tag/001D. We do not define 'strictly full' subcategories.
-/
protected instance full_subcategory {C : Type u₂} [category C] (Z : C → Prop) : category (Subtype fun (X : C) => Z X) :=
  induced_category.category subtype.val

/--
The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def full_subcategory_inclusion {C : Type u₂} [category C] (Z : C → Prop) : (Subtype fun (X : C) => Z X) ⥤ C :=
  induced_functor subtype.val

@[simp] theorem full_subcategory_inclusion.obj {C : Type u₂} [category C] (Z : C → Prop) {X : Subtype fun (X : C) => Z X} : functor.obj (full_subcategory_inclusion Z) X = subtype.val X :=
  rfl

@[simp] theorem full_subcategory_inclusion.map {C : Type u₂} [category C] (Z : C → Prop) {X : Subtype fun (X : C) => Z X} {Y : Subtype fun (X : C) => Z X} {f : X ⟶ Y} : functor.map (full_subcategory_inclusion Z) f = f :=
  rfl

protected instance full_subcategory.full {C : Type u₂} [category C] (Z : C → Prop) : full (full_subcategory_inclusion Z) :=
  induced_category.full subtype.val

protected instance full_subcategory.faithful {C : Type u₂} [category C] (Z : C → Prop) : faithful (full_subcategory_inclusion Z) :=
  induced_category.faithful subtype.val

