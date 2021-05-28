/-
Copyright (c) 2019 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.groupoid
import Mathlib.control.equiv_functor
import Mathlib.category_theory.types
import PostPort

universes u₁ v₁ u₂ v₂ 

namespace Mathlib

namespace category_theory


/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
def core (C : Type u₁)  :=
  C

protected instance core_category {C : Type u₁} [category C] : groupoid (core C) :=
  groupoid.mk fun (X Y : core C) (f : X ⟶ Y) => iso.symm f

namespace core


@[simp] theorem id_hom {C : Type u₁} [category C] (X : core C) : iso.hom 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_hom {C : Type u₁} [category C] {X : core C} {Y : core C} {Z : core C} (f : X ⟶ Y) (g : Y ⟶ Z) : iso.hom (f ≫ g) = iso.hom f ≫ iso.hom g :=
  rfl

/-- The core of a category is naturally included in the category. -/
def inclusion {C : Type u₁} [category C] : core C ⥤ C :=
  functor.mk id fun (X Y : core C) (f : X ⟶ Y) => iso.hom f

/-- A functor from a groupoid to a category C factors through the core of C. -/
-- Note that this function is not functorial

-- (consider the two functors from [0] to [1], and the natural transformation between them).

def functor_to_core {C : Type u₁} [category C] {G : Type u₂} [groupoid G] (F : G ⥤ C) : G ⥤ core C :=
  functor.mk (fun (X : G) => functor.obj F X)
    fun (X Y : G) (f : X ⟶ Y) => iso.mk (functor.map F f) (functor.map F (inv f))

/--
We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `core C ⥤ C`.
-/
end core


def core.forget_functor_to_core {C : Type u₁} [category C] {G : Type u₂} [groupoid G] : (G ⥤ core C) ⥤ G ⥤ C :=
  functor.obj (whiskering_right G (core C) C) core.inclusion

/--
`of_equiv_functor m` lifts a type-level `equiv_functor`
to a categorical functor `core (Type u₁) ⥤ core (Type u₂)`.
-/
def of_equiv_functor (m : Type u₁ → Type u₂) [equiv_functor m] : core (Type u₁) ⥤ core (Type u₂) :=
  functor.mk m fun (α β : core (Type u₁)) (f : α ⟶ β) => equiv.to_iso (equiv_functor.map_equiv m (iso.to_equiv f))

