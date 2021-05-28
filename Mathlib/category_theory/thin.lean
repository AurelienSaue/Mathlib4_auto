/-
Copyright (c) 2019 Scott Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.functor_category
import Mathlib.category_theory.isomorphism
import Mathlib.PostPort

universes u₁ v₁ v₂ u₂ 

namespace Mathlib

/-!
# Thin categories

A thin category (also known as a sparse category) is a category with at most one morphism between
each pair of objects.

Examples include posets, but also some indexing categories (diagrams) for special shapes of
(co)limits.

To construct a category instance one only needs to specify the `category_struct` part,
as the axioms hold for free.

If `C` is thin, then the category of functors to `C` is also thin.
Further, to show two objects are isomorphic in a thin category, it suffices only to give a morphism
in each direction.
-/

namespace category_theory


/-- Construct a category instance from a category_struct, using the fact that
    hom spaces are subsingletons to prove the axioms. -/
def thin_category {C : Type u₁} [category_struct C] [∀ (X Y : C), subsingleton (X ⟶ Y)] : category C :=
  category.mk

-- We don't assume anything about where the category instance on `C` came from.

-- In particular this allows `C` to be a preorder, with the category instance inherited from the

-- preorder structure.

/-- If `C` is a thin category, then `D ⥤ C` is a thin category. -/
protected instance functor_thin {C : Type u₁} [category C] {D : Type u₂} [category D] [∀ (X Y : C), subsingleton (X ⟶ Y)] (F₁ : D ⥤ C) (F₂ : D ⥤ C) : subsingleton (F₁ ⟶ F₂) :=
  subsingleton.intro
    fun (α β : F₁ ⟶ F₂) =>
      nat_trans.ext α β (funext fun (_x : D) => subsingleton.elim (nat_trans.app α _x) (nat_trans.app β _x))

/-- To show `X ≅ Y` in a thin category, it suffices to just give any morphism in each direction. -/
def iso_of_both_ways {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] {X : C} {Y : C} (f : X ⟶ Y) (g : Y ⟶ X) : X ≅ Y :=
  iso.mk f g

protected instance subsingleton_iso {C : Type u₁} [category C] [∀ (X Y : C), subsingleton (X ⟶ Y)] {X : C} {Y : C} : subsingleton (X ≅ Y) :=
  subsingleton.intro fun (i₁ i₂ : X ≅ Y) => iso.ext (subsingleton.elim (iso.hom i₁) (iso.hom i₂))

