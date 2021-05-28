/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.single_obj
import Mathlib.PostPort

universes v u u_1 u_2 

namespace Mathlib

/-!
# Category of groupoids

This file contains the definition of the category `Groupoid` of all groupoids.
In this category objects are groupoids and morphisms are functors
between these groupoids.

We also provide two “forgetting” functors: `objects : Groupoid ⥤ Type`
and `forget_to_Cat : Groupoid ⥤ Cat`.

## Implementation notes

Though `Groupoid` is not a concrete category, we use `bundled` to define
its carrier type.
-/

namespace category_theory


/-- Category of groupoids -/
def Groupoid  :=
  bundled groupoid

namespace Groupoid


protected instance inhabited : Inhabited Groupoid :=
  { default := bundled.of (single_obj PUnit) }

protected instance str (C : Groupoid) : groupoid (bundled.α C) :=
  bundled.str C

/-- Construct a bundled `Groupoid` from the underlying type and the typeclass. -/
def of (C : Type u) [groupoid C] : Groupoid :=
  bundled.of C

/-- Category structure on `Groupoid` -/
protected instance category : large_category Groupoid :=
  category.mk

/-- Functor that gets the set of objects of a groupoid. It is not
called `forget`, because it is not a faithful functor. -/
def objects : Groupoid ⥤ Type u :=
  functor.mk bundled.α fun (C D : Groupoid) (F : C ⟶ D) => functor.obj F

/-- Forgetting functor to `Cat` -/
def forget_to_Cat : Groupoid ⥤ Cat :=
  functor.mk (fun (C : Groupoid) => Cat.of (bundled.α C)) fun (C D : Groupoid) => id

protected instance forget_to_Cat_full : full forget_to_Cat :=
  full.mk fun (C D : Groupoid) => id

protected instance forget_to_Cat_faithful : faithful forget_to_Cat :=
  faithful.mk

