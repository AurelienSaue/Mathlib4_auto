/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.products
import Mathlib.set_theory.cardinal
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# Any small complete category is a preorder

We show that any small category which has all (small) limits is a preorder: In particular, we show
that if a small category `C` in universe `u` has products of size `u`, then for any `X Y : C`
there is at most one morphism `X ⟶ Y`.
Note that in Lean, a preorder category is strictly one where the morphisms are in `Prop`, so
we instead show that the homsets are subsingleton.

## References

* https://ncatlab.org/nlab/show/complete+small+category#in_classical_logic

## Tags

small complete, preorder, Freyd
-/

namespace category_theory


/--
A small category with products is a thin category.

in Lean, a preorder category is one where the morphisms are in Prop, which is weaker than the usual
notion of a preorder/thin category which says that each homset is subsingleton; we show the latter
rather than providing a `preorder C` instance.
-/
protected instance has_hom.hom.subsingleton {C : Type u} [small_category C] [limits.has_products C]
    {X : C} {Y : C} : subsingleton (X ⟶ Y) :=
  sorry

end Mathlib