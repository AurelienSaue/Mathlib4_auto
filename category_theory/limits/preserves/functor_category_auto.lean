/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.presheaf
import Mathlib.category_theory.limits.functor_category
import Mathlib.category_theory.limits.preserves.shapes.binary_products
import PostPort

universes u₂ v₁ v₂ 

namespace Mathlib

/-!
# Preservation of (co)limits in the functor category

Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
for `F : C ⥤ D` preserves colimits.

The idea of the proof is simply that products and colimits in the functor category are computed
pointwise, so pointwise preservation implies general preservation.

# References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/

namespace category_theory


/--
If `X × -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -` for
`F : C ⥤ D` also preserves colimits.

Note this is (mathematically) a special case of the statement that
"if limits commute with colimits in `D`, then they do as well in `C ⥤ D`"
but the story in Lean is a bit more complex, and this statement isn't directly a special case.
That is, even with a formalised proof of the general statement, there would still need to be some
work to convert to this version: namely, the natural isomorphism
`(evaluation C D).obj k ⋙ prod.functor.obj (F.obj k) ≅ prod.functor.obj F ⋙ (evaluation C D).obj k`
-/
def functor_category.prod_preserves_colimits {C : Type v₂} [category C] {D : Type u₂} [category D] [limits.has_binary_products D] [limits.has_colimits D] [(X : D) → limits.preserves_colimits (functor.obj limits.prod.functor X)] (F : C ⥤ D) : limits.preserves_colimits (functor.obj limits.prod.functor F) := sorry

