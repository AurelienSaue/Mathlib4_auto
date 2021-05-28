/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# Constructing pullbacks from binary products and equalizers

If a category as binary products and equalizers, then it has pullbacks.
Also, if a category has binary coproducts and coequalizers, then it has pushouts
-/

namespace category_theory.limits


/-- If the product `X ⨯ Y` and the equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
    pullback of `f` and `g` exists: It is given by composing the equalizer with the projections. -/
theorem has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair {C : Type u} [𝒞 : category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (pair X Y)] [has_limit (parallel_pair (prod.fst ≫ f) (prod.snd ≫ g))] : has_limit (cospan f g) := sorry

/-- If a category has all binary products and all equalizers, then it also has all pullbacks.
    As usual, this is not an instance, since there may be a more direct way to construct
    pullbacks. -/
theorem has_pullbacks_of_has_binary_products_of_has_equalizers (C : Type u) [𝒞 : category C] [has_binary_products C] [has_equalizers C] : has_pullbacks C :=
  has_limits_of_shape.mk fun (F : walking_cospan ⥤ C) => has_limit_of_iso (iso.symm (diagram_iso_cospan F))

/-- If the coproduct `Y ⨿ Z` and the coequalizer of `f ≫ ι₁` and `g ≫ ι₂` exist, then the
    pushout of `f` and `g` exists: It is given by composing the inclusions with the coequalizer. -/
theorem has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair {C : Type u} [𝒞 : category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (pair Y Z)] [has_colimit (parallel_pair (f ≫ coprod.inl) (g ≫ coprod.inr))] : has_colimit (span f g) := sorry

/-- If a category has all binary coproducts and all coequalizers, then it also has all pushouts.
    As usual, this is not an instance, since there may be a more direct way to construct
    pushouts. -/
theorem has_pushouts_of_has_binary_coproducts_of_has_coequalizers (C : Type u) [𝒞 : category C] [has_binary_coproducts C] [has_coequalizers C] : has_pushouts C :=
  has_pushouts_of_has_colimit_span C

