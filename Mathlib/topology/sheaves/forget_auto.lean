/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.sheaf
import Mathlib.category_theory.limits.preserves.shapes.products
import Mathlib.category_theory.limits.types
import Mathlib.PostPort

universes u₁ v u₂ 

namespace Mathlib

/-!
# Checking the sheaf condition on the underlying presheaf of types.

If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

namespace Top


namespace presheaf


namespace sheaf_condition


/--
When `G` preserves limits, the sheaf condition diagram for `F` composed with `G` is
naturally isomorphic to the sheaf condition diagram for `F ⋙ G`.
-/
def diagram_comp_preserves_limits {C : Type u₁} [category_theory.category C]
    [category_theory.limits.has_limits C] {D : Type u₂} [category_theory.category D]
    [category_theory.limits.has_limits D] (G : C ⥤ D) [category_theory.limits.preserves_limits G]
    {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) :
    sheaf_condition_equalizer_products.diagram F U ⋙ G ≅
        sheaf_condition_equalizer_products.diagram (F ⋙ G) U :=
  category_theory.nat_iso.of_components
    (fun (X_1 : category_theory.limits.walking_parallel_pair) =>
      category_theory.limits.walking_parallel_pair.cases_on X_1
        (category_theory.limits.preserves_product.iso G
          fun (i : ι) => category_theory.functor.obj F (opposite.op (U i)))
        (category_theory.limits.preserves_product.iso G
          fun (p : ι × ι) =>
            category_theory.functor.obj F (opposite.op (U (prod.fst p) ⊓ U (prod.snd p)))))
    sorry

/--
When `G` preserves limits, the image under `G` of the sheaf condition fork for `F`
is the sheaf condition fork for `F ⋙ G`,
postcomposed with the inverse of the natural isomorphism `diagram_comp_preserves_limits`.
-/
def map_cone_fork {C : Type u₁} [category_theory.category C] [category_theory.limits.has_limits C]
    {D : Type u₂} [category_theory.category D] [category_theory.limits.has_limits D] (G : C ⥤ D)
    [category_theory.limits.preserves_limits G] {X : Top} (F : presheaf C X) {ι : Type v}
    (U : ι → topological_space.opens ↥X) :
    category_theory.functor.map_cone G (sheaf_condition_equalizer_products.fork F U) ≅
        category_theory.functor.obj
          (category_theory.limits.cones.postcompose
            (category_theory.iso.inv (diagram_comp_preserves_limits G F U)))
          (sheaf_condition_equalizer_products.fork (F ⋙ G) U) :=
  category_theory.limits.cones.ext
    (category_theory.iso.refl
      (category_theory.limits.cone.X
        (category_theory.functor.map_cone G (sheaf_condition_equalizer_products.fork F U))))
    sorry

end sheaf_condition


/--
If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in both `C` and `D`),
then checking the sheaf condition for a presheaf `F : presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices to check it on the underlying sheaf of types.

Another useful example is the forgetful functor `TopCommRing ⥤ Top`.

See https://stacks.math.columbia.edu/tag/0073.
In fact we prove a stronger version with arbitrary complete target category.
-/
def sheaf_condition_equiv_sheaf_condition_comp {C : Type u₁} [category_theory.category C]
    {D : Type u₂} [category_theory.category D] (G : C ⥤ D) [category_theory.reflects_isomorphisms G]
    [category_theory.limits.has_limits C] [category_theory.limits.has_limits D]
    [category_theory.limits.preserves_limits G] {X : Top} (F : presheaf C X) :
    sheaf_condition F ≃ sheaf_condition (F ⋙ G) :=
  sorry

end Mathlib