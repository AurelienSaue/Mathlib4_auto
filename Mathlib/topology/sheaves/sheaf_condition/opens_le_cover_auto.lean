/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.sheaves.presheaf
import Mathlib.category_theory.limits.cofinal
import Mathlib.topology.sheaves.sheaf_condition.pairwise_intersections
import PostPort

universes v u 

namespace Mathlib

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → opens X` we can form the subcategory
`{ V : opens X // ∃ i, V ≤ U i }`, which has `supr U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/

namespace Top


namespace presheaf


namespace sheaf_condition


/--
The category of open sets contained in some element of the cover.
-/
def opens_le_cover {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X)  :=
  Subtype fun (V : topological_space.opens ↥X) => ∃ (i : ι), V ≤ U i

protected instance opens_le_cover.inhabited {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) [Inhabited ι] : Inhabited (opens_le_cover U) :=
  { default := { val := ⊥, property := sorry } }

protected instance opens_le_cover.category_theory.category {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.category (opens_le_cover U) :=
  category_theory.full_subcategory fun (V : topological_space.opens ↥X) => ∃ (i : ι), V ≤ U i

namespace opens_le_cover


/--
An arbitrarily chosen index such that `V ≤ U i`.
-/
def index {X : Top} {ι : Type v} {U : ι → topological_space.opens ↥X} (V : opens_le_cover U) : ι :=
  Exists.some sorry

/--
The morphism from `V` to `U i` for some `i`.
-/
def hom_to_index {X : Top} {ι : Type v} {U : ι → topological_space.opens ↥X} (V : opens_le_cover U) : subtype.val V ⟶ U (index V) :=
  category_theory.hom_of_le sorry

end opens_le_cover


/--
`supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opens_le_cover_cocone {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.cocone
  (category_theory.full_subcategory_inclusion fun (X_1 : topological_space.opens ↥X) => ∃ (i : ι), X_1 ≤ U i) :=
  category_theory.limits.cocone.mk (supr U)
    (category_theory.nat_trans.mk
      fun (V : opens_le_cover U) =>
        opens_le_cover.hom_to_index V ≫ topological_space.opens.le_supr U (opens_le_cover.index V))

end sheaf_condition


/--
An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`sheaf_condition_equiv_sheaf_condition_opens_le_cover`).

A presheaf is a sheaf if `F` sends the cone `(opens_le_cover_cocone U).op` to a limit cone.
(Recall `opens_le_cover_cocone U`, has cone point `supr U`,
mapping down to any `V` which is contained in some `U i`.)
-/
def sheaf_condition_opens_le_cover {C : Type u} [category_theory.category C] {X : Top} (F : presheaf C X)  :=
  {ι : Type v} →
    (U : ι → topological_space.opens ↥X) →
      category_theory.limits.is_limit
        (category_theory.functor.map_cone F (category_theory.limits.cocone.op (sheaf_condition.opens_le_cover_cocone U)))

namespace sheaf_condition


/--
Implementation detail:
the object level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
@[simp] def pairwise_to_opens_le_cover_obj {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.pairwise ι → opens_le_cover U :=
  sorry

/--
Implementation detail:
the morphism level of `pairwise_to_opens_le_cover : pairwise ι ⥤ opens_le_cover U`
-/
def pairwise_to_opens_le_cover_map {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) {V : category_theory.pairwise ι} {W : category_theory.pairwise ι} : (V ⟶ W) → (pairwise_to_opens_le_cover_obj U V ⟶ pairwise_to_opens_le_cover_obj U W) :=
  sorry

/--
The category of single and double intersections of the `U i` maps into the category
of open sets below some `U i`.
-/
def pairwise_to_opens_le_cover {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.pairwise ι ⥤ opens_le_cover U :=
  category_theory.functor.mk (pairwise_to_opens_le_cover_obj U)
    fun (V W : category_theory.pairwise ι) (i : V ⟶ W) => pairwise_to_opens_le_cover_map U i

protected instance category_theory.comma.nonempty {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) (V : opens_le_cover U) : Nonempty (category_theory.comma (category_theory.functor.from_punit V) (pairwise_to_opens_le_cover U)) :=
  Nonempty.intro (category_theory.comma.mk (opens_le_cover.hom_to_index V))

/--
The diagram consisting of the `U i` and `U i ⊓ U j` is cofinal in the diagram
of all opens contained in some `U i`.
-/
-- This is a case bash: for each pair of types of objects in `pairwise ι`,

-- we have to explicitly construct a zigzag.

protected instance pairwise_to_opens_le_cover.category_theory.cofinal {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.cofinal (pairwise_to_opens_le_cover U) := sorry

/--
The diagram in `opens X` indexed by pairwise intersections from `U` is isomorphic
(in fact, equal) to the diagram factored through `opens_le_cover U`.
-/
def pairwise_diagram_iso {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.pairwise.diagram U ≅
  pairwise_to_opens_le_cover U ⋙
    category_theory.full_subcategory_inclusion fun (V : topological_space.opens ↥X) => ∃ (i : ι), V ≤ U i :=
  category_theory.iso.mk
    (category_theory.nat_trans.mk
      fun (X_1 : category_theory.pairwise ι) =>
        category_theory.pairwise.cases_on X_1 (fun (i : ι) => 𝟙) fun (i j : ι) => 𝟙)
    (category_theory.nat_trans.mk
      fun (X_1 : category_theory.pairwise ι) =>
        category_theory.pairwise.cases_on X_1 (fun (i : ι) => 𝟙) fun (i j : ι) => 𝟙)

/--
The cocone `pairwise.cocone U` with cocone point `supr U` over `pairwise.diagram U` is isomorphic
to the cocone `opens_le_cover_cocone U` (with the same cocone point)
after appropriate whiskering and postcomposition.
-/
def pairwise_cocone_iso {X : Top} {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.cocone.op (category_theory.pairwise.cocone U) ≅
  category_theory.functor.obj
    (category_theory.equivalence.functor
      (category_theory.limits.cones.postcompose_equivalence (category_theory.nat_iso.op (pairwise_diagram_iso U))))
    (category_theory.limits.cone.whisker (category_theory.functor.op (pairwise_to_opens_le_cover U))
      (category_theory.limits.cocone.op (opens_le_cover_cocone U))) :=
  category_theory.limits.cones.ext
    (category_theory.iso.refl
      (category_theory.limits.cone.X (category_theory.limits.cocone.op (category_theory.pairwise.cocone U))))
    sorry

end sheaf_condition


/--
The sheaf condition
in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`
is equivalent to the reformulation
in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections {C : Type u} [category_theory.category C] {X : Top} (F : presheaf C X) : sheaf_condition_opens_le_cover F ≃ sheaf_condition_pairwise_intersections F := sorry

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over all `{ V : opens X // ∃ i, V ≤ U i }`.
-/
def sheaf_condition_equiv_sheaf_condition_opens_le_cover {C : Type u} [category_theory.category C] {X : Top} [category_theory.limits.has_products C] (F : presheaf C X) : sheaf_condition F ≃ sheaf_condition_opens_le_cover F :=
  equiv.trans (sheaf_condition_equiv_sheaf_condition_pairwise_intersections F)
    (equiv.symm (sheaf_condition_opens_le_cover_equiv_sheaf_condition_pairwise_intersections F))

