/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.sheaf_condition.equalizer_products
import Mathlib.category_theory.full_subcategory
import Mathlib.PostPort

universes u v l 

namespace Mathlib

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category with products.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i ⊓ U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.

## Equivalent conditions

While the "official" definition is in terms of an equalizer diagram,
in `src/topology/sheaves/sheaf_condition/pairwise_intersections.lean`
and in `src/topology/sheaves/sheaf_condition/open_le_cover.lean`
we provide two equivalent conditions (and prove they are equivalent).

The first is that `F.obj U` is the limit point of the diagram consisting of all the `F.obj (U i)`
and `F.obj (U i ⊓ U j)`.
(That is, we explode the equalizer of two products out into its component pieces.)

The second is that `F.obj U` is the limit point of the diagram constisting of all the `F.obj V`,
for those `V : opens X` such that `V ≤ U i` for some `i`.
(This condition is particularly easy to state, and perhaps should become the "official" definition.)

-/

namespace Top


namespace presheaf


/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
-- One might prefer to work with sets of opens, rather than indexed families,

-- which would reduce the universe level here to `max u v`.

-- However as it's a subsingleton the universe level doesn't matter much.

def sheaf_condition {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X)  :=
  {ι : Type v} →
    (U : ι → topological_space.opens ↥X) → category_theory.limits.is_limit (sheaf_condition_equalizer_products.fork F U)

/--
The presheaf valued in `punit` over any topological space is a sheaf.
-/
def sheaf_condition_punit {X : Top} (F : presheaf (category_theory.discrete PUnit) X) : sheaf_condition F :=
  fun (ι : Type v) (U : ι → topological_space.opens ↥X) => category_theory.limits.punit_cone_is_limit

-- Let's construct a trivial example, to keep the inhabited linter happy.

protected instance sheaf_condition_inhabited {X : Top} (F : presheaf (category_theory.discrete PUnit) X) : Inhabited (sheaf_condition F) :=
  { default := sheaf_condition_punit F }

/--
Transfer the sheaf condition across an isomorphism of presheaves.
-/
def sheaf_condition_equiv_of_iso {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {G : presheaf C X} (α : F ≅ G) : sheaf_condition F ≃ sheaf_condition G := sorry

end presheaf


/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
structure sheaf (C : Type u) [category_theory.category C] [category_theory.limits.has_products C] (X : Top) 
where
  presheaf : presheaf C X
  sheaf_condition : presheaf.sheaf_condition presheaf

protected instance sheaf.category_theory.category (C : Type u) [category_theory.category C] [category_theory.limits.has_products C] (X : Top) : category_theory.category (sheaf C X) :=
  category_theory.induced_category.category sheaf.presheaf

-- Let's construct a trivial example, to keep the inhabited linter happy.

protected instance sheaf_inhabited (X : Top) : Inhabited (sheaf (category_theory.discrete PUnit) X) :=
  { default := sheaf.mk (category_theory.functor.star (topological_space.opens ↥Xᵒᵖ)) Inhabited.default }

namespace sheaf


/--
The forgetful functor from sheaves to presheaves.
-/
def forget (C : Type u) [category_theory.category C] [category_theory.limits.has_products C] (X : Top) : sheaf C X ⥤ presheaf C X :=
  category_theory.induced_functor presheaf

