/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.sheaves.sheaf
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.category_theory.category.pairwise
import PostPort

universes v u 

namespace Mathlib

/-!
# Equivalent formulations of the sheaf condition

We give an equivalent formulation of the sheaf condition.

Given any indexed type `ι`, we define `overlap ι`,
a category with objects corresponding to
* individual open sets, `single i`, and
* intersections of pairs of open sets, `pair i j`,
with morphisms from `pair i j` to both `single i` and `single j`.

Any open cover `U : ι → opens X` provides a functor `diagram U : overlap ι ⥤ (opens X)ᵒᵖ`.

There is a canonical cone over this functor, `cone U`, whose cone point is `supr U`,
and in fact this is a limit cone.

A presheaf `F : presheaf C X` is a sheaf precisely if it preserves this limit.
We express this in two equivalent ways, as
* `is_limit (F.map_cone (cone U))`, or
* `preserves_limit (diagram U) F`
-/

namespace Top.presheaf


/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`sheaf_condition_equiv_sheaf_condition_pairwise_intersections`).

A presheaf is a sheaf if `F` sends the cone `(pairwise.cocone U).op` to a limit cone.
(Recall `pairwise.cocone U`, has cone point `supr U`, mapping down to the `U i` and the `U i ⊓ U j`.)
-/
def sheaf_condition_pairwise_intersections {X : Top} {C : Type u} [category_theory.category C] (F : presheaf C X)  :=
  {ι : Type v} →
    (U : ι → topological_space.opens ↥X) →
      category_theory.limits.is_limit
        (category_theory.functor.map_cone F (category_theory.limits.cocone.op (category_theory.pairwise.cocone U)))

/--
An alternative formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections`).

A presheaf is a sheaf if `F` preserves the limit of `pairwise.diagram U`.
(Recall `pairwise.diagram U` is the diagram consisting of the pairwise intersections
`U i ⊓ U j` mapping into the open sets `U i`. This diagram has limit `supr U`.)
-/
def sheaf_condition_preserves_limit_pairwise_intersections {X : Top} {C : Type u} [category_theory.category C] (F : presheaf C X)  :=
  {ι : Type v} →
    (U : ι → topological_space.opens ↥X) →
      category_theory.limits.preserves_limit (category_theory.functor.op (category_theory.pairwise.diagram U)) F

/-!
The remainder of this file shows that these conditions are equivalent
to the usual sheaf condition.
-/

namespace sheaf_condition_pairwise_intersections


/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
def cone_equiv_functor_obj {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) (c : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F)) : category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
  category_theory.limits.cone.mk (category_theory.limits.cone.X c)
    (category_theory.nat_trans.mk
      fun (Z : category_theory.limits.walking_parallel_pair) =>
        category_theory.limits.walking_parallel_pair.cases_on Z
          (category_theory.limits.pi.lift
            fun (i : ι) =>
              category_theory.nat_trans.app (category_theory.limits.cone.π c)
                (opposite.op (category_theory.pairwise.single i)))
          (category_theory.limits.pi.lift
            fun (b : ι × ι) =>
              category_theory.nat_trans.app (category_theory.limits.cone.π c)
                (opposite.op (category_theory.pairwise.pair (prod.fst b) (prod.snd b)))))

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
def cone_equiv_functor {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F) ⥤
  category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U) :=
  category_theory.functor.mk
    (fun (c : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F)) =>
      cone_equiv_functor_obj F U c)
    fun (c c' : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F))
      (f : c ⟶ c') => category_theory.limits.cone_morphism.mk (category_theory.limits.cone_morphism.hom f)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simp] theorem cone_equiv_inverse_obj_π_app {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) (c : category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U)) (x : category_theory.pairwise ιᵒᵖ) : category_theory.nat_trans.app (category_theory.limits.cone.π (cone_equiv_inverse_obj F U c)) x =
  opposite.op_induction
    (fun (x : category_theory.pairwise ι) =>
      category_theory.pairwise.cases_on x
        (fun (i : ι) =>
          category_theory.nat_trans.app (category_theory.limits.cone.π c)
              category_theory.limits.walking_parallel_pair.zero ≫
            category_theory.limits.pi.π (fun (i : ι) => category_theory.functor.obj F (opposite.op (U i))) i)
        fun (i j : ι) =>
          category_theory.nat_trans.app (category_theory.limits.cone.π c)
              category_theory.limits.walking_parallel_pair.one ≫
            category_theory.limits.pi.π
              (fun (p : ι × ι) => category_theory.functor.obj F (opposite.op (U (prod.fst p) ⊓ U (prod.snd p)))) (i, j))
    x :=
  Eq.refl (category_theory.nat_trans.app (category_theory.limits.cone.π (cone_equiv_inverse_obj F U c)) x)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simp] theorem cone_equiv_inverse_map_hom {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) (c : category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U)) (c' : category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U)) (f : c ⟶ c') : category_theory.limits.cone_morphism.hom (category_theory.functor.map (cone_equiv_inverse F U) f) =
  category_theory.limits.cone_morphism.hom f :=
  Eq.refl (category_theory.limits.cone_morphism.hom (category_theory.functor.map (cone_equiv_inverse F U) f))

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
def cone_equiv_unit_iso_app {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) (c : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F)) : category_theory.functor.obj 𝟭 c ≅ category_theory.functor.obj (cone_equiv_functor F U ⋙ cone_equiv_inverse F U) c :=
  category_theory.iso.mk (category_theory.limits.cone_morphism.mk 𝟙) (category_theory.limits.cone_morphism.mk 𝟙)

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simp] theorem cone_equiv_unit_iso_hom_app_hom {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : ∀ (X_1 : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F)),
  category_theory.limits.cone_morphism.hom
      (category_theory.nat_trans.app (category_theory.iso.hom (cone_equiv_unit_iso F U)) X_1) =
    𝟙 :=
  fun (X_1 : category_theory.limits.cone (category_theory.functor.op (category_theory.pairwise.diagram U) ⋙ F)) =>
    Eq.refl 𝟙

/-- Implementation of `sheaf_condition_pairwise_intersections.cone_equiv`. -/
@[simp] theorem cone_equiv_counit_iso_hom_app_hom {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : ∀ (X_1 : category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U)),
  category_theory.limits.cone_morphism.hom
      (category_theory.nat_trans.app (category_theory.iso.hom (cone_equiv_counit_iso F U)) X_1) =
    𝟙 :=
  fun (X_1 : category_theory.limits.cone (sheaf_condition_equalizer_products.diagram F U)) => Eq.refl 𝟙

/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simp] theorem cone_equiv_functor_2 {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.equivalence.functor (cone_equiv F U) = cone_equiv_functor F U :=
  Eq.refl (category_theory.equivalence.functor (cone_equiv F U))

/--
If `sheaf_condition_equalizer_products.fork` is an equalizer,
then `F.map_cone (cone U)` is a limit cone.
-/
def is_limit_map_cone_of_is_limit_sheaf_condition_fork {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) (P : category_theory.limits.is_limit (sheaf_condition_equalizer_products.fork F U)) : category_theory.limits.is_limit
  (category_theory.functor.map_cone F (category_theory.limits.cocone.op (category_theory.pairwise.cocone U))) :=
  category_theory.limits.is_limit.of_iso_limit
    (coe_fn
      (equiv.symm (category_theory.limits.is_limit.of_cone_equiv (category_theory.equivalence.symm (cone_equiv F U)))) P)
    (category_theory.iso.mk (category_theory.limits.cone_morphism.mk 𝟙) (category_theory.limits.cone_morphism.mk 𝟙))

/--
If `F.map_cone (cone U)` is a limit cone,
then `sheaf_condition_equalizer_products.fork` is an equalizer.
-/
def is_limit_sheaf_condition_fork_of_is_limit_map_cone {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) (Q : category_theory.limits.is_limit
  (category_theory.functor.map_cone F (category_theory.limits.cocone.op (category_theory.pairwise.cocone U)))) : category_theory.limits.is_limit (sheaf_condition_equalizer_products.fork F U) :=
  category_theory.limits.is_limit.of_iso_limit
    (coe_fn (equiv.symm (category_theory.limits.is_limit.of_cone_equiv (cone_equiv F U))) Q)
    (category_theory.iso.mk (category_theory.limits.cone_morphism.mk 𝟙) (category_theory.limits.cone_morphism.mk 𝟙))

end sheaf_condition_pairwise_intersections


/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of a limit diagram over `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_equiv_sheaf_condition_pairwise_intersections {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) : sheaf_condition F ≃ sheaf_condition_pairwise_intersections F :=
  equiv.Pi_congr_right
    fun (i : Type v) =>
      equiv.Pi_congr_right
        fun (U : i → topological_space.opens ↥X) =>
          equiv_of_subsingleton_of_subsingleton
            (sheaf_condition_pairwise_intersections.is_limit_map_cone_of_is_limit_sheaf_condition_fork F U)
            (sheaf_condition_pairwise_intersections.is_limit_sheaf_condition_fork_of_is_limit_map_cone F U)

/--
The sheaf condition in terms of an equalizer diagram is equivalent
to the reformulation in terms of the presheaf preserving the limit of the diagram
consisting of the `U i` and `U i ⊓ U j`.
-/
def sheaf_condition_equiv_sheaf_condition_preserves_limit_pairwise_intersections {X : Top} {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] (F : presheaf C X) : sheaf_condition F ≃ sheaf_condition_preserves_limit_pairwise_intersections F := sorry

