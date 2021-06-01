/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.reflexive
import Mathlib.category_theory.limits.preserves.limits
import Mathlib.category_theory.monad.limits
import Mathlib.category_theory.monad.coequalizer
import Mathlib.PostPort

universes v₁ u₁ u₂ 

namespace Mathlib

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a right adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `category_theory.monad.monadic_of_has_preserves_reflects_G_split_coequalizers`
* `G` creates `G`-split coequalizers, see
  `category_theory.monad.monadic_of_creates_G_split_coequalizers`
  (The converse of this is also shown, see
   `category_theory.monad.creates_G_split_coequalizers_of_monadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `category_theory.monad.monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms`

## Tags

Beck, monadicity, descent

## TODO

Dualise to show comonadicity theorems.
-/

namespace category_theory


namespace monad


-- Hide the implementation details in this namespace.

namespace monadicity_internal


-- We use these parameters and notations to simplify the statements of internal constructions

-- here.

/--
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
protected instance main_pair_reflexive {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G] (A : algebra (left_adjoint G ⋙ G)) :
    is_reflexive_pair (functor.map (left_adjoint G) (algebra.a A))
        (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
          (functor.obj (left_adjoint G) (algebra.A A))) :=
  sorry

/--
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
protected instance main_pair_G_split {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G] (A : algebra (left_adjoint G ⋙ G)) :
    functor.is_split_pair G (functor.map (left_adjoint G) (algebra.a A))
        (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
          (functor.obj (left_adjoint G) (algebra.A A))) :=
  has_split_coequalizer.mk
    (Exists.intro (algebra.A A)
      (Exists.intro (algebra.a A) (Nonempty.intro (beck_split_coequalizer A))))

/-- The object function for the left adjoint to the comparison functor. -/
def comparison_left_adjoint_obj {C : Type u₁} {D : Type u₂} [category C] [category D] {G : D ⥤ C}
    [is_right_adjoint G] (A : algebra (left_adjoint G ⋙ G))
    [limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
        (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
          (functor.obj (left_adjoint G) (algebra.A A)))] :
    D :=
  limits.coequalizer (functor.map (left_adjoint G) (algebra.a A))
    (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
      (functor.obj (left_adjoint G) (algebra.A A)))

/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
def comparison_left_adjoint_hom_equiv {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G] (A : algebra (left_adjoint G ⋙ G)) (B : D)
    [limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
        (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
          (functor.obj (left_adjoint G) (algebra.A A)))] :
    (comparison_left_adjoint_obj A ⟶ B) ≃ (A ⟶ functor.obj (comparison G) B) :=
  equiv.trans
    (equiv.trans
      (limits.cofork.is_colimit.hom_iso
        (limits.colimit.is_colimit
          (limits.parallel_pair (functor.map (left_adjoint G) (algebra.a A))
            (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
              (functor.obj (left_adjoint G) (algebra.A A)))))
        B)
      (equiv.subtype_congr (adjunction.hom_equiv (adjunction.of_right_adjoint G) (algebra.A A) B)
        sorry))
    (equiv.mk
      (fun
        (g :
        Subtype
          fun (g : algebra.A A ⟶ functor.obj G B) =>
            functor.map G (functor.map (left_adjoint G) g) ≫
                functor.map G
                  (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G)) B) =
              algebra.a A ≫ g) =>
        algebra.hom.mk ↑g)
      (fun (f : A ⟶ functor.obj (comparison G) B) => { val := algebra.hom.f f, property := sorry })
      sorry sorry)

/--
Construct the adjunction to the comparison functor.
-/
def left_adjoint_comparison {C : Type u₁} {D : Type u₂} [category C] [category D] {G : D ⥤ C}
    [is_right_adjoint G]
    [∀ (A : algebra (left_adjoint G ⋙ G)),
        limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (algebra.A A)))] :
    algebra (left_adjoint G ⋙ G) ⥤ D :=
  adjunction.left_adjoint_of_equiv
    (fun (A : algebra (left_adjoint G ⋙ G)) (B : D) => comparison_left_adjoint_hom_equiv A B) sorry

/--
Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
def comparison_adjunction {C : Type u₁} {D : Type u₂} [category C] [category D] {G : D ⥤ C}
    [is_right_adjoint G]
    [∀ (A : algebra (left_adjoint G ⋙ G)),
        limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (algebra.A A)))] :
    left_adjoint_comparison ⊣ comparison G :=
  adjunction.adjunction_of_equiv_left
    (fun (A : algebra (left_adjoint G ⋙ G)) (B : D) => comparison_left_adjoint_hom_equiv A B) sorry

theorem comparison_adjunction_unit_f_aux {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G]
    [∀ (A : algebra (left_adjoint G ⋙ G)),
        limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (algebra.A A)))]
    (A : algebra (left_adjoint G ⋙ G)) :
    algebra.hom.f (nat_trans.app (adjunction.unit comparison_adjunction) A) =
        coe_fn
          (adjunction.hom_equiv (adjunction.of_right_adjoint G) (algebra.A A)
            (limits.coequalizer (functor.map (left_adjoint G) (algebra.a A))
              (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
                (functor.obj (left_adjoint G) (algebra.A A)))))
          (limits.coequalizer.π (functor.map (left_adjoint G) (algebra.a A))
            (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
              (functor.obj (left_adjoint G) (algebra.A A)))) :=
  sorry

/--
This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simp] theorem unit_cofork_ι_app {C : Type u₁} {D : Type u₂} [category C] [category D] {G : D ⥤ C}
    [is_right_adjoint G] (A : algebra (left_adjoint G ⋙ G))
    [limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
        (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
          (functor.obj (left_adjoint G) (algebra.A A)))]
    (X : limits.walking_parallel_pair) :
    nat_trans.app (limits.cocone.ι (unit_cofork A)) X =
        limits.walking_parallel_pair.rec
          (functor.map G (functor.map (left_adjoint G) (algebra.a A)) ≫
            functor.map G
              (limits.coequalizer.π (functor.map (left_adjoint G) (algebra.a A))
                (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
                  (functor.obj (left_adjoint G) (algebra.A A)))))
          (functor.map G
            (limits.coequalizer.π (functor.map (left_adjoint G) (algebra.a A))
              (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
                (functor.obj (left_adjoint G) (algebra.A A)))))
          X :=
  sorry

theorem comparison_adjunction_unit_f {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G]
    [∀ (A : algebra (left_adjoint G ⋙ G)),
        limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (algebra.A A)))]
    (A : algebra (left_adjoint G ⋙ G)) :
    algebra.hom.f (nat_trans.app (adjunction.unit comparison_adjunction) A) =
        limits.is_colimit.desc (beck_coequalizer A) (unit_cofork A) :=
  sorry

/--
The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simp] theorem counit_cofork_ι_app {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G] (B : D) (X : limits.walking_parallel_pair) :
    nat_trans.app (limits.cocone.ι (counit_cofork B)) X =
        limits.walking_parallel_pair.rec
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
              (functor.obj (left_adjoint G) (functor.obj G B)) ≫
            nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G)) B)
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G)) B) X :=
  sorry

/-- The unit cofork is a colimit provided `G` preserves it.  -/
def unit_colimit_of_preserves_coequalizer {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G] (A : algebra (left_adjoint G ⋙ G))
    [limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
        (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
          (functor.obj (left_adjoint G) (algebra.A A)))]
    [limits.preserves_colimit
        (limits.parallel_pair (functor.map (left_adjoint G) (algebra.a A))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (algebra.A A))))
        G] :
    limits.is_colimit (unit_cofork A) :=
  limits.is_colimit_of_has_coequalizer_of_preserves_colimit G
    (functor.map (left_adjoint G) (algebra.a A))
    (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
      (functor.obj (left_adjoint G) (algebra.A A)))

/-- The counit cofork is a colimit provided `G` reflects it. -/
def counit_coequalizer_of_reflects_coequalizer {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G] (B : D)
    [limits.reflects_colimit
        (limits.parallel_pair
          (functor.map (left_adjoint G)
            (functor.map G (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G)) B)))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (functor.obj G B))))
        G] :
    limits.is_colimit (counit_cofork B) :=
  limits.is_colimit_of_is_colimit_cofork_map G (counit_cofork._proof_1 B)
    (beck_coequalizer (functor.obj (comparison G) B))

theorem comparison_adjunction_counit_app {C : Type u₁} {D : Type u₂} [category C] [category D]
    {G : D ⥤ C} [is_right_adjoint G]
    [∀ (A : algebra (left_adjoint G ⋙ G)),
        limits.has_coequalizer (functor.map (left_adjoint G) (algebra.a A))
          (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
            (functor.obj (left_adjoint G) (algebra.A A)))]
    (B : D) :
    nat_trans.app (adjunction.counit comparison_adjunction) B =
        limits.colimit.desc
          (limits.parallel_pair
            (functor.map (left_adjoint G)
              (functor.map G (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G)) B)))
            (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint G))
              (functor.obj (left_adjoint G) (functor.obj G B))))
          (counit_cofork B) :=
  sorry

end monadicity_internal


/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadic_of_creates_G_split_coequalizers`.
-/
def creates_G_split_coequalizers_of_monadic {C : Type u₁} {D : Type u₂} [category C] [category D]
    (G : D ⥤ C) [monadic_right_adjoint G] {A : D} {B : D} (f : A ⟶ B) (g : A ⟶ B)
    [functor.is_split_pair G f g] : creates_colimit (limits.parallel_pair f g) G :=
  monadic_creates_colimit_of_preserves_colimit G (limits.parallel_pair f g)

/--
To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `C` has them.
-/
def monadic_of_has_preserves_reflects_G_split_coequalizers {C : Type u₁} {D : Type u₂} [category C]
    [category D] (G : D ⥤ C) [is_right_adjoint G]
    [∀ {A B : D} (f g : A ⟶ B) [_inst_5 : functor.is_split_pair G f g], limits.has_coequalizer f g]
    [{A B : D} →
        (f g : A ⟶ B) →
          [_inst_7 : functor.is_split_pair G f g] →
            limits.preserves_colimit (limits.parallel_pair f g) G]
    [{A B : D} →
        (f g : A ⟶ B) →
          [_inst_9 : functor.is_split_pair G f g] →
            limits.reflects_colimit (limits.parallel_pair f g) G] :
    monadic_right_adjoint G :=
  sorry

/--
Beck's monadicity theorem. If `G` has a right adjoint and creates coequalizers of `G`-split pairs,
then it is monadic.
This is the converse of `creates_G_split_of_monadic`.
-/
def monadic_of_creates_G_split_coequalizers {C : Type u₁} {D : Type u₂} [category C] [category D]
    (G : D ⥤ C) [is_right_adjoint G]
    [{A B : D} →
        (f g : A ⟶ B) →
          [_inst_5 : functor.is_split_pair G f g] → creates_colimit (limits.parallel_pair f g) G] :
    monadic_right_adjoint G :=
  let _inst :
    ∀ {A B : D} (f g : A ⟶ B) [_inst_6 : functor.is_split_pair G f g],
      limits.has_colimit (limits.parallel_pair f g ⋙ G) :=
    sorry;
  monadic_of_has_preserves_reflects_G_split_coequalizers G

/--
An alternate version of Beck's monadicity theorem. If `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
def monadic_of_has_preserves_G_split_coequalizers_of_reflects_isomorphisms {C : Type u₁}
    {D : Type u₂} [category C] [category D] (G : D ⥤ C) [is_right_adjoint G]
    [reflects_isomorphisms G]
    [∀ {A B : D} (f g : A ⟶ B) [_inst_6 : functor.is_split_pair G f g], limits.has_coequalizer f g]
    [{A B : D} →
        (f g : A ⟶ B) →
          [_inst_8 : functor.is_split_pair G f g] →
            limits.preserves_colimit (limits.parallel_pair f g) G] :
    monadic_right_adjoint G :=
  monadic_of_has_preserves_reflects_G_split_coequalizers G

/--
Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadic_of_has_preserves_reflexive_coequalizers_of_reflects_isomorphisms {C : Type u₁}
    {D : Type u₂} [category C] [category D] (G : D ⥤ C) [is_right_adjoint G]
    [limits.has_reflexive_coequalizers D] [reflects_isomorphisms G]
    [{A B : D} →
        (f g : A ⟶ B) →
          [_inst_7 : is_reflexive_pair f g] →
            limits.preserves_colimit (limits.parallel_pair f g) G] :
    monadic_right_adjoint G :=
  sorry

end Mathlib