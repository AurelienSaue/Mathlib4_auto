/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.reflexive
import Mathlib.category_theory.adjunction.default
import Mathlib.category_theory.monad.adjunction
import Mathlib.category_theory.monad.coequalizer
import Mathlib.PostPort

universes u₂ u₃ v₂ v₃ v₁ u₁ v₄ u₄ 

namespace Mathlib

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.
The adjoint triangle theorem says that given a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `monadic_adjoint_triangle_lift`, i.e. if `U` is monadic,
`A` has reflexive coequalizers then `R : A ⥤ B` has a left adjoint provided `R ⋙ U` does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` and `V` are monadic and `A` has reflexive coequalizers, then if `R` has a left adjoint
then `Q` has a left adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : F' ⊣ R ⋙ U`.

## TODO

Dualise to lift right adjoints through comonads (by reversing 1-cells) and dualise to lift right
adjoints through monads (by reversing 2-cells), and the combination.

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/

namespace category_theory


-- Hide implementation details in this namespace

namespace lift_adjoint


/--
To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume it's always a
coequalizer of something (i.e. a regular epi).
-/
def counit_coequalises {B : Type u₂} {C : Type u₃} [category B] [category C] {U : B ⥤ C} {F : C ⥤ B}
    (adj₁ : F ⊣ U) [(X : B) → regular_epi (nat_trans.app (adjunction.counit adj₁) X)] (X : B) :
    limits.is_colimit
        (limits.cofork.of_π (nat_trans.app (adjunction.counit adj₁) X)
          (counit_coequalises._proof_1 adj₁ X)) :=
  limits.cofork.is_colimit.mk' (limits.cofork.of_π (nat_trans.app (adjunction.counit adj₁) X) sorry)
    fun
      (s :
      limits.cofork (functor.map F (functor.map U (nat_trans.app (adjunction.counit adj₁) X)))
        (nat_trans.app (adjunction.counit adj₁) (functor.obj F (functor.obj U X)))) =>
      { val :=
          subtype.val
            (regular_epi.desc' (nat_trans.app (adjunction.counit adj₁) X) (limits.cofork.π s)
              sorry),
        property := sorry }

/--
(Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the composite

`F' U F U X ⟶ F' U F U R F U' X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a left adjoint to
`R`.
-/
def other_map {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B] [category C]
    {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A) (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U) (X : B) :
    functor.obj F' (functor.obj U (functor.obj F (functor.obj U X))) ⟶
        functor.obj F' (functor.obj U X) :=
  functor.map F'
      (functor.map U
        (functor.map F (nat_trans.app (adjunction.unit adj₂) (functor.obj U X)) ≫
          nat_trans.app (adjunction.counit adj₁)
            (functor.obj R (functor.obj F' (functor.obj U X))))) ≫
    nat_trans.app (adjunction.counit adj₂) (functor.obj F' (functor.obj U X))

/--
`(F'Uε_X, other_map X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
it has a coequalizer.
-/
protected instance other_map.category_theory.is_reflexive_pair {A : Type u₁} {B : Type u₂}
    {C : Type u₃} [category A] [category B] [category C] {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B)
    (F' : C ⥤ A) (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U) (X : B) :
    is_reflexive_pair (functor.map F' (functor.map U (nat_trans.app (adjunction.counit adj₁) X)))
        (other_map R F' adj₁ adj₂ X) :=
  sorry

/--
Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`other_map`.
-/
def construct_left_adjoint_obj {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B]
    [category C] {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A) (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)
    [limits.has_reflexive_coequalizers A] (Y : B) : A :=
  limits.coequalizer (functor.map F' (functor.map U (nat_trans.app (adjunction.counit adj₁) Y)))
    (other_map R F' adj₁ adj₂ Y)

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
def construct_left_adjoint_equiv {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B]
    [category C] {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A) (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)
    [limits.has_reflexive_coequalizers A]
    [(X : B) → regular_epi (nat_trans.app (adjunction.counit adj₁) X)] (Y : A) (X : B) :
    (construct_left_adjoint_obj R F' adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ functor.obj R Y) :=
  equiv.trans
    (equiv.trans
      (equiv.trans
        (limits.cofork.is_colimit.hom_iso
          (limits.colimit.is_colimit
            (limits.parallel_pair
              (functor.map F' (functor.map U (nat_trans.app (adjunction.counit adj₁) X)))
              (other_map R F' adj₁ adj₂ X)))
          Y)
        (equiv.subtype_congr (adjunction.hom_equiv adj₂ (functor.obj U X) Y) sorry))
      (equiv.subtype_congr
        (equiv.symm (adjunction.hom_equiv adj₁ (functor.obj U X) (functor.obj R Y))) sorry))
    (equiv.symm (limits.cofork.is_colimit.hom_iso (counit_coequalises adj₁ X) (functor.obj R Y)))

/-- Construct the left adjoint to `R`, with object map `construct_left_adjoint_obj`. -/
def construct_left_adjoint {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B]
    [category C] {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A) (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)
    [limits.has_reflexive_coequalizers A]
    [(X : B) → regular_epi (nat_trans.app (adjunction.counit adj₁) X)] : B ⥤ A :=
  adjunction.left_adjoint_of_equiv
    (fun (X : B) (Y : A) => construct_left_adjoint_equiv R F' adj₁ adj₂ Y X) sorry

end lift_adjoint


/--
The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
def adjoint_triangle_lift {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B]
    [category C] {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
    [(X : B) → regular_epi (nat_trans.app (adjunction.counit adj₁) X)]
    [limits.has_reflexive_coequalizers A] [is_right_adjoint (R ⋙ U)] : is_right_adjoint R :=
  is_right_adjoint.mk
    (lift_adjoint.construct_left_adjoint R (left_adjoint (R ⋙ U)) adj₁
      (adjunction.of_right_adjoint (R ⋙ U)))
    (adjunction.adjunction_of_equiv_left
      (fun (X : B) (Y : A) =>
        lift_adjoint.construct_left_adjoint_equiv R (left_adjoint (R ⋙ U)) adj₁
          (adjunction.of_right_adjoint (R ⋙ U)) Y X)
      sorry)

/--
If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjoint_triangle_lift` which is often more useful in practice.
-/
def monadic_adjoint_triangle_lift {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A]
    [category B] [category C] (U : B ⥤ C) [monadic_right_adjoint U] {R : A ⥤ B}
    [limits.has_reflexive_coequalizers A] [is_right_adjoint (R ⋙ U)] : is_right_adjoint R :=
  let R' : A ⥤ monad.algebra (left_adjoint U ⋙ U) := R ⋙ monad.comparison U;
  let this : is_right_adjoint (R' ⋙ functor.inv (monad.comparison U)) :=
    adjunction.right_adjoint_of_comp;
  let this_1 : R' ⋙ functor.inv (monad.comparison U) ≅ R :=
    iso_whisker_left R (functor.fun_inv_id (monad.comparison U)) ≪≫ functor.right_unitor R;
  adjunction.right_adjoint_of_nat_iso this_1

/--
Suppose we have a commutative square of functors

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` has a left adjoint such that
each component of the counit is a regular epi.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
def adjoint_square_lift {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B]
    [category C] {D : Type u₄} [category D] (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [is_right_adjoint U] [is_right_adjoint V] [is_right_adjoint R]
    [(X : B) → regular_epi (nat_trans.app (adjunction.counit (adjunction.of_right_adjoint V)) X)]
    [limits.has_reflexive_coequalizers A] : is_right_adjoint Q :=
  let this : is_right_adjoint (Q ⋙ V) := adjunction.right_adjoint_of_nat_iso comm;
  adjoint_triangle_lift Q (adjunction.of_right_adjoint V)

/--
Suppose we have a commutative square of functors

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` is monadic.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
def monadic_adjoint_square_lift {A : Type u₁} {B : Type u₂} {C : Type u₃} [category A] [category B]
    [category C] {D : Type u₄} [category D] (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
    (comm : U ⋙ R ≅ Q ⋙ V) [is_right_adjoint U] [monadic_right_adjoint V] [is_right_adjoint R]
    [limits.has_reflexive_coequalizers A] : is_right_adjoint Q :=
  let this : is_right_adjoint (Q ⋙ V) := adjunction.right_adjoint_of_nat_iso comm;
  monadic_adjoint_triangle_lift V

end Mathlib