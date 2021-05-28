/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.closed.cartesian
import Mathlib.category_theory.limits.preserves.shapes.binary_products
import Mathlib.category_theory.adjunction.fully_faithful
import PostPort

universes v u u' l 

namespace Mathlib

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a cartesian closed functor: one which (naturally) preserves exponentials.

Define the Frobenius morphism, and show it is an isomorphism iff the exponential comparison is an
isomorphism.

## TODO
Some of the results here are true more generally for closed objects and for closed monoidal
categories, and these could be generalised.

## References
https://ncatlab.org/nlab/show/cartesian+closed+functor
https://ncatlab.org/nlab/show/Frobenius+reciprocity

## Tags
Frobenius reciprocity, cartesian closed functor

-/

namespace category_theory


/--
The Frobenius morphism for an adjunction `L ⊣ F` at `A` is given by the morphism

    L(FA ⨯ B) ⟶ LFA ⨯ LB ⟶ A ⨯ LB

natural in `B`, where the first morphism is the product comparison and the latter uses the counit
of the adjunction.

We will show that if `C` and `D` are cartesian closed, then this morphism is an isomorphism for all
`A` iff `F` is a cartesian closed functor, i.e. it preserves exponentials.
-/
def frobenius_morphism {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) {L : D ⥤ C} (h : L ⊣ F) (A : C) : functor.obj limits.prod.functor (functor.obj F A) ⋙ L ⟶ L ⋙ functor.obj limits.prod.functor A :=
  limits.prod_comparison_nat_trans L (functor.obj F A) ≫
    whisker_left L (functor.map limits.prod.functor (nat_trans.app (adjunction.counit h) A))

/--
If `F` is full and faithful and has a left adjoint `L` which preserves binary products, then the
Frobenius morphism is an isomorphism.
-/
protected instance frobenius_morphism_iso_of_preserves_binary_products {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) {L : D ⥤ C} (h : L ⊣ F) (A : C) [limits.preserves_limits_of_shape (discrete limits.walking_pair) L] [full F] [faithful F] : is_iso (frobenius_morphism F h A) :=
  nat_iso.is_iso_of_is_iso_app (frobenius_morphism F h A)

/--
The exponential comparison map.
`F` is a cartesian closed functor if this is an iso for all `A`.
-/
def exp_comparison {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (A : C) : exp A ⋙ F ⟶ F ⋙ exp (functor.obj F A) :=
  coe_fn (transfer_nat_trans (exp.adjunction A) (exp.adjunction (functor.obj F A)))
    (iso.inv (limits.prod_comparison_nat_iso F A))

theorem exp_comparison_ev {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (A : C) (B : C) : limits.prod.map 𝟙 (nat_trans.app (exp_comparison F A) B) ≫ nat_trans.app (ev (functor.obj F A)) (functor.obj F B) =
  inv (limits.prod_comparison F A (functor.obj (exp A) B)) ≫ functor.map F (nat_trans.app (ev A) B) := sorry

theorem coev_exp_comparison {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (A : C) (B : C) : functor.map F (nat_trans.app (coev A) B) ≫ nat_trans.app (exp_comparison F A) (A ⨯ B) =
  nat_trans.app (coev (functor.obj F A)) (functor.obj F B) ≫
    functor.map (exp (functor.obj F A)) (inv (limits.prod_comparison F A B)) := sorry

theorem uncurry_exp_comparison {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (A : C) (B : C) : cartesian_closed.uncurry (nat_trans.app (exp_comparison F A) B) =
  inv (limits.prod_comparison F A (functor.obj (exp A) B)) ≫ functor.map F (nat_trans.app (ev A) B) := sorry

/-- The exponential comparison map is natural in `A`. -/
theorem exp_comparison_whisker_left {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] {A : C} {A' : C} (f : A' ⟶ A) : exp_comparison F A ≫ whisker_left F (pre (functor.map F f)) = whisker_right (pre f) F ≫ exp_comparison F A' := sorry

/--
The functor `F` is cartesian closed (ie preserves exponentials) if each natural transformation
`exp_comparison F A` is an isomorphism
-/
class cartesian_closed_functor {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] 
where
  comparison_iso : (A : C) → is_iso (exp_comparison F A)

theorem frobenius_morphism_mate {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) {L : D ⥤ C} [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (h : L ⊣ F) (A : C) : coe_fn
    (transfer_nat_trans_self (adjunction.comp (functor.obj limits.prod.functor A) (exp A) h (exp.adjunction A))
      (adjunction.comp L F (exp.adjunction (functor.obj F A)) h))
    (frobenius_morphism F h A) =
  exp_comparison F A := sorry

/--
If the exponential comparison transformation (at `A`) is an isomorphism, then the Frobenius morphism
at `A` is an isomorphism.
-/
def frobenius_morphism_iso_of_exp_comparison_iso {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) {L : D ⥤ C} [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (h : L ⊣ F) (A : C) [i : is_iso (exp_comparison F A)] : is_iso (frobenius_morphism F h A) :=
  transfer_nat_trans_self_of_iso (adjunction.comp (functor.obj limits.prod.functor A) (exp A) h (exp.adjunction A))
    (adjunction.comp L F (exp.adjunction (functor.obj F A)) h) (frobenius_morphism F h A)

/--
If the Frobenius morphism at `A` is an isomorphism, then the exponential comparison transformation
(at `A`) is an isomorphism.
-/
def exp_comparison_iso_of_frobenius_morphism_iso {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) {L : D ⥤ C} [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (h : L ⊣ F) (A : C) [i : is_iso (frobenius_morphism F h A)] : is_iso (exp_comparison F A) :=
  eq.mpr sorry
    (category_theory.transfer_nat_trans_self_iso
      (adjunction.comp (functor.obj limits.prod.functor A) (exp A) h (exp.adjunction A))
      (adjunction.comp L F (exp.adjunction (functor.obj F A)) h) (frobenius_morphism F h A))

/--
If `F` is full and faithful, and has a left adjoint which preserves binary products, then it is
cartesian closed.

TODO: Show the converse, that if `F` is cartesian closed and its left adjoint preserves binary
products, then it is full and faithful.
-/
def cartesian_closed_functor_of_left_adjoint_preserves_binary_products {C : Type u} [category C] {D : Type u'} [category D] [limits.has_finite_products C] [limits.has_finite_products D] (F : C ⥤ D) {L : D ⥤ C} [cartesian_closed C] [cartesian_closed D] [limits.preserves_limits_of_shape (discrete limits.walking_pair) F] (h : L ⊣ F) [full F] [faithful F] [limits.preserves_limits_of_shape (discrete limits.walking_pair) L] : cartesian_closed_functor F :=
  cartesian_closed_functor.mk fun (A : C) => exp_comparison_iso_of_frobenius_morphism_iso F h A

