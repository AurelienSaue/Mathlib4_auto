/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.eq_to_hom
import PostPort

universes u₁ u₂ v₁ v₂ u₃ u₄ v₃ v₄ 

namespace Mathlib

namespace category_theory


/--
`prod C D` gives the cartesian product of two categories.

See https://stacks.math.columbia.edu/tag/001K.
-/
protected instance prod (C : Type u₁) [category C] (D : Type u₂) [category D] : category (C × D) :=
  category.mk

-- rfl lemmas for category.prod

@[simp] theorem prod_id (C : Type u₁) [category C] (D : Type u₂) [category D] (X : C) (Y : D) : 𝟙 = (𝟙, 𝟙) :=
  rfl

@[simp] theorem prod_comp (C : Type u₁) [category C] (D : Type u₂) [category D] {P : C} {Q : C} {R : C} {S : D} {T : D} {U : D} (f : (P, S) ⟶ (Q, T)) (g : (Q, T) ⟶ (R, U)) : f ≫ g = (prod.fst f ≫ prod.fst g, prod.snd f ≫ prod.snd g) :=
  rfl

@[simp] theorem prod_id_fst (C : Type u₁) [category C] (D : Type u₂) [category D] (X : C × D) : prod.fst 𝟙 = 𝟙 :=
  rfl

@[simp] theorem prod_id_snd (C : Type u₁) [category C] (D : Type u₂) [category D] (X : C × D) : prod.snd 𝟙 = 𝟙 :=
  rfl

@[simp] theorem prod_comp_fst (C : Type u₁) [category C] (D : Type u₂) [category D] {X : C × D} {Y : C × D} {Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) : prod.fst (f ≫ g) = prod.fst f ≫ prod.fst g :=
  rfl

@[simp] theorem prod_comp_snd (C : Type u₁) [category C] (D : Type u₂) [category D] {X : C × D} {Y : C × D} {Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) : prod.snd (f ≫ g) = prod.snd f ≫ prod.snd g :=
  rfl

/--
`prod.category.uniform C D` is an additional instance specialised so both factors have the same
universe levels. This helps typeclass resolution.
-/
protected instance uniform_prod (C : Type u₁) [category C] (D : Type u₁) [category D] : category (C × D) :=
  category_theory.prod C D

-- Next we define the natural functors into and out of product categories. For now this doesn't

-- address the universal properties.

namespace prod


/-- `sectl C Z` is the functor `C ⥤ C × D` given by `X ↦ (X, Z)`. -/
@[simp] theorem sectl_obj (C : Type u₁) [category C] {D : Type u₂} [category D] (Z : D) (X : C) : functor.obj (sectl C Z) X = (X, Z) :=
  Eq.refl (functor.obj (sectl C Z) X)

/-- `sectr Z D` is the functor `D ⥤ C × D` given by `Y ↦ (Z, Y)` . -/
def sectr {C : Type u₁} [category C] (Z : C) (D : Type u₂) [category D] : D ⥤ C × D :=
  functor.mk (fun (X : D) => (Z, X)) fun (X Y : D) (f : X ⟶ Y) => (𝟙, f)

/-- `fst` is the functor `(X, Y) ↦ X`. -/
@[simp] theorem fst_obj (C : Type u₁) [category C] (D : Type u₂) [category D] (X : C × D) : functor.obj (fst C D) X = prod.fst X :=
  Eq.refl (functor.obj (fst C D) X)

/-- `snd` is the functor `(X, Y) ↦ Y`. -/
@[simp] theorem snd_map (C : Type u₁) [category C] (D : Type u₂) [category D] (X : C × D) (Y : C × D) (f : X ⟶ Y) : functor.map (snd C D) f = prod.snd f :=
  Eq.refl (functor.map (snd C D) f)

/-- The functor swapping the factors of a cartesian product of categories, `C × D ⥤ D × C`. -/
@[simp] theorem swap_map (C : Type u₁) [category C] (D : Type u₂) [category D] (_x : C × D) : ∀ (_x_1 : C × D) (f : _x ⟶ _x_1), functor.map (swap C D) f = (prod.snd f, prod.fst f) :=
  fun (_x_1 : C × D) (f : _x ⟶ _x_1) => Eq.refl (functor.map (swap C D) f)

/--
Swapping the factors of a cartesion product of categories twice is naturally isomorphic
to the identity functor.
-/
@[simp] theorem symmetry_hom_app (C : Type u₁) [category C] (D : Type u₂) [category D] (X : C × D) : nat_trans.app (iso.hom (symmetry C D)) X = 𝟙 :=
  Eq.refl (nat_trans.app (iso.hom (symmetry C D)) X)

/--
The equivalence, given by swapping factors, between `C × D` and `D × C`.
-/
@[simp] theorem braiding_counit_iso_inv_app (C : Type u₁) [category C] (D : Type u₂) [category D] (X : D × C) : nat_trans.app (iso.inv (equivalence.counit_iso (braiding C D))) X = inv (eq_to_hom (braiding._proof_3 C D X)) :=
  Eq.refl (inv (eq_to_hom (braiding._proof_3 C D X)))

protected instance swap_is_equivalence (C : Type u₁) [category C] (D : Type u₂) [category D] : is_equivalence (swap C D) :=
  is_equivalence.of_equivalence (braiding C D)

end prod


/--
The "evaluation at `X`" functor, such that
`(evaluation.obj X).obj F = F.obj X`,
which is functorial in both `X` and `F`.
-/
def evaluation (C : Type u₁) [category C] (D : Type u₂) [category D] : C ⥤ (C ⥤ D) ⥤ D :=
  functor.mk
    (fun (X : C) => functor.mk (fun (F : C ⥤ D) => functor.obj F X) fun (F G : C ⥤ D) (α : F ⟶ G) => nat_trans.app α X)
    fun (X Y : C) (f : X ⟶ Y) => nat_trans.mk fun (F : C ⥤ D) => functor.map F f

/--
The "evaluation of `F` at `X`" functor,
as a functor `C × (C ⥤ D) ⥤ D`.
-/
@[simp] theorem evaluation_uncurried_obj (C : Type u₁) [category C] (D : Type u₂) [category D] (p : C × (C ⥤ D)) : functor.obj (evaluation_uncurried C D) p = functor.obj (prod.snd p) (prod.fst p) :=
  Eq.refl (functor.obj (evaluation_uncurried C D) p)

namespace functor


/-- The cartesian product of two functors. -/
@[simp] theorem prod_obj {A : Type u₁} [category A] {B : Type u₂} [category B] {C : Type u₃} [category C] {D : Type u₄} [category D] (F : A ⥤ B) (G : C ⥤ D) (X : A × C) : obj (prod F G) X = (obj F (prod.fst X), obj G (prod.snd X)) :=
  Eq.refl (obj (prod F G) X)

/- Because of limitations in Lean 3's handling of notations, we do not setup a notation `F × G`.
   You can use `F.prod G` as a "poor man's infix", or just write `functor.prod F G`. -/

end functor


namespace nat_trans


/-- The cartesian product of two natural transformations. -/
@[simp] theorem prod_app {A : Type u₁} [category A] {B : Type u₂} [category B] {C : Type u₃} [category C] {D : Type u₄} [category D] {F : A ⥤ B} {G : A ⥤ B} {H : C ⥤ D} {I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (X : A × C) : app (prod α β) X = (app α (prod.fst X), app β (prod.snd X)) :=
  Eq.refl (app (prod α β) X)

