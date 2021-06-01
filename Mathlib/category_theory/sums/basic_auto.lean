/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.eq_to_hom
import Mathlib.PostPort

universes u₁ v₁ 

namespace Mathlib

/-#
Disjoint unions of categories, functors, and natural transformations.
-/

namespace category_theory


/--
`sum C D` gives the direct sum of two categories.
-/
protected instance sum (C : Type u₁) [category C] (D : Type u₁) [category D] : category (C ⊕ D) :=
  category.mk

@[simp] theorem sum_comp_inl (C : Type u₁) [category C] (D : Type u₁) [category D] {P : C} {Q : C}
    {R : C} (f : sum.inl P ⟶ sum.inl Q) (g : sum.inl Q ⟶ sum.inl R) : f ≫ g = f ≫ g :=
  rfl

@[simp] theorem sum_comp_inr (C : Type u₁) [category C] (D : Type u₁) [category D] {P : D} {Q : D}
    {R : D} (f : sum.inr P ⟶ sum.inr Q) (g : sum.inr Q ⟶ sum.inr R) : f ≫ g = f ≫ g :=
  rfl

namespace sum


/-- `inl_` is the functor `X ↦ inl X`. -/
-- Unfortunate naming here, suggestions welcome.

def inl_ (C : Type u₁) [category C] (D : Type u₁) [category D] : C ⥤ C ⊕ D :=
  functor.mk (fun (X : C) => sum.inl X) fun (X Y : C) (f : X ⟶ Y) => f

/-- `inr_` is the functor `X ↦ inr X`. -/
def inr_ (C : Type u₁) [category C] (D : Type u₁) [category D] : D ⥤ C ⊕ D :=
  functor.mk (fun (X : D) => sum.inr X) fun (X Y : D) (f : X ⟶ Y) => f

/-- The functor exchanging two direct summand categories. -/
def swap (C : Type u₁) [category C] (D : Type u₁) [category D] : C ⊕ D ⥤ D ⊕ C :=
  functor.mk (fun (X : C ⊕ D) => sorry) fun (X Y : C ⊕ D) (f : X ⟶ Y) => sorry

@[simp] theorem swap_obj_inl (C : Type u₁) [category C] (D : Type u₁) [category D] (X : C) :
    functor.obj (swap C D) (sum.inl X) = sum.inr X :=
  rfl

@[simp] theorem swap_obj_inr (C : Type u₁) [category C] (D : Type u₁) [category D] (X : D) :
    functor.obj (swap C D) (sum.inr X) = sum.inl X :=
  rfl

@[simp] theorem swap_map_inl (C : Type u₁) [category C] (D : Type u₁) [category D] {X : C} {Y : C}
    {f : sum.inl X ⟶ sum.inl Y} : functor.map (swap C D) f = f :=
  rfl

@[simp] theorem swap_map_inr (C : Type u₁) [category C] (D : Type u₁) [category D] {X : D} {Y : D}
    {f : sum.inr X ⟶ sum.inr Y} : functor.map (swap C D) f = f :=
  rfl

namespace swap


/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
def equivalence (C : Type u₁) [category C] (D : Type u₁) [category D] : C ⊕ D ≌ D ⊕ C :=
  equivalence.mk (swap C D) (swap D C)
    (nat_iso.of_components (fun (X : C ⊕ D) => eq_to_iso sorry) sorry)
    (nat_iso.of_components (fun (X : D ⊕ C) => eq_to_iso sorry) sorry)

protected instance is_equivalence (C : Type u₁) [category C] (D : Type u₁) [category D] :
    is_equivalence (swap C D) :=
  is_equivalence.of_equivalence (equivalence C D)

/-- The double swap on `C ⊕ D` is naturally isomorphic to the identity functor. -/
def symmetry (C : Type u₁) [category C] (D : Type u₁) [category D] : swap C D ⋙ swap D C ≅ 𝟭 :=
  iso.symm (equivalence.unit_iso (equivalence C D))

end swap


end sum


namespace functor


/-- The sum of two functors. -/
def sum {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁} [category C]
    {D : Type u₁} [category D] (F : A ⥤ B) (G : C ⥤ D) : A ⊕ C ⥤ B ⊕ D :=
  mk (fun (X : A ⊕ C) => sorry) fun (X Y : A ⊕ C) (f : X ⟶ Y) => sorry

@[simp] theorem sum_obj_inl {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁}
    [category C] {D : Type u₁} [category D] (F : A ⥤ B) (G : C ⥤ D) (a : A) :
    obj (sum F G) (sum.inl a) = sum.inl (obj F a) :=
  rfl

@[simp] theorem sum_obj_inr {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁}
    [category C] {D : Type u₁} [category D] (F : A ⥤ B) (G : C ⥤ D) (c : C) :
    obj (sum F G) (sum.inr c) = sum.inr (obj G c) :=
  rfl

@[simp] theorem sum_map_inl {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁}
    [category C] {D : Type u₁} [category D] (F : A ⥤ B) (G : C ⥤ D) {a : A} {a' : A}
    (f : sum.inl a ⟶ sum.inl a') : map (sum F G) f = map F f :=
  rfl

@[simp] theorem sum_map_inr {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁}
    [category C] {D : Type u₁} [category D] (F : A ⥤ B) (G : C ⥤ D) {c : C} {c' : C}
    (f : sum.inr c ⟶ sum.inr c') : map (sum F G) f = map G f :=
  rfl

end functor


namespace nat_trans


/-- The sum of two natural transformations. -/
def sum {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁} [category C]
    {D : Type u₁} [category D] {F : A ⥤ B} {G : A ⥤ B} {H : C ⥤ D} {I : C ⥤ D} (α : F ⟶ G)
    (β : H ⟶ I) : functor.sum F H ⟶ functor.sum G I :=
  mk fun (X : A ⊕ C) => sorry

@[simp] theorem sum_app_inl {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁}
    [category C] {D : Type u₁} [category D] {F : A ⥤ B} {G : A ⥤ B} {H : C ⥤ D} {I : C ⥤ D}
    (α : F ⟶ G) (β : H ⟶ I) (a : A) : app (sum α β) (sum.inl a) = app α a :=
  rfl

@[simp] theorem sum_app_inr {A : Type u₁} [category A] {B : Type u₁} [category B] {C : Type u₁}
    [category C] {D : Type u₁} [category D] {F : A ⥤ B} {G : A ⥤ B} {H : C ⥤ D} {I : C ⥤ D}
    (α : F ⟶ G) (β : H ⟶ I) (c : C) : app (sum α β) (sum.inr c) = app β c :=
  rfl

end Mathlib