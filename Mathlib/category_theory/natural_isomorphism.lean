/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.functor_category
import Mathlib.category_theory.isomorphism
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ u₃ v₃ 

namespace Mathlib

/-!
# Natural isomorphisms

For the most part, natural isomorphisms are just another sort of isomorphism.

We provide some special support for extracting components:
* if `α : F ≅ G`, then `a.app X : F.obj X ≅ G.obj X`,
and building natural isomorphisms from components:
*
```
nat_iso.of_components
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
F ≅ G
```
only needing to check naturality in one direction.

## Implementation

Note that `nat_iso` is a namespace without a corresponding definition;
we put some declarations that are specifically about natural isomorphisms in the `iso`
namespace so that they are available using dot notation.
-/

-- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory


namespace iso


/-- The application of a natural isomorphism to an object. We put this definition in a different
namespace, so that we can use `α.app` -/
@[simp] theorem app_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) : hom (app α X) = nat_trans.app (hom α) X :=
  Eq.refl (hom (app α X))

@[simp] theorem hom_inv_id_app_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) {X' : D} (f' : functor.obj F X ⟶ X') : nat_trans.app (hom α) X ≫ nat_trans.app (inv α) X ≫ f' = f' := sorry

@[simp] theorem inv_hom_id_app_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) {X' : D} (f' : functor.obj G X ⟶ X') : nat_trans.app (inv α) X ≫ nat_trans.app (hom α) X ≫ f' = f' := sorry

end iso


namespace nat_iso


@[simp] theorem trans_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) (X : C) : iso.app (α ≪≫ β) X = iso.app α X ≪≫ iso.app β X :=
  rfl

theorem app_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) : iso.hom (iso.app α X) = nat_trans.app (iso.hom α) X :=
  rfl

theorem app_inv {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) : iso.inv (iso.app α X) = nat_trans.app (iso.inv α) X :=
  rfl

protected instance hom_app_is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) : is_iso (nat_trans.app (iso.hom α) X) :=
  is_iso.mk (nat_trans.app (iso.inv α) X)

protected instance inv_app_is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) (X : C) : is_iso (nat_trans.app (iso.inv α) X) :=
  is_iso.mk (nat_trans.app (iso.hom α) X)

/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the later, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp norm form,
but for now it breaks too many proofs.
-/

@[simp] theorem cancel_nat_iso_hom_left {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) {X : C} {Z : D} (g : functor.obj G X ⟶ Z) (g' : functor.obj G X ⟶ Z) : nat_trans.app (iso.hom α) X ≫ g = nat_trans.app (iso.hom α) X ≫ g' ↔ g = g' := sorry

@[simp] theorem cancel_nat_iso_inv_left {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) {X : C} {Z : D} (g : functor.obj F X ⟶ Z) (g' : functor.obj F X ⟶ Z) : nat_trans.app (iso.inv α) X ≫ g = nat_trans.app (iso.inv α) X ≫ g' ↔ g = g' := sorry

@[simp] theorem cancel_nat_iso_hom_right {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) {X : D} {Y : C} (f : X ⟶ functor.obj F Y) (f' : X ⟶ functor.obj F Y) : f ≫ nat_trans.app (iso.hom α) Y = f' ≫ nat_trans.app (iso.hom α) Y ↔ f = f' := sorry

@[simp] theorem cancel_nat_iso_inv_right {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) {X : D} {Y : C} (f : X ⟶ functor.obj G Y) (f' : X ⟶ functor.obj G Y) : f ≫ nat_trans.app (iso.inv α) Y = f' ≫ nat_trans.app (iso.inv α) Y ↔ f = f' := sorry

@[simp] theorem cancel_nat_iso_hom_right_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) {W : D} {X : D} {X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ functor.obj F Y) (f' : W ⟶ X') (g' : X' ⟶ functor.obj F Y) : f ≫ g ≫ nat_trans.app (iso.hom α) Y = f' ≫ g' ≫ nat_trans.app (iso.hom α) Y ↔ f ≫ g = f' ≫ g' := sorry

@[simp] theorem cancel_nat_iso_inv_right_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ≅ G) {W : D} {X : D} {X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ functor.obj G Y) (f' : W ⟶ X') (g' : X' ⟶ functor.obj G Y) : f ≫ g ≫ nat_trans.app (iso.inv α) Y = f' ≫ g' ≫ nat_trans.app (iso.inv α) Y ↔ f ≫ g = f' ≫ g' := sorry

theorem naturality_1 {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {X : C} {Y : C} (α : F ≅ G) (f : X ⟶ Y) : nat_trans.app (iso.inv α) X ≫ functor.map F f ≫ nat_trans.app (iso.hom α) Y = functor.map G f := sorry

theorem naturality_2 {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {X : C} {Y : C} (α : F ≅ G) (f : X ⟶ Y) : nat_trans.app (iso.hom α) X ≫ functor.map G f ≫ nat_trans.app (iso.inv α) Y = functor.map F f := sorry

/--
A natural transformation is an isomorphism if all its components are isomorphisms.
-/
-- Making this an instance would cause a typeclass inference loop with `is_iso_app_of_is_iso`.

def is_iso_of_is_iso_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ⟶ G) [(X : C) → is_iso (nat_trans.app α X)] : is_iso α :=
  is_iso.mk (nat_trans.mk fun (X : C) => inv (nat_trans.app α X))

/--
The components of a natural isomorphism are isomorphisms.
-/
protected instance is_iso_app_of_is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ⟶ G) [is_iso α] (X : C) : is_iso (nat_trans.app α X) :=
  is_iso.mk (nat_trans.app (inv α) X)

/--
Construct a natural isomorphism between functors by giving object level isomorphisms,
and checking naturality only in the forward direction.
-/
def of_components {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (app : (X : C) → functor.obj F X ≅ functor.obj G X) (naturality : ∀ {X Y : C} (f : X ⟶ Y), functor.map F f ≫ iso.hom (app Y) = iso.hom (app X) ≫ functor.map G f) : F ≅ G :=
  iso.mk (nat_trans.mk fun (X : C) => iso.hom (app X)) (inv (nat_trans.mk fun (X : C) => iso.hom (app X)))

@[simp] theorem of_components.app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (app' : (X : C) → functor.obj F X ≅ functor.obj G X) (naturality : ∀ {X Y : C} (f : X ⟶ Y), functor.map F f ≫ iso.hom (app' Y) = iso.hom (app' X) ≫ functor.map G f) (X : C) : iso.app (of_components app' naturality) X = app' X :=
  iso.ext (Eq.refl (iso.hom (iso.app (of_components app' naturality) X)))

@[simp] theorem of_components.hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (app : (X : C) → functor.obj F X ≅ functor.obj G X) (naturality : ∀ {X Y : C} (f : X ⟶ Y), functor.map F f ≫ iso.hom (app Y) = iso.hom (app X) ≫ functor.map G f) (X : C) : nat_trans.app (iso.hom (of_components app naturality)) X = iso.hom (app X) :=
  rfl

@[simp] theorem of_components.inv_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (app : (X : C) → functor.obj F X ≅ functor.obj G X) (naturality : ∀ {X Y : C} (f : X ⟶ Y), functor.map F f ≫ iso.hom (app Y) = iso.hom (app X) ≫ functor.map G f) (X : C) : nat_trans.app (iso.inv (of_components app naturality)) X = iso.inv (app X) :=
  rfl

/-- Horizontal composition of natural isomorphisms. -/
def hcomp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} {I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I :=
  iso.mk (iso.hom α ◫ iso.hom β) (iso.inv α ◫ iso.inv β)

