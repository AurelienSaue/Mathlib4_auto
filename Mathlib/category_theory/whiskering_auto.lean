/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import Mathlib.PostPort

universes u₁ u₂ u₃ v₁ v₂ v₃ u₄ v₄ u₅ v₅ 

namespace Mathlib

namespace category_theory


/--
If `α : G ⟶ H` then
`whisker_left F α : (F ⋙ G) ⟶ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
@[simp] theorem whisker_left_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) {G : D ⥤ E} {H : D ⥤ E} (α : G ⟶ H) (X : C) :
    nat_trans.app (whisker_left F α) X = nat_trans.app α (functor.obj F X) :=
  Eq.refl (nat_trans.app (whisker_left F α) X)

/--
If `α : G ⟶ H` then
`whisker_right α F : (G ⋙ F) ⟶ (G ⋙ F)` has components `F.map (α.app X)`.
-/
def whisker_right {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E]
    {G : C ⥤ D} {H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) : G ⋙ F ⟶ H ⋙ F :=
  nat_trans.mk fun (X : C) => functor.map F (nat_trans.app α X)

/--
Left-composition gives a functor `(C ⥤ D) ⥤ ((D ⥤ E) ⥤ (C ⥤ E))`.

`(whiskering_lift.obj F).obj G` is `F ⋙ G`, and
`(whiskering_lift.obj F).map α` is `whisker_left F α`.
-/
def whiskering_left (C : Type u₁) [category C] (D : Type u₂) [category D] (E : Type u₃)
    [category E] : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E :=
  functor.mk
    (fun (F : C ⥤ D) =>
      functor.mk (fun (G : D ⥤ E) => F ⋙ G) fun (G H : D ⥤ E) (α : G ⟶ H) => whisker_left F α)
    fun (F G : C ⥤ D) (τ : F ⟶ G) =>
      nat_trans.mk fun (H : D ⥤ E) => nat_trans.mk fun (c : C) => functor.map H (nat_trans.app τ c)

/--
Right-composition gives a functor `(D ⥤ E) ⥤ ((C ⥤ D) ⥤ (C ⥤ E))`.

`(whiskering_right.obj H).obj F` is `F ⋙ H`, and
`(whiskering_right.obj H).map α` is `whisker_right α H`.
-/
@[simp] theorem whiskering_right_obj_map (C : Type u₁) [category C] (D : Type u₂) [category D]
    (E : Type u₃) [category E] (H : D ⥤ E) (_x : C ⥤ D) :
    ∀ (_x_1 : C ⥤ D) (α : _x ⟶ _x_1),
        functor.map (functor.obj (whiskering_right C D E) H) α = whisker_right α H :=
  fun (_x_1 : C ⥤ D) (α : _x ⟶ _x_1) =>
    Eq.refl (functor.map (functor.obj (whiskering_right C D E) H) α)

@[simp] theorem whisker_left_id {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) {G : D ⥤ E} : whisker_left F (nat_trans.id G) = nat_trans.id (F ⋙ G) :=
  rfl

@[simp] theorem whisker_left_id' {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) {G : D ⥤ E} : whisker_left F 𝟙 = 𝟙 :=
  rfl

@[simp] theorem whisker_right_id {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {G : C ⥤ D} (F : D ⥤ E) :
    whisker_right (nat_trans.id G) F = nat_trans.id (G ⋙ F) :=
  functor.map_id (functor.obj (whiskering_right C D E) F) G

@[simp] theorem whisker_right_id' {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {G : C ⥤ D} (F : D ⥤ E) : whisker_right 𝟙 F = 𝟙 :=
  functor.map_id (functor.obj (whiskering_right C D E) F) G

@[simp] theorem whisker_left_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (F : C ⥤ D) {G : D ⥤ E} {H : D ⥤ E} {K : D ⥤ E} (α : G ⟶ H)
    (β : H ⟶ K) : whisker_left F (α ≫ β) = whisker_left F α ≫ whisker_left F β :=
  rfl

@[simp] theorem whisker_right_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {G : C ⥤ D} {H : C ⥤ D} {K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K)
    (F : D ⥤ E) : whisker_right (α ≫ β) F = whisker_right α F ≫ whisker_right β F :=
  functor.map_comp (functor.obj (whiskering_right C D E) F) α β

/--
If `α : G ≅ H` is a natural isomorphism then
`iso_whisker_left F α : (F ⋙ G) ≅ (F ⋙ H)` has components `α.app (F.obj X)`.
-/
def iso_whisker_left {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) {G : D ⥤ E} {H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  functor.map_iso (functor.obj (whiskering_left C D E) F) α

@[simp] theorem iso_whisker_left_hom {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (F : C ⥤ D) {G : D ⥤ E} {H : D ⥤ E} (α : G ≅ H) :
    iso.hom (iso_whisker_left F α) = whisker_left F (iso.hom α) :=
  rfl

@[simp] theorem iso_whisker_left_inv {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (F : C ⥤ D) {G : D ⥤ E} {H : D ⥤ E} (α : G ≅ H) :
    iso.inv (iso_whisker_left F α) = whisker_left F (iso.inv α) :=
  rfl

/--
If `α : G ≅ H` then
`iso_whisker_right α F : (G ⋙ F) ≅ (G ⋙ F)` has components `F.map_iso (α.app X)`.
-/
def iso_whisker_right {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {G : C ⥤ D} {H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  functor.map_iso (functor.obj (whiskering_right C D E) F) α

@[simp] theorem iso_whisker_right_hom {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {G : C ⥤ D} {H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    iso.hom (iso_whisker_right α F) = whisker_right (iso.hom α) F :=
  rfl

@[simp] theorem iso_whisker_right_inv {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {G : C ⥤ D} {H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) :
    iso.inv (iso_whisker_right α F) = whisker_right (iso.inv α) F :=
  rfl

protected instance is_iso_whisker_left {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (F : C ⥤ D) {G : D ⥤ E} {H : D ⥤ E} (α : G ⟶ H) [is_iso α] :
    is_iso (whisker_left F α) :=
  is_iso.mk (iso.inv (iso_whisker_left F (as_iso α)))

protected instance is_iso_whisker_right {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {G : C ⥤ D} {H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [is_iso α] :
    is_iso (whisker_right α F) :=
  is_iso.mk (iso.inv (iso_whisker_right (as_iso α) F))

@[simp] theorem whisker_left_twice {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {B : Type u₄} [category B] (F : B ⥤ C) (G : C ⥤ D) {H : D ⥤ E}
    {K : D ⥤ E} (α : H ⟶ K) : whisker_left F (whisker_left G α) = whisker_left (F ⋙ G) α :=
  rfl

@[simp] theorem whisker_right_twice {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {B : Type u₄} [category B] {H : B ⥤ C} {K : B ⥤ C} (F : C ⥤ D)
    (G : D ⥤ E) (α : H ⟶ K) : whisker_right (whisker_right α F) G = whisker_right α (F ⋙ G) :=
  rfl

theorem whisker_right_left {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {B : Type u₄} [category B] (F : B ⥤ C) {G : C ⥤ D} {H : C ⥤ D} (α : G ⟶ H)
    (K : D ⥤ E) : whisker_right (whisker_left F α) K = whisker_left F (whisker_right α K) :=
  rfl

namespace functor


/--
The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
@[simp] theorem left_unitor_hom_app {A : Type u₁} [category A] {B : Type u₂} [category B]
    (F : A ⥤ B) (X : A) : nat_trans.app (iso.hom (left_unitor F)) X = 𝟙 :=
  Eq.refl (nat_trans.app (iso.hom (left_unitor F)) X)

/--
The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
@[simp] theorem right_unitor_hom_app {A : Type u₁} [category A] {B : Type u₂} [category B]
    (F : A ⥤ B) (X : A) : nat_trans.app (iso.hom (right_unitor F)) X = 𝟙 :=
  Eq.refl (nat_trans.app (iso.hom (right_unitor F)) X)

/--
The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H))`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
@[simp] theorem associator_inv_app {A : Type u₁} [category A] {B : Type u₂} [category B]
    {C : Type u₃} [category C] {D : Type u₄} [category D] (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    (_x : A) : nat_trans.app (iso.inv (associator F G H)) _x = 𝟙 :=
  Eq.refl (nat_trans.app (iso.inv (associator F G H)) _x)

theorem triangle {A : Type u₁} [category A] {B : Type u₂} [category B] {C : Type u₃} [category C]
    (F : A ⥤ B) (G : B ⥤ C) :
    iso.hom (associator F 𝟭 G) ≫ whisker_left F (iso.hom (left_unitor G)) =
        whisker_right (iso.hom (right_unitor F)) G :=
  sorry

theorem pentagon {A : Type u₁} [category A] {B : Type u₂} [category B] {C : Type u₃} [category C]
    {D : Type u₄} [category D] {E : Type u₅} [category E] (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
    (K : D ⥤ E) :
    whisker_right (iso.hom (associator F G H)) K ≫
          iso.hom (associator F (G ⋙ H) K) ≫ whisker_left F (iso.hom (associator G H K)) =
        iso.hom (associator (F ⋙ G) H K) ≫ iso.hom (associator F G (H ⋙ K)) :=
  sorry

end Mathlib