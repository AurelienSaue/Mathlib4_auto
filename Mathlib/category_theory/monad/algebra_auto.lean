/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monad.basic
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.reflects_isomorphisms
import PostPort

universes v₁ u₁ l 

namespace Mathlib

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad,
and provides the category instance for them.

Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category, as well as the adjoint pair of forgetful and
cofree functors, respectively from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

namespace category_theory


namespace monad


/-- An Eilenberg-Moore algebra for a monad `T`.
    cf Definition 5.2.3 in [Riehl][riehl2017]. -/
structure algebra {C : Type u₁} [category C] (T : C ⥤ C) [monad T] 
where
  A : C
  a : functor.obj T A ⟶ A
  unit' : autoParam (nat_trans.app η_ A ≫ a = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  assoc' : autoParam (nat_trans.app μ_ A ≫ a = functor.map T a ≫ a)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem algebra.unit {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (c : algebra T) : nat_trans.app η_ (algebra.A c) ≫ algebra.a c = 𝟙 := sorry

theorem algebra.assoc {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (c : algebra T) : nat_trans.app μ_ (algebra.A c) ≫ algebra.a c = functor.map T (algebra.a c) ≫ algebra.a c := sorry

theorem algebra.assoc_assoc {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (c : algebra T) {X' : C} (f' : algebra.A c ⟶ X') : nat_trans.app μ_ (algebra.A c) ≫ algebra.a c ≫ f' = functor.map T (algebra.a c) ≫ algebra.a c ≫ f' := sorry

namespace algebra


/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
structure hom {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (A : algebra T) (B : algebra T) 
where
  f : A A ⟶ A B
  h' : autoParam (functor.map T f ≫ a B = a A ≫ f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem hom.h {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {A : algebra T} {B : algebra T} (c : hom A B) : functor.map T (hom.f c) ≫ a B = a A ≫ hom.f c := sorry

@[simp] theorem hom.h_assoc {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {A : algebra T} {B : algebra T} (c : hom A B) {X' : C} (f' : A B ⟶ X') : functor.map T (hom.f c) ≫ a B ≫ f' = a A ≫ hom.f c ≫ f' := sorry

namespace hom


/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
def id {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (A : algebra T) : hom A A :=
  mk 𝟙

protected instance inhabited {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (A : algebra T) : Inhabited (hom A A) :=
  { default := mk 𝟙 }

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
def comp {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {P : algebra T} {Q : algebra T} {R : algebra T} (f : hom P Q) (g : hom Q R) : hom P R :=
  mk (f f ≫ f g)

end hom


protected instance category_theory.category_struct {C : Type u₁} [category C] {T : C ⥤ C} [monad T] : category_struct (algebra T) :=
  category_struct.mk hom.id hom.comp

@[simp] theorem comp_eq_comp {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {A : algebra T} {A' : algebra T} {A'' : algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : hom.comp f g = f ≫ g :=
  rfl

@[simp] theorem id_eq_id {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (A : algebra T) : hom.id A = 𝟙 :=
  rfl

@[simp] theorem id_f {C : Type u₁} [category C] {T : C ⥤ C} [monad T] (A : algebra T) : hom.f 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_f {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {A : algebra T} {A' : algebra T} {A'' : algebra T} (f : A ⟶ A') (g : A' ⟶ A'') : hom.f (f ≫ g) = hom.f f ≫ hom.f g :=
  rfl

/-- The category of Eilenberg-Moore algebras for a monad.
    cf Definition 5.2.4 in [Riehl][riehl2017]. -/
protected instance EilenbergMoore {C : Type u₁} [category C] {T : C ⥤ C} [monad T] : category (algebra T) :=
  category.mk

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simp] theorem iso_mk_hom_f {C : Type u₁} [category C] {T : C ⥤ C} [monad T] {A : algebra T} {B : algebra T} (h : A A ≅ A B) (w : functor.map T (iso.hom h) ≫ a B = a A ≫ iso.hom h) : hom.f (iso.hom (iso_mk h w)) = iso.hom h :=
  Eq.refl (hom.f (iso.hom (iso_mk h w)))

end algebra


/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[simp] theorem forget_map {C : Type u₁} [category C] (T : C ⥤ C) [monad T] (A : algebra T) (B : algebra T) (f : A ⟶ B) : functor.map (forget T) f = algebra.hom.f f :=
  Eq.refl (functor.map (forget T) f)

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[simp] theorem free_obj_A {C : Type u₁} [category C] (T : C ⥤ C) [monad T] (X : C) : algebra.A (functor.obj (free T) X) = functor.obj T X :=
  Eq.refl (algebra.A (functor.obj (free T) X))

protected instance algebra.inhabited {C : Type u₁} [category C] (T : C ⥤ C) [monad T] [Inhabited C] : Inhabited (algebra T) :=
  { default := functor.obj (free T) Inhabited.default }

/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for a monad.
    cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if

-- those are added too

@[simp] theorem adj_counit {C : Type u₁} [category C] (T : C ⥤ C) [monad T] : adjunction.counit (adj T) =
  nat_trans.mk
    fun (Y : algebra T) =>
      equiv.inv_fun
        (adjunction.core_hom_equiv.hom_equiv
          (adjunction.core_hom_equiv.mk
            fun (X : C) (Y : algebra T) =>
              equiv.mk (fun (f : functor.obj (free T) X ⟶ Y) => nat_trans.app η_ X ≫ algebra.hom.f f)
                (fun (f : X ⟶ functor.obj (forget T) Y) => algebra.hom.mk (functor.map T f ≫ algebra.a Y))
                (adj._proof_2 T X Y) (adj._proof_3 T X Y))
          (functor.obj (forget T) Y) (functor.obj 𝟭 Y))
        𝟙 :=
  Eq.refl (adjunction.counit (adj T))

/--
Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
def algebra_iso_of_iso {C : Type u₁} [category C] (T : C ⥤ C) [monad T] {A : algebra T} {B : algebra T} (f : A ⟶ B) [is_iso (algebra.hom.f f)] : is_iso f :=
  is_iso.mk (algebra.hom.mk (inv (algebra.hom.f f)))

protected instance forget_reflects_iso {C : Type u₁} [category C] (T : C ⥤ C) [monad T] : reflects_isomorphisms (forget T) :=
  reflects_isomorphisms.mk fun (A B : algebra T) => algebra_iso_of_iso T

protected instance forget_faithful {C : Type u₁} [category C] (T : C ⥤ C) [monad T] : faithful (forget T) :=
  faithful.mk

end monad


namespace comonad


/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
structure coalgebra {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] 
where
  A : C
  a : A ⟶ functor.obj G A
  counit' : autoParam (a ≫ nat_trans.app ε_ A = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  coassoc' : autoParam (a ≫ nat_trans.app δ_ A = a ≫ functor.map G a)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem coalgebra.counit {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (c : coalgebra G) : coalgebra.a c ≫ nat_trans.app ε_ (coalgebra.A c) = 𝟙 := sorry

theorem coalgebra.coassoc {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (c : coalgebra G) : coalgebra.a c ≫ nat_trans.app δ_ (coalgebra.A c) = coalgebra.a c ≫ functor.map G (coalgebra.a c) := sorry

theorem coalgebra.counit_assoc {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (c : coalgebra G) {X' : C} (f' : coalgebra.A c ⟶ X') : coalgebra.a c ≫ nat_trans.app ε_ (coalgebra.A c) ≫ f' = f' := sorry

namespace coalgebra


/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
structure hom {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (A : coalgebra G) (B : coalgebra G) 
where
  f : A A ⟶ A B
  h' : autoParam (a A ≫ functor.map G f = f ≫ a B)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem hom.h {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] {A : coalgebra G} {B : coalgebra G} (c : hom A B) : a A ≫ functor.map G (hom.f c) = hom.f c ≫ a B := sorry

@[simp] theorem hom.h_assoc {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] {A : coalgebra G} {B : coalgebra G} (c : hom A B) {X' : C} (f' : functor.obj G (A B) ⟶ X') : a A ≫ functor.map G (hom.f c) ≫ f' = hom.f c ≫ a B ≫ f' := sorry

namespace hom


/-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/
def id {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (A : coalgebra G) : hom A A :=
  mk 𝟙

/-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/
def comp {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] {P : coalgebra G} {Q : coalgebra G} {R : coalgebra G} (f : hom P Q) (g : hom Q R) : hom P R :=
  mk (f f ≫ f g)

end hom


/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
protected instance category_theory.category_struct {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] : category_struct (coalgebra G) :=
  category_struct.mk hom.id hom.comp

@[simp] theorem comp_eq_comp {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] {A : coalgebra G} {A' : coalgebra G} {A'' : coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : hom.comp f g = f ≫ g :=
  rfl

@[simp] theorem id_eq_id {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (A : coalgebra G) : hom.id A = 𝟙 :=
  rfl

@[simp] theorem id_f {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] (A : coalgebra G) : hom.f 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_f {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] {A : coalgebra G} {A' : coalgebra G} {A'' : coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') : hom.f (f ≫ g) = hom.f f ≫ hom.f g :=
  rfl

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
protected instance EilenbergMoore {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] : category (coalgebra G) :=
  category.mk

/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simp] theorem iso_mk_hom_f {C : Type u₁} [category C] {G : C ⥤ C} [comonad G] {A : coalgebra G} {B : coalgebra G} (h : A A ≅ A B) (w : a A ≫ functor.map G (iso.hom h) = iso.hom h ≫ a B) : hom.f (iso.hom (iso_mk h w)) = iso.hom h :=
  Eq.refl (hom.f (iso.hom (iso_mk h w)))

end coalgebra


/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic structure. -/
def forget {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] : coalgebra G ⥤ C :=
  functor.mk (fun (A : coalgebra G) => coalgebra.A A) fun (A B : coalgebra G) (f : A ⟶ B) => coalgebra.hom.f f

/--
Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalgebra isomorphism.
-/
def coalgebra_iso_of_iso {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] {A : coalgebra G} {B : coalgebra G} (f : A ⟶ B) [is_iso (coalgebra.hom.f f)] : is_iso f :=
  is_iso.mk (coalgebra.hom.mk (inv (coalgebra.hom.f f)))

protected instance forget_reflects_iso {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] : reflects_isomorphisms (forget G) :=
  reflects_isomorphisms.mk fun (A B : coalgebra G) => coalgebra_iso_of_iso G

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any object. -/
@[simp] theorem cofree_map_f {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] (X : C) (Y : C) (f : X ⟶ Y) : coalgebra.hom.f (functor.map (cofree G) f) = functor.map G f :=
  Eq.refl (coalgebra.hom.f (functor.map (cofree G) f))

/--
The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if

-- those are added too

@[simp] theorem adj_counit {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] : adjunction.counit (adj G) = nat_trans.mk (nat_trans.app ε_) := sorry

protected instance forget_faithful {C : Type u₁} [category C] (G : C ⥤ C) [comonad G] : faithful (forget G) :=
  faithful.mk

