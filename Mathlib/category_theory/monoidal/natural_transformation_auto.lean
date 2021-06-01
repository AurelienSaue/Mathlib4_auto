/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.functor
import Mathlib.category_theory.full_subcategory
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l u₃ v₃ 

namespace Mathlib

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

(Lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
-/

namespace category_theory


/--
A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
structure monoidal_nat_trans {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] (F : lax_monoidal_functor C D) (G : lax_monoidal_functor C D)
    extends nat_trans (lax_monoidal_functor.to_functor F) (lax_monoidal_functor.to_functor G) where
  unit' :
    autoParam (lax_monoidal_functor.ε F ≫ nat_trans.app _to_nat_trans 𝟙_ = lax_monoidal_functor.ε G)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  tensor' :
    autoParam
      (∀ (X Y : C),
        lax_monoidal_functor.μ F X Y ≫ nat_trans.app _to_nat_trans (X ⊗ Y) =
          (nat_trans.app _to_nat_trans X ⊗ nat_trans.app _to_nat_trans Y) ≫
            lax_monoidal_functor.μ G X Y)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem monoidal_nat_trans.tensor {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] {F : lax_monoidal_functor C D}
    {G : lax_monoidal_functor C D} (c : monoidal_nat_trans F G) (X : C) (Y : C) :
    lax_monoidal_functor.μ F X Y ≫ nat_trans.app (monoidal_nat_trans.to_nat_trans c) (X ⊗ Y) =
        (nat_trans.app (monoidal_nat_trans.to_nat_trans c) X ⊗
            nat_trans.app (monoidal_nat_trans.to_nat_trans c) Y) ≫
          lax_monoidal_functor.μ G X Y :=
  sorry

@[simp] theorem monoidal_nat_trans.tensor_assoc {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] {F : lax_monoidal_functor C D}
    {G : lax_monoidal_functor C D} (c : monoidal_nat_trans F G) (X : C) (Y : C) {X' : D}
    (f' : functor.obj (lax_monoidal_functor.to_functor G) (X ⊗ Y) ⟶ X') :
    lax_monoidal_functor.μ F X Y ≫ nat_trans.app (monoidal_nat_trans.to_nat_trans c) (X ⊗ Y) ≫ f' =
        (nat_trans.app (monoidal_nat_trans.to_nat_trans c) X ⊗
            nat_trans.app (monoidal_nat_trans.to_nat_trans c) Y) ≫
          lax_monoidal_functor.μ G X Y ≫ f' :=
  sorry

@[simp] theorem monoidal_nat_trans.unit {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] {F : lax_monoidal_functor C D}
    {G : lax_monoidal_functor C D} (c : monoidal_nat_trans F G) :
    lax_monoidal_functor.ε F ≫ nat_trans.app (monoidal_nat_trans.to_nat_trans c) 𝟙_ =
        lax_monoidal_functor.ε G :=
  sorry

@[simp] theorem monoidal_nat_trans.unit_assoc {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] {F : lax_monoidal_functor C D}
    {G : lax_monoidal_functor C D} (c : monoidal_nat_trans F G) {X' : D}
    (f' : functor.obj (lax_monoidal_functor.to_functor G) 𝟙_ ⟶ X') :
    lax_monoidal_functor.ε F ≫ nat_trans.app (monoidal_nat_trans.to_nat_trans c) 𝟙_ ≫ f' =
        lax_monoidal_functor.ε G ≫ f' :=
  sorry

namespace monoidal_nat_trans


/--
The identity monoidal natural transformation.
-/
def id {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D]
    [monoidal_category D] (F : lax_monoidal_functor C D) : monoidal_nat_trans F F :=
  mk (nat_trans.mk (nat_trans.app 𝟙))

protected instance inhabited {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] (F : lax_monoidal_functor C D) :
    Inhabited (monoidal_nat_trans F F) :=
  { default := id F }

/--
Vertical composition of monoidal natural transformations.
-/
def vcomp {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D]
    [monoidal_category D] {F : lax_monoidal_functor C D} {G : lax_monoidal_functor C D}
    {H : lax_monoidal_functor C D} (α : monoidal_nat_trans F G) (β : monoidal_nat_trans G H) :
    monoidal_nat_trans F H :=
  mk (nat_trans.mk (nat_trans.app (nat_trans.vcomp (to_nat_trans α) (to_nat_trans β))))

protected instance category_lax_monoidal_functor {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] : category (lax_monoidal_functor C D) :=
  category.mk

@[simp] theorem comp_to_nat_trans' {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] {F : lax_monoidal_functor C D} {G : lax_monoidal_functor C D}
    {H : lax_monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
    to_nat_trans (α ≫ β) = to_nat_trans α ≫ to_nat_trans β :=
  rfl

protected instance category_monoidal_functor {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] : category (monoidal_functor C D) :=
  induced_category.category monoidal_functor.to_lax_monoidal_functor

@[simp] theorem comp_to_nat_trans'' {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] {F : monoidal_functor C D} {G : monoidal_functor C D}
    {H : monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
    to_nat_trans (α ≫ β) = to_nat_trans α ≫ to_nat_trans β :=
  rfl

/--
Horizontal composition of monoidal natural transformations.
-/
@[simp] theorem hcomp_to_nat_trans {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] {E : Type u₃} [category E] [monoidal_category E]
    {F : lax_monoidal_functor C D} {G : lax_monoidal_functor C D} {H : lax_monoidal_functor D E}
    {K : lax_monoidal_functor D E} (α : monoidal_nat_trans F G) (β : monoidal_nat_trans H K) :
    to_nat_trans (hcomp α β) = to_nat_trans α ◫ to_nat_trans β :=
  Eq.refl (to_nat_trans (hcomp α β))

end monoidal_nat_trans


namespace monoidal_nat_iso


protected instance is_iso_of_is_iso_app {C : Type u₁} [category C] [monoidal_category C]
    {D : Type u₂} [category D] [monoidal_category D] {F : lax_monoidal_functor C D}
    {G : lax_monoidal_functor C D} (α : F ⟶ G)
    [(X : C) → is_iso (nat_trans.app (monoidal_nat_trans.to_nat_trans α) X)] : is_iso α :=
  is_iso.mk
    (monoidal_nat_trans.mk
      (nat_trans.mk fun (X : C) => inv (nat_trans.app (monoidal_nat_trans.to_nat_trans α) X)))

/--
Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction.
-/
def of_components {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D]
    [monoidal_category D] {F : lax_monoidal_functor C D} {G : lax_monoidal_functor C D}
    (app :
      (X : C) →
        functor.obj (lax_monoidal_functor.to_functor F) X ≅
          functor.obj (lax_monoidal_functor.to_functor G) X)
    (naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        functor.map (lax_monoidal_functor.to_functor F) f ≫ iso.hom (app Y) =
          iso.hom (app X) ≫ functor.map (lax_monoidal_functor.to_functor G) f)
    (unit : lax_monoidal_functor.ε F ≫ iso.hom (app 𝟙_) = lax_monoidal_functor.ε G)
    (tensor :
      ∀ (X Y : C),
        lax_monoidal_functor.μ F X Y ≫ iso.hom (app (X ⊗ Y)) =
          (iso.hom (app X) ⊗ iso.hom (app Y)) ≫ lax_monoidal_functor.μ G X Y) :
    F ≅ G :=
  as_iso (monoidal_nat_trans.mk (nat_trans.mk fun (X : C) => iso.hom (app X)))

@[simp] theorem of_components.hom_app {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] {F : lax_monoidal_functor C D} {G : lax_monoidal_functor C D}
    (app :
      (X : C) →
        functor.obj (lax_monoidal_functor.to_functor F) X ≅
          functor.obj (lax_monoidal_functor.to_functor G) X)
    (naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        functor.map (lax_monoidal_functor.to_functor F) f ≫ iso.hom (app Y) =
          iso.hom (app X) ≫ functor.map (lax_monoidal_functor.to_functor G) f)
    (unit : lax_monoidal_functor.ε F ≫ iso.hom (app 𝟙_) = lax_monoidal_functor.ε G)
    (tensor :
      ∀ (X Y : C),
        lax_monoidal_functor.μ F X Y ≫ iso.hom (app (X ⊗ Y)) =
          (iso.hom (app X) ⊗ iso.hom (app Y)) ≫ lax_monoidal_functor.μ G X Y)
    (X : C) :
    nat_trans.app
          (monoidal_nat_trans.to_nat_trans (iso.hom (of_components app naturality unit tensor))) X =
        iso.hom (app X) :=
  rfl

@[simp] theorem of_components.inv_app {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] {F : lax_monoidal_functor C D} {G : lax_monoidal_functor C D}
    (app :
      (X : C) →
        functor.obj (lax_monoidal_functor.to_functor F) X ≅
          functor.obj (lax_monoidal_functor.to_functor G) X)
    (naturality :
      ∀ {X Y : C} (f : X ⟶ Y),
        functor.map (lax_monoidal_functor.to_functor F) f ≫ iso.hom (app Y) =
          iso.hom (app X) ≫ functor.map (lax_monoidal_functor.to_functor G) f)
    (unit : lax_monoidal_functor.ε F ≫ iso.hom (app 𝟙_) = lax_monoidal_functor.ε G)
    (tensor :
      ∀ (X Y : C),
        lax_monoidal_functor.μ F X Y ≫ iso.hom (app (X ⊗ Y)) =
          (iso.hom (app X) ⊗ iso.hom (app Y)) ≫ lax_monoidal_functor.μ G X Y)
    (X : C) :
    nat_trans.app
          (monoidal_nat_trans.to_nat_trans (iso.inv (of_components app naturality unit tensor))) X =
        iso.inv (app X) :=
  rfl

end Mathlib