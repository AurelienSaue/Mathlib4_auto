/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.natural_transformation
import Mathlib.category_theory.monoidal.discrete
import Mathlib.PostPort

universes v u l v₁ u₁ v₂ u₂ u₃ v₃ 

namespace Mathlib

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `braided_monoidal_category` another typeclass, but then have `symmetric_monoidal_category`
extend this. The rationale is that we are not carrying any additional data,
just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

-/

namespace category_theory


/--
A braided monoidal category is a monoidal category equipped with a braiding isomorphism
`β_ X Y : X ⊗ Y ≅ Y ⊗ X`
which is natural in both arguments,
and also satisfies the two hexagon identities.
-/
-- braiding natural iso:

class braided_category (C : Type u) [category C] [monoidal_category C] 
where
  braiding : (X Y : C) → X ⊗ Y ≅ Y ⊗ X
  braiding_naturality' : autoParam
  (∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), (f ⊗ g) ≫ iso.hom (braiding Y Y') = iso.hom (braiding X X') ≫ (g ⊗ f))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  hexagon_forward' : autoParam
  (∀ (X Y Z : C),
    iso.hom α_ ≫ iso.hom (braiding X (Y ⊗ Z)) ≫ iso.hom α_ =
      (iso.hom (braiding X Y) ⊗ 𝟙) ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.hom (braiding X Z)))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  hexagon_reverse' : autoParam
  (∀ (X Y Z : C),
    iso.inv α_ ≫ iso.hom (braiding (X ⊗ Y) Z) ≫ iso.inv α_ =
      (𝟙 ⊗ iso.hom (braiding Y Z)) ≫ iso.inv α_ ≫ (iso.hom (braiding X Z) ⊗ 𝟙))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- hexagon identities:

@[simp] theorem braided_category.braiding_naturality {C : Type u} [category C] [monoidal_category C] [c : braided_category C] {X : C} {X' : C} {Y : C} {Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (f ⊗ g) ≫ iso.hom (braided_category.braiding Y Y') = iso.hom (braided_category.braiding X X') ≫ (g ⊗ f) := sorry

@[simp] theorem braided_category.braiding_naturality_assoc {C : Type u} [category C] [monoidal_category C] [c : braided_category C] {X : C} {X' : C} {Y : C} {Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : ∀ {X'_1 : C} (f' : Y' ⊗ Y ⟶ X'_1),
  (f ⊗ g) ≫ iso.hom (braided_category.braiding Y Y') ≫ f' = iso.hom (braided_category.braiding X X') ≫ (g ⊗ f) ≫ f' := sorry

theorem braided_category.hexagon_forward {C : Type u} [category C] [monoidal_category C] [c : braided_category C] (X : C) (Y : C) (Z : C) : iso.hom α_ ≫ iso.hom (braided_category.braiding X (Y ⊗ Z)) ≫ iso.hom α_ =
  (iso.hom (braided_category.braiding X Y) ⊗ 𝟙) ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.hom (braided_category.braiding X Z)) := sorry

theorem braided_category.hexagon_reverse {C : Type u} [category C] [monoidal_category C] [c : braided_category C] (X : C) (Y : C) (Z : C) : iso.inv α_ ≫ iso.hom (braided_category.braiding (X ⊗ Y) Z) ≫ iso.inv α_ =
  (𝟙 ⊗ iso.hom (braided_category.braiding Y Z)) ≫ iso.inv α_ ≫ (iso.hom (braided_category.braiding X Z) ⊗ 𝟙) := sorry

notation:1024 "β_" => Mathlib.category_theory.braided_category.braiding

/-!
We now establish how the braiding interacts with the unitors.

I couldn't find a detailed proof in print, but this is discussed in:

* Proposition 1 of André Joyal and Ross Street,
  "Braided monoidal categories", Macquarie Math Reports 860081 (1986).
* Proposition 2.1 of André Joyal and Ross Street,
  "Braided tensor categories" , Adv. Math. 102 (1993), 20–78.
* Exercise 8.1.6 of Etingof, Gelaki, Nikshych, Ostrik,
  "Tensor categories", vol 25, Mathematical Surveys and Monographs (2015), AMS.
-/

theorem braiding_left_unitor_aux₁ (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (X : C) : iso.hom α_ ≫ (𝟙 ⊗ iso.inv β_) ≫ iso.inv α_ ≫ (iso.hom λ_ ⊗ 𝟙) = (iso.hom λ_ ⊗ 𝟙) ≫ iso.inv β_ := sorry

theorem braiding_left_unitor_aux₂ (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (X : C) : (iso.hom β_ ⊗ 𝟙) ≫ (iso.hom λ_ ⊗ 𝟙) = iso.hom ρ_ ⊗ 𝟙 := sorry

@[simp] theorem braiding_left_unitor (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (X : C) : iso.hom β_ ≫ iso.hom λ_ = iso.hom ρ_ := sorry

theorem braiding_right_unitor_aux₁ (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (X : C) : iso.inv α_ ≫ (iso.inv β_ ⊗ 𝟙) ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.hom ρ_) = (𝟙 ⊗ iso.hom ρ_) ≫ iso.inv β_ := sorry

theorem braiding_right_unitor_aux₂ (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (X : C) : (𝟙 ⊗ iso.hom β_) ≫ (𝟙 ⊗ iso.hom ρ_) = 𝟙 ⊗ iso.hom λ_ := sorry

@[simp] theorem braiding_right_unitor (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (X : C) : iso.hom β_ ≫ iso.hom ρ_ = iso.hom λ_ := sorry

/--
A symmetric monoidal category is a braided monoidal category for which the braiding is symmetric.

See https://stacks.math.columbia.edu/tag/0FFW.
-/
class symmetric_category (C : Type u) [category C] [monoidal_category C] 
extends braided_category C
where
  symmetry' : autoParam (C → C → iso.hom β_ ≫ iso.hom β_ = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- braiding symmetric:

@[simp] theorem symmetric_category.symmetry {C : Type u} [category C] [monoidal_category C] [c : symmetric_category C] (X : C) (Y : C) : iso.hom β_ ≫ iso.hom β_ = 𝟙 := sorry

@[simp] theorem symmetric_category.symmetry_assoc {C : Type u} [category C] [monoidal_category C] [c : symmetric_category C] (X : C) (Y : C) {X' : C} (f' : X ⊗ Y ⟶ X') : iso.hom β_ ≫ iso.hom β_ ≫ f' = f' := sorry

/--
A lax braided functor between braided monoidal categories is a lax monoidal functor
which preserves the braiding.
-/
structure lax_braided_functor (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (D : Type u₂) [category D] [monoidal_category D] [braided_category D] 
extends lax_monoidal_functor C D
where
  braided' : autoParam
  (∀ (X Y : C),
    lax_monoidal_functor.μ _to_lax_monoidal_functor X Y ≫
        functor.map (lax_monoidal_functor.to_functor _to_lax_monoidal_functor) (iso.hom β_) =
      iso.hom β_ ≫ lax_monoidal_functor.μ _to_lax_monoidal_functor Y X)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem lax_braided_functor.braided {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] (c : lax_braided_functor C D) (X : C) (Y : C) : lax_monoidal_functor.μ (lax_braided_functor.to_lax_monoidal_functor c) X Y ≫
    functor.map (lax_monoidal_functor.to_functor (lax_braided_functor.to_lax_monoidal_functor c)) (iso.hom β_) =
  iso.hom β_ ≫ lax_monoidal_functor.μ (lax_braided_functor.to_lax_monoidal_functor c) Y X := sorry

namespace lax_braided_functor


/-- The identity lax braided monoidal functor. -/
def id (C : Type u₁) [category C] [monoidal_category C] [braided_category C] : lax_braided_functor C C :=
  mk (monoidal_functor.to_lax_monoidal_functor (monoidal_functor.id C))

protected instance inhabited (C : Type u₁) [category C] [monoidal_category C] [braided_category C] : Inhabited (lax_braided_functor C C) :=
  { default := id C }

/-- The composition of lax braided monoidal functors. -/
def comp {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] {E : Type u₃} [category E] [monoidal_category E] [braided_category E] (F : lax_braided_functor C D) (G : lax_braided_functor D E) : lax_braided_functor C E :=
  mk
    (lax_monoidal_functor.mk (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F ⊗⋙ to_lax_monoidal_functor G))
      (lax_monoidal_functor.ε (to_lax_monoidal_functor F ⊗⋙ to_lax_monoidal_functor G))
      (lax_monoidal_functor.μ (to_lax_monoidal_functor F ⊗⋙ to_lax_monoidal_functor G)))

protected instance category_lax_braided_functor {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] : category (lax_braided_functor C D) :=
  induced_category.category to_lax_monoidal_functor

@[simp] theorem comp_to_nat_trans {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] {F : lax_braided_functor C D} {G : lax_braided_functor C D} {H : lax_braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} : monoidal_nat_trans.to_nat_trans (α ≫ β) = monoidal_nat_trans.to_nat_trans α ≫ monoidal_nat_trans.to_nat_trans β :=
  rfl

/--
Interpret a natural isomorphism of the underlyling lax monoidal functors as an
isomorphism of the lax braided monoidal functors.
-/
@[simp] theorem mk_iso_hom {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] {F : lax_braided_functor C D} {G : lax_braided_functor C D} (i : to_lax_monoidal_functor F ≅ to_lax_monoidal_functor G) : iso.hom (mk_iso i) = iso.hom i :=
  Eq.refl (iso.hom (mk_iso i))

end lax_braided_functor


/--
A braided functor between braided monoidal categories is a monoidal functor
which preserves the braiding.
-/
-- Note this is stated different than for `lax_braided_functor`.

structure braided_functor (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (D : Type u₂) [category D] [monoidal_category D] [braided_category D] 
extends monoidal_functor C D
where
  braided' : autoParam
  (∀ (X Y : C),
    functor.map (lax_monoidal_functor.to_functor (monoidal_functor.to_lax_monoidal_functor _to_monoidal_functor))
        (iso.hom β_) =
      inv (lax_monoidal_functor.μ (monoidal_functor.to_lax_monoidal_functor _to_monoidal_functor) X Y) ≫
        iso.hom β_ ≫ lax_monoidal_functor.μ (monoidal_functor.to_lax_monoidal_functor _to_monoidal_functor) Y X)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- We move the `μ X Y` to the right hand side,

-- so that this makes a good `@[simp]` lemma.

@[simp] theorem braided_functor.braided {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] (c : braided_functor C D) (X : C) (Y : C) : functor.map
    (lax_monoidal_functor.to_functor (monoidal_functor.to_lax_monoidal_functor (braided_functor.to_monoidal_functor c)))
    (iso.hom β_) =
  inv (lax_monoidal_functor.μ (monoidal_functor.to_lax_monoidal_functor (braided_functor.to_monoidal_functor c)) X Y) ≫
    iso.hom β_ ≫
      lax_monoidal_functor.μ (monoidal_functor.to_lax_monoidal_functor (braided_functor.to_monoidal_functor c)) Y X := sorry

namespace braided_functor


/-- Turn a braided functor into a lax braided functor. -/
def to_lax_braided_functor (C : Type u₁) [category C] [monoidal_category C] [braided_category C] (D : Type u₂) [category D] [monoidal_category D] [braided_category D] (F : braided_functor C D) : lax_braided_functor C D :=
  lax_braided_functor.mk (monoidal_functor.to_lax_monoidal_functor (to_monoidal_functor F))

/-- The identity braided monoidal functor. -/
@[simp] theorem id_to_monoidal_functor (C : Type u₁) [category C] [monoidal_category C] [braided_category C] : to_monoidal_functor (id C) = monoidal_functor.id C :=
  Eq.refl (to_monoidal_functor (id C))

protected instance inhabited (C : Type u₁) [category C] [monoidal_category C] [braided_category C] : Inhabited (braided_functor C C) :=
  { default := id C }

/-- The composition of braided monoidal functors. -/
@[simp] theorem comp_to_monoidal_functor {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] {E : Type u₃} [category E] [monoidal_category E] [braided_category E] (F : braided_functor C D) (G : braided_functor D E) : to_monoidal_functor (comp F G) = to_monoidal_functor F ⊗⋙ to_monoidal_functor G :=
  Eq.refl (to_monoidal_functor (comp F G))

protected instance category_braided_functor {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] : category (braided_functor C D) :=
  induced_category.category to_monoidal_functor

@[simp] theorem comp_to_nat_trans {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] {F : braided_functor C D} {G : braided_functor C D} {H : braided_functor C D} {α : F ⟶ G} {β : G ⟶ H} : monoidal_nat_trans.to_nat_trans (α ≫ β) = monoidal_nat_trans.to_nat_trans α ≫ monoidal_nat_trans.to_nat_trans β :=
  rfl

/--
Interpret a natural isomorphism of the underlyling monoidal functors as an
isomorphism of the braided monoidal functors.
-/
def mk_iso {C : Type u₁} [category C] [monoidal_category C] [braided_category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] {F : braided_functor C D} {G : braided_functor C D} (i : to_monoidal_functor F ≅ to_monoidal_functor G) : F ≅ G :=
  iso.mk (iso.hom i) (iso.inv i)

end braided_functor


protected instance comm_monoid_discrete (M : Type u) [comm_monoid M] : comm_monoid (discrete M) :=
  id _inst_10

protected instance discrete.braided_category (M : Type u) [comm_monoid M] : braided_category (discrete M) :=
  braided_category.mk fun (X Y : discrete M) => eq_to_iso sorry

/--
A multiplicative morphism between commutative monoids gives a braided functor between
the corresponding discrete braided monoidal categories.
-/
def discrete.braided_functor {M : Type u} [comm_monoid M] {N : Type u} [comm_monoid N] (F : M →* N) : braided_functor (discrete M) (discrete N) :=
  braided_functor.mk (monoidal_functor.mk (monoidal_functor.to_lax_monoidal_functor (discrete.monoidal_functor F)))

