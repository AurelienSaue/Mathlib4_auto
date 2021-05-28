/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.category
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l u₃ v₃ 

namespace Mathlib

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).
satisfying various axioms.

A monoidal functor is a lax monoidal functor for which `ε` and `μ` are isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See also `category_theory.monoidal.functorial` for a typeclass decorating an object-level
function with the additional data of a monoidal functor.
This is useful when stating that a pre-existing functor is monoidal.

See `category_theory.monoidal.natural_transformation` for monoidal natural transformations.

We show in `category_theory.monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## Future work
* Oplax monoidal functors.

## References

See https://stacks.math.columbia.edu/tag/0FFL.
-/

namespace category_theory


/-- A lax monoidal functor is a functor `F : C ⥤ D` between monoidal categories, equipped with morphisms
    `ε : 𝟙 _D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`, satisfying the
    the appropriate coherences. -/
-- unit morphism

structure lax_monoidal_functor (C : Type u₁) [category C] [monoidal_category C] (D : Type u₂) [category D] [monoidal_category D] 
extends C ⥤ D
where
  ε : 𝟙_ ⟶ functor.obj _to_functor 𝟙_
  μ : (X Y : C) → functor.obj _to_functor X ⊗ functor.obj _to_functor Y ⟶ functor.obj _to_functor (X ⊗ Y)
  μ_natural' : autoParam
  (∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
    (functor.map _to_functor f ⊗ functor.map _to_functor g) ≫ μ Y Y' = μ X X' ≫ functor.map _to_functor (f ⊗ g))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  associativity' : autoParam
  (∀ (X Y Z : C),
    (μ X Y ⊗ 𝟙) ≫ μ (X ⊗ Y) Z ≫ functor.map _to_functor (iso.hom α_) = iso.hom α_ ≫ (𝟙 ⊗ μ Y Z) ≫ μ X (Y ⊗ Z))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  left_unitality' : autoParam (∀ (X : C), iso.hom λ_ = (ε ⊗ 𝟙) ≫ μ 𝟙_ X ≫ functor.map _to_functor (iso.hom λ_))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right_unitality' : autoParam (∀ (X : C), iso.hom ρ_ = (𝟙 ⊗ ε) ≫ μ X 𝟙_ ≫ functor.map _to_functor (iso.hom ρ_))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- tensorator

-- associativity of the tensorator

-- unitality

@[simp] theorem lax_monoidal_functor.μ_natural {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (c : lax_monoidal_functor C D) {X : C} {Y : C} {X' : C} {Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (functor.map (lax_monoidal_functor.to_functor c) f ⊗ functor.map (lax_monoidal_functor.to_functor c) g) ≫
    lax_monoidal_functor.μ c Y Y' =
  lax_monoidal_functor.μ c X X' ≫ functor.map (lax_monoidal_functor.to_functor c) (f ⊗ g) := sorry

@[simp] theorem lax_monoidal_functor.μ_natural_assoc {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (c : lax_monoidal_functor C D) {X : C} {Y : C} {X' : C} {Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : ∀ {X'_1 : D} (f' : functor.obj (lax_monoidal_functor.to_functor c) (Y ⊗ Y') ⟶ X'_1),
  (functor.map (lax_monoidal_functor.to_functor c) f ⊗ functor.map (lax_monoidal_functor.to_functor c) g) ≫
      lax_monoidal_functor.μ c Y Y' ≫ f' =
    lax_monoidal_functor.μ c X X' ≫ functor.map (lax_monoidal_functor.to_functor c) (f ⊗ g) ≫ f' := sorry

@[simp] theorem lax_monoidal_functor.left_unitality {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (c : lax_monoidal_functor C D) (X : C) : iso.hom λ_ =
  (lax_monoidal_functor.ε c ⊗ 𝟙) ≫
    lax_monoidal_functor.μ c 𝟙_ X ≫ functor.map (lax_monoidal_functor.to_functor c) (iso.hom λ_) := sorry

@[simp] theorem lax_monoidal_functor.right_unitality {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (c : lax_monoidal_functor C D) (X : C) : iso.hom ρ_ =
  (𝟙 ⊗ lax_monoidal_functor.ε c) ≫
    lax_monoidal_functor.μ c X 𝟙_ ≫ functor.map (lax_monoidal_functor.to_functor c) (iso.hom ρ_) := sorry

@[simp] theorem lax_monoidal_functor.associativity {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (c : lax_monoidal_functor C D) (X : C) (Y : C) (Z : C) : (lax_monoidal_functor.μ c X Y ⊗ 𝟙) ≫
    lax_monoidal_functor.μ c (X ⊗ Y) Z ≫ functor.map (lax_monoidal_functor.to_functor c) (iso.hom α_) =
  iso.hom α_ ≫ (𝟙 ⊗ lax_monoidal_functor.μ c Y Z) ≫ lax_monoidal_functor.μ c X (Y ⊗ Z) := sorry

-- When `rewrite_search` lands, add @[search] attributes to

-- lax_monoidal_functor.μ_natural lax_monoidal_functor.left_unitality

-- lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

/--
A monoidal functor is a lax monoidal functor for which the tensorator and unitor as isomorphisms.

See https://stacks.math.columbia.edu/tag/0FFL.
-/
structure monoidal_functor (C : Type u₁) [category C] [monoidal_category C] (D : Type u₂) [category D] [monoidal_category D] 
extends lax_monoidal_functor C D
where
  ε_is_iso : autoParam (is_iso (lax_monoidal_functor.ε _to_lax_monoidal_functor))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "apply_instance") [])
  μ_is_iso : autoParam ((X Y : C) → is_iso (lax_monoidal_functor.μ _to_lax_monoidal_functor X Y))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "apply_instance") [])

/--
The unit morphism of a (strong) monoidal functor as an isomorphism.
-/
def monoidal_functor.ε_iso {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : monoidal_functor C D) : 𝟙_ ≅ functor.obj (lax_monoidal_functor.to_functor (monoidal_functor.to_lax_monoidal_functor F)) 𝟙_ :=
  as_iso (lax_monoidal_functor.ε (monoidal_functor.to_lax_monoidal_functor F))

/--
The tensorator of a (strong) monoidal functor as an isomorphism.
-/
def monoidal_functor.μ_iso {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : monoidal_functor C D) (X : C) (Y : C) : functor.obj (lax_monoidal_functor.to_functor (monoidal_functor.to_lax_monoidal_functor F)) X ⊗
    functor.obj (lax_monoidal_functor.to_functor (monoidal_functor.to_lax_monoidal_functor F)) Y ≅
  functor.obj (lax_monoidal_functor.to_functor (monoidal_functor.to_lax_monoidal_functor F)) (X ⊗ Y) :=
  as_iso (lax_monoidal_functor.μ (monoidal_functor.to_lax_monoidal_functor F) X Y)

namespace lax_monoidal_functor


/-- The identity lax monoidal functor. -/
@[simp] theorem id_ε (C : Type u₁) [category C] [monoidal_category C] : ε (id C) = 𝟙 :=
  Eq.refl (ε (id C))

protected instance inhabited (C : Type u₁) [category C] [monoidal_category C] : Inhabited (lax_monoidal_functor C C) :=
  { default := id C }

end lax_monoidal_functor


namespace monoidal_functor


theorem map_tensor {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : monoidal_functor C D) {X : C} {Y : C} {X' : C} {Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : functor.map (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F)) (f ⊗ g) =
  inv (lax_monoidal_functor.μ (to_lax_monoidal_functor F) X X') ≫
    (functor.map (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F)) f ⊗
        functor.map (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F)) g) ≫
      lax_monoidal_functor.μ (to_lax_monoidal_functor F) Y Y' := sorry

theorem map_left_unitor {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : monoidal_functor C D) (X : C) : functor.map (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F)) (iso.hom λ_) =
  inv (lax_monoidal_functor.μ (to_lax_monoidal_functor F) 𝟙_ X) ≫
    (inv (lax_monoidal_functor.ε (to_lax_monoidal_functor F)) ⊗ 𝟙) ≫ iso.hom λ_ := sorry

theorem map_right_unitor {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : monoidal_functor C D) (X : C) : functor.map (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F)) (iso.hom ρ_) =
  inv (lax_monoidal_functor.μ (to_lax_monoidal_functor F) X 𝟙_) ≫
    (𝟙 ⊗ inv (lax_monoidal_functor.ε (to_lax_monoidal_functor F))) ≫ iso.hom ρ_ := sorry

/-- The tensorator as a natural isomorphism. -/
def μ_nat_iso {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : monoidal_functor C D) : functor.prod (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F))
      (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F)) ⋙
    monoidal_category.tensor D ≅
  monoidal_category.tensor C ⋙ lax_monoidal_functor.to_functor (to_lax_monoidal_functor F) :=
  nat_iso.of_components (fun (X : C × C) => μ_iso F (prod.fst X) (prod.snd X)) sorry

/-- The identity monoidal functor. -/
def id (C : Type u₁) [category C] [monoidal_category C] : monoidal_functor C C :=
  mk (lax_monoidal_functor.mk (functor.mk (functor.obj 𝟭) (functor.map 𝟭)) 𝟙 fun (X Y : C) => 𝟙)

protected instance inhabited (C : Type u₁) [category C] [monoidal_category C] : Inhabited (monoidal_functor C C) :=
  { default := id C }

end monoidal_functor


namespace lax_monoidal_functor


-- The proofs here are horrendous; rewrite_search helps a lot.

/-- The composition of two lax monoidal functors is again lax monoidal. -/
@[simp] theorem comp_ε {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] {E : Type u₃} [category E] [monoidal_category E] (F : lax_monoidal_functor C D) (G : lax_monoidal_functor D E) : ε (comp F G) = ε G ≫ functor.map (to_functor G) (ε F) :=
  Eq.refl (ε (comp F G))

infixr:80 " ⊗⋙ " => Mathlib.category_theory.lax_monoidal_functor.comp

end lax_monoidal_functor


namespace monoidal_functor


/-- The composition of two monoidal functors is again monoidal. -/
def comp {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] {E : Type u₃} [category E] [monoidal_category E] (F : monoidal_functor C D) (G : monoidal_functor D E) : monoidal_functor C E :=
  mk
    (lax_monoidal_functor.mk (lax_monoidal_functor.to_functor (to_lax_monoidal_functor F ⊗⋙ to_lax_monoidal_functor G))
      (lax_monoidal_functor.ε (to_lax_monoidal_functor F ⊗⋙ to_lax_monoidal_functor G))
      (lax_monoidal_functor.μ (to_lax_monoidal_functor F ⊗⋙ to_lax_monoidal_functor G)))

infixr:80 " ⊗⋙ " => Mathlib.category_theory.monoidal_functor.comp

