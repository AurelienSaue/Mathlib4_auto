/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.functor
import Mathlib.category_theory.functorial
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l 

namespace Mathlib

/-!
# Unbundled lax monoidal functors

## Design considerations
The essential problem I've encountered that requires unbundled functors is
having an existing (non-monoidal) functor `F : C ⥤ D` between monoidal categories,
and wanting to assert that it has an extension to a lax monoidal functor.

The two options seem to be
1. Construct a separate `F' : lax_monoidal_functor C D`,
   and assert `F'.to_functor ≅ F`.
2. Introduce unbundled functors and unbundled lax monoidal functors,
   and construct `lax_monoidal F.obj`, then construct `F' := lax_monoidal_functor.of F.obj`.

Both have costs, but as for option 2. the cost is in library design,
while in option 1. the cost is users having to carry around additional isomorphisms forever,
I wanted to introduce unbundled functors.

TODO:
later, we may want to do this for strong monoidal functors as well,
but the immediate application, for enriched categories, only requires this notion.
-/

namespace category_theory


/-- An unbundled description of lax monoidal functors. -/
-- Perhaps in the future we'll redefine `lax_monoidal_functor` in terms of this,

-- but that isn't the immediate plan.

-- unit morphism

class lax_monoidal {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : C → D) [functorial F] 
where
  ε : 𝟙_ ⟶ F 𝟙_
  μ : (X Y : C) → F X ⊗ F Y ⟶ F (X ⊗ Y)
  μ_natural' : autoParam (∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), (map F f ⊗ map F g) ≫ μ Y Y' = μ X X' ≫ map F (f ⊗ g))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  associativity' : autoParam (∀ (X Y Z : C), (μ X Y ⊗ 𝟙) ≫ μ (X ⊗ Y) Z ≫ map F (iso.hom α_) = iso.hom α_ ≫ (𝟙 ⊗ μ Y Z) ≫ μ X (Y ⊗ Z))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  left_unitality' : autoParam (∀ (X : C), iso.hom λ_ = (ε ⊗ 𝟙) ≫ μ 𝟙_ X ≫ map F (iso.hom λ_))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right_unitality' : autoParam (∀ (X : C), iso.hom ρ_ = (𝟙 ⊗ ε) ≫ μ X 𝟙_ ≫ map F (iso.hom ρ_))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- tensorator

-- associativity of the tensorator

-- unitality

@[simp] theorem lax_monoidal.μ_natural {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] {F : C → D} [functorial F] [c : lax_monoidal F] {X : C} {Y : C} {X' : C} {Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : (map F f ⊗ map F g) ≫ lax_monoidal.μ F Y Y' = lax_monoidal.μ F X X' ≫ map F (f ⊗ g) := sorry

theorem lax_monoidal.left_unitality {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] {F : C → D} [functorial F] [c : lax_monoidal F] (X : C) : iso.hom λ_ = (lax_monoidal.ε F ⊗ 𝟙) ≫ lax_monoidal.μ F 𝟙_ X ≫ map F (iso.hom λ_) := sorry

-- The unitality axioms cannot be used as simp lemmas because they require

theorem lax_monoidal.right_unitality {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] {F : C → D} [functorial F] [c : lax_monoidal F] (X : C) : iso.hom ρ_ = (𝟙 ⊗ lax_monoidal.ε F) ≫ lax_monoidal.μ F X 𝟙_ ≫ map F (iso.hom ρ_) := sorry

-- higher-order matching to figure out the `F` and `X` from `F X`.

@[simp] theorem lax_monoidal.associativity {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] {F : C → D} [functorial F] [c : lax_monoidal F] (X : C) (Y : C) (Z : C) : (lax_monoidal.μ F X Y ⊗ 𝟙) ≫ lax_monoidal.μ F (X ⊗ Y) Z ≫ map F (iso.hom α_) =
  iso.hom α_ ≫ (𝟙 ⊗ lax_monoidal.μ F Y Z) ≫ lax_monoidal.μ F X (Y ⊗ Z) := sorry

namespace lax_monoidal_functor


/--
Construct a bundled `lax_monoidal_functor` from the object level function
and `functorial` and `lax_monoidal` typeclasses.
-/
@[simp] theorem of_μ {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : C → D) [I₁ : functorial F] [I₂ : lax_monoidal F] (X : C) (Y : C) : μ (of F) X Y = lax_monoidal.μ F X Y :=
  Eq.refl (μ (of F) X Y)

end lax_monoidal_functor


protected instance lax_monoidal_functor.obj.lax_monoidal {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂} [category D] [monoidal_category D] (F : lax_monoidal_functor C D) : lax_monoidal (functor.obj (lax_monoidal_functor.to_functor F)) :=
  lax_monoidal.mk (lax_monoidal_functor.ε F) (lax_monoidal_functor.μ F)

protected instance lax_monoidal_id {C : Type u₁} [category C] [monoidal_category C] : lax_monoidal id :=
  lax_monoidal.mk 𝟙 fun (X Y : C) => 𝟙

