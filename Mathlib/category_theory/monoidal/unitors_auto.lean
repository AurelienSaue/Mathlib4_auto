/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.category
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# The two morphisms `λ_ (𝟙_ C)` and `ρ_ (𝟙_ C)` from `𝟙_ C ⊗ 𝟙_ C` to `𝟙_ C` are equal.

This is suprisingly difficult to prove directly from the usual axioms for a monoidal category!

This proof follows the diagram given at
https://people.math.osu.edu/penneys.2/QS2019/VicaryHandout.pdf

It should be a consequence of the coherence theorem for monoidal categories
(although quite possibly it is a necessary building block of any proof).
-/

namespace category_theory.monoidal_category


namespace unitors_equal


theorem cells_1_2 {C : Type u} [category C] [monoidal_category C] :
    iso.hom ρ_ = iso.inv λ_ ≫ (𝟙 ⊗ iso.hom ρ_) ≫ iso.hom λ_ :=
  sorry

theorem cells_4 {C : Type u} [category C] [monoidal_category C] :
    iso.inv λ_ ≫ (𝟙 ⊗ iso.hom λ_) = iso.hom λ_ ≫ iso.inv λ_ :=
  sorry

theorem cells_4' {C : Type u} [category C] [monoidal_category C] :
    iso.inv λ_ = iso.hom λ_ ≫ iso.inv λ_ ≫ (𝟙 ⊗ iso.inv λ_) :=
  sorry

theorem cells_3_4 {C : Type u} [category C] [monoidal_category C] : iso.inv λ_ = 𝟙 ⊗ iso.inv λ_ :=
  sorry

theorem cells_1_4 {C : Type u} [category C] [monoidal_category C] :
    iso.hom ρ_ = (𝟙 ⊗ iso.inv λ_) ≫ (𝟙 ⊗ iso.hom ρ_) ≫ iso.hom λ_ :=
  sorry

theorem cells_6 {C : Type u} [category C] [monoidal_category C] :
    (iso.inv ρ_ ⊗ 𝟙) ≫ iso.hom ρ_ = iso.hom ρ_ ≫ iso.inv ρ_ :=
  sorry

theorem cells_6' {C : Type u} [category C] [monoidal_category C] :
    iso.inv ρ_ ⊗ 𝟙 = iso.hom ρ_ ≫ iso.inv ρ_ ≫ iso.inv ρ_ :=
  sorry

theorem cells_5_6 {C : Type u} [category C] [monoidal_category C] : iso.inv ρ_ ⊗ 𝟙 = iso.inv ρ_ :=
  sorry

theorem cells_7 {C : Type u} [category C] [monoidal_category C] :
    𝟙 ⊗ iso.inv λ_ = (iso.inv ρ_ ⊗ 𝟙) ≫ iso.hom α_ :=
  sorry

theorem cells_1_7 {C : Type u} [category C] [monoidal_category C] :
    iso.hom ρ_ = iso.inv ρ_ ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.hom ρ_) ≫ iso.hom λ_ :=
  sorry

theorem cells_8 {C : Type u} [category C] [monoidal_category C] :
    iso.hom α_ = iso.inv ρ_ ≫ (iso.hom α_ ⊗ 𝟙) ≫ iso.hom ρ_ :=
  sorry

theorem cells_14 {C : Type u} [category C] [monoidal_category C] :
    iso.inv ρ_ ≫ iso.inv ρ_ = iso.inv ρ_ ≫ (iso.inv ρ_ ⊗ 𝟙) :=
  sorry

theorem cells_9 {C : Type u} [category C] [monoidal_category C] :
    iso.hom α_ ⊗ 𝟙 = iso.hom α_ ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.inv α_) ≫ iso.inv α_ :=
  sorry

theorem cells_10_13 {C : Type u} [category C] [monoidal_category C] :
    (iso.inv ρ_ ⊗ 𝟙) ≫ iso.hom α_ ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.inv α_) ≫ iso.inv α_ =
        (𝟙 ⊗ iso.inv ρ_) ⊗ 𝟙 :=
  sorry

theorem cells_9_13 {C : Type u} [category C] [monoidal_category C] :
    (iso.inv ρ_ ⊗ 𝟙) ≫ (iso.hom α_ ⊗ 𝟙) = (𝟙 ⊗ iso.inv ρ_) ⊗ 𝟙 :=
  sorry

theorem cells_15 {C : Type u} [category C] [monoidal_category C] :
    iso.inv ρ_ ≫ ((𝟙 ⊗ iso.inv ρ_) ⊗ 𝟙) ≫ iso.hom ρ_ ≫ (𝟙 ⊗ iso.hom ρ_) = 𝟙 :=
  sorry

end unitors_equal


theorem unitors_equal {C : Type u} [category C] [monoidal_category C] : iso.hom λ_ = iso.hom ρ_ :=
  sorry

end Mathlib