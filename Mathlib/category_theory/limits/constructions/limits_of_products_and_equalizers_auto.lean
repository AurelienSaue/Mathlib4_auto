/-
-- Copyright (c) 2020 Bhavik Mehta. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Bhavik Mehta, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.category_theory.limits.preserves.shapes.products
import Mathlib.category_theory.limits.preserves.shapes.equalizers
import PostPort

universes u v u₂ 

namespace Mathlib

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

namespace category_theory.limits


-- We hide the "implementation details" inside a namespace

namespace has_limit_of_has_products_of_has_equalizers


/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
def build_limit {C : Type u} [category C] {J : Type v} [small_category J] {F : J ⥤ C} {c₁ : fan (functor.obj F)} {c₂ : fan fun (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p) => functor.obj F (prod.snd (sigma.fst f))} (s : cone.X c₁ ⟶ cone.X c₂) (t : cone.X c₁ ⟶ cone.X c₂) (hs : ∀ (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p),
  s ≫ nat_trans.app (cone.π c₂) f = nat_trans.app (cone.π c₁) (prod.fst (sigma.fst f)) ≫ functor.map F (sigma.snd f)) (ht : ∀ (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p),
  t ≫ nat_trans.app (cone.π c₂) f = nat_trans.app (cone.π c₁) (prod.snd (sigma.fst f))) (i : fork s t) : cone F :=
  cone.mk (cone.X i) (nat_trans.mk fun (j : J) => fork.ι i ≫ nat_trans.app (cone.π c₁) j)

/--
(Implementation) Show the cone constructed in `build_limit` is limiting, provided the cones used in
its construction are.
-/
def build_is_limit {C : Type u} [category C] {J : Type v} [small_category J] {F : J ⥤ C} {c₁ : fan (functor.obj F)} {c₂ : fan fun (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p) => functor.obj F (prod.snd (sigma.fst f))} (s : cone.X c₁ ⟶ cone.X c₂) (t : cone.X c₁ ⟶ cone.X c₂) (hs : ∀ (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p),
  s ≫ nat_trans.app (cone.π c₂) f = nat_trans.app (cone.π c₁) (prod.fst (sigma.fst f)) ≫ functor.map F (sigma.snd f)) (ht : ∀ (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p),
  t ≫ nat_trans.app (cone.π c₂) f = nat_trans.app (cone.π c₁) (prod.snd (sigma.fst f))) {i : fork s t} (t₁ : is_limit c₁) (t₂ : is_limit c₂) (hi : is_limit i) : is_limit (build_limit s t hs ht i) :=
  is_limit.mk
    fun (q : cone F) =>
      is_limit.lift hi (fork.of_ι (is_limit.lift t₁ (fan.mk (cone.X q) fun (j : J) => nat_trans.app (cone.π q) j)) sorry)

end has_limit_of_has_products_of_has_equalizers


/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
theorem has_limit_of_equalizer_and_product {C : Type u} [category C] {J : Type v} [small_category J] (F : J ⥤ C) [has_limit (discrete.functor (functor.obj F))] [has_limit
  (discrete.functor
    fun (f : sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p) => functor.obj F (prod.snd (sigma.fst f)))] [has_equalizers C] : has_limit F := sorry

/--
Any category with products and equalizers has all limits.

See https://stacks.math.columbia.edu/tag/002N.
-/
theorem limits_from_equalizers_and_products {C : Type u} [category C] [has_products C] [has_equalizers C] : has_limits C :=
  has_limits.mk
    fun (J : Type v) (𝒥 : small_category J) =>
      has_limits_of_shape.mk fun (F : J ⥤ C) => has_limit_of_equalizer_and_product F

/--
Any category with finite products and equalizers has all finite limits.

See https://stacks.math.columbia.edu/tag/002O.
-/
theorem finite_limits_from_equalizers_and_finite_products {C : Type u} [category C] [has_finite_products C] [has_equalizers C] : has_finite_limits C :=
  fun (J : Type v) (_x : small_category J) (_x_1 : fin_category J) =>
    has_limits_of_shape.mk fun (F : J ⥤ C) => has_limit_of_equalizer_and_product F

/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
def preserves_limit_of_preserves_equalizers_and_product {C : Type u} [category C] {J : Type v} [small_category J] {D : Type u₂} [category D] [has_limits_of_shape (discrete J) C] [has_limits_of_shape (discrete (sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p)) C] [has_equalizers C] (G : C ⥤ D) [preserves_limits_of_shape walking_parallel_pair G] [preserves_limits_of_shape (discrete J) G] [preserves_limits_of_shape (discrete (sigma fun (p : J × J) => prod.fst p ⟶ prod.snd p)) G] : preserves_limits_of_shape J G := sorry

/-- If G preserves equalizers and finite products, it preserves finite limits. -/
def preserves_finite_limits_of_preserves_equalizers_and_finite_products {C : Type u} [category C] {D : Type u₂} [category D] [has_equalizers C] [has_finite_products C] (G : C ⥤ D) [preserves_limits_of_shape walking_parallel_pair G] [(J : Type v) → [_inst_8 : fintype J] → preserves_limits_of_shape (discrete J) G] (J : Type v) [small_category J] [fin_category J] : preserves_limits_of_shape J G :=
  preserves_limit_of_preserves_equalizers_and_product G

/-- If G preserves equalizers and products, it preserves all limits. -/
def preserves_limits_of_preserves_equalizers_and_products {C : Type u} [category C] {D : Type u₂} [category D] [has_equalizers C] [has_products C] (G : C ⥤ D) [preserves_limits_of_shape walking_parallel_pair G] [(J : Type v) → preserves_limits_of_shape (discrete J) G] : preserves_limits G :=
  preserves_limits.mk fun (J : Type v) (𝒥 : small_category J) => preserves_limit_of_preserves_equalizers_and_product G

