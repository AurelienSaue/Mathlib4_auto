/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.category_theory.is_connected
import PostPort

universes v₁ u_1 u₂ v₂ 

namespace Mathlib

/-!
# Connected limits

A connected limit is a limit whose shape is a connected category.

We give examples of connected categories, and prove that the functor given
by `(X × -)` preserves any connected limit. That is, any limit of shape `J`
where `J` is a connected category is preserved by the functor `(X × -)`.
-/

namespace category_theory


protected instance wide_pullback_shape_connected (J : Type v₁) : is_connected (limits.wide_pullback_shape J) :=
  is_connected.of_induct
    fun (p : set (limits.wide_pullback_shape J)) (hp : none ∈ p)
      (t : ∀ {j₁ j₂ : limits.wide_pullback_shape J}, (j₁ ⟶ j₂) → (j₁ ∈ p ↔ j₂ ∈ p)) (j : limits.wide_pullback_shape J) =>
      option.cases_on j hp
        fun (j : J) =>
          eq.mpr (id (Eq._oldrec (Eq.refl (some j ∈ p)) (propext (t (limits.wide_pullback_shape.hom.term j))))) hp

protected instance wide_pushout_shape_connected (J : Type v₁) : is_connected (limits.wide_pushout_shape J) :=
  is_connected.of_induct
    fun (p : set (limits.wide_pushout_shape J)) (hp : none ∈ p)
      (t : ∀ {j₁ j₂ : limits.wide_pushout_shape J}, (j₁ ⟶ j₂) → (j₁ ∈ p ↔ j₂ ∈ p)) (j : limits.wide_pushout_shape J) =>
      option.cases_on j hp
        fun (j : J) =>
          eq.mpr (id (Eq._oldrec (Eq.refl (some j ∈ p)) (Eq.symm (propext (t (limits.wide_pushout_shape.hom.init j))))))
            hp

protected instance parallel_pair_inhabited : Inhabited limits.walking_parallel_pair :=
  { default := limits.walking_parallel_pair.one }

protected instance parallel_pair_connected : is_connected limits.walking_parallel_pair :=
  is_connected.of_induct
    fun (p : set limits.walking_parallel_pair) (ᾰ : limits.walking_parallel_pair.one ∈ p)
      (t : ∀ {j₁ j₂ : limits.walking_parallel_pair}, (j₁ ⟶ j₂) → (j₁ ∈ p ↔ j₂ ∈ p)) (j : limits.walking_parallel_pair) =>
      limits.walking_parallel_pair.cases_on j
        (eq.mpr
          (id
            (Eq._oldrec (Eq.refl (limits.walking_parallel_pair.zero ∈ p))
              (propext (t limits.walking_parallel_pair_hom.left))))
          ᾰ)
        ᾰ

namespace prod_preserves_connected_limits


/-- (Impl). The obvious natural transformation from (X × K -) to K. -/
def γ₂ {C : Type u₂} [category C] [limits.has_binary_products C] {J : Type v₂} [small_category J] {K : J ⥤ C} (X : C) : K ⋙ functor.obj limits.prod.functor X ⟶ K :=
  nat_trans.mk fun (Y : J) => limits.prod.snd

/-- (Impl). The obvious natural transformation from (X × K -) to X -/
@[simp] theorem γ₁_app {C : Type u₂} [category C] [limits.has_binary_products C] {J : Type v₂} [small_category J] {K : J ⥤ C} (X : C) (Y : J) : nat_trans.app (γ₁ X) Y = limits.prod.fst :=
  Eq.refl (nat_trans.app (γ₁ X) Y)

/-- (Impl). Given a cone for (X × K -), produce a cone for K using the natural transformation `γ₂` -/
@[simp] theorem forget_cone_π {C : Type u₂} [category C] [limits.has_binary_products C] {J : Type v₂} [small_category J] {X : C} {K : J ⥤ C} (s : limits.cone (K ⋙ functor.obj limits.prod.functor X)) : limits.cone.π (forget_cone s) = limits.cone.π s ≫ γ₂ X :=
  Eq.refl (limits.cone.π (forget_cone s))

end prod_preserves_connected_limits


/--
The functor `(X × -)` preserves any connected limit.
Note that this functor does not preserve the two most obvious disconnected limits - that is,
`(X × -)` does not preserve products or terminal object, eg `(X ⨯ A) ⨯ (X ⨯ B)` is not isomorphic to
`X ⨯ (A ⨯ B)` and `X ⨯ 1` is not isomorphic to `1`.
-/
def prod_preserves_connected_limits {C : Type u₂} [category C] [limits.has_binary_products C] {J : Type v₂} [small_category J] [is_connected J] (X : C) : limits.preserves_limits_of_shape J (functor.obj limits.prod.functor X) :=
  limits.preserves_limits_of_shape.mk
    fun (K : J ⥤ C) =>
      limits.preserves_limit.mk
        fun (c : limits.cone K) (l : limits.is_limit c) =>
          limits.is_limit.mk
            fun (s : limits.cone (K ⋙ functor.obj limits.prod.functor X)) =>
              limits.prod.lift (nat_trans.app (limits.cone.π s) (classical.arbitrary J) ≫ limits.prod.fst)
                (limits.is_limit.lift l sorry)

