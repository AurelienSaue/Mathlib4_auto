/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.abel
import Mathlib.category_theory.limits.shapes.biproducts
import Mathlib.category_theory.preadditive.default
import PostPort

universes u v 

namespace Mathlib

/-!
# Basic facts about morphisms between biproducts in preadditive categories.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

The remaining lemmas hold in any preadditive category.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.
-/

namespace category_theory


/--
If
```
(f 0)
(0 g)
```
is invertible, then `f` is invertible.
-/
def is_iso_left_of_is_iso_biprod_map {C : Type u} [category C] [limits.has_zero_morphisms C] [limits.has_binary_biproducts C] {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (limits.biprod.map f g)] : is_iso f :=
  is_iso.mk (limits.biprod.inl ≫ inv (limits.biprod.map f g) ≫ limits.biprod.fst)

/--
If
```
(f 0)
(0 g)
```
is invertible, then `g` is invertible.
-/
def is_iso_right_of_is_iso_biprod_map {C : Type u} [category C] [limits.has_zero_morphisms C] [limits.has_binary_biproducts C] {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [is_iso (limits.biprod.map f g)] : is_iso g :=
  let _inst : is_iso (limits.biprod.map g f) := eq.mpr sorry is_iso.comp_is_iso;
  is_iso_left_of_is_iso_biprod_map g f

/--
The "matrix" morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` with specified components.
-/
def biprod.of_components {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂ :=
  limits.biprod.fst ≫ f₁₁ ≫ limits.biprod.inl + limits.biprod.fst ≫ f₁₂ ≫ limits.biprod.inr +
      limits.biprod.snd ≫ f₂₁ ≫ limits.biprod.inl +
    limits.biprod.snd ≫ f₂₂ ≫ limits.biprod.inr

@[simp] theorem biprod.inl_of_components {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) : limits.biprod.inl ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ = f₁₁ ≫ limits.biprod.inl + f₁₂ ≫ limits.biprod.inr := sorry

@[simp] theorem biprod.inr_of_components {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) : limits.biprod.inr ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ = f₂₁ ≫ limits.biprod.inl + f₂₂ ≫ limits.biprod.inr := sorry

@[simp] theorem biprod.of_components_fst {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) : biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ limits.biprod.fst = limits.biprod.fst ≫ f₁₁ + limits.biprod.snd ≫ f₂₁ := sorry

@[simp] theorem biprod.of_components_snd {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) : biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ limits.biprod.snd = limits.biprod.fst ≫ f₁₂ + limits.biprod.snd ≫ f₂₂ := sorry

@[simp] theorem biprod.of_components_eq {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) : biprod.of_components (limits.biprod.inl ≫ f ≫ limits.biprod.fst) (limits.biprod.inl ≫ f ≫ limits.biprod.snd)
    (limits.biprod.inr ≫ f ≫ limits.biprod.fst) (limits.biprod.inr ≫ f ≫ limits.biprod.snd) =
  f := sorry

@[simp] theorem biprod.of_components_comp {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} {Z₁ : C} {Z₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) (g₁₁ : Y₁ ⟶ Z₁) (g₁₂ : Y₁ ⟶ Z₂) (g₂₁ : Y₂ ⟶ Z₁) (g₂₂ : Y₂ ⟶ Z₂) : biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ biprod.of_components g₁₁ g₁₂ g₂₁ g₂₂ =
  biprod.of_components (f₁₁ ≫ g₁₁ + f₁₂ ≫ g₂₁) (f₁₁ ≫ g₁₂ + f₁₂ ≫ g₂₂) (f₂₁ ≫ g₁₁ + f₂₂ ≫ g₂₁) (f₂₁ ≫ g₁₂ + f₂₂ ≫ g₂₂) := sorry

/--
The unipotent upper triangular matrix
```
(1 r)
(0 1)
```
as an isomorphism.
-/
@[simp] theorem biprod.unipotent_upper_hom {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} (r : X₁ ⟶ X₂) : iso.hom (biprod.unipotent_upper r) = biprod.of_components 𝟙 r 0 𝟙 :=
  Eq.refl (iso.hom (biprod.unipotent_upper r))

/--
The unipotent lower triangular matrix
```
(1 0)
(r 1)
```
as an isomorphism.
-/
@[simp] theorem biprod.unipotent_lower_hom {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} (r : X₂ ⟶ X₁) : iso.hom (biprod.unipotent_lower r) = biprod.of_components 𝟙 0 r 𝟙 :=
  Eq.refl (iso.hom (biprod.unipotent_lower r))

/--
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.

(This is the version of `biprod.gaussian` written in terms of components.)
-/
def biprod.gaussian' {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) [is_iso f₁₁] : psigma
  fun (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) =>
    psigma
      fun (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) =>
        psigma
          fun (g₂₂ : X₂ ⟶ Y₂) =>
            iso.hom L ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ iso.hom R = limits.biprod.map f₁₁ g₂₂ :=
  psigma.mk (biprod.unipotent_lower (-f₂₁ ≫ inv f₁₁))
    (psigma.mk (biprod.unipotent_upper (-inv f₁₁ ≫ f₁₂)) (psigma.mk (f₂₂ - f₂₁ ≫ inv f₁₁ ≫ f₁₂) sorry))

/--
If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
via Gaussian elimination.
-/
def biprod.gaussian {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f : X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂) [is_iso (limits.biprod.inl ≫ f ≫ limits.biprod.fst)] : psigma
  fun (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) =>
    psigma
      fun (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) =>
        psigma
          fun (g₂₂ : X₂ ⟶ Y₂) =>
            iso.hom L ≫ f ≫ iso.hom R = limits.biprod.map (limits.biprod.inl ≫ f ≫ limits.biprod.fst) g₂₂ :=
  let this :
    psigma
      fun (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂) =>
        psigma
          fun (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) =>
            psigma
              fun (g₂₂ : X₂ ⟶ Y₂) =>
                iso.hom L ≫
                    biprod.of_components (limits.biprod.inl ≫ f ≫ limits.biprod.fst)
                        (limits.biprod.inl ≫ f ≫ limits.biprod.snd) (limits.biprod.inr ≫ f ≫ limits.biprod.fst)
                        (limits.biprod.inr ≫ f ≫ limits.biprod.snd) ≫
                      iso.hom R =
                  limits.biprod.map (limits.biprod.inl ≫ f ≫ limits.biprod.fst) g₂₂ :=
    biprod.gaussian' (limits.biprod.inl ≫ f ≫ limits.biprod.fst) (limits.biprod.inl ≫ f ≫ limits.biprod.snd)
      (limits.biprod.inr ≫ f ≫ limits.biprod.fst) (limits.biprod.inr ≫ f ≫ limits.biprod.snd);
  eq.mpr sorry (eq.mp sorry this)

/--
If `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` via a two-by-two matrix whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim' {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f₁₁ : X₁ ⟶ Y₁) (f₁₂ : X₁ ⟶ Y₂) (f₂₁ : X₂ ⟶ Y₁) (f₂₂ : X₂ ⟶ Y₂) [is_iso f₁₁] [is_iso (biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂)] : X₂ ≅ Y₂ :=
  psigma.cases_on (biprod.gaussian' f₁₁ f₁₂ f₂₁ f₂₂)
    fun (L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂)
      (snd :
      psigma
        fun (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂) =>
          psigma
            fun (g₂₂ : X₂ ⟶ Y₂) =>
              iso.hom L ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ iso.hom R = limits.biprod.map f₁₁ g₂₂) =>
      psigma.cases_on snd
        fun (R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂)
          (snd_snd :
          psigma
            fun (g₂₂ : X₂ ⟶ Y₂) =>
              iso.hom L ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ iso.hom R = limits.biprod.map f₁₁ g₂₂) =>
          psigma.cases_on snd_snd
            fun (g : X₂ ⟶ Y₂)
              (w : iso.hom L ≫ biprod.of_components f₁₁ f₁₂ f₂₁ f₂₂ ≫ iso.hom R = limits.biprod.map f₁₁ g) =>
              let _inst : is_iso (limits.biprod.map f₁₁ g) := eq.mpr sorry is_iso.comp_is_iso;
              let _inst_6 : is_iso g := is_iso_right_of_is_iso_biprod_map f₁₁ g;
              as_iso g

/--
If `f` is an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
then we can construct an isomorphism `X₂ ≅ Y₂`, via Gaussian elimination.
-/
def biprod.iso_elim {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {X₁ : C} {X₂ : C} {Y₁ : C} {Y₂ : C} (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂) [is_iso (limits.biprod.inl ≫ iso.hom f ≫ limits.biprod.fst)] : X₂ ≅ Y₂ :=
  let _inst :
    is_iso
      (biprod.of_components (limits.biprod.inl ≫ iso.hom f ≫ limits.biprod.fst)
        (limits.biprod.inl ≫ iso.hom f ≫ limits.biprod.snd) (limits.biprod.inr ≫ iso.hom f ≫ limits.biprod.fst)
        (limits.biprod.inr ≫ iso.hom f ≫ limits.biprod.snd)) :=
    eq.mpr sorry (is_iso.of_iso f);
  biprod.iso_elim' (limits.biprod.inl ≫ iso.hom f ≫ limits.biprod.fst) (limits.biprod.inl ≫ iso.hom f ≫ limits.biprod.snd)
    (limits.biprod.inr ≫ iso.hom f ≫ limits.biprod.fst) (limits.biprod.inr ≫ iso.hom f ≫ limits.biprod.snd)

theorem biprod.column_nonzero_of_iso {C : Type u} [category C] [preadditive C] [limits.has_binary_biproducts C] {W : C} {X : C} {Y : C} {Z : C} (f : W ⊞ X ⟶ Y ⊞ Z) [is_iso f] : 𝟙 = 0 ∨ limits.biprod.inl ≫ f ≫ limits.biprod.fst ≠ 0 ∨ limits.biprod.inl ≫ f ≫ limits.biprod.snd ≠ 0 := sorry

theorem biproduct.column_nonzero_of_iso' {C : Type u} [category C] [preadditive C] {σ : Type v} {τ : Type v} [DecidableEq σ] [DecidableEq τ] [fintype τ] {S : σ → C} [limits.has_biproduct S] {T : τ → C} [limits.has_biproduct T] (s : σ) (f : ⨁ S ⟶ ⨁ T) [is_iso f] : (∀ (t : τ), limits.biproduct.ι S s ≫ f ≫ limits.biproduct.π T t = 0) → 𝟙 = 0 := sorry

/--
If `f : ⨁ S ⟶ ⨁ T` is an isomorphism, and `s` is a non-trivial summand of the source,
then there is some `t` in the target so that the `s, t` matrix entry of `f` is nonzero.
-/
def biproduct.column_nonzero_of_iso {C : Type u} [category C] [preadditive C] {σ : Type v} {τ : Type v} [DecidableEq σ] [DecidableEq τ] [fintype τ] {S : σ → C} [limits.has_biproduct S] {T : τ → C} [limits.has_biproduct T] (s : σ) (nz : 𝟙 ≠ 0) [(t : τ) → DecidableEq (S s ⟶ T t)] (f : ⨁ S ⟶ ⨁ T) [is_iso f] : trunc (psigma fun (t : τ) => limits.biproduct.ι S s ≫ f ≫ limits.biproduct.π T t ≠ 0) :=
  trunc_sigma_of_exists sorry

