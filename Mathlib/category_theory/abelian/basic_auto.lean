/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.limits.constructions.pullbacks
import Mathlib.category_theory.limits.shapes.biproducts
import Mathlib.category_theory.limits.shapes.images
import Mathlib.category_theory.abelian.non_preadditive
import PostPort

universes v u l 

namespace Mathlib

/-!
# Abelian categories

This file contains the definition and basic properties of abelian categories.

There are many definitions of abelian category. Our definition is as follows:
A category is called abelian if it is preadditive,
has a finite products, kernels and cokernels,
and if every monomorphism and epimorphism is normal.

It should be noted that if we also assume coproducts, then preadditivity is
actually a consequence of the other properties, as we show in
`non_preadditive_abelian.lean`. However, this fact is of little practical
relevance, since essentially all interesting abelian categories come with a
preadditive structure. In this way, by requiring preadditivity, we allow the
user to pass in the preadditive structure the specific category they are
working with has natively.

## Main definitions

* `abelian` is the type class indicating that a category is abelian. It extends `preadditive`.
* `abelian.image f` is `kernel (cokernel.π f)`, and
* `abelian.coimage f` is `cokernel (kernel.ι f)`.

## Main results

* In an abelian category, mono + epi = iso.
* If `f : X ⟶ Y`, then the map `factor_thru_image f : X ⟶ image f` is an epimorphism, and the map
  `factor_thru_coimage f : coimage f ⟶ Y` is a monomorphism.
* Factoring through the image and coimage is a strong epi-mono factorisation. This means that
  * every abelian category has images. We instantiated this in such a way that `abelian.image f` is
    definitionally equal to `limits.image f`, and
  * there is a canonical isomorphism `coimage_iso_image : coimage f ≅ image f` such that
    `coimage.π f ≫ (coimage_iso_image f).hom ≫ image.ι f = f`. The lemma stating this is called
    `full_image_factorisation`.
* Every epimorphism is a cokernel of its kernel. Every monomorphism is a kernel of its cokernel.
* The pullback of an epimorphism is an epimorphism. The pushout of a monomorphism is a monomorphism.
  (This is not to be confused with the fact that the pullback of a monomorphism is a monomorphism,
  which is true in any category).

## Implementation notes

The typeclass `abelian` does not extend `non_preadditive_abelian`,
to avoid having to deal with comparing the two `has_zero_morphisms` instances
(one from `preadditive` in `abelian`, and the other a field of `non_preadditive_abelian`).
As a consequence, at the beginning of this file we trivially build
a `non_preadditive_abelian` instance from an `abelian` instance,
and use this to restate a number of theorems,
in each case just reusing the proof from `non_preadditive_abelian.lean`.

We don't show this yet, but abelian categories are finitely complete and finitely cocomplete.
However, the limits we can construct at this level of generality will most likely be less nice than
the ones that can be created in specific applications. For this reason, we adopt the following
convention:

* If the statement of a theorem involves limits, the existence of these limits should be made an
  explicit typeclass parameter.
* If a limit only appears in a proof, but not in the statement of a theorem, the limit should not
  be a typeclass parameter, but instead be created using `abelian.has_pullbacks` or a similar
  definition.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* [P. Aluffi, *Algebra: Chaper 0*][aluffi2016]

-/

namespace category_theory


/--
A (preadditive) category `C` is called abelian if it has all finite products,
all kernels and cokernels, and if every monomorphism is the kernel of some morphism
and every epimorphism is the cokernel of some morphism.

(This definition implies the existence of zero objects:
finite products give a terminal object, and in a preadditive category
any terminal object is a zero object.)
-/
class abelian (C : Type u) [category C] 
extends preadditive C
where
  has_finite_products : limits.has_finite_products C
  has_kernels : limits.has_kernels C
  has_cokernels : limits.has_cokernels C
  normal_mono : {X Y : C} → (f : X ⟶ Y) → [_inst_2 : mono f] → normal_mono f
  normal_epi : {X Y : C} → (f : X ⟶ Y) → [_inst_2 : epi f] → normal_epi f

end category_theory


namespace category_theory.abelian


/-- An abelian category has finite biproducts. -/
theorem has_finite_biproducts {C : Type u} [category C] [abelian C] : limits.has_finite_biproducts C :=
  limits.has_finite_biproducts.of_has_finite_products

/-- Every abelian category is, in particular, `non_preadditive_abelian`. -/
def non_preadditive_abelian {C : Type u} [category C] [abelian C] : non_preadditive_abelian C :=
  non_preadditive_abelian.mk normal_mono normal_epi

/-- In an abelian category, every epimorphism is strong. -/
theorem strong_epi_of_epi {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : strong_epi f :=
  category_theory.strong_epi_of_regular_epi f

/-- In an abelian category, a monomorphism which is also an epimorphism is an isomorphism. -/
def is_iso_of_mono_of_epi {C : Type u} [category C] [abelian C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] [epi f] : is_iso f :=
  is_iso_of_mono_of_strong_epi f

theorem mono_of_zero_kernel {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (R : C) (l : limits.is_limit
  (limits.kernel_fork.of_ι 0
    ((fun (this : 0 ≫ f = 0) => this)
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : R ⟶ Q) (e_1 : a = a_1) (ᾰ ᾰ_1 : R ⟶ Q) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (0 ≫ f) 0 limits.zero_comp 0 0 (Eq.refl 0))
            (propext (eq_self_iff_true 0))))
        trivial)))) : mono f :=
  non_preadditive_abelian.mono_of_zero_kernel f R l

theorem mono_of_kernel_ι_eq_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (h : limits.kernel.ι f = 0) : mono f :=
  preadditive.mono_of_kernel_zero h

theorem epi_of_zero_cokernel {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (R : C) (l : limits.is_colimit
  (limits.cokernel_cofork.of_π 0
    ((fun (this : f ≫ 0 = 0) => this)
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : P ⟶ R) (e_1 : a = a_1) (ᾰ ᾰ_1 : P ⟶ R) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (f ≫ 0) 0 limits.comp_zero 0 0 (Eq.refl 0))
            (propext (eq_self_iff_true 0))))
        trivial)))) : epi f :=
  non_preadditive_abelian.epi_of_zero_cokernel f R l

theorem epi_of_cokernel_π_eq_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) (h : limits.cokernel.π f = 0) : epi f := sorry

namespace images


/-- The kernel of the cokernel of `f` is called the image of `f`. -/
protected def image {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : C :=
  limits.kernel (limits.cokernel.π f)

/-- The inclusion of the image into the codomain. -/
protected def image.ι {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : images.image f ⟶ Q :=
  limits.kernel.ι (limits.cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected def factor_thru_image {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : P ⟶ images.image f :=
  limits.kernel.lift (limits.cokernel.π f) f sorry

/-- `f` factors through its image via the canonical morphism `p`. -/
@[simp] theorem image.fac_assoc {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) {X' : C} (f' : Q ⟶ X') : images.factor_thru_image f ≫ image.ι f ≫ f' = f ≫ f' := sorry

/-- The map `p : P ⟶ image f` is an epimorphism -/
protected instance factor_thru_image.category_theory.epi {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : epi (images.factor_thru_image f) :=
  (fun (this : epi (non_preadditive_abelian.factor_thru_image f)) => this)
    (non_preadditive_abelian.factor_thru_image.category_theory.epi f)

theorem image_ι_comp_eq_zero {C : Type u} [category C] [abelian C] {P : C} {Q : C} {f : P ⟶ Q} {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : image.ι f ≫ g = 0 := sorry

protected instance mono_factor_thru_image {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [mono f] : mono (images.factor_thru_image f) :=
  mono_of_mono_fac (image.fac f)

protected instance is_iso_factor_thru_image {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [mono f] : is_iso (images.factor_thru_image f) :=
  is_iso_of_mono_of_epi (images.factor_thru_image f)

/-- Factoring through the image is a strong epi-mono factorisation. -/
@[simp] theorem image_strong_epi_mono_factorisation_to_mono_factorisation_m {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : limits.mono_factorisation.m
    (limits.strong_epi_mono_factorisation.to_mono_factorisation (image_strong_epi_mono_factorisation f)) =
  image.ι f :=
  Eq.refl
    (limits.mono_factorisation.m
      (limits.strong_epi_mono_factorisation.to_mono_factorisation (image_strong_epi_mono_factorisation f)))

end images


namespace coimages


/-- The cokernel of the kernel of `f` is called the coimage of `f`. -/
protected def coimage {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : C :=
  limits.cokernel (limits.kernel.ι f)

/-- The projection onto the coimage. -/
protected def coimage.π {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : P ⟶ coimages.coimage f :=
  limits.cokernel.π (limits.kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected def factor_thru_coimage {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : coimages.coimage f ⟶ Q :=
  limits.cokernel.desc (limits.kernel.ι f) f sorry

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected theorem coimage.fac {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : coimage.π f ≫ coimages.factor_thru_coimage f = f :=
  limits.cokernel.π_desc (limits.kernel.ι f) f (factor_thru_coimage._proof_1 f)

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
protected instance factor_thru_coimage.category_theory.mono {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : mono (coimages.factor_thru_coimage f) :=
  (fun (this : mono (non_preadditive_abelian.factor_thru_coimage f)) => this)
    (non_preadditive_abelian.factor_thru_coimage.category_theory.mono f)

protected instance epi_factor_thru_coimage {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : epi (coimages.factor_thru_coimage f) :=
  epi_of_epi_fac (coimage.fac f)

protected instance is_iso_factor_thru_coimage {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : is_iso (coimages.factor_thru_coimage f) :=
  is_iso_of_mono_of_epi (coimages.factor_thru_coimage f)

/-- Factoring through the coimage is a strong epi-mono factorisation. -/
@[simp] theorem coimage_strong_epi_mono_factorisation_to_mono_factorisation_m {C : Type u} [category C] [abelian C] {P : C} {Q : C} (f : P ⟶ Q) : limits.mono_factorisation.m
    (limits.strong_epi_mono_factorisation.to_mono_factorisation (coimage_strong_epi_mono_factorisation f)) =
  coimages.factor_thru_coimage f :=
  Eq.refl
    (limits.mono_factorisation.m
      (limits.strong_epi_mono_factorisation.to_mono_factorisation (coimage_strong_epi_mono_factorisation f)))

end coimages


/-- An abelian category has strong epi-mono factorisations. -/
protected instance category_theory.limits.has_strong_epi_mono_factorisations {C : Type u} [category C] [abelian C] : limits.has_strong_epi_mono_factorisations C :=
  limits.has_strong_epi_mono_factorisations.mk fun (X Y : C) (f : X ⟶ Y) => images.image_strong_epi_mono_factorisation f

/- In particular, this means that it has well-behaved images. -/

/-- There is a canonical isomorphism between the coimage and the image of a morphism. -/
def coimage_iso_image {C : Type u} [category C] [abelian C] {X : C} {Y : C} (f : X ⟶ Y) : coimages.coimage f ≅ images.image f :=
  limits.is_image.iso_ext
    (limits.strong_epi_mono_factorisation.to_mono_is_image (coimages.coimage_strong_epi_mono_factorisation f))
    (limits.strong_epi_mono_factorisation.to_mono_is_image (images.image_strong_epi_mono_factorisation f))

/-- There is a canonical isomorphism between the abelian image and the categorical image of a
    morphism. -/
def image_iso_image {C : Type u} [category C] [abelian C] {X : C} {Y : C} (f : X ⟶ Y) : images.image f ≅ limits.image f :=
  limits.is_image.iso_ext
    (limits.strong_epi_mono_factorisation.to_mono_is_image (images.image_strong_epi_mono_factorisation f))
    (limits.image.is_image f)

/-- There is a canonical isomorphism between the abelian coimage and the categorical image of a
    morphism. -/
def coimage_iso_image' {C : Type u} [category C] [abelian C] {X : C} {Y : C} (f : X ⟶ Y) : coimages.coimage f ≅ limits.image f :=
  limits.is_image.iso_ext
    (limits.strong_epi_mono_factorisation.to_mono_is_image (coimages.coimage_strong_epi_mono_factorisation f))
    (limits.image.is_image f)

theorem full_image_factorisation {C : Type u} [category C] [abelian C] {X : C} {Y : C} (f : X ⟶ Y) : coimages.coimage.π f ≫ iso.hom (coimage_iso_image f) ≫ images.image.ι f = f := sorry

/-- In an abelian category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel {C : Type u} [category C] [abelian C] {X : C} {Y : C} {f : X ⟶ Y} [epi f] (s : limits.fork f 0) (h : limits.is_limit s) : limits.is_colimit (limits.cokernel_cofork.of_π f (epi_is_cokernel_of_kernel._proof_1 s)) :=
  non_preadditive_abelian.epi_is_cokernel_of_kernel s h

/-- In an abelian category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel {C : Type u} [category C] [abelian C] {X : C} {Y : C} {f : X ⟶ Y} [mono f] (s : limits.cofork f 0) (h : limits.is_colimit s) : limits.is_limit (limits.kernel_fork.of_ι f (mono_is_kernel_of_cokernel._proof_1 s)) :=
  non_preadditive_abelian.mono_is_kernel_of_cokernel s h

/-- Any abelian category has pullbacks -/
theorem has_pullbacks {C : Type u} [category C] [abelian C] : limits.has_pullbacks C :=
  limits.has_pullbacks_of_has_binary_products_of_has_equalizers C

/-- Any abelian category has pushouts -/
theorem has_pushouts {C : Type u} [category C] [abelian C] : limits.has_pushouts C :=
  limits.has_pushouts_of_has_binary_coproducts_of_has_coequalizers C

namespace pullback_to_biproduct_is_kernel


/-! This section contains a slightly technical result about pullbacks and biproducts.
    We will need it in the proof that the pullback of an epimorphism is an epimorpism. -/

/-- The canonical map `pullback f g ⟶ X ⊞ Y` -/
def pullback_to_biproduct {C : Type u} [category C] [abelian C] [limits.has_pullbacks C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : limits.pullback f g ⟶ X ⊞ Y :=
  limits.biprod.lift limits.pullback.fst limits.pullback.snd

/-- The canonical map `pullback f g ⟶ X ⊞ Y` induces a kernel cone on the map
    `biproduct X Y ⟶ Z` induced by `f` and `g`. A slightly more intuitive way to think of
    this may be that it induces an equalizer fork on the maps induced by `(f, 0)` and
    `(0, g)`. -/
def pullback_to_biproduct_fork {C : Type u} [category C] [abelian C] [limits.has_pullbacks C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : limits.kernel_fork (limits.biprod.desc f (-g)) :=
  limits.kernel_fork.of_ι (pullback_to_biproduct f g) sorry

/-- The canonical map `pullback f g ⟶ X ⊞ Y` is a kernel of the map induced by
    `(f, -g)`. -/
def is_limit_pullback_to_biproduct {C : Type u} [category C] [abelian C] [limits.has_pullbacks C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : limits.is_limit (pullback_to_biproduct_fork f g) :=
  limits.fork.is_limit.mk (pullback_to_biproduct_fork f g)
    (fun (s : limits.fork (limits.biprod.desc f (-g)) 0) =>
      limits.pullback.lift (limits.fork.ι s ≫ limits.biprod.fst) (limits.fork.ι s ≫ limits.biprod.snd) sorry)
    sorry sorry

end pullback_to_biproduct_is_kernel


namespace biproduct_to_pushout_is_cokernel


/-- The canonical map `Y ⊞ Z ⟶ pushout f g` -/
def biproduct_to_pushout {C : Type u} [category C] [abelian C] [limits.has_pushouts C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : Y ⊞ Z ⟶ limits.pushout f g :=
  limits.biprod.desc limits.pushout.inl limits.pushout.inr

/-- The canonical map `Y ⊞ Z ⟶ pushout f g` induces a cokernel cofork on the map
    `X ⟶ Y ⊞ Z` induced by `f` and `-g`. -/
def biproduct_to_pushout_cofork {C : Type u} [category C] [abelian C] [limits.has_pushouts C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : limits.cokernel_cofork (limits.biprod.lift f (-g)) :=
  limits.cokernel_cofork.of_π (biproduct_to_pushout f g) sorry

/-- The cofork induced by the canonical map `Y ⊞ Z ⟶ pushout f g` is in fact a colimit cokernel
    cofork. -/
def is_colimit_biproduct_to_pushout {C : Type u} [category C] [abelian C] [limits.has_pushouts C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : limits.is_colimit (biproduct_to_pushout_cofork f g) :=
  limits.cofork.is_colimit.mk (biproduct_to_pushout_cofork f g)
    (fun (s : limits.cofork (limits.biprod.lift f (-g)) 0) =>
      limits.pushout.desc (limits.biprod.inl ≫ limits.cofork.π s) (limits.biprod.inr ≫ limits.cofork.π s) sorry)
    sorry sorry

end biproduct_to_pushout_is_cokernel


/-- In an abelian category, the pullback of an epimorphism is an epimorphism.
    Proof from [aluffi2016, IX.2.3], cf. [borceux-vol2, 1.7.6] -/
-- It will suffice to consider some morphism e : Y ⟶ R such that

protected instance epi_pullback_of_epi_f {C : Type u} [category C] [abelian C] [limits.has_pullbacks C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [epi f] : epi limits.pullback.snd := sorry

-- pullback.snd ≫ e = 0 and show that e = 0.

/-- In an abelian category, the pullback of an epimorphism is an epimorphism. -/
-- It will suffice to consider some morphism e : X ⟶ R such that

protected instance epi_pullback_of_epi_g {C : Type u} [category C] [abelian C] [limits.has_pullbacks C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [epi g] : epi limits.pullback.fst := sorry

-- pullback.fst ≫ e = 0 and show that e = 0.

protected instance mono_pushout_of_mono_f {C : Type u} [category C] [abelian C] [limits.has_pushouts C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono f] : mono limits.pushout.inr := sorry

protected instance mono_pushout_of_mono_g {C : Type u} [category C] [abelian C] [limits.has_pushouts C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono g] : mono limits.pushout.inl := sorry

end category_theory.abelian


namespace category_theory.non_preadditive_abelian


/-- Every non_preadditive_abelian category can be promoted to an abelian category. -/
def abelian (C : Type u) [category C] [non_preadditive_abelian C] : abelian C :=
  abelian.mk (fun (X Y : C) (f : X ⟶ Y) (_inst_2_1 : mono f) => eq.mpr sorry (normal_mono f))
    fun (X Y : C) (f : X ⟶ Y) (_inst_2_1 : epi f) => eq.mpr sorry (normal_epi f)

