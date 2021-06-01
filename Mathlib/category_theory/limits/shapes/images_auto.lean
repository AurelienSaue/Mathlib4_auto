/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.shapes.strong_epi
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main definitions

* A `mono_factorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism
* `is_image F` means that a given mono factorisation `F` has the universal property of the image.
* `has_image f` means that we have chosen an image for the morphism `f : X ⟶ Y`.
  * In this case, `image f` is the image object, `image.ι f : image f ⟶ Y` is the monomorphism `m`
    of the factorisation and `factor_thru_image f : X ⟶ image f` is the morphism `e`.
* `has_images C` means that every morphism in `C` has an image.
* Let `f : X ⟶ Y` and `g : P ⟶ Q` be morphisms in `C`, which we will represent as objects of the
  arrow category `arrow C`. Then `sq : f ⟶ g` is a commutative square in `C`. If `f` and `g` have
  images, then `has_image_map sq` represents the fact that there is a morphism
  `i : image f ⟶ image g` making the diagram

  X ----→ image f ----→ Y
  |         |           |
  |         |           |
  ↓         ↓           ↓
  P ----→ image g ----→ Q

  commute, where the top row is the image factorisation of `f`, the bottom row is the image
  factorisation of `g`, and the outer rectangle is the commutative square `sq`.
* If a category `has_images`, then `has_image_maps` means that every commutative square admits an
  image map.
* If a category `has_images`, then `has_strong_epi_images` means that the morphism to the image is
  always a strong epimorphism.

## Main statements

* When `C` has equalizers, the morphism `e` appearing in an image factorisation is an epimorphism.
* When `C` has strong epi images, then these images admit image maps.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

-/

namespace category_theory.limits


/-- A factorisation of a morphism `f = e ≫ m`, with `m` monic. -/
structure mono_factorisation {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) where
  I : C
  m : I ⟶ Y
  m_mono : mono m
  e : X ⟶ I
  fac' :
    autoParam (e ≫ m = f)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem mono_factorisation.fac {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    (c : mono_factorisation f) : mono_factorisation.e c ≫ mono_factorisation.m c = f :=
  sorry

@[simp] theorem mono_factorisation.fac_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    (c : mono_factorisation f) {X' : C} (f' : Y ⟶ X') :
    mono_factorisation.e c ≫ mono_factorisation.m c ≫ f' = f ≫ f' :=
  sorry

namespace mono_factorisation


/-- The obvious factorisation of a monomorphism through itself. -/
def self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] : mono_factorisation f :=
  mk X f 𝟙

-- I'm not sure we really need this, but the linter says that an inhabited instance ought to exist...

protected instance inhabited {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] :
    Inhabited (mono_factorisation f) :=
  { default := self f }

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely determined. -/
theorem ext {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) {F : mono_factorisation f}
    {F' : mono_factorisation f} (hI : I F = I F') (hm : m F = eq_to_hom hI ≫ m F') : F = F' :=
  sorry

end mono_factorisation


/-- Data exhibiting that a given factorisation through a mono is initial. -/
structure is_image {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} (F : mono_factorisation f)
    where
  lift : (F' : mono_factorisation f) → mono_factorisation.I F ⟶ mono_factorisation.I F'
  lift_fac' :
    autoParam
      (∀ (F' : mono_factorisation f), lift F' ≫ mono_factorisation.m F' = mono_factorisation.m F)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem is_image.lift_fac {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} (c : is_image F) (F' : mono_factorisation f) :
    is_image.lift c F' ≫ mono_factorisation.m F' = mono_factorisation.m F :=
  sorry

@[simp] theorem is_image.lift_fac_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} (c : is_image F) (F' : mono_factorisation f) {X' : C} (f' : Y ⟶ X') :
    is_image.lift c F' ≫ mono_factorisation.m F' ≫ f' = mono_factorisation.m F ≫ f' :=
  sorry

@[simp] theorem is_image.fac_lift_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} (hF : is_image F) (F' : mono_factorisation f) {X' : C}
    (f' : mono_factorisation.I F' ⟶ X') :
    mono_factorisation.e F ≫ is_image.lift hF F' ≫ f' = mono_factorisation.e F' ≫ f' :=
  sorry

namespace is_image


/-- The trivial factorisation of a monomorphism satisfies the universal property. -/
def self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] :
    is_image (mono_factorisation.self f) :=
  mk fun (F' : mono_factorisation f) => mono_factorisation.e F'

protected instance inhabited {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] :
    Inhabited (is_image (mono_factorisation.self f)) :=
  { default := self f }

/-- Two factorisations through monomorphisms satisfying the universal property
must factor through isomorphic objects. -/
-- TODO this is another good candidate for a future `unique_up_to_canonical_iso`.

@[simp] theorem iso_ext_hom {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} {F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F') :
    iso.hom (iso_ext hF hF') = lift hF F' :=
  Eq.refl (iso.hom (iso_ext hF hF'))

theorem iso_ext_hom_m {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} {F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F') :
    iso.hom (iso_ext hF hF') ≫ mono_factorisation.m F' = mono_factorisation.m F :=
  sorry

theorem iso_ext_inv_m {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} {F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F') :
    iso.inv (iso_ext hF hF') ≫ mono_factorisation.m F = mono_factorisation.m F' :=
  sorry

theorem e_iso_ext_hom {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} {F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F') :
    mono_factorisation.e F ≫ iso.hom (iso_ext hF hF') = mono_factorisation.e F' :=
  sorry

theorem e_iso_ext_inv {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    {F : mono_factorisation f} {F' : mono_factorisation f} (hF : is_image F) (hF' : is_image F') :
    mono_factorisation.e F' ≫ iso.inv (iso_ext hF hF') = mono_factorisation.e F :=
  sorry

end is_image


/-- Data exhibiting that a morphism `f` has an image. -/
structure image_factorisation {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) where
  F : mono_factorisation f
  is_image : is_image F

protected instance inhabited_image_factorisation {C : Type u} [category C] {X : C} {Y : C}
    (f : X ⟶ Y) [mono f] : Inhabited (image_factorisation f) :=
  { default := image_factorisation.mk (mono_factorisation.self f) (is_image.self f) }

/-- `has_image f` means that there exists an image factorisation of `f`. -/
class has_image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) where
  mk' :: (exists_image : Nonempty (image_factorisation f))

theorem has_image.mk {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    (F : image_factorisation f) : has_image f :=
  has_image.mk' (Nonempty.intro F)

/-- The chosen factorisation of `f` through a monomorphism. -/
def image.mono_factorisation {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] :
    mono_factorisation f :=
  image_factorisation.F (Classical.choice has_image.exists_image)

/-- The witness of the universal property for the chosen factorisation of `f` through a monomorphism. -/
def image.is_image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] :
    is_image (image.mono_factorisation f) :=
  image_factorisation.is_image (Classical.choice has_image.exists_image)

/-- The categorical image of a morphism. -/
/-- The inclusion of the image of a morphism into the target. -/
def image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] : C :=
  mono_factorisation.I sorry

def image.ι {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] : image f ⟶ Y :=
  mono_factorisation.m (image.mono_factorisation f)

@[simp] theorem image.as_ι {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] :
    mono_factorisation.m (image.mono_factorisation f) = image.ι f :=
  rfl

protected instance image.ι.category_theory.mono {C : Type u} [category C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_image f] : mono (image.ι f) :=
  mono_factorisation.m_mono (image.mono_factorisation f)

/-- The map from the source to the image of a morphism. -/
/-- Rewrite in terms of the `factor_thru_image` interface. -/
def factor_thru_image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] :
    X ⟶ image f :=
  mono_factorisation.e (image.mono_factorisation f)

@[simp] theorem as_factor_thru_image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_image f] : mono_factorisation.e (image.mono_factorisation f) = factor_thru_image f :=
  rfl

@[simp] theorem image.fac_assoc {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f]
    {X' : C} (f' : Y ⟶ X') : factor_thru_image f ≫ image.ι f ≫ f' = f ≫ f' :=
  sorry

/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the image. -/
def image.lift {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [has_image f]
    (F' : mono_factorisation f) : image f ⟶ mono_factorisation.I F' :=
  is_image.lift (image.is_image f) F'

@[simp] theorem image.lift_fac {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [has_image f]
    (F' : mono_factorisation f) : image.lift F' ≫ mono_factorisation.m F' = image.ι f :=
  is_image.lift_fac' (image.is_image f) F'

@[simp] theorem image.fac_lift {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [has_image f]
    (F' : mono_factorisation f) : factor_thru_image f ≫ image.lift F' = mono_factorisation.e F' :=
  is_image.fac_lift (image.is_image f) F'

@[simp] theorem is_image.lift_ι_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y}
    [has_image f] {F : mono_factorisation f} (hF : is_image F) {X' : C} (f' : Y ⟶ X') :
    is_image.lift hF (image.mono_factorisation f) ≫ image.ι f ≫ f' = mono_factorisation.m F ≫ f' :=
  sorry

-- TODO we could put a category structure on `mono_factorisation f`,

-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s

-- (they then automatically commute with the `e`s)

-- and show that an `image_of f` gives an initial object there

-- (uniqueness of the lift comes for free).

protected instance lift_mono {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [has_image f]
    (F' : mono_factorisation f) : mono (image.lift F') :=
  mono_of_mono (image.lift F') (mono_factorisation.m F')

theorem has_image.uniq {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} [has_image f]
    (F' : mono_factorisation f) (l : image f ⟶ mono_factorisation.I F')
    (w : l ≫ mono_factorisation.m F' = image.ι f) : l = image.lift F' :=
  sorry

/-- `has_images` represents a choice of image for every morphism -/
class has_images (C : Type u) [category C] where
  has_image : ∀ {X Y : C} (f : X ⟶ Y), has_image f

/-- The image of a monomorphism is isomorphic to the source. -/
def image_mono_iso_source {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f]
    [mono f] : image f ≅ X :=
  is_image.iso_ext (image.is_image f) (is_image.self f)

@[simp] theorem image_mono_iso_source_inv_ι {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_image f] [mono f] : iso.inv (image_mono_iso_source f) ≫ image.ι f = f :=
  sorry

@[simp] theorem image_mono_iso_source_hom_self_assoc {C : Type u} [category C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_image f] [mono f] {X' : C} (f' : Y ⟶ X') :
    iso.hom (image_mono_iso_source f) ≫ f ≫ f' = image.ι f ≫ f' :=
  sorry

-- This is the proof that `factor_thru_image f` is an epimorphism

-- from https://en.wikipedia.org/wiki/Image_(category_theory), which is in turn taken from:

-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1

theorem image.ext {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f] {W : C}
    {g : image f ⟶ W} {h : image f ⟶ W} [has_limit (parallel_pair g h)]
    (w : factor_thru_image f ≫ g = factor_thru_image f ≫ h) : g = h :=
  sorry

protected instance factor_thru_image.category_theory.epi {C : Type u} [category C] {X : C} {Y : C}
    (f : X ⟶ Y) [has_image f] [∀ {Z : C} (g h : image f ⟶ Z), has_limit (parallel_pair g h)] :
    epi (factor_thru_image f) :=
  epi.mk
    fun (Z : C) (g h : image f ⟶ Z) (w : factor_thru_image f ≫ g = factor_thru_image f ≫ h) =>
      image.ext f w

theorem epi_image_of_epi {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f]
    [E : epi f] : epi (image.ι f) :=
  epi_of_epi (factor_thru_image f) (image.ι f)

theorem epi_of_epi_image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [has_image f]
    [epi (image.ι f)] [epi (factor_thru_image f)] : epi f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (epi f)) (Eq.symm (image.fac f))))
    (epi_comp (factor_thru_image f) (image.ι f))

/--
An equation between morphisms gives a comparison map between the images
(which momentarily we prove is an iso).
-/
def image.eq_to_hom {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {f' : X ⟶ Y} [has_image f]
    [has_image f'] (h : f = f') : image f ⟶ image f' :=
  image.lift (mono_factorisation.mk (image f') (image.ι f') (factor_thru_image f'))

protected instance image.eq_to_hom.category_theory.is_iso {C : Type u} [category C] {X : C} {Y : C}
    {f : X ⟶ Y} {f' : X ⟶ Y} [has_image f] [has_image f'] (h : f = f') :
    is_iso (image.eq_to_hom h) :=
  is_iso.mk (image.eq_to_hom sorry)

/-- An equation between morphisms gives an isomorphism between the images. -/
def image.eq_to_iso {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {f' : X ⟶ Y} [has_image f]
    [has_image f'] (h : f = f') : image f ≅ image f' :=
  as_iso (image.eq_to_hom h)

/--
As long as the category has equalizers,
the image inclusion maps commute with `image.eq_to_iso`.
-/
theorem image.eq_fac {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {f' : X ⟶ Y}
    [has_image f] [has_image f'] [has_equalizers C] (h : f = f') :
    image.ι f = iso.hom (image.eq_to_iso h) ≫ image.ι f' :=
  sorry

/-- The comparison map `image (f ≫ g) ⟶ image g`. -/
def image.pre_comp {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)
    [has_image g] [has_image (f ≫ g)] : image (f ≫ g) ⟶ image g :=
  image.lift (mono_factorisation.mk (image g) (image.ι g) (f ≫ factor_thru_image g))

@[simp] theorem image.factor_thru_image_pre_comp {C : Type u} [category C] {X : C} {Y : C}
    (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z) [has_image g] [has_image (f ≫ g)] :
    factor_thru_image (f ≫ g) ≫ image.pre_comp f g = f ≫ factor_thru_image g :=
  sorry

/--
The two step comparison map
  `image (f ≫ (g ≫ h)) ⟶ image (g ≫ h) ⟶ image h`
agrees with the one step comparison map
  `image (f ≫ (g ≫ h)) ≅ image ((f ≫ g) ≫ h) ⟶ image h`.
 -/
theorem image.pre_comp_comp {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) {Z : C}
    (g : Y ⟶ Z) {W : C} (h : Z ⟶ W) [has_image (g ≫ h)] [has_image (f ≫ g ≫ h)] [has_image h]
    [has_image ((f ≫ g) ≫ h)] :
    image.pre_comp f (g ≫ h) ≫ image.pre_comp g h =
        image.eq_to_hom (Eq.symm (category.assoc f g h)) ≫ image.pre_comp (f ≫ g) h :=
  sorry

/--
`image.pre_comp f g` is an isomorphism when `f` is an isomorphism
(we need `C` to have equalizers to prove this).
-/
protected instance image.is_iso_precomp_iso {C : Type u} [category C] {X : C} {Y : C} {Z : C}
    (g : Y ⟶ Z) [has_equalizers C] (f : X ≅ Y) [has_image g] [has_image (iso.hom f ≫ g)] :
    is_iso (image.pre_comp (iso.hom f) g) :=
  is_iso.mk
    (image.lift
      (mono_factorisation.mk (image (iso.hom f ≫ g)) (image.ι (iso.hom f ≫ g))
        (iso.inv f ≫ factor_thru_image (iso.hom f ≫ g))))

-- Note that in general we don't have the other comparison map you might expect

-- `image f ⟶ image (f ≫ g)`.

/-- Postcomposing by an isomorphism induces an isomorphism on the image. -/
def image.post_comp_is_iso {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z)
    [has_equalizers C] [is_iso g] [has_image f] [has_image (f ≫ g)] : image f ≅ image (f ≫ g) :=
  iso.mk
    (image.lift
      (mono_factorisation.mk (image (f ≫ g)) (image.ι (f ≫ g) ≫ inv g) (factor_thru_image (f ≫ g))))
    (image.lift (mono_factorisation.mk (image f) (image.ι f ≫ g) (factor_thru_image f)))

@[simp] theorem image.post_comp_is_iso_hom_comp_image_ι_assoc {C : Type u} [category C] {X : C}
    {Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z) [has_equalizers C] [is_iso g] [has_image f]
    [has_image (f ≫ g)] {X' : C} (f' : Z ⟶ X') :
    iso.hom (image.post_comp_is_iso f g) ≫ image.ι (f ≫ g) ≫ f' = image.ι f ≫ g ≫ f' :=
  sorry

@[simp] theorem image.post_comp_is_iso_inv_comp_image_ι_assoc {C : Type u} [category C] {X : C}
    {Y : C} (f : X ⟶ Y) {Z : C} (g : Y ⟶ Z) [has_equalizers C] [is_iso g] [has_image f]
    [has_image (f ≫ g)] {X' : C} (f' : Y ⟶ X') :
    iso.inv (image.post_comp_is_iso f g) ≫ image.ι f ≫ f' = image.ι (f ≫ g) ≫ inv g ≫ f' :=
  sorry

end category_theory.limits


namespace category_theory.limits


protected instance hom.has_image {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_image f] : has_image (comma.hom (arrow.mk f)) :=
  (fun (this : has_image f) => this) _inst_2

/-- An image map is a morphism `image f → image g` fitting into a commutative square and satisfying
    the obvious commutativity conditions. -/
structure image_map {C : Type u} [category C] {f : arrow C} {g : arrow C} [has_image (comma.hom f)]
    [has_image (comma.hom g)] (sq : f ⟶ g)
    where
  map : image (comma.hom f) ⟶ image (comma.hom g)
  map_ι' :
    autoParam (map ≫ image.ι (comma.hom g) = image.ι (comma.hom f) ≫ comma_morphism.right sq)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

protected instance inhabited_image_map {C : Type u} [category C] {f : arrow C}
    [has_image (comma.hom f)] : Inhabited (image_map 𝟙) :=
  { default := image_map.mk 𝟙 }

@[simp] theorem image_map.map_ι {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] {sq : f ⟶ g} (c : image_map sq) :
    image_map.map c ≫ image.ι (comma.hom g) = image.ι (comma.hom f) ≫ comma_morphism.right sq :=
  sorry

@[simp] theorem image_map.map_ι_assoc {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] {sq : f ⟶ g} (c : image_map sq) {X' : C}
    (f' : comma.right g ⟶ X') :
    image_map.map c ≫ image.ι (comma.hom g) ≫ f' =
        image.ι (comma.hom f) ≫ comma_morphism.right sq ≫ f' :=
  sorry

@[simp] theorem image_map.factor_map {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g) (m : image_map sq) :
    factor_thru_image (comma.hom f) ≫ image_map.map m =
        comma_morphism.left sq ≫ factor_thru_image (comma.hom g) :=
  sorry

/-- To give an image map for a commutative square with `f` at the top and `g` at the bottom, it
    suffices to give a map between any mono factorisation of `f` and any image factorisation of
    `g`. -/
def image_map.transport {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g)
    (F : mono_factorisation (comma.hom f)) {F' : mono_factorisation (comma.hom g)}
    (hF' : is_image F') {map : mono_factorisation.I F ⟶ mono_factorisation.I F'}
    (map_ι : map ≫ mono_factorisation.m F' = mono_factorisation.m F ≫ comma_morphism.right sq) :
    image_map sq :=
  image_map.mk (image.lift F ≫ map ≫ is_image.lift hF' (image.mono_factorisation (comma.hom g)))

/-- `has_image_map sq` means that there is an `image_map` for the square `sq`. -/
class has_image_map {C : Type u} [category C] {f : arrow C} {g : arrow C} [has_image (comma.hom f)]
    [has_image (comma.hom g)] (sq : f ⟶ g)
    where
  mk' :: (has_image_map : Nonempty (image_map sq))

theorem has_image_map.mk {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] {sq : f ⟶ g} (m : image_map sq) :
    has_image_map sq :=
  has_image_map.mk' (Nonempty.intro m)

theorem has_image_map.transport {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g)
    (F : mono_factorisation (comma.hom f)) {F' : mono_factorisation (comma.hom g)}
    (hF' : is_image F') (map : mono_factorisation.I F ⟶ mono_factorisation.I F')
    (map_ι : map ≫ mono_factorisation.m F' = mono_factorisation.m F ≫ comma_morphism.right sq) :
    has_image_map sq :=
  has_image_map.mk (image_map.transport sq F hF' map_ι)

/-- Obtain an `image_map` from a `has_image_map` instance. -/
def has_image_map.image_map {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g) [has_image_map sq] :
    image_map sq :=
  Classical.choice has_image_map.has_image_map

theorem image_map.ext_iff {C : Type u} {_inst_1 : category C} {f : arrow C} {g : arrow C}
    {_inst_2 : has_image (comma.hom f)} {_inst_3 : has_image (comma.hom g)} {sq : f ⟶ g}
    (x : image_map sq) (y : image_map sq) : x = y ↔ image_map.map x = image_map.map y :=
  sorry

protected instance image_map.subsingleton {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g) :
    subsingleton (image_map sq) :=
  subsingleton.intro
    fun (a b : image_map sq) =>
      image_map.ext a b
        (iff.mp (cancel_mono (image.ι (comma.hom g)))
          (eq.mpr
            (id
              ((fun (a a_1 : image (comma.hom f) ⟶ functor.obj 𝟭 (comma.right g)) (e_1 : a = a_1)
                  (ᾰ ᾰ_1 : image (comma.hom f) ⟶ functor.obj 𝟭 (comma.right g)) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg Eq e_1) e_2)
                (image_map.map a ≫ image.ι (comma.hom g))
                (image.ι (comma.hom f) ≫ comma_morphism.right sq) (image_map.map_ι a)
                (image_map.map b ≫ image.ι (comma.hom g))
                (image.ι (comma.hom f) ≫ comma_morphism.right sq) (image_map.map_ι b)))
            (Eq.refl (image.ι (comma.hom f) ≫ comma_morphism.right sq))))

/-- The map on images induced by a commutative square. -/
def image.map {C : Type u} [category C] {f : arrow C} {g : arrow C} [has_image (comma.hom f)]
    [has_image (comma.hom g)] (sq : f ⟶ g) [has_image_map sq] :
    image (comma.hom f) ⟶ image (comma.hom g) :=
  image_map.map (has_image_map.image_map sq)

theorem image.factor_map {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g) [has_image_map sq] :
    factor_thru_image (comma.hom f) ≫ image.map sq =
        comma_morphism.left sq ≫ factor_thru_image (comma.hom g) :=
  sorry

theorem image.map_ι {C : Type u} [category C] {f : arrow C} {g : arrow C} [has_image (comma.hom f)]
    [has_image (comma.hom g)] (sq : f ⟶ g) [has_image_map sq] :
    image.map sq ≫ image.ι (comma.hom g) = image.ι (comma.hom f) ≫ comma_morphism.right sq :=
  sorry

theorem image.map_hom_mk'_ι {C : Type u} [category C] {X : C} {Y : C} {P : C} {Q : C} {k : X ⟶ Y}
    [has_image k] {l : P ⟶ Q} [has_image l] {m : X ⟶ P} {n : Y ⟶ Q} (w : m ≫ l = k ≫ n)
    [has_image_map (arrow.hom_mk' w)] : image.map (arrow.hom_mk' w) ≫ image.ι l = image.ι k ≫ n :=
  image.map_ι (arrow.hom_mk' w)

/-- Image maps for composable commutative squares induce an image map in the composite square. -/
def image_map_comp {C : Type u} [category C] {f : arrow C} {g : arrow C} [has_image (comma.hom f)]
    [has_image (comma.hom g)] (sq : f ⟶ g) [has_image_map sq] {h : arrow C}
    [has_image (comma.hom h)] (sq' : g ⟶ h) [has_image_map sq'] : image_map (sq ≫ sq') :=
  image_map.mk (image.map sq ≫ image.map sq')

@[simp] theorem image.map_comp {C : Type u} [category C] {f : arrow C} {g : arrow C}
    [has_image (comma.hom f)] [has_image (comma.hom g)] (sq : f ⟶ g) [has_image_map sq]
    {h : arrow C} [has_image (comma.hom h)] (sq' : g ⟶ h) [has_image_map sq']
    [has_image_map (sq ≫ sq')] : image.map (sq ≫ sq') = image.map sq ≫ image.map sq' :=
  sorry

/-- The identity `image f ⟶ image f` fits into the commutative square represented by the identity
    morphism `𝟙 f` in the arrow category. -/
def image_map_id {C : Type u} [category C] (f : arrow C) [has_image (comma.hom f)] : image_map 𝟙 :=
  image_map.mk 𝟙

@[simp] theorem image.map_id {C : Type u} [category C] (f : arrow C) [has_image (comma.hom f)]
    [has_image_map 𝟙] : image.map 𝟙 = 𝟙 :=
  sorry

/-- If a category `has_image_maps`, then all commutative squares induce morphisms on images. -/
class has_image_maps (C : Type u) [category C] [has_images C] where
  has_image_map : ∀ {f g : arrow C} (st : f ⟶ g), has_image_map st

/-- The functor from the arrow category of `C` to `C` itself that maps a morphism to its image
    and a commutative square to the induced morphism on images. -/
@[simp] theorem im_map {C : Type u} [category C] [has_images C] [has_image_maps C] (_x : arrow C) :
    ∀ (_x_1 : arrow C) (st : _x ⟶ _x_1), functor.map im st = image.map st :=
  fun (_x_1 : arrow C) (st : _x ⟶ _x_1) => Eq.refl (functor.map im st)

/-- A strong epi-mono factorisation is a decomposition `f = e ≫ m` with `e` a strong epimorphism
    and `m` a monomorphism. -/
structure strong_epi_mono_factorisation {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    extends mono_factorisation f where
  e_strong_epi : strong_epi (mono_factorisation.e _to_mono_factorisation)

/-- Satisfying the inhabited linter -/
protected instance strong_epi_mono_factorisation_inhabited {C : Type u} [category C] {X : C} {Y : C}
    (f : X ⟶ Y) [strong_epi f] : Inhabited (strong_epi_mono_factorisation f) :=
  { default := strong_epi_mono_factorisation.mk (mono_factorisation.mk Y 𝟙 f) }

/-- A mono factorisation coming from a strong epi-mono factorisation always has the universal
    property of the image. -/
def strong_epi_mono_factorisation.to_mono_is_image {C : Type u} [category C] {X : C} {Y : C}
    {f : X ⟶ Y} (F : strong_epi_mono_factorisation f) :
    is_image (strong_epi_mono_factorisation.to_mono_factorisation F) :=
  is_image.mk fun (G : mono_factorisation f) => arrow.lift (arrow.hom_mk' sorry)

/-- A category has strong epi-mono factorisations if every morphism admits a strong epi-mono
    factorisation. -/
class has_strong_epi_mono_factorisations (C : Type u) [category C] where
  mk' :: (has_fac : ∀ {X Y : C} (f : X ⟶ Y), Nonempty (strong_epi_mono_factorisation f))

theorem has_strong_epi_mono_factorisations.mk {C : Type u} [category C]
    (d : {X Y : C} → (f : X ⟶ Y) → strong_epi_mono_factorisation f) :
    has_strong_epi_mono_factorisations C :=
  has_strong_epi_mono_factorisations.mk' fun (X Y : C) (f : X ⟶ Y) => Nonempty.intro (d f)

protected instance has_images_of_has_strong_epi_mono_factorisations {C : Type u} [category C]
    [has_strong_epi_mono_factorisations C] : has_images C :=
  has_images.mk sorry

/-- A category has strong epi images if it has all images and `factor_thru_image f` is a strong
    epimorphism for all `f`. -/
class has_strong_epi_images (C : Type u) [category C] [has_images C] where
  strong_factor_thru_image : ∀ {X Y : C} (f : X ⟶ Y), strong_epi (factor_thru_image f)

/-- If there is a single strong epi-mono factorisation of `f`, then every image factorisation is a
    strong epi-mono factorisation. -/
theorem strong_epi_of_strong_epi_mono_factorisation {C : Type u} [category C] {X : C} {Y : C}
    {f : X ⟶ Y} (F : strong_epi_mono_factorisation f) {F' : mono_factorisation f}
    (hF' : is_image F') : strong_epi (mono_factorisation.e F') :=
  sorry

theorem strong_epi_factor_thru_image_of_strong_epi_mono_factorisation {C : Type u} [category C]
    {X : C} {Y : C} {f : X ⟶ Y} [has_image f] (F : strong_epi_mono_factorisation f) :
    strong_epi (factor_thru_image f) :=
  strong_epi_of_strong_epi_mono_factorisation F (image.is_image f)

/-- If we constructed our images from strong epi-mono factorisations, then these images are
    strong epi images. -/
protected instance has_strong_epi_images_of_has_strong_epi_mono_factorisations {C : Type u}
    [category C] [has_strong_epi_mono_factorisations C] : has_strong_epi_images C :=
  has_strong_epi_images.mk
    fun (X Y : C) (f : X ⟶ Y) =>
      strong_epi_factor_thru_image_of_strong_epi_mono_factorisation
        (Classical.choice (has_strong_epi_mono_factorisations.has_fac f))

/-- A category with strong epi images has image maps. -/
protected instance has_image_maps_of_has_strong_epi_images {C : Type u} [category C] [has_images C]
    [has_strong_epi_images C] : has_image_maps C :=
  has_image_maps.mk sorry

/-- If a category has images, equalizers and pullbacks, then images are automatically strong epi
    images. -/
protected instance has_strong_epi_images_of_has_pullbacks_of_has_equalizers {C : Type u}
    [category C] [has_images C] [has_pullbacks C] [has_equalizers C] : has_strong_epi_images C :=
  sorry

/--
If `C` has strong epi mono factorisations, then the image is unique up to isomorphism, in that if
`f` factors as a strong epi followed by a mono, this factorisation is essentially the image
factorisation.
-/
def image.iso_strong_epi_mono {C : Type u} [category C] [has_strong_epi_mono_factorisations C]
    {X : C} {Y : C} {f : X ⟶ Y} {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e]
    [mono m] : I' ≅ image f :=
  is_image.iso_ext
    (strong_epi_mono_factorisation.to_mono_is_image
      (strong_epi_mono_factorisation.mk (mono_factorisation.mk I' m e)))
    (image.is_image f)

@[simp] theorem image.iso_strong_epi_mono_hom_comp_ι {C : Type u} [category C]
    [has_strong_epi_mono_factorisations C] {X : C} {Y : C} {f : X ⟶ Y} {I' : C} (e : X ⟶ I')
    (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e] [mono m] :
    iso.hom (image.iso_strong_epi_mono e m comm) ≫ image.ι f = m :=
  is_image.lift_fac
    (strong_epi_mono_factorisation.to_mono_is_image
      (strong_epi_mono_factorisation.mk (mono_factorisation.mk I' m e)))
    (image.mono_factorisation f)

@[simp] theorem image.iso_strong_epi_mono_inv_comp_mono {C : Type u} [category C]
    [has_strong_epi_mono_factorisations C] {X : C} {Y : C} {f : X ⟶ Y} {I' : C} (e : X ⟶ I')
    (m : I' ⟶ Y) (comm : e ≫ m = f) [strong_epi e] [mono m] :
    iso.inv (image.iso_strong_epi_mono e m comm) ≫ m = image.ι f :=
  image.lift_fac
    (strong_epi_mono_factorisation.to_mono_factorisation
      (strong_epi_mono_factorisation.mk (mono_factorisation.mk I' m e)))

end Mathlib