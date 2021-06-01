/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import Mathlib.category_theory.full_subcategory
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l 

namespace Mathlib

/-!
# Essential image of a functor

The essential image `ess_image` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into a essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/

namespace category_theory


namespace functor


/--
The essential image of a functor `F` consists of those objects in the target category which are
isomorphic to an object in the image of the function `F.obj`. In other words, this is the closure
under isomorphism of the function `F.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def ess_image {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D) : set D :=
  fun (Y : D) => ∃ (X : C), Nonempty (obj F X ≅ Y)

/-- Get the witnessing object that `Y` is in the subcategory given by `F`. -/
def ess_image.witness {C : Type u₁} {D : Type u₂} [category C] [category D] {F : C ⥤ D} {Y : D}
    (h : Y ∈ ess_image F) : C :=
  Exists.some h

/-- Extract the isomorphism between `F.obj h.witness` and `Y` itself. -/
def ess_image.get_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {F : C ⥤ D} {Y : D}
    (h : Y ∈ ess_image F) : obj F (ess_image.witness h) ≅ Y :=
  Classical.choice sorry

/-- Being in the essential image is a "hygenic" property: it is preserved under isomorphism. -/
theorem ess_image.of_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {F : C ⥤ D} {Y : D}
    {Y' : D} (h : Y ≅ Y') (hY : Y ∈ ess_image F) : Y' ∈ ess_image F :=
  Exists.imp (fun (B : C) => nonempty.map fun (_x : obj F B ≅ Y) => _x ≪≫ h) hY

/--
If `Y` is in the essential image of `F` then it is in the essential image of `F'` as long as
`F ≅ F'`.
-/
theorem ess_image.of_nat_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {F : C ⥤ D}
    {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : Y ∈ ess_image F) : Y ∈ ess_image F' :=
  Exists.imp (fun (X : C) => nonempty.map fun (t : obj F X ≅ Y) => iso.app (iso.symm h) X ≪≫ t) hY

/-- Isomorphic functors have equal essential images. -/
theorem ess_image_eq_of_nat_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {F : C ⥤ D}
    {F' : C ⥤ D} (h : F ≅ F') : ess_image F = ess_image F' :=
  set.ext fun (A : D) => { mp := ess_image.of_nat_iso h, mpr := ess_image.of_nat_iso (iso.symm h) }

/-- An object in the image is in the essential image. -/
theorem obj_mem_ess_image {C : Type u₁} {D : Type u₂} [category C] [category D] (F : D ⥤ C)
    (Y : D) : obj F Y ∈ ess_image F :=
  Exists.intro Y (Nonempty.intro (iso.refl (obj F Y)))

protected instance ess_image.category_theory.category {C : Type u₁} {D : Type u₂} [category C]
    [category D] {F : C ⥤ D} : category ↥(ess_image F) :=
  category_theory.full_subcategory fun (x : D) => x ∈ ess_image F

/-- The essential image as a subcategory has a fully faithful inclusion into the target category. -/
@[simp] theorem ess_image_inclusion_obj {C : Type u₁} {D : Type u₂} [category C] [category D]
    (F : C ⥤ D) (c : Subtype fun (X : D) => (fun (x : D) => x ∈ ess_image F) X) :
    obj (ess_image_inclusion F) c = ↑c :=
  Eq.refl ↑c

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
def to_ess_image {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D) :
    C ⥤ ↥(ess_image F) :=
  mk (fun (X : C) => { val := obj F X, property := obj_mem_ess_image F X })
    fun (X Y : C) (f : X ⟶ Y) => preimage (ess_image_inclusion F) (map F f)

/--
The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simp] theorem to_ess_image_comp_essential_image_inclusion_hom_app {C : Type u₁} {D : Type u₂}
    [category C] [category D] {F : C ⥤ D} (X : C) :
    nat_trans.app (iso.hom to_ess_image_comp_essential_image_inclusion) X = 𝟙 :=
  Eq.refl 𝟙

end functor


/--
A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential image
of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class ess_surj {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D) where
  mem_ess_image : ∀ (Y : D), Y ∈ functor.ess_image F

protected instance functor.to_ess_image.ess_surj {C : Type u₁} {D : Type u₂} [category C]
    [category D] {F : C ⥤ D} : ess_surj (functor.to_ess_image F) :=
  ess_surj.mk fun (_x : ↥(functor.ess_image F)) => sorry

/-- Given an essentially surjective functor, we can find a preimage for every object `Y` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `Y`, see
    `obj_obj_preimage_iso`. -/
/-- Applying an essentially surjective functor to a preimage of `Y` yields an object that is
def functor.obj_preimage {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D)
    [ess_surj F] (Y : D) : C :=
  functor.ess_image.witness (ess_surj.mem_ess_image F Y)

    isomorphic to `Y`. -/
def functor.obj_obj_preimage_iso {C : Type u₁} {D : Type u₂} [category C] [category D] (F : C ⥤ D)
    [ess_surj F] (Y : D) : functor.obj F (functor.obj_preimage F Y) ≅ Y :=
  functor.ess_image.get_iso (ess_surj.mem_ess_image F Y)

end Mathlib