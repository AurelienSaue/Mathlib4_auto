/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.images
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# The morphism from `image f` to `kernel g` when `f ≫ g = 0`

We define the map, as the lift of `image.ι f` to `kernel g`,
and check some basic properties:

* this map is a monomorphism
* given `A --0--> B --g--> C`, where `[mono g]`, this map is an epimorphism
* given `A --f--> B --0--> C`, where `[epi f]`, this map is an epimorphism

In later files, we define the homology of complex as the cokernel of this map,
and say a complex is exact at a point if this map is an epimorphism.
-/

namespace category_theory


/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/

/--
The morphism from `image f` to `kernel g` when `f ≫ g = 0`.
-/
def image_to_kernel_map {V : Type u} [category V] [limits.has_zero_morphisms V]
    [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C)
    (w : f ≫ g = 0) : limits.image f ⟶ limits.kernel g :=
  limits.kernel.lift g (limits.image.ι f) sorry

@[simp] theorem image_to_kernel_map_zero_left {V : Type u} [category V]
    [limits.has_zero_morphisms V] [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V}
    {C : V} (g : B ⟶ C) [limits.has_zero_object V] {w : 0 ≫ g = 0} :
    image_to_kernel_map 0 g w = 0 :=
  sorry

theorem image_to_kernel_map_zero_right {V : Type u} [category V] [limits.has_zero_morphisms V]
    [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V} {C : V} (f : A ⟶ B)
    {w : f ≫ 0 = 0} : image_to_kernel_map f 0 w = limits.image.ι f ≫ inv (limits.kernel.ι 0) :=
  sorry

theorem image_to_kernel_map_comp_right {V : Type u} [category V] [limits.has_zero_morphisms V]
    [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C)
    {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    image_to_kernel_map f (g ≫ h)
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : A ⟶ D) (e_1 : a = a_1) (ᾰ ᾰ_1 : A ⟶ D) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (f ≫ g ≫ h) 0 (Eq.trans (reassoc_of w D h) limits.zero_comp) 0 0 (Eq.refl 0))
                (propext (eq_self_iff_true 0))))
            trivial) =
        image_to_kernel_map f g w ≫
          limits.kernel.lift (g ≫ h) (limits.kernel.ι g)
            (eq.mpr
              (id
                (Eq.trans
                  ((fun (a a_1 : limits.kernel g ⟶ D) (e_1 : a = a_1) (ᾰ ᾰ_1 : limits.kernel g ⟶ D)
                      (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                    (limits.kernel.ι g ≫ g ≫ h) 0
                    (Eq.trans (limits.kernel.condition_assoc g h) limits.zero_comp) 0 0 (Eq.refl 0))
                  (propext (eq_self_iff_true 0))))
              trivial) :=
  sorry

theorem image_to_kernel_map_comp_left {V : Type u} [category V] [limits.has_zero_morphisms V]
    [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C)
    {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    image_to_kernel_map (h ≫ f) g
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : Z ⟶ C) (e_1 : a = a_1) (ᾰ ᾰ_1 : Z ⟶ C) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  ((h ≫ f) ≫ g) 0
                  (Eq.trans
                    (Eq.trans (category.assoc h f g)
                      ((fun (ᾰ ᾰ_1 : Z ⟶ A) (e_1 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : A ⟶ C) (e_2 : ᾰ_2 = ᾰ_3) =>
                          congr (congr_arg category_struct.comp e_1) e_2)
                        h h (Eq.refl h) (f ≫ g) 0 w))
                    limits.comp_zero)
                  0 0 (Eq.refl 0))
                (propext (eq_self_iff_true 0))))
            trivial) =
        limits.image.pre_comp h f ≫ image_to_kernel_map f g w :=
  sorry

@[simp] theorem image_to_kernel_map_comp_iso {V : Type u} [category V] [limits.has_zero_morphisms V]
    [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C)
    {D : V} (h : C ⟶ D) [is_iso h] (w : f ≫ g ≫ h = 0) :
    image_to_kernel_map f (g ≫ h) w =
        image_to_kernel_map f g
            (iff.mp (cancel_mono h)
              (eq.mpr
                (id
                  ((fun (a a_1 : A ⟶ D) (e_1 : a = a_1) (ᾰ ᾰ_1 : A ⟶ D) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg Eq e_1) e_2)
                    ((f ≫ g) ≫ h) (f ≫ g ≫ h) (category.assoc f g h) (0 ≫ h) 0 limits.zero_comp))
                (eq.mp (Eq.refl (f ≫ g ≫ h = 0)) w))) ≫
          iso.inv (limits.kernel_comp_is_iso g h) :=
  sorry

@[simp] theorem image_to_kernel_map_iso_comp {V : Type u} [category V] [limits.has_zero_morphisms V]
    [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C)
    {Z : V} (h : Z ⟶ A) [is_iso h] (w : (h ≫ f) ≫ g = 0) :
    image_to_kernel_map (h ≫ f) g w =
        limits.image.pre_comp h f ≫
          image_to_kernel_map f g
            (iff.mp (cancel_epi h)
              (eq.mpr
                (id
                  ((fun (a a_1 : Z ⟶ C) (e_1 : a = a_1) (ᾰ ᾰ_1 : Z ⟶ C) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg Eq e_1) e_2)
                    (h ≫ f ≫ g) (h ≫ f ≫ g) (Eq.refl (h ≫ f ≫ g)) (h ≫ 0) 0 limits.comp_zero))
                (eq.mp
                  ((fun (a a_1 : Z ⟶ C) (e_1 : a = a_1) (ᾰ ᾰ_1 : Z ⟶ C) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg Eq e_1) e_2)
                    ((h ≫ f) ≫ g) (h ≫ f ≫ g) (category.assoc h f g) 0 0 (Eq.refl 0))
                  w))) :=
  sorry

@[simp] theorem image_to_kernel_map_comp_hom_inv_comp {V : Type u} [category V]
    [limits.has_zero_morphisms V] [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V}
    {C : V} (f : A ⟶ B) (g : B ⟶ C) {Z : V} {i : B ≅ Z} (w : (f ≫ iso.hom i) ≫ iso.inv i ≫ g = 0) :
    image_to_kernel_map (f ≫ iso.hom i) (iso.inv i ≫ g) w =
        iso.inv (limits.image.post_comp_is_iso f (iso.hom i)) ≫
          image_to_kernel_map f g
              (eq.mpr (id (Eq.refl (f ≫ g = 0)))
                (eq.mp
                  ((fun (a a_1 : A ⟶ C) (e_1 : a = a_1) (ᾰ ᾰ_1 : A ⟶ C) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg Eq e_1) e_2)
                    ((f ≫ iso.hom i) ≫ iso.inv i ≫ g) (f ≫ g)
                    (Eq.trans (category.assoc f (iso.hom i) (iso.inv i ≫ g))
                      ((fun (ᾰ ᾰ_1 : A ⟶ B) (e_1 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : B ⟶ C) (e_2 : ᾰ_2 = ᾰ_3) =>
                          congr (congr_arg category_struct.comp e_1) e_2)
                        f f (Eq.refl f) (iso.hom i ≫ iso.inv i ≫ g) g (iso.hom_inv_id_assoc i g)))
                    0 0 (Eq.refl 0))
                  w)) ≫
            iso.inv (limits.kernel_is_iso_comp (iso.inv i) g) :=
  sorry

/--
`image_to_kernel_map` for `A --0--> B --g--> C`, where `[mono g]` is an epi
(i.e. the sequence is exact at `B`).
-/
theorem image_to_kernel_map_epi_of_zero_of_mono {V : Type u} [category V]
    [limits.has_zero_morphisms V] [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V}
    {C : V} (g : B ⟶ C) [mono g] [limits.has_zero_object V] :
    epi
        (image_to_kernel_map 0 g
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : A ⟶ C) (e_1 : a = a_1) (ᾰ ᾰ_1 : A ⟶ C) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (0 ≫ g) 0 limits.zero_comp 0 0 (Eq.refl 0))
                (propext (eq_self_iff_true 0))))
            trivial)) :=
  sorry

/--
`image_to_kernel_map` for `A --f--> B --0--> C`, where `[epi g]` is an epi
(i.e. the sequence is exact at `B`).
-/
theorem image_to_kernel_map_epi_of_epi_of_zero {V : Type u} [category V]
    [limits.has_zero_morphisms V] [limits.has_images V] [limits.has_equalizers V] {A : V} {B : V}
    {C : V} (f : A ⟶ B) [epi f] :
    epi
        (image_to_kernel_map f 0
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : A ⟶ C) (e_1 : a = a_1) (ᾰ ᾰ_1 : A ⟶ C) (e_2 : ᾰ = ᾰ_1) =>
                    congr (congr_arg Eq e_1) e_2)
                  (f ≫ 0) 0 limits.comp_zero 0 0 (Eq.refl 0))
                (propext (eq_self_iff_true 0))))
            trivial)) :=
  sorry

end Mathlib