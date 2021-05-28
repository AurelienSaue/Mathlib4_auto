/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.homology.chain_complex
import Mathlib.algebra.homology.image_to_kernel_map
import PostPort

universes u v 

namespace Mathlib

/-!
# (Co)homology groups for complexes

We setup that part of the theory of homology groups which works in
any category with kernels and images.

We define the homology groups themselves, and show that they induce maps on kernels.

Under the additional assumption that our category has equalizers and functorial images, we construct
induced morphisms on images and functorial induced morphisms in homology.

## Chains and cochains

Throughout we work with complexes graded by an arbitrary `[add_comm_group β]`,
with a differential with grading `b : β`.
Thus we're simultaneously doing homology and cohomology groups
(and in future, e.g., enabling computing homologies for successive pages of spectral sequences).

At the end of the file we set up abbreviations `cohomology` and `graded_cohomology`,
so that when you're working with a `C : cochain_complex V`, you can write `C.cohomology i`
rather than the confusing `C.homology i`.
-/

namespace homological_complex


/-- The map induced by a chain map between the kernels of the differentials. -/
def kernel_map {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_kernels V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : category_theory.limits.kernel (category_theory.differential_object.d C i) ⟶
  category_theory.limits.kernel (category_theory.differential_object.d C' i) :=
  category_theory.limits.kernel.lift (category_theory.differential_object.d C' i)
    (category_theory.limits.kernel.ι (category_theory.differential_object.d C i) ≫
      category_theory.differential_object.hom.f f i)
    sorry

@[simp] theorem kernel_map_condition {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_kernels V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : kernel_map f i ≫ category_theory.limits.kernel.ι (category_theory.differential_object.d C' i) =
  category_theory.limits.kernel.ι (category_theory.differential_object.d C i) ≫
    category_theory.differential_object.hom.f f i := sorry

@[simp] theorem kernel_map_id {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_kernels V] (C : homological_complex V b) (i : β) : kernel_map 𝟙 i = 𝟙 := sorry

@[simp] theorem kernel_map_comp {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_kernels V] {C : homological_complex V b} {C' : homological_complex V b} {C'' : homological_complex V b} (f : C ⟶ C') (g : C' ⟶ C'') (i : β) : kernel_map (f ≫ g) i = kernel_map f i ≫ kernel_map g i := sorry

/-- The kernels of the differentials of a complex form a `β`-graded object. -/
def kernel_functor {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_kernels V] : homological_complex V b ⥤ category_theory.graded_object β V :=
  category_theory.functor.mk
    (fun (C : homological_complex V b) (i : β) =>
      category_theory.limits.kernel (category_theory.differential_object.d C i))
    fun (X Y : homological_complex V b) (f : X ⟶ Y) (i : β) => kernel_map f i

/-- A morphism of complexes induces a morphism on the images of the differentials in every
    degree. -/
def image_map {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_image_maps V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : category_theory.limits.image (category_theory.differential_object.d C i) ⟶
  category_theory.limits.image (category_theory.differential_object.d C' i) :=
  category_theory.limits.image.map (category_theory.arrow.hom_mk' sorry)

@[simp] theorem image_map_ι {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_image_maps V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : image_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C C' f i ≫
    category_theory.limits.image.ι (category_theory.differential_object.d C' i) =
  category_theory.limits.image.ι (category_theory.differential_object.d C i) ≫
    category_theory.differential_object.hom.f f (i + b) :=
  category_theory.limits.image.map_hom_mk'_ι (Eq.symm (comm_at V _inst_1 _inst_2 β _inst_3 b C C' f i))

/--
The connecting morphism from the image of `d i` to the kernel of `d (i ± 1)`.
-/
def image_to_kernel_map {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] (C : homological_complex V b) (i : β) : category_theory.limits.image (category_theory.differential_object.d C i) ⟶
  category_theory.limits.kernel (category_theory.differential_object.d C (i + b)) :=
  category_theory.image_to_kernel_map (category_theory.differential_object.d C i)
    (category_theory.differential_object.d C (i + b)) sorry

@[simp] theorem image_to_kernel_map_condition {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] (C : homological_complex V b) (i : β) : image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C i ≫
    category_theory.limits.kernel.ι (category_theory.differential_object.d C (i + b)) =
  category_theory.limits.image.ι (category_theory.differential_object.d C i) := sorry

theorem image_to_kernel_map_comp_kernel_map {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_image_maps V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C i ≫ kernel_map f (i + b) =
  image_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_6 C C' f i ≫
    image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C' i := sorry

/-- The `i`-th homology group of the complex `C`. -/
def homology_group {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] (i : β) (C : homological_complex V b) : V :=
  category_theory.limits.cokernel (image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C (i - b))

/-- A chain map induces a morphism in homology at every degree. -/
def homology_map {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : homology_group V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 i C ⟶
  homology_group V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 i C' :=
  category_theory.limits.cokernel.desc (image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C (i - b))
    (kernel_map f (i - b + b) ≫
      category_theory.limits.cokernel.π (image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C' (i - b)))
    sorry

@[simp] theorem homology_map_condition {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] {C : homological_complex V b} {C' : homological_complex V b} (f : C ⟶ C') (i : β) : category_theory.limits.cokernel.π (image_to_kernel_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C (i - b)) ≫
    homology_map ((fun (_x : β) => V) (i - b)) _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C C' f i =
  kernel_map f (i - b + b) ≫
    category_theory.limits.cokernel.π
      (image_to_kernel_map ((fun (_x : β) => V) (i - b)) _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 C' (i - b)) := sorry

@[simp] theorem homology_map_id {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] (C : homological_complex V b) (i : β) : homology_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C C 𝟙 i = 𝟙 := sorry

@[simp] theorem homology_map_comp {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] {C : homological_complex V b} {C' : homological_complex V b} {C'' : homological_complex V b} (f : C ⟶ C') (g : C' ⟶ C'') (i : β) : homology_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C C'' (f ≫ g) i =
  homology_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C C' f i ≫
    homology_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C' C'' g i := sorry

/-- The `i`-th homology functor from `β` graded complexes to `V`. -/
def homology (V : Type u) [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] (i : β) : homological_complex V b ⥤ V :=
  category_theory.functor.mk
    (fun (C : homological_complex V b) => homology_group V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 i C)
    fun (C C' : homological_complex V b) (f : C ⟶ C') =>
      homology_map V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C C' f i

/-- The homology functor from `β` graded complexes to `β` graded objects in `V`. -/
def graded_homology (V : Type u) [category_theory.category V] [category_theory.limits.has_zero_morphisms V] {β : Type} [add_comm_group β] {b : β} [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] : homological_complex V b ⥤ category_theory.graded_object β V :=
  category_theory.functor.mk
    (fun (C : homological_complex V b) (i : β) =>
      homology_group V _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 i C)
    fun (C C' : homological_complex V b) (f : C ⟶ C') (i : β) =>
      homology_map ((fun (_x : β) => V) i) _inst_1 _inst_2 β _inst_3 b _inst_4 _inst_5 _inst_6 _inst_7 C C' f i

end homological_complex


/-!
We now set up abbreviations so that you can write `C.cohomology i` or `(graded_cohomology V).map f`,
etc., when `C` is a cochain complex.
-/

namespace cochain_complex


/-- The `i`-th cohomology group of the cochain complex `C`. -/
def cohomology_group {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] (C : cochain_complex V) (i : ℤ) : V :=
  homological_complex.homology_group V _inst_1 _inst_2 ℤ (linear_ordered_add_comm_group.to_add_comm_group ℤ) 1 _inst_4
    _inst_5 _inst_6 i C

/-- A chain map induces a morphism in cohomology at every degree. -/
def cohomology_map {V : Type u} [category_theory.category V] [category_theory.limits.has_zero_morphisms V] [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] {C : cochain_complex V} {C' : cochain_complex V} (f : C ⟶ C') (i : ℤ) : cohomology_group V _inst_1 _inst_2 _inst_4 _inst_5 _inst_6 C i ⟶
  cohomology_group V _inst_1 _inst_2 _inst_4 _inst_5 _inst_6 C' i :=
  homological_complex.homology_map V _inst_1 _inst_2 ℤ (linear_ordered_add_comm_group.to_add_comm_group ℤ) 1 _inst_4
    _inst_5 _inst_6 _inst_7 C C' f i

/-- The `i`-th homology functor from cohain complexes to `V`. -/
def cohomology (V : Type u) [category_theory.category V] [category_theory.limits.has_zero_morphisms V] [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] (i : ℤ) : cochain_complex V ⥤ V :=
  homological_complex.homology V _inst_1 _inst_2 ℤ (linear_ordered_add_comm_group.to_add_comm_group ℤ) 1 _inst_4 _inst_5
    _inst_6 _inst_7 i

/-- The cohomology functor from cochain complexes to `ℤ`-graded objects in `V`. -/
def graded_cohomology (V : Type u) [category_theory.category V] [category_theory.limits.has_zero_morphisms V] [category_theory.limits.has_images V] [category_theory.limits.has_equalizers V] [category_theory.limits.has_cokernels V] [category_theory.limits.has_image_maps V] : cochain_complex V ⥤ category_theory.graded_object ℤ V :=
  homological_complex.graded_homology V _inst_1 _inst_2 ℤ (linear_ordered_add_comm_group.to_add_comm_group ℤ) 1 _inst_4
    _inst_5 _inst_6 _inst_7

