/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.homology.image_to_kernel_map
import PostPort

universes v u l 

namespace Mathlib

/-!
# Exact sequences

In a category with zero morphisms, images, and equalizers we say that `f : A ⟶ B` and `g : B ⟶ C`
are exact if `f ≫ g = 0` and the natural map `image f ⟶ kernel g` is an epimorphism.

This definition is equivalent to the homology at `B` vanishing (at least for preadditive
categories). At this level of generality, this is not necessarily equivalent to other reasonable
definitions of exactness, for example that the inclusion map `image.ι f` is a kernel of `g` or that
the map `image f ⟶ kernel g` is an isomorphism. By adding more assumptions on our category, we get
these equivalences and more. Currently, there is one particular set of assumptions mathlib knows
about: abelian categories. Consequently, many interesting results about exact sequences are found in
`category_theory/abelian/exact.lean`.

# Main results
* Suppose that cokernels exist and that `f` and `g` are exact. If `s` is any kernel fork over `g`
  and `t` is any cokernel cofork over `f`, then `fork.ι s ≫ cofork.π t = 0`.
* Precomposing the first morphism with an epimorphism retains exactness. Postcomposing the second
  morphism with a monomorphism retains exactness.
* If `f` and `g` are exact and `i` is an isomorphism, then `f ≫ i.hom` and `i.inv ≫ g` are also
  exact.

# Future work
* Short exact sequences, split exact sequences, the splitting lemma (maybe only for abelian
  categories?)
* Two adjacent maps in a chain complex are exact iff the homology vanishes

-/

namespace category_theory


/-- Two morphisms `f : A ⟶ B`, `g : B ⟶ C` are called exact if `f ≫ g = 0` and the natural map
    `image f ⟶ kernel g` is an epimorphism. -/
class exact {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C) 
where
  w : f ≫ g = 0
  epi : epi (image_to_kernel_map f g w)

@[simp] theorem exact.w_assoc {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {C : V} {f : A ⟶ B} {g : B ⟶ C} [c : exact f g] {X' : V} (f' : C ⟶ X') : f ≫ g ≫ f' = 0 ≫ f' := sorry

theorem exact_comp_hom_inv_comp {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {C : V} {D : V} {f : A ⟶ B} {g : B ⟶ C} [exact f g] (i : B ≅ D) : exact (f ≫ iso.hom i) (iso.inv i ≫ g) := sorry

theorem exact_comp_hom_inv_comp_iff {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {C : V} {D : V} {f : A ⟶ B} {g : B ⟶ C} (i : B ≅ D) : exact (f ≫ iso.hom i) (iso.inv i ≫ g) ↔ exact f g := sorry

theorem exact_epi_comp {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {C : V} {D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} [exact g h] [epi f] : exact (f ≫ g) h := sorry

theorem exact_comp_mono {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {C : V} {D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} [exact f g] [mono h] : exact f (g ≫ h) := sorry

theorem exact_kernel {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] {A : V} {B : V} {f : A ⟶ B} : exact (limits.kernel.ι f) f := sorry

theorem kernel_ι_eq_zero_of_exact_zero_left {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] (A : V) {B : V} {C : V} {g : B ⟶ C} [exact 0 g] : limits.kernel.ι g = 0 := sorry

theorem exact_zero_left_of_mono {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] (A : V) {B : V} {C : V} {g : B ⟶ C} [limits.has_zero_object V] [mono g] : exact 0 g := sorry

@[simp] theorem kernel_comp_cokernel_assoc {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] [limits.has_cokernels V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C) [exact f g] {X' : V} (f' : limits.cokernel f ⟶ X') : limits.kernel.ι g ≫ limits.cokernel.π f ≫ f' = 0 ≫ f' := sorry

theorem comp_eq_zero_of_exact {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] [limits.has_cokernels V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C) [exact f g] {X : V} {Y : V} {ι : X ⟶ B} (hι : ι ≫ g = 0) {π : B ⟶ Y} (hπ : f ≫ π = 0) : ι ≫ π = 0 := sorry

@[simp] theorem fork_ι_comp_cofork_π {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] [limits.has_cokernels V] {A : V} {B : V} {C : V} (f : A ⟶ B) (g : B ⟶ C) [exact f g] (s : limits.kernel_fork g) (t : limits.cokernel_cofork f) : limits.fork.ι s ≫ limits.cofork.π t = 0 :=
  comp_eq_zero_of_exact f g (limits.kernel_fork.condition s) (limits.cokernel_cofork.condition t)

theorem exact_of_zero {V : Type u} [category V] [limits.has_zero_morphisms V] [limits.has_equalizers V] [limits.has_images V] [limits.has_zero_object V] {A : V} {C : V} (f : A ⟶ 0) (g : 0 ⟶ C) : exact f g := sorry

