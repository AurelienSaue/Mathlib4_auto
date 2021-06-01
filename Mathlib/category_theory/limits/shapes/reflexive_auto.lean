/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.kernel_pair
import Mathlib.PostPort

universes v u l v₂ u₂ 

namespace Mathlib

/-!
# Reflexive coequalizers

We define reflexive pairs as a pair of morphisms which have a common section. We say a category has
reflexive coequalizers if it has coequalizers of all reflexive pairs.
Reflexive coequalizers often enjoy nicer properties than general coequalizers, and feature heavily
in some versions of the monadicity theorem.

We also give some examples of reflexive pairs: for an adjunction `F ⊣ G` with counit `ε`, the pair
`(FGε_B, ε_FGB)` is reflexive. If a pair `f,g` is a kernel pair for some morphism, then it is
reflexive.

# TODO
* If `C` has binary coproducts and reflexive coequalizers, then it has all coequalizers.
* If `T` is a monad on cocomplete category `C`, then `algebra T` is cocomplete iff it has reflexive
  coequalizers.
* If `C` is locally cartesian closed and has reflexive coequalizers, then it has images: in fact
  regular epi (and hence strong epi) images.
-/

namespace category_theory


/--
The pair `f g : A ⟶ B` is reflexive if there is a morphism `B ⟶ A` which is a section for both.
-/
class is_reflexive_pair {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B) (g : A ⟶ B) where
  common_section : ∃ (s : B ⟶ A), s ≫ f = 𝟙 ∧ s ≫ g = 𝟙

/--
The pair `f g : A ⟶ B` is coreflexive if there is a morphism `B ⟶ A` which is a retraction for both.
-/
class is_coreflexive_pair {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B) (g : A ⟶ B) where
  common_retraction : ∃ (s : B ⟶ A), f ≫ s = 𝟙 ∧ g ≫ s = 𝟙

theorem is_reflexive_pair.mk' {C : Type u} [category C] {A : C} {B : C} {f : A ⟶ B} {g : A ⟶ B}
    (s : B ⟶ A) (sf : s ≫ f = 𝟙) (sg : s ≫ g = 𝟙) : is_reflexive_pair f g :=
  is_reflexive_pair.mk (Exists.intro s { left := sf, right := sg })

theorem is_coreflexive_pair.mk' {C : Type u} [category C] {A : C} {B : C} {f : A ⟶ B} {g : A ⟶ B}
    (s : B ⟶ A) (fs : f ≫ s = 𝟙) (gs : g ≫ s = 𝟙) : is_coreflexive_pair f g :=
  is_coreflexive_pair.mk (Exists.intro s { left := fs, right := gs })

/-- Get the common section for a reflexive pair. -/
def common_section {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B) (g : A ⟶ B)
    [is_reflexive_pair f g] : B ⟶ A :=
  Exists.some (is_reflexive_pair.common_section f g)

@[simp] theorem section_comp_left_assoc {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B)
    (g : A ⟶ B) [is_reflexive_pair f g] {X' : C} (f' : B ⟶ X') : common_section f g ≫ f ≫ f' = f' :=
  sorry

@[simp] theorem section_comp_right {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B) (g : A ⟶ B)
    [is_reflexive_pair f g] : common_section f g ≫ g = 𝟙 :=
  and.right (Exists.some_spec (is_reflexive_pair.common_section f g))

/-- Get the common retraction for a coreflexive pair. -/
def common_retraction {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B) (g : A ⟶ B)
    [is_coreflexive_pair f g] : B ⟶ A :=
  Exists.some (is_coreflexive_pair.common_retraction f g)

@[simp] theorem left_comp_retraction_assoc {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B)
    (g : A ⟶ B) [is_coreflexive_pair f g] {X' : C} (f' : A ⟶ X') :
    f ≫ common_retraction f g ≫ f' = f' :=
  sorry

@[simp] theorem right_comp_retraction_assoc {C : Type u} [category C] {A : C} {B : C} (f : A ⟶ B)
    (g : A ⟶ B) [is_coreflexive_pair f g] {X' : C} (f' : A ⟶ X') :
    g ≫ common_retraction f g ≫ f' = f' :=
  sorry

/-- If `f,g` is a kernel pair for some morphism `q`, then it is reflexive. -/
theorem is_kernel_pair.is_reflexive_pair {C : Type u} [category C] {A : C} {B : C} {R : C}
    {f : R ⟶ A} {g : R ⟶ A} {q : A ⟶ B} (h : is_kernel_pair q f g) : is_reflexive_pair f g :=
  is_reflexive_pair.mk' (subtype.val (is_kernel_pair.lift' h 𝟙 𝟙 rfl))
    (and.left (subtype.property (is_kernel_pair.lift' h 𝟙 𝟙 rfl)))
    (and.right (subtype.property (is_kernel_pair.lift' h 𝟙 𝟙 rfl)))

/-- If `f,g` is reflexive, then `g,f` is reflexive. -/
-- This shouldn't be an instance as it would instantly loop.

theorem is_reflexive_pair.swap {C : Type u} [category C] {A : C} {B : C} {f : A ⟶ B} {g : A ⟶ B}
    [is_reflexive_pair f g] : is_reflexive_pair g f :=
  is_reflexive_pair.mk' (common_section f g) (section_comp_right f g) (section_comp_left f g)

/-- If `f,g` is coreflexive, then `g,f` is coreflexive. -/
-- This shouldn't be an instance as it would instantly loop.

theorem is_coreflexive_pair.swap {C : Type u} [category C] {A : C} {B : C} {f : A ⟶ B} {g : A ⟶ B}
    [is_coreflexive_pair f g] : is_coreflexive_pair g f :=
  is_coreflexive_pair.mk' (common_retraction f g) (right_comp_retraction f g)
    (left_comp_retraction f g)

/-- For an adjunction `F ⊣ G` with counit `ε`, the pair `(FGε_B, ε_FGB)` is reflexive. -/
protected instance app.is_reflexive_pair {C : Type u} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (B : D) :
    is_reflexive_pair (functor.map F (functor.map G (nat_trans.app (adjunction.counit adj) B)))
        (nat_trans.app (adjunction.counit adj) (functor.obj F (functor.obj G B))) :=
  is_reflexive_pair.mk' (functor.map F (nat_trans.app (adjunction.unit adj) (functor.obj G B)))
    (eq.mpr
      (id
        (Eq._oldrec
          (Eq.refl
            (functor.map F (nat_trans.app (adjunction.unit adj) (functor.obj G B)) ≫
                functor.map F (functor.map G (nat_trans.app (adjunction.counit adj) B)) =
              𝟙))
          (Eq.symm
            (functor.map_comp F (nat_trans.app (adjunction.unit adj) (functor.obj G B))
              (functor.map G (nat_trans.app (adjunction.counit adj) B))))))
      (eq.mpr
        (id
          (Eq._oldrec
            (Eq.refl
              (functor.map F
                  (nat_trans.app (adjunction.unit adj) (functor.obj G B) ≫
                    functor.map G (nat_trans.app (adjunction.counit adj) B)) =
                𝟙))
            (adjunction.right_triangle_components adj)))
        (functor.map_id F (functor.obj G (functor.obj 𝟭 B)))))
    (adjunction.left_triangle_components adj)

namespace limits


/-- `C` has reflexive coequalizers if it has coequalizers for every reflexive pair. -/
class has_reflexive_coequalizers (C : Type u) [category C] where
  has_coeq : ∀ {A B : C} (f g : A ⟶ B) [_inst_3 : is_reflexive_pair f g], has_coequalizer f g

/-- `C` has coreflexive equalizers if it has equalizers for every coreflexive pair. -/
class has_coreflexive_equalizers (C : Type u) [category C] where
  has_eq : ∀ {A B : C} (f g : A ⟶ B) [_inst_3 : is_coreflexive_pair f g], has_equalizer f g

theorem has_coequalizer_of_common_section (C : Type u) [category C] [has_reflexive_coequalizers C]
    {A : C} {B : C} {f : A ⟶ B} {g : A ⟶ B} (r : B ⟶ A) (rf : r ≫ f = 𝟙) (rg : r ≫ g = 𝟙) :
    has_coequalizer f g :=
  let _inst : is_reflexive_pair f g := is_reflexive_pair.mk' r rf rg;
  has_reflexive_coequalizers.has_coeq f g

theorem has_equalizer_of_common_retraction (C : Type u) [category C] [has_coreflexive_equalizers C]
    {A : C} {B : C} {f : A ⟶ B} {g : A ⟶ B} (r : B ⟶ A) (fr : f ≫ r = 𝟙) (gr : g ≫ r = 𝟙) :
    has_equalizer f g :=
  let _inst : is_coreflexive_pair f g := is_coreflexive_pair.mk' r fr gr;
  has_coreflexive_equalizers.has_eq f g

/-- If `C` has coequalizers, then it has reflexive coequalizers. -/
protected instance has_reflexive_coequalizers_of_has_coequalizers (C : Type u) [category C]
    [has_coequalizers C] : has_reflexive_coequalizers C :=
  has_reflexive_coequalizers.mk
    fun (A B : C) (f g : A ⟶ B) (i : is_reflexive_pair f g) =>
      limits.has_colimit_of_has_colimits_of_shape (parallel_pair f g)

/-- If `C` has equalizers, then it has coreflexive equalizers. -/
protected instance has_coreflexive_equalizers_of_has_equalizers (C : Type u) [category C]
    [has_equalizers C] : has_coreflexive_equalizers C :=
  has_coreflexive_equalizers.mk
    fun (A B : C) (f g : A ⟶ B) (i : is_coreflexive_pair f g) =>
      limits.has_limit_of_has_limits_of_shape (parallel_pair f g)

end Mathlib