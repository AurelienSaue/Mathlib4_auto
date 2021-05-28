/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.category_theory.limits.shapes.normal_mono
import Mathlib.category_theory.preadditive.default
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Every non_preadditive_abelian category is preadditive

In mathlib, we define an abelian category as a preadditive category with a zero object,
kernels and cokernels, products and coproducts and in which every monomorphism and epimorphis is
normal.

While virtually every interesting abelian category has a natural preadditive structure (which is why
it is included in the definition), preadditivity is not actually needed: Every category that has
all of the other properties appearing in the definition of an abelian category admits a preadditive
structure. This is the construction we carry out in this file.

The proof proceeds in roughly five steps:
1. Prove some results (for example that all equalizers exist) that would be trivial if we already
   had the preadditive structure but are a bit of work without it.
2. Develop images and coimages to show that every monomorphism is the kernel of its cokernel.

The results of the first two steps are also useful for the "normal" development of abelian
categories, and will be used there.

3. For every object `A`, define a "subtraction" morphism `σ : A ⨯ A ⟶ A` and use it to define
   subtraction on morphisms as `f - g := prod.lift f g ≫ σ`.
4. Prove a small number of identities about this subtraction from the definition of `σ`.
5. From these identities, prove a large number of other identities that imply that defining
   `f + g := f - (0 - g)` indeed gives an abelian group structure on morphisms such that composition
   is bilinear.

The construction is non-trivial and it is quite remarkable that this abelian group structure can
be constructed purely from the existence of a few limits and colimits. What's even more impressive
is that all additive structures on a category are in some sense isomorphic, so for abelian
categories with a natural preadditive structure, this construction manages to "almost" reconstruct
this natural structure. However, we have not formalized this isomorphism.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

-/

namespace category_theory


/-- We call a category `non_preadditive_abelian` if it has a zero object, kernels, cokernels, binary
    products and coproducts, and every monomorphism and every epimorphism is normal. -/
class non_preadditive_abelian (C : Type u) [category C] 
where
  has_zero_object : limits.has_zero_object C
  has_zero_morphisms : limits.has_zero_morphisms C
  has_kernels : limits.has_kernels C
  has_cokernels : limits.has_cokernels C
  has_finite_products : limits.has_finite_products C
  has_finite_coproducts : limits.has_finite_coproducts C
  normal_mono : {X Y : C} → (f : X ⟶ Y) → [_inst_2 : mono f] → normal_mono f
  normal_epi : {X Y : C} → (f : X ⟶ Y) → [_inst_2 : epi f] → normal_epi f

end category_theory


namespace category_theory.non_preadditive_abelian


/-- In a `non_preadditive_abelian` category, every epimorphism is strong. -/
theorem strong_epi_of_epi {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : strong_epi f :=
  category_theory.strong_epi_of_regular_epi f

/-- In a `non_preadditive_abelian` category, a monomorphism which is also an epimorphism is an
    isomorphism. -/
def is_iso_of_mono_of_epi {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] [epi f] : is_iso f :=
  is_iso_of_mono_of_strong_epi f

/-- The pullback of two monomorphisms exists. -/
theorem pullback_of_mono {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} {Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [mono a] [mono b] : limits.has_limit (limits.cospan a b) := sorry

/-- The pushout of two epimorphisms exists. -/
theorem pushout_of_epi {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} {Z : C} (a : X ⟶ Y) (b : X ⟶ Z) [epi a] [epi b] : limits.has_colimit (limits.span a b) := sorry

/-- The pullback of `(𝟙 X, f)` and `(𝟙 X, g)` -/
/-- The equalizer of `f` and `g` exists. -/
theorem has_limit_parallel_pair {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : limits.has_limit (limits.parallel_pair f g) := sorry

/-- The pushout of `(𝟙 Y, f)` and `(𝟙 Y, g)`. -/
/-- The coequalizer of `f` and `g` exists. -/
theorem has_colimit_parallel_pair {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : limits.has_colimit (limits.parallel_pair f g) := sorry

/-- A `non_preadditive_abelian` category has all equalizers. -/
protected instance has_equalizers {C : Type u} [category C] [non_preadditive_abelian C] : limits.has_equalizers C :=
  limits.has_equalizers_of_has_limit_parallel_pair C

/-- A `non_preadditive_abelian` category has all coequalizers. -/
protected instance has_coequalizers {C : Type u} [category C] [non_preadditive_abelian C] : limits.has_coequalizers C :=
  limits.has_coequalizers_of_has_colimit_parallel_pair C

/-- If a zero morphism is a kernel of `f`, then `f` is a monomorphism. -/
theorem mono_of_zero_kernel {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) (l : limits.is_limit
  (limits.kernel_fork.of_ι 0
    ((fun (this : 0 ≫ f = 0) => this)
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : Z ⟶ Y) (e_1 : a = a_1) (ᾰ ᾰ_1 : Z ⟶ Y) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (0 ≫ f) 0 limits.zero_comp 0 0 (Eq.refl 0))
            (propext (eq_self_iff_true 0))))
        trivial)))) : mono f := sorry

/-- If a zero morphism is a cokernel of `f`, then `f` is an epimorphism. -/
theorem epi_of_zero_cokernel {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (Z : C) (l : limits.is_colimit
  (limits.cokernel_cofork.of_π 0
    ((fun (this : f ≫ 0 = 0) => this)
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : X ⟶ Z) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ Z) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (f ≫ 0) 0 limits.comp_zero 0 0 (Eq.refl 0))
            (propext (eq_self_iff_true 0))))
        trivial)))) : epi f := sorry

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`. -/
def zero_kernel_of_cancel_zero {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (hf : ∀ (Z : C) (g : Z ⟶ X), g ≫ f = 0 → g = 0) : limits.is_limit (limits.kernel_fork.of_ι 0 (zero_kernel_of_cancel_zero._proof_1 f)) :=
  limits.fork.is_limit.mk (limits.kernel_fork.of_ι 0 sorry) (fun (s : limits.fork f 0) => 0) sorry sorry

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f`. -/
def zero_cokernel_of_zero_cancel {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (hf : ∀ (Z : C) (g : Y ⟶ Z), f ≫ g = 0 → g = 0) : limits.is_colimit (limits.cokernel_cofork.of_π 0 (zero_cokernel_of_zero_cancel._proof_1 f)) :=
  limits.cofork.is_colimit.mk (limits.cokernel_cofork.of_π 0 sorry) (fun (s : limits.cofork f 0) => 0) sorry sorry

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `f` is a monomorphism. -/
theorem mono_of_cancel_zero {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (hf : ∀ (Z : C) (g : Z ⟶ X), g ≫ f = 0 → g = 0) : mono f :=
  mono_of_zero_kernel f 0 (zero_kernel_of_cancel_zero f hf)

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `g` is a monomorphism. -/
theorem epi_of_zero_cancel {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) (hf : ∀ (Z : C) (g : Y ⟶ Z), f ≫ g = 0 → g = 0) : epi f :=
  epi_of_zero_cokernel f 0 (zero_cokernel_of_zero_cancel f hf)

/-- The kernel of the cokernel of `f` is called the image of `f`. -/
protected def image {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : C :=
  limits.kernel (limits.cokernel.π f)

/-- The inclusion of the image into the codomain. -/
protected def image.ι {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : non_preadditive_abelian.image f ⟶ Q :=
  limits.kernel.ι (limits.cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
protected def factor_thru_image {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : P ⟶ non_preadditive_abelian.image f :=
  limits.kernel.lift (limits.cokernel.π f) f sorry

/-- `f` factors through its image via the canonical morphism `p`. -/
@[simp] theorem image.fac_assoc {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) {X' : C} (f' : Q ⟶ X') : non_preadditive_abelian.factor_thru_image f ≫ image.ι f ≫ f' = f ≫ f' := sorry

/-- The map `p : P ⟶ image f` is an epimorphism -/
protected instance factor_thru_image.category_theory.epi {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : epi (non_preadditive_abelian.factor_thru_image f) := sorry

-- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.

protected instance mono_factor_thru_image {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) [mono f] : mono (non_preadditive_abelian.factor_thru_image f) :=
  mono_of_mono_fac (image.fac f)

protected instance is_iso_factor_thru_image {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) [mono f] : is_iso (non_preadditive_abelian.factor_thru_image f) :=
  is_iso_of_mono_of_epi (non_preadditive_abelian.factor_thru_image f)

/-- The cokernel of the kernel of `f` is called the coimage of `f`. -/
protected def coimage {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : C :=
  limits.cokernel (limits.kernel.ι f)

/-- The projection onto the coimage. -/
protected def coimage.π {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : P ⟶ non_preadditive_abelian.coimage f :=
  limits.cokernel.π (limits.kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
protected def factor_thru_coimage {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : non_preadditive_abelian.coimage f ⟶ Q :=
  limits.cokernel.desc (limits.kernel.ι f) f sorry

/-- `f` factors through its coimage via the canonical morphism `p`. -/
protected theorem coimage.fac {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : coimage.π f ≫ non_preadditive_abelian.factor_thru_coimage f = f :=
  limits.cokernel.π_desc (limits.kernel.ι f) f (factor_thru_coimage._proof_1 f)

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
protected instance factor_thru_coimage.category_theory.mono {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) : mono (non_preadditive_abelian.factor_thru_coimage f) := sorry

protected instance epi_factor_thru_coimage {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : epi (non_preadditive_abelian.factor_thru_coimage f) :=
  epi_of_epi_fac (coimage.fac f)

protected instance is_iso_factor_thru_coimage {C : Type u} [category C] [non_preadditive_abelian C] {P : C} {Q : C} (f : P ⟶ Q) [epi f] : is_iso (non_preadditive_abelian.factor_thru_coimage f) :=
  is_iso_of_mono_of_epi (non_preadditive_abelian.factor_thru_coimage f)

/-- In a `non_preadditive_abelian` category, an epi is the cokernel of its kernel. More precisely:
    If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} {f : X ⟶ Y} [epi f] (s : limits.fork f 0) (h : limits.is_limit s) : limits.is_colimit (limits.cokernel_cofork.of_π f (epi_is_cokernel_of_kernel._proof_1 s)) :=
  limits.is_cokernel.cokernel_iso (limits.fork.ι s) f
    (limits.cokernel.of_iso_comp
      (nat_trans.app (limits.cone.π (limits.limit.cone (limits.parallel_pair f 0))) limits.walking_parallel_pair.zero)
      (limits.fork.ι s) (limits.is_limit.cone_point_unique_up_to_iso (limits.limit.is_limit (limits.parallel_pair f 0)) h)
      sorry)
    (as_iso (non_preadditive_abelian.factor_thru_coimage f)) sorry

/-- In a `non_preadditive_abelian` category, a mono is the kernel of its cokernel. More precisely:
    If `f` is a monomorphism and `s` is some colimit cokernel cocone on `f`, then `f` is a kernel
    of `cofork.π s`. -/
def mono_is_kernel_of_cokernel {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} {f : X ⟶ Y} [mono f] (s : limits.cofork f 0) (h : limits.is_colimit s) : limits.is_limit (limits.kernel_fork.of_ι f (mono_is_kernel_of_cokernel._proof_1 s)) :=
  limits.is_kernel.iso_kernel (limits.cofork.π s) f
    (limits.kernel.of_comp_iso
      (nat_trans.app (limits.cocone.ι (limits.colimit.cocone (limits.parallel_pair f 0)))
        limits.walking_parallel_pair.one)
      (limits.cofork.π s)
      (limits.is_colimit.cocone_point_unique_up_to_iso h (limits.colimit.is_colimit (limits.parallel_pair f 0))) sorry)
    (as_iso (non_preadditive_abelian.factor_thru_image f)) sorry

/-- The composite `A ⟶ A ⨯ A ⟶ cokernel (Δ A)`, where the first map is `(𝟙 A, 0)` and the second map
    is the canonical projection into the cokernel. -/
def r {C : Type u} [category C] [non_preadditive_abelian C] (A : C) : A ⟶ limits.cokernel (limits.diag A) :=
  limits.prod.lift 𝟙 0 ≫ limits.cokernel.π (limits.diag A)

protected instance mono_Δ {C : Type u} [category C] [non_preadditive_abelian C] {A : C} : mono (limits.diag A) :=
  mono_of_mono_fac (limits.prod.lift_fst 𝟙 𝟙)

protected instance mono_r {C : Type u} [category C] [non_preadditive_abelian C] {A : C} : mono (r A) := sorry

protected instance epi_r {C : Type u} [category C] [non_preadditive_abelian C] {A : C} : epi (r A) := sorry

protected instance is_iso_r {C : Type u} [category C] [non_preadditive_abelian C] {A : C} : is_iso (r A) :=
  is_iso_of_mono_of_epi (r A)

/-- The composite `A ⨯ A ⟶ cokernel (diag A) ⟶ A` given by the natural projection into the cokernel
    followed by the inverse of `r`. In the category of modules, using the normal kernels and
    cokernels, this map is equal to the map `(a, b) ↦ a - b`, hence the name `σ` for
    "subtraction". -/
def σ {C : Type u} [category C] [non_preadditive_abelian C] {A : C} : A ⨯ A ⟶ A :=
  limits.cokernel.π (limits.diag A) ≫ inv (r A)

@[simp] theorem diag_σ {C : Type u} [category C] [non_preadditive_abelian C] {X : C} : limits.diag X ≫ σ = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (limits.diag X ≫ σ = 0)) (limits.cokernel.condition_assoc (limits.diag X) (inv (r X)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 ≫ inv (r X) = 0)) limits.zero_comp)) (Eq.refl 0))

@[simp] theorem lift_σ_assoc {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {X' : C} (f' : X ⟶ X') : limits.prod.lift 𝟙 0 ≫ limits.cokernel.π (limits.diag X) ≫ inv (r X) ≫ f' = f' := sorry

theorem lift_map {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) : limits.prod.lift 𝟙 0 ≫ limits.prod.map f f = f ≫ limits.prod.lift 𝟙 0 := sorry

/-- σ is a cokernel of Δ X. -/
def is_colimit_σ {C : Type u} [category C] [non_preadditive_abelian C] {X : C} : limits.is_colimit (limits.cokernel_cofork.of_π σ diag_σ) :=
  limits.cokernel.cokernel_iso (limits.diag X) σ (iso.symm (as_iso (r X))) sorry

/-- This is the key identity satisfied by `σ`. -/
theorem σ_comp {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (f : X ⟶ Y) : σ ≫ f = limits.prod.map f f ≫ σ := sorry

/- We write `f - g` for `prod.lift f g ≫ σ`. -/

/-- Subtraction of morphisms in a `non_preadditive_abelian` category. -/
def has_sub {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} : Sub (X ⟶ Y) :=
  { sub := fun (f g : X ⟶ Y) => limits.prod.lift f g ≫ σ }

/- We write `-f` for `0 - f`. -/

/-- Negation of morphisms in a `non_preadditive_abelian` category. -/
def has_neg {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} : Neg (X ⟶ Y) :=
  { neg := fun (f : X ⟶ Y) => 0 - f }

/- We write `f + g` for `f - (-g)`. -/

/-- Addition of morphisms in a `non_preadditive_abelian` category. -/
def has_add {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} : Add (X ⟶ Y) :=
  { add := fun (f g : X ⟶ Y) => f - -g }

theorem sub_def {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : a - b = limits.prod.lift a b ≫ σ :=
  rfl

theorem add_def {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : a + b = a - -b :=
  rfl

theorem neg_def {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : -a = 0 - a :=
  rfl

theorem sub_zero {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : a - 0 = a := sorry

theorem sub_self {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : a - a = 0 := sorry

theorem lift_sub_lift {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) (c : X ⟶ Y) (d : X ⟶ Y) : limits.prod.lift a b - limits.prod.lift c d = limits.prod.lift (a - c) (b - d) := sorry

theorem sub_sub_sub {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) (c : X ⟶ Y) (d : X ⟶ Y) : a - c - (b - d) = a - b - (c - d) := sorry

theorem neg_sub {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : -a - b = -b - a := sorry

theorem neg_neg {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : --a = a := sorry

theorem add_comm {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : a + b = b + a := sorry

theorem add_neg {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : a + -b = a - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + -b = a - b)) (add_def a (-b))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - --b = a - b)) (neg_neg b))) (Eq.refl (a - b)))

theorem add_neg_self {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : a + -a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + -a = 0)) (add_neg a a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - a = 0)) (sub_self a))) (Eq.refl 0))

theorem neg_add_self {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : -a + a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-a + a = 0)) (add_comm (-a) a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -a = 0)) (add_neg_self a))) (Eq.refl 0))

theorem neg_sub' {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : -(a - b) = -a + b := sorry

theorem neg_add {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) : -(a + b) = -a - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (-(a + b) = -a - b)) (add_def a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (-(a - -b) = -a - b)) (neg_sub' a (-b))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (-a + -b = -a - b)) (add_neg (-a) b))) (Eq.refl (-a - b))))

theorem sub_add {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) (c : X ⟶ Y) : a - b + c = a - (b - c) := sorry

theorem add_assoc {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) (b : X ⟶ Y) (c : X ⟶ Y) : a + b + c = a + (b + c) := sorry

theorem add_zero {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} (a : X ⟶ Y) : a + 0 = a := sorry

theorem comp_sub {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y ⟶ Z) : f ≫ (g - h) = f ≫ g - f ≫ h := sorry

theorem sub_comp {C : Type u} [category C] [non_preadditive_abelian C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Y) (h : Y ⟶ Z) : (f - g) ≫ h = f ≫ h - g ≫ h := sorry

theorem comp_add {C : Type u} [category C] [non_preadditive_abelian C] (X : C) (Y : C) (Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := sorry

theorem add_comp {C : Type u} [category C] [non_preadditive_abelian C] (X : C) (Y : C) (Z : C) (f : X ⟶ Y) (g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := sorry

/-- Every `non_preadditive_abelian` category is preadditive. -/
def preadditive {C : Type u} [category C] [non_preadditive_abelian C] : preadditive C :=
  preadditive.mk

