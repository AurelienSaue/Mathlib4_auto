/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group.hom
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes v u l u_1 

namespace Mathlib

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

* Definition of preadditive categories and basic properties
* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

## Implementation notes

The simp normal form for negation and composition is to push negations as far as possible to
the outside. For example, `f ≫ (-g)` and `(-f) ≫ g` both become `-(f ≫ g)`, and `(-f) ≫ (-g)`
is simplified to `f ≫ g`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

## Tags

additive, preadditive, Hom group, Ab-category, Ab-enriched
-/

namespace category_theory


/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class preadditive (C : Type u) [category C] where
  hom_group :
    autoParam ((P Q : C) → add_comm_group (P ⟶ Q))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])
  add_comp' :
    autoParam (∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  comp_add' :
    autoParam (∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g')
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem preadditive.add_comp {C : Type u} [category C] [c : preadditive C] (P : C) (Q : C)
    (R : C) (f : P ⟶ Q) (f' : P ⟶ Q) (g : Q ⟶ R) : (f + f') ≫ g = f ≫ g + f' ≫ g :=
  sorry

@[simp] theorem preadditive.comp_add {C : Type u} [category C] [c : preadditive C] (P : C) (Q : C)
    (R : C) (f : P ⟶ Q) (g : Q ⟶ R) (g' : Q ⟶ R) : f ≫ (g + g') = f ≫ g + f ≫ g' :=
  sorry

@[simp] theorem preadditive.add_comp_assoc {C : Type u} [category C] [c : preadditive C] (P : C)
    (Q : C) (R : C) (f : P ⟶ Q) (f' : P ⟶ Q) (g : Q ⟶ R) {X' : C} :
    ∀ (f'_1 : R ⟶ X'), (f + f') ≫ g ≫ f'_1 = (f ≫ g + f' ≫ g) ≫ f'_1 :=
  sorry

theorem preadditive.comp_add_assoc {C : Type u} [category C] [c : preadditive C] (P : C) (Q : C)
    (R : C) (f : P ⟶ Q) (g : Q ⟶ R) (g' : Q ⟶ R) {X' : C} (f' : R ⟶ X') :
    f ≫ (g + g') ≫ f' = (f ≫ g + f ≫ g') ≫ f' :=
  sorry

end category_theory


namespace category_theory.preadditive


/-- Composition by a fixed left argument as a group homomorphism -/
def left_comp {C : Type u} [category C] [preadditive C] {P : C} {Q : C} (R : C) (f : P ⟶ Q) :
    (Q ⟶ R) →+ (P ⟶ R) :=
  add_monoid_hom.mk' (fun (g : Q ⟶ R) => f ≫ g) sorry

/-- Composition by a fixed right argument as a group homomorphism -/
def right_comp {C : Type u} [category C] [preadditive C] (P : C) {Q : C} {R : C} (g : Q ⟶ R) :
    (P ⟶ Q) →+ (P ⟶ R) :=
  add_monoid_hom.mk' (fun (f : P ⟶ Q) => f ≫ g) sorry

@[simp] theorem sub_comp_assoc {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C}
    (f : P ⟶ Q) (f' : P ⟶ Q) (g : Q ⟶ R) {X' : C} :
    ∀ (f'_1 : R ⟶ X'), (f - f') ≫ g ≫ f'_1 = (f ≫ g - f' ≫ g) ≫ f'_1 :=
  sorry

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.

@[simp] theorem comp_sub {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C}
    (f : P ⟶ Q) (g : Q ⟶ R) (g' : Q ⟶ R) : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  add_monoid_hom.map_sub (left_comp R f) g g'

@[simp] theorem neg_comp {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C}
    (f : P ⟶ Q) (g : Q ⟶ R) : (-f) ≫ g = -f ≫ g :=
  add_monoid_hom.map_neg (right_comp P g) f

/- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma. -/

theorem comp_neg_assoc {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C} (f : P ⟶ Q)
    (g : Q ⟶ R) {X' : C} (f' : R ⟶ X') : f ≫ (-g) ≫ f' = (-f ≫ g) ≫ f' :=
  sorry

theorem neg_comp_neg {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C} (f : P ⟶ Q)
    (g : Q ⟶ R) : (-f) ≫ (-g) = f ≫ g :=
  sorry

theorem comp_sum {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C} {J : Type u_1}
    {s : finset J} (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
    (f ≫ finset.sum s fun (j : J) => g j) = finset.sum s fun (j : J) => f ≫ g j :=
  sorry

theorem sum_comp_assoc {C : Type u} [category C] [preadditive C] {P : C} {Q : C} {R : C}
    {J : Type u_1} {s : finset J} (f : J → (P ⟶ Q)) (g : Q ⟶ R) {X' : C} (f' : R ⟶ X') :
    finset.sum s f ≫ g ≫ f' = (finset.sum s fun (j : J) => f j ≫ g) ≫ f' :=
  sorry

protected instance has_neg.neg.category_theory.epi {C : Type u} [category C] [preadditive C] {P : C}
    {Q : C} {f : P ⟶ Q} [epi f] : epi (-f) :=
  epi.mk
    fun (R : C) (g g' : Q ⟶ R) (H : (-f) ≫ g = (-f) ≫ g') =>
      eq.mp (Eq._oldrec (Eq.refl (-g = -g')) (propext neg_inj))
        (eq.mp (Eq._oldrec (Eq.refl (f ≫ (-g) = f ≫ (-g'))) (propext (cancel_epi f)))
          (eq.mp (Eq._oldrec (Eq.refl (f ≫ (-g) = -f ≫ g')) (Eq.symm (comp_neg f g')))
            (eq.mp (Eq._oldrec (Eq.refl (-f ≫ g = -f ≫ g')) (Eq.symm (comp_neg f g)))
              (eq.mp (Eq._oldrec (Eq.refl (-f ≫ g = (-f) ≫ g')) (neg_comp f g'))
                (eq.mp (Eq._oldrec (Eq.refl ((-f) ≫ g = (-f) ≫ g')) (neg_comp f g)) H)))))

protected instance has_neg.neg.category_theory.mono {C : Type u} [category C] [preadditive C]
    {P : C} {Q : C} {f : P ⟶ Q} [mono f] : mono (-f) :=
  mono.mk
    fun (R : C) (g g' : R ⟶ P) (H : g ≫ (-f) = g' ≫ (-f)) =>
      eq.mp (Eq._oldrec (Eq.refl (-g = -g')) (propext neg_inj))
        (eq.mp (Eq._oldrec (Eq.refl ((-g) ≫ f = (-g') ≫ f)) (propext (cancel_mono f)))
          (eq.mp (Eq._oldrec (Eq.refl ((-g) ≫ f = -g' ≫ f)) (Eq.symm (neg_comp g' f)))
            (eq.mp (Eq._oldrec (Eq.refl (-g ≫ f = -g' ≫ f)) (Eq.symm (neg_comp g f)))
              (eq.mp (Eq._oldrec (Eq.refl (-g ≫ f = g' ≫ (-f))) (comp_neg g' f))
                (eq.mp (Eq._oldrec (Eq.refl (g ≫ (-f) = g' ≫ (-f))) (comp_neg g f)) H)))))

protected instance preadditive_has_zero_morphisms {C : Type u} [category C] [preadditive C] :
    limits.has_zero_morphisms C :=
  limits.has_zero_morphisms.mk

theorem mono_of_cancel_zero {C : Type u} [category C] [preadditive C] {Q : C} {R : C} (f : Q ⟶ R)
    (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) : mono f :=
  mono.mk
    fun (P : C) (g g' : P ⟶ Q) (hg : g ≫ f = g' ≫ f) =>
      iff.mp sub_eq_zero
        (h (g - g')
          (Eq.trans (add_monoid_hom.map_sub (right_comp P f) g g') (iff.mpr sub_eq_zero hg)))

theorem mono_iff_cancel_zero {C : Type u} [category C] [preadditive C] {Q : C} {R : C} (f : Q ⟶ R) :
    mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
  { mp := fun (m : mono f) (P : C) (g : P ⟶ Q) => limits.zero_of_comp_mono f,
    mpr := mono_of_cancel_zero f }

theorem mono_of_kernel_zero {C : Type u} [category C] [preadditive C] {X : C} {Y : C} {f : X ⟶ Y}
    [limits.has_limit (limits.parallel_pair f 0)] (w : limits.kernel.ι f = 0) : mono f :=
  sorry

theorem epi_of_cancel_zero {C : Type u} [category C] [preadditive C] {P : C} {Q : C} (f : P ⟶ Q)
    (h : ∀ {R : C} (g : Q ⟶ R), f ≫ g = 0 → g = 0) : epi f :=
  epi.mk
    fun (R : C) (g g' : Q ⟶ R) (hg : f ≫ g = f ≫ g') =>
      iff.mp sub_eq_zero
        (h (g - g')
          (Eq.trans (add_monoid_hom.map_sub (left_comp R f) g g') (iff.mpr sub_eq_zero hg)))

theorem epi_iff_cancel_zero {C : Type u} [category C] [preadditive C] {P : C} {Q : C} (f : P ⟶ Q) :
    epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
  { mp := fun (e : epi f) (R : C) (g : Q ⟶ R) => limits.zero_of_epi_comp f,
    mpr := epi_of_cancel_zero f }

theorem epi_of_cokernel_zero {C : Type u} [category C] [preadditive C] {X : C} {Y : C} (f : X ⟶ Y)
    [limits.has_colimit (limits.parallel_pair f 0)] (w : limits.cokernel.π f = 0) : epi f :=
  sorry

end preadditive


/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
theorem preadditive.has_limit_parallel_pair {C : Type u} [category C] [preadditive C] {X : C}
    {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [limits.has_kernel (f - g)] :
    limits.has_limit (limits.parallel_pair f g) :=
  sorry

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
theorem preadditive.has_equalizers_of_has_kernels {C : Type u} [category C] [preadditive C]
    [limits.has_kernels C] : limits.has_equalizers C :=
  limits.has_equalizers_of_has_limit_parallel_pair C

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
theorem preadditive.has_colimit_parallel_pair {C : Type u} [category C] [preadditive C] {X : C}
    {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [limits.has_cokernel (f - g)] :
    limits.has_colimit (limits.parallel_pair f g) :=
  sorry

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
theorem preadditive.has_coequalizers_of_has_cokernels {C : Type u} [category C] [preadditive C]
    [limits.has_cokernels C] : limits.has_coequalizers C :=
  limits.has_coequalizers_of_has_colimit_parallel_pair C

end Mathlib