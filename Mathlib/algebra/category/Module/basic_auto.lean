/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Group.basic
import Mathlib.category_theory.concrete_category.default
import Mathlib.category_theory.limits.shapes.kernels
import Mathlib.category_theory.preadditive.default
import Mathlib.linear_algebra.basic
import Mathlib.PostPort

universes v u l u_1 

namespace Mathlib

/-- The category of R-modules and their morphisms. -/
structure Module (R : Type u) [ring R] where
  carrier : Type v
  is_add_comm_group : add_comm_group carrier
  is_module : module R carrier

namespace Module


-- TODO revisit this after #1438 merges, to check coercions and instances are handled consistently

protected instance has_coe_to_sort (R : Type u) [ring R] : has_coe_to_sort (Module R) :=
  has_coe_to_sort.mk (Type v) carrier

protected instance category_theory.category (R : Type u) [ring R] :
    category_theory.category (Module R) :=
  category_theory.category.mk

protected instance category_theory.concrete_category (R : Type u) [ring R] :
    category_theory.concrete_category (Module R) :=
  category_theory.concrete_category.mk
    (category_theory.functor.mk (fun (R_1 : Module R) => ↥R_1)
      fun (R_1 S : Module R) (f : R_1 ⟶ S) => ⇑f)

protected instance has_forget_to_AddCommGroup (R : Type u) [ring R] :
    category_theory.has_forget₂ (Module R) AddCommGroup :=
  category_theory.has_forget₂.mk
    (category_theory.functor.mk (fun (M : Module R) => AddCommGroup.of ↥M)
      fun (M₁ M₂ : Module R) (f : M₁ ⟶ M₂) => linear_map.to_add_monoid_hom f)

/-- The object in the category of R-modules associated to an R-module -/
def of (R : Type u) [ring R] (X : Type v) [add_comm_group X] [module R X] : Module R := mk X

protected instance inhabited (R : Type u) [ring R] : Inhabited (Module R) :=
  { default := of R PUnit }

@[simp] theorem coe_of (R : Type u) [ring R] (X : Type u) [add_comm_group X] [module R X] :
    ↥(of R X) = X :=
  rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
module. -/
@[simp] theorem of_self_iso_inv {R : Type u} [ring R] (M : Module R) :
    category_theory.iso.inv (of_self_iso M) = 𝟙 :=
  Eq.refl (category_theory.iso.inv (of_self_iso M))

protected instance of.subsingleton {R : Type u} [ring R] : subsingleton ↥(of R PUnit) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (subsingleton ↥(of R PUnit))) (coe_of R PUnit)))
    punit.subsingleton

protected instance category_theory.limits.has_zero_object {R : Type u} [ring R] :
    category_theory.limits.has_zero_object (Module R) :=
  category_theory.limits.has_zero_object.mk (of R PUnit)
    (fun (X : Module R) => unique.mk { default := 0 } sorry)
    fun (X : Module R) => unique.mk { default := 0 } sorry

@[simp] theorem id_apply {R : Type u} [ring R] {M : Module R} (m : ↥M) : coe_fn 𝟙 m = m := rfl

@[simp] theorem coe_comp {R : Type u} [ring R] {M : Module R} {N : Module R} {U : Module R}
    (f : M ⟶ N) (g : N ⟶ U) : ⇑(f ≫ g) = ⇑g ∘ ⇑f :=
  rfl

end Module


/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Module.as_hom {R : Type u} [ring R] {X₁ : Type v} {X₂ : Type v} [add_comm_group X₁]
    [module R X₁] [add_comm_group X₂] [module R X₂] :
    linear_map R X₁ X₂ → (Module.of R X₁ ⟶ Module.of R X₂) :=
  id

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
@[simp] theorem linear_equiv.to_Module_iso_inv {R : Type u} [ring R] {X₁ : Type v} {X₂ : Type v}
    {g₁ : add_comm_group X₁} {g₂ : add_comm_group X₂} {m₁ : module R X₁} {m₂ : module R X₂}
    (e : linear_equiv R X₁ X₂) :
    category_theory.iso.inv (linear_equiv.to_Module_iso e) = ↑(linear_equiv.symm e) :=
  Eq.refl (category_theory.iso.inv (linear_equiv.to_Module_iso e))

/--
Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s.

This version is better than `linear_equiv_to_Module_iso` when applicable, because Lean can't see
`Module.of R M` is defeq to `M` when `M : Module R`. -/
def linear_equiv.to_Module_iso' {R : Type u} [ring R] {M : Module R} {N : Module R}
    (i : linear_equiv R ↥M ↥N) : M ≅ N :=
  category_theory.iso.mk ↑i ↑(linear_equiv.symm i)

namespace category_theory.iso


/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
@[simp] theorem to_linear_equiv_apply {R : Type u} [ring R] {X : Module R} {Y : Module R}
    (i : X ≅ Y) : ∀ (ᾰ : ↥X), coe_fn (to_linear_equiv i) ᾰ = coe_fn (hom i) ᾰ :=
  fun (ᾰ : ↥X) => Eq.refl (coe_fn (to_linear_equiv i) ᾰ)

end category_theory.iso


/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms
in `Module` -/
@[simp] theorem linear_equiv_iso_Module_iso_hom {R : Type u} [ring R] {X : Type u} {Y : Type u}
    [add_comm_group X] [add_comm_group Y] [module R X] [module R Y] (e : linear_equiv R X Y) :
    category_theory.iso.hom linear_equiv_iso_Module_iso e = linear_equiv.to_Module_iso e :=
  Eq.refl (category_theory.iso.hom linear_equiv_iso_Module_iso e)

namespace Module


protected instance category_theory.preadditive {R : Type u} [ring R] :
    category_theory.preadditive (Module R) :=
  category_theory.preadditive.mk

theorem ker_eq_bot_of_mono {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N)
    [category_theory.mono f] : linear_map.ker f = ⊥ :=
  linear_map.ker_eq_bot_of_cancel
    fun (u v : linear_map R ↥(linear_map.ker f) ↥M) => iff.mp (category_theory.cancel_mono f)

theorem range_eq_top_of_epi {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N)
    [category_theory.epi f] : linear_map.range f = ⊤ :=
  linear_map.range_eq_top_of_cancel
    fun (u v : linear_map R (↥N) (submodule.quotient (linear_map.range f))) =>
      iff.mp (category_theory.cancel_epi f)

theorem mono_of_ker_eq_bot {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N)
    (hf : linear_map.ker f = ⊥) : category_theory.mono f :=
  category_theory.concrete_category.mono_of_injective f (iff.mp linear_map.ker_eq_bot hf)

theorem epi_of_range_eq_top {R : Type u} [ring R] {M : Module R} {N : Module R} (f : M ⟶ N)
    (hf : linear_map.range f = ⊤) : category_theory.epi f :=
  category_theory.concrete_category.epi_of_surjective f (iff.mp linear_map.range_eq_top hf)

end Module


protected instance Module.has_coe {R : Type u} [ring R] (M : Type u) [add_comm_group M]
    [module R M] : has_coe (submodule R M) (Module R) :=
  has_coe.mk fun (N : submodule R M) => Module.of R ↥N

end Mathlib