/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.algebra.algebra.subalgebra
import Mathlib.algebra.free_algebra
import Mathlib.algebra.category.CommRing.basic
import Mathlib.algebra.category.Module.basic
import Mathlib.PostPort

universes v u l u_1 

namespace Mathlib

/-- The category of R-modules and their morphisms. -/
structure Algebra (R : Type u) [comm_ring R] where
  carrier : Type v
  is_ring : ring carrier
  is_algebra : algebra R carrier

namespace Algebra


protected instance has_coe_to_sort (R : Type u) [comm_ring R] : has_coe_to_sort (Algebra R) :=
  has_coe_to_sort.mk (Type v) carrier

protected instance category_theory.category (R : Type u) [comm_ring R] :
    category_theory.category (Algebra R) :=
  category_theory.category.mk

protected instance category_theory.concrete_category (R : Type u) [comm_ring R] :
    category_theory.concrete_category (Algebra R) :=
  category_theory.concrete_category.mk
    (category_theory.functor.mk (fun (R_1 : Algebra R) => ↥R_1)
      fun (R_1 S : Algebra R) (f : R_1 ⟶ S) => ⇑f)

protected instance has_forget_to_Ring (R : Type u) [comm_ring R] :
    category_theory.has_forget₂ (Algebra R) Ring :=
  category_theory.has_forget₂.mk
    (category_theory.functor.mk (fun (A : Algebra R) => Ring.of ↥A)
      fun (A₁ A₂ : Algebra R) (f : A₁ ⟶ A₂) => alg_hom.to_ring_hom f)

protected instance has_forget_to_Module (R : Type u) [comm_ring R] :
    category_theory.has_forget₂ (Algebra R) (Module R) :=
  category_theory.has_forget₂.mk
    (category_theory.functor.mk (fun (M : Algebra R) => Module.of R ↥M)
      fun (M₁ M₂ : Algebra R) (f : M₁ ⟶ M₂) => alg_hom.to_linear_map f)

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (R : Type u) [comm_ring R] (X : Type v) [ring X] [algebra R X] : Algebra R := mk X

protected instance inhabited (R : Type u) [comm_ring R] : Inhabited (Algebra R) :=
  { default := of R R }

@[simp] theorem coe_of (R : Type u) [comm_ring R] (X : Type u) [ring X] [algebra R X] :
    ↥(of R X) = X :=
  rfl

/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simp] theorem of_self_iso_hom {R : Type u} [comm_ring R] (M : Algebra R) :
    category_theory.iso.hom (of_self_iso M) = 𝟙 :=
  Eq.refl (category_theory.iso.hom (of_self_iso M))

@[simp] theorem id_apply {R : Type u} [comm_ring R] {M : Module R} (m : ↥M) : coe_fn 𝟙 m = m := rfl

@[simp] theorem coe_comp {R : Type u} [comm_ring R] {M : Module R} {N : Module R} {U : Module R}
    (f : M ⟶ N) (g : N ⟶ U) : ⇑(f ≫ g) = ⇑g ∘ ⇑f :=
  rfl

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
@[simp] theorem free_obj_is_algebra (R : Type u) [comm_ring R] (S : Type u_1) :
    is_algebra (category_theory.functor.obj (free R) S) = free_algebra.algebra R S :=
  Eq.refl (is_algebra (category_theory.functor.obj (free R) S))

/-- The free/forget ajunction for `R`-algebras. -/
def adj (R : Type u) [comm_ring R] : free R ⊣ category_theory.forget (Algebra R) :=
  category_theory.adjunction.mk_of_hom_equiv
    (category_theory.adjunction.core_hom_equiv.mk
      fun (X : Type (max u u_1)) (A : Algebra R) => equiv.symm (free_algebra.lift R))

end Algebra


/-- Build an isomorphism in the category `Algebra R` from a `alg_equiv` between `algebra`s. -/
@[simp] theorem alg_equiv.to_Algebra_iso_hom {R : Type u} [comm_ring R] {X₁ : Type u} {X₂ : Type u}
    {g₁ : ring X₁} {g₂ : ring X₂} {m₁ : algebra R X₁} {m₂ : algebra R X₂} (e : alg_equiv R X₁ X₂) :
    category_theory.iso.hom (alg_equiv.to_Algebra_iso e) = ↑e :=
  Eq.refl (category_theory.iso.hom (alg_equiv.to_Algebra_iso e))

namespace category_theory.iso


/-- Build a `alg_equiv` from an isomorphism in the category `Algebra R`. -/
@[simp] theorem to_alg_equiv_apply {R : Type u} [comm_ring R] {X : Algebra R} {Y : Algebra R}
    (i : X ≅ Y) : ∀ (ᾰ : ↥X), coe_fn (to_alg_equiv i) ᾰ = coe_fn (hom i) ᾰ :=
  fun (ᾰ : ↥X) => Eq.refl (coe_fn (to_alg_equiv i) ᾰ)

end category_theory.iso


/-- Algebra equivalences between `algebras`s are the same as (isomorphic to) isomorphisms in
`Algebra`. -/
def alg_equiv_iso_Algebra_iso {R : Type u} [comm_ring R] {X : Type u} {Y : Type u} [ring X] [ring Y]
    [algebra R X] [algebra R Y] : alg_equiv R X Y ≅ Algebra.of R X ≅ Algebra.of R Y :=
  category_theory.iso.mk (fun (e : alg_equiv R X Y) => alg_equiv.to_Algebra_iso e)
    fun (i : Algebra.of R X ≅ Algebra.of R Y) => category_theory.iso.to_alg_equiv i

protected instance Algebra.has_coe {R : Type u} [comm_ring R] (X : Type u) [ring X] [algebra R X] :
    has_coe (subalgebra R X) (Algebra R) :=
  has_coe.mk fun (N : subalgebra R X) => Algebra.of R ↥N

protected instance Algebra.forget_reflects_isos {R : Type u} [comm_ring R] :
    category_theory.reflects_isomorphisms (category_theory.forget (Algebra R)) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : Algebra R) (f : X ⟶ Y)
      (_x :
      category_theory.is_iso
        (category_theory.functor.map (category_theory.forget (Algebra R)) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget (Algebra R)) X ≅
          category_theory.functor.obj (category_theory.forget (Algebra R)) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget (Algebra R)) f);
      let e : alg_equiv R ↥X ↥Y :=
        alg_equiv.mk (alg_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry sorry
          sorry sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (alg_equiv.to_Algebra_iso e))

end Mathlib