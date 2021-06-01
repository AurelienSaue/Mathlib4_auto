/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Module.monoidal
import Mathlib.algebra.category.Algebra.basic
import Mathlib.category_theory.monoidal.Mon_
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# `Mon_ (Module R) ≌ Algebra R`

The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.

Moreover, this equivalence is compatible with the forgetful functors to `Module R`.
-/

namespace Module


namespace Mon_Module_equivalence_Algebra


@[simp] theorem Mon_.X.ring_zero {R : Type u} [comm_ring R] (A : Mon_ (Module R)) :
    0 = add_comm_group.zero :=
  Eq.refl 0

protected instance Mon_.X.algebra {R : Type u} [comm_ring R] (A : Mon_ (Module R)) :
    algebra R ↥(Mon_.X A) :=
  algebra.mk (ring_hom.mk (linear_map.to_fun (Mon_.one A)) sorry sorry sorry sorry) sorry sorry

@[simp] theorem algebra_map {R : Type u} [comm_ring R] (A : Mon_ (Module R)) (r : R) :
    coe_fn (algebra_map R ↥(Mon_.X A)) r = coe_fn (Mon_.one A) r :=
  rfl

/--
Converting a monoid object in `Module R` to a bundled algebra.
-/
@[simp] theorem functor_obj {R : Type u} [comm_ring R] (A : Mon_ (Module R)) :
    category_theory.functor.obj functor A = Algebra.of R ↥(Mon_.X A) :=
  Eq.refl (category_theory.functor.obj functor A)

/--
Converting a bundled algebra to a monoid object in `Module R`.
-/
def inverse_obj {R : Type u} [comm_ring R] (A : Algebra R) : Mon_ (Module R) :=
  Mon_.mk (of R ↥A) (algebra.linear_map R ↥A) (algebra.lmul' R)

/--
Converting a bundled algebra to a monoid object in `Module R`.
-/
@[simp] theorem inverse_map_hom {R : Type u} [comm_ring R] (A : Algebra R) (B : Algebra R)
    (f : A ⟶ B) : Mon_.hom.hom (category_theory.functor.map inverse f) = alg_hom.to_linear_map f :=
  Eq.refl (Mon_.hom.hom (category_theory.functor.map inverse f))

end Mon_Module_equivalence_Algebra


/--
The category of internal monoid objects in `Module R`
is equivalent to the category of "native" bundled `R`-algebras.
-/
def Mon_Module_equivalence_Algebra {R : Type u} [comm_ring R] : Mon_ (Module R) ≌ Algebra R :=
  category_theory.equivalence.mk' sorry sorry
    (category_theory.nat_iso.of_components
      (fun (A : Mon_ (Module R)) =>
        category_theory.iso.mk (Mon_.hom.mk (linear_map.mk id sorry sorry))
          (Mon_.hom.mk (linear_map.mk id sorry sorry)))
      sorry)
    (category_theory.nat_iso.of_components
      (fun (A : Algebra R) =>
        category_theory.iso.mk (alg_hom.mk id sorry sorry sorry sorry sorry)
          (alg_hom.mk id sorry sorry sorry sorry sorry))
      sorry)

/--
The equivalence `Mon_ (Module R) ≌ Algebra R`
is naturally compatible with the forgetful functors to `Module R`.
-/
def Mon_Module_equivalence_Algebra_forget {R : Type u} [comm_ring R] :
    Mon_Module_equivalence_Algebra.functor ⋙ category_theory.forget₂ (Algebra R) (Module R) ≅
        Mon_.forget (Module R) :=
  category_theory.nat_iso.of_components
    (fun (A : Mon_ (Module R)) =>
      category_theory.iso.mk (linear_map.mk id sorry sorry) (linear_map.mk id sorry sorry))
    sorry

end Mathlib