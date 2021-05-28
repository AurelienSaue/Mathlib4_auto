/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.CommRing.basic
import Mathlib.data.mv_polynomial.default
import Mathlib.PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

namespace CommRing


/--
The free functor `Type u ⥤ CommRing` sending a type `X` to the multivariable (commutative)
polynomials with variables `x : X`.
-/
def free : Type u ⥤ CommRing :=
  category_theory.functor.mk (fun (α : Type u) => of (mv_polynomial α ℤ))
    fun (X Y : Type u) (f : X ⟶ Y) => ↑(mv_polynomial.rename f)

@[simp] theorem free_obj_coe {α : Type u} : ↥(category_theory.functor.obj free α) = mv_polynomial α ℤ :=
  rfl

@[simp] theorem free_map_coe {α : Type u} {β : Type u} {f : α → β} : ⇑(category_theory.functor.map free f) = ⇑(mv_polynomial.rename f) :=
  rfl

/--
The free-forgetful adjunction for commutative rings.
-/
def adj : free ⊣ category_theory.forget CommRing :=
  category_theory.adjunction.mk_of_hom_equiv
    (category_theory.adjunction.core_hom_equiv.mk fun (X : Type (max u_1 u_2)) (R : CommRing) => mv_polynomial.hom_equiv)

