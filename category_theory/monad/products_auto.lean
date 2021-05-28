/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.over
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.category_theory.limits.creates
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.monad.algebra
import PostPort

universes u v 

namespace Mathlib

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of comonads is equivalent to the
over category of `X`.

## TODO

Show that `over.forget X : over X ⥤ C` is a comonadic left adjoint and `under.forget : under X ⥤ C`
is a monadic right adjoint.
-/

namespace category_theory


/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
protected instance obj.comonad {C : Type u} [category C] (X : C) [limits.has_binary_products C] : comonad (functor.obj limits.prod.functor X) :=
  comonad.mk (nat_trans.mk fun (Y : C) => limits.prod.snd)
    (nat_trans.mk fun (Y : C) => limits.prod.lift limits.prod.fst 𝟙)

/--
The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
def coalgebra_to_over {C : Type u} [category C] (X : C) [limits.has_binary_products C] : comonad.coalgebra (functor.obj limits.prod.functor X) ⥤ over X :=
  functor.mk
    (fun (A : comonad.coalgebra (functor.obj limits.prod.functor X)) => over.mk (comonad.coalgebra.a A ≫ limits.prod.fst))
    fun (A₁ A₂ : comonad.coalgebra (functor.obj limits.prod.functor X)) (f : A₁ ⟶ A₂) =>
      over.hom_mk (comonad.coalgebra.hom.f f)

/--
The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simp] theorem over_to_coalgebra_map_f {C : Type u} [category C] (X : C) [limits.has_binary_products C] (f₁ : over X) (f₂ : over X) (g : f₁ ⟶ f₂) : comonad.coalgebra.hom.f (functor.map (over_to_coalgebra X) g) = comma_morphism.left g :=
  Eq.refl (comonad.coalgebra.hom.f (functor.map (over_to_coalgebra X) g))

/-- The equivalence from coalgebras for the product comonad to the over category. -/
def coalgebra_equiv_over {C : Type u} [category C] (X : C) [limits.has_binary_products C] : comonad.coalgebra (functor.obj limits.prod.functor X) ≌ over X :=
  equivalence.mk' (coalgebra_to_over X) (over_to_coalgebra X)
    (nat_iso.of_components
      (fun (A : comonad.coalgebra (functor.obj limits.prod.functor X)) =>
        comonad.coalgebra.iso_mk (iso.refl (comonad.coalgebra.A (functor.obj 𝟭 A))) sorry)
      sorry)
    (nat_iso.of_components
      (fun (f : over X) =>
        over.iso_mk (iso.refl (comma.left (functor.obj (over_to_coalgebra X ⋙ coalgebra_to_over X) f))))
      sorry)

/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simp] theorem obj.monad_μ_app {C : Type u} [category C] (X : C) [limits.has_binary_coproducts C] (Y : C) : nat_trans.app μ_ Y = limits.coprod.desc limits.coprod.inl 𝟙 :=
  Eq.refl (nat_trans.app μ_ Y)

/--
The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
def algebra_to_under {C : Type u} [category C] (X : C) [limits.has_binary_coproducts C] : monad.algebra (functor.obj limits.coprod.functor X) ⥤ under X :=
  functor.mk
    (fun (A : monad.algebra (functor.obj limits.coprod.functor X)) => under.mk (limits.coprod.inl ≫ monad.algebra.a A))
    fun (A₁ A₂ : monad.algebra (functor.obj limits.coprod.functor X)) (f : A₁ ⟶ A₂) =>
      under.hom_mk (monad.algebra.hom.f f)

/--
The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simp] theorem under_to_algebra_obj_A {C : Type u} [category C] (X : C) [limits.has_binary_coproducts C] (f : under X) : monad.algebra.A (functor.obj (under_to_algebra X) f) = comma.right f :=
  Eq.refl (monad.algebra.A (functor.obj (under_to_algebra X) f))

/--
The equivalence from algebras for the coproduct monad to the under category.
-/
@[simp] theorem algebra_equiv_under_unit_iso {C : Type u} [category C] (X : C) [limits.has_binary_coproducts C] : equivalence.unit_iso (algebra_equiv_under X) =
  nat_iso.of_components
    (fun (A : monad.algebra (functor.obj limits.coprod.functor X)) =>
      monad.algebra.iso_mk (iso.refl (monad.algebra.A (functor.obj 𝟭 A))) (algebra_equiv_under._proof_1 X A))
    (algebra_equiv_under._proof_2 X) :=
  Eq.refl (equivalence.unit_iso (algebra_equiv_under X))

