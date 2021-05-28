/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monad.bundled
import Mathlib.category_theory.monoidal.End
import Mathlib.category_theory.monoidal.Mon_
import Mathlib.category_theory.category.Cat
import PostPort

universes u v 

namespace Mathlib

/-!

# The equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

A monad "is just" a monoid in the category of endofunctors.

# Definitions/Theorems

1. `to_Mon` associates a monoid object in `C ⥤ C` to any monad on `C`.
2. `Monad_to_Mon` is the functorial version of `to_Mon`.
3. `of_Mon` associates a monad on `C` to any monoid object in `C ⥤ C`.
4. `Monad_Mon_equiv` is the equivalence between `Monad C` and `Mon_ (C ⥤ C)`.

-/

namespace category_theory


namespace Monad


/-- To every `Monad C` we associated a monoid object in `C ⥤ C`.-/
@[simp] theorem to_Mon_mul {C : Type u} [category C] : ∀ (ᾰ : Monad C), Mon_.mul (to_Mon ᾰ) = μ_ :=
  fun (ᾰ : Monad C) => Eq.refl (Mon_.mul (to_Mon ᾰ))

/-- Passing from `Monad C` to `Mon_ (C ⥤ C)` is functorial. -/
@[simp] theorem Monad_to_Mon_obj (C : Type u) [category C] : ∀ (ᾰ : Monad C), functor.obj (Monad_to_Mon C) ᾰ = to_Mon ᾰ :=
  fun (ᾰ : Monad C) => Eq.refl (functor.obj (Monad_to_Mon C) ᾰ)

/-- To every monoid object in `C ⥤ C` we associate a `Monad C`. -/
def of_Mon {C : Type u} [category C] : Mon_ (C ⥤ C) → Monad C :=
  fun (M : Mon_ (C ⥤ C)) => mk (Mon_.X M)

/-- Passing from `Mon_ (C ⥤ C)` to `Monad C` is functorial. -/
def Mon_to_Monad (C : Type u) [category C] : Mon_ (C ⥤ C) ⥤ Monad C :=
  functor.mk of_Mon
    fun (_x _x_1 : Mon_ (C ⥤ C)) (f : _x ⟶ _x_1) => monad_hom.mk (nat_trans.mk (nat_trans.app (Mon_.hom.hom f)))

namespace Monad_Mon_equiv


/-- Isomorphism of functors used in `Monad_Mon_equiv` -/
@[simp] theorem counit_iso_hom_app_hom {C : Type u} [category C] (_x : Mon_ (C ⥤ C)) : Mon_.hom.hom (nat_trans.app (iso.hom counit_iso) _x) = 𝟙 :=
  Eq.refl (Mon_.hom.hom (nat_trans.app (iso.hom counit_iso) _x))

/-- Auxilliary definition for `Monad_Mon_equiv` -/
def unit_iso_hom {C : Type u} [category C] : 𝟭 ⟶ Monad_to_Mon C ⋙ Mon_to_Monad C :=
  nat_trans.mk fun (_x : Monad C) => monad_hom.mk (nat_trans.mk fun (_x_1 : C) => 𝟙)

/-- Auxilliary definition for `Monad_Mon_equiv` -/
@[simp] theorem unit_iso_inv_app_to_nat_trans_app {C : Type u} [category C] (_x : Monad C) : ∀ (_x_1 : C), nat_trans.app (monad_hom.to_nat_trans (nat_trans.app unit_iso_inv _x)) _x_1 = 𝟙 :=
  fun (_x_1 : C) => Eq.refl (nat_trans.app (monad_hom.to_nat_trans (nat_trans.app unit_iso_inv _x)) _x_1)

/-- Isomorphism of functors used in `Monad_Mon_equiv` -/
def unit_iso {C : Type u} [category C] : 𝟭 ≅ Monad_to_Mon C ⋙ Mon_to_Monad C :=
  iso.mk unit_iso_hom unit_iso_inv

end Monad_Mon_equiv


/-- Oh, monads are just monoids in the category of endofunctors (equivalence of categories). -/
def Monad_Mon_equiv (C : Type u) [category C] : Monad C ≌ Mon_ (C ⥤ C) :=
  equivalence.mk' (Monad_to_Mon C) (Mon_to_Monad C) sorry sorry

