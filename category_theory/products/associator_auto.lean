/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.products.basic
import PostPort

universes u₁ u₂ u₃ v₁ v₂ v₃ 

namespace Mathlib

/-#
The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/

namespace category_theory.prod


/--
The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
@[simp] theorem associator_map (C : Type u₁) [category C] (D : Type u₂) [category D] (E : Type u₃) [category E] (_x : (C × D) × E) : ∀ (_x_1 : (C × D) × E) (f : _x ⟶ _x_1),
  functor.map (associator C D E) f = (prod.fst (prod.fst f), prod.snd (prod.fst f), prod.snd f) :=
  fun (_x_1 : (C × D) × E) (f : _x ⟶ _x_1) => Eq.refl (functor.map (associator C D E) f)

/--
The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simp] theorem inverse_associator_map (C : Type u₁) [category C] (D : Type u₂) [category D] (E : Type u₃) [category E] (_x : C × D × E) : ∀ (_x_1 : C × D × E) (f : _x ⟶ _x_1),
  functor.map (inverse_associator C D E) f = ((prod.fst f, prod.fst (prod.snd f)), prod.snd (prod.snd f)) :=
  fun (_x_1 : C × D × E) (f : _x ⟶ _x_1) => Eq.refl (functor.map (inverse_associator C D E) f)

/--
The equivalence of categories expressing associativity of products of categories.
-/
def associativity (C : Type u₁) [category C] (D : Type u₂) [category D] (E : Type u₃) [category E] : (C × D) × E ≌ C × D × E :=
  equivalence.mk (associator C D E) (inverse_associator C D E)
    (nat_iso.of_components (fun (X : (C × D) × E) => eq_to_iso sorry) sorry)
    (nat_iso.of_components (fun (X : C × D × E) => eq_to_iso sorry) sorry)

protected instance associator_is_equivalence (C : Type u₁) [category C] (D : Type u₂) [category D] (E : Type u₃) [category E] : is_equivalence (associator C D E) :=
  is_equivalence.of_equivalence (associativity C D E)

protected instance inverse_associator_is_equivalence (C : Type u₁) [category C] (D : Type u₂) [category D] (E : Type u₃) [category E] : is_equivalence (inverse_associator C D E) :=
  is_equivalence.of_equivalence_inverse (associativity C D E)

