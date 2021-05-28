/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monoidal.braided
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.terminal
import PostPort

universes u v 

namespace Mathlib

/-!
# The natural monoidal structure on any category with finite (co)products.

A category with a monoidal structure provided in this way is sometimes called a (co)cartesian category,
although this is also sometimes used to mean a finitely complete category.
(See <https://ncatlab.org/nlab/show/cartesian+category>.)

As this works with either products or coproducts,
and sometimes we want to think of a different monoidal structure entirely,
we don't set up either construct as an instance.

## Implementation
We had previously chosen to rely on `has_terminal` and `has_binary_products` instead of
`has_finite_products`, because we were later relying on the definitional form of the tensor product.
Now that `has_limit` has been refactored to be a `Prop`,
this issue is irrelevant and we could simplify the construction here.

See `category_theory.monoidal.of_chosen_finite_products` for a variant of this construction
which allows specifying a particular choice of terminal object and binary products.
-/

namespace category_theory


/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_has_finite_products (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] : monoidal_category C :=
  monoidal_category.mk (fun (X Y : C) => X ⨯ Y)
    (fun (_x _x_1 _x_2 _x_3 : C) (f : _x ⟶ _x_1) (g : _x_2 ⟶ _x_3) => limits.prod.map f g) (⊤_C) limits.prod.associator
    (fun (P : C) => limits.prod.left_unitor P) fun (P : C) => limits.prod.right_unitor P

/--
The monoidal structure coming from finite products is symmetric.
-/
@[simp] theorem symmetric_of_has_finite_products_to_braided_category_braiding (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) (Y : C) : β_ = limits.prod.braiding X Y :=
  Eq.refl β_

namespace monoidal_of_has_finite_products


@[simp] theorem tensor_obj (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) (Y : C) : X ⊗ Y = (X ⨯ Y) :=
  rfl

@[simp] theorem tensor_hom (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.prod.map f g :=
  rfl

@[simp] theorem left_unitor_hom (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) : iso.hom λ_ = limits.prod.snd :=
  rfl

@[simp] theorem left_unitor_inv (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) : iso.inv λ_ = limits.prod.lift (limits.terminal.from X) 𝟙 :=
  rfl

@[simp] theorem right_unitor_hom (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) : iso.hom ρ_ = limits.prod.fst :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular

@[simp] theorem right_unitor_inv (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) : iso.inv ρ_ = limits.prod.lift 𝟙 (limits.terminal.from X) :=
  rfl

-- categories the right hand side will simplify significantly further.

-- For now, we'll plan to create specialised simp lemmas in each particular category.

theorem associator_hom (C : Type u) [category C] [limits.has_terminal C] [limits.has_binary_products C] (X : C) (Y : C) (Z : C) : iso.hom α_ =
  limits.prod.lift (limits.prod.fst ≫ limits.prod.fst)
    (limits.prod.lift (limits.prod.fst ≫ limits.prod.snd) limits.prod.snd) :=
  rfl

end monoidal_of_has_finite_products


/-- A category with an initial object and binary coproducts has a natural monoidal structure. -/
def monoidal_of_has_finite_coproducts (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] : monoidal_category C :=
  monoidal_category.mk (fun (X Y : C) => X ⨿ Y)
    (fun (_x _x_1 _x_2 _x_3 : C) (f : _x ⟶ _x_1) (g : _x_2 ⟶ _x_3) => limits.coprod.map f g) (⊥_C)
    limits.coprod.associator limits.coprod.left_unitor limits.coprod.right_unitor

/--
The monoidal structure coming from finite coproducts is symmetric.
-/
def symmetric_of_has_finite_coproducts (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] : symmetric_category C :=
  symmetric_category.mk

namespace monoidal_of_has_finite_coproducts


@[simp] theorem tensor_obj (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] (X : C) (Y : C) : X ⊗ Y = (X ⨿ Y) :=
  rfl

@[simp] theorem tensor_hom (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : f ⊗ g = limits.coprod.map f g :=
  rfl

@[simp] theorem left_unitor_hom (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] (X : C) : iso.hom λ_ = limits.coprod.desc (limits.initial.to X) 𝟙 :=
  rfl

@[simp] theorem right_unitor_hom (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] (X : C) : iso.hom ρ_ = limits.coprod.desc 𝟙 (limits.initial.to X) :=
  rfl

@[simp] theorem left_unitor_inv (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] (X : C) : iso.inv λ_ = limits.coprod.inr :=
  rfl

-- We don't mark this as a simp lemma, even though in many particular

@[simp] theorem right_unitor_inv (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] (X : C) : iso.inv ρ_ = limits.coprod.inl :=
  rfl

-- categories the right hand side will simplify significantly further.

-- For now, we'll plan to create specialised simp lemmas in each particular category.

theorem associator_hom (C : Type u) [category C] [limits.has_initial C] [limits.has_binary_coproducts C] (X : C) (Y : C) (Z : C) : iso.hom α_ =
  limits.coprod.desc (limits.coprod.desc limits.coprod.inl (limits.coprod.inl ≫ limits.coprod.inr))
    (limits.coprod.inr ≫ limits.coprod.inr) :=
  rfl

