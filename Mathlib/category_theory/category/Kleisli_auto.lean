/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

The Kleisli construction on the Type category

TODO: generalise this to work with category_theory.monad
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.category.default
import Mathlib.PostPort

universes u v u_1 u_2 

namespace Mathlib

namespace category_theory


def Kleisli (m : Type u → Type v) [Monad m] := Type u

def Kleisli.mk (m : Type u → Type v) [Monad m] (α : Type u) : Kleisli m := α

protected instance Kleisli.category_struct {m : Type u_1 → Type u_2} [Monad m] :
    category_struct (Kleisli m) :=
  category_struct.mk (fun (α : Kleisli m) (x : α) => pure x)
    fun (X Y Z : Kleisli m) (f : X ⟶ Y) (g : Y ⟶ Z) => f >=> g

protected instance Kleisli.category {m : Type u_1 → Type u_2} [Monad m] [is_lawful_monad m] :
    category (Kleisli m) :=
  category.mk

@[simp] theorem Kleisli.id_def {m : Type u_1 → Type u_2} [Monad m] [is_lawful_monad m]
    (α : Kleisli m) : 𝟙 = pure :=
  rfl

theorem Kleisli.comp_def {m : Type u_1 → Type u_2} [Monad m] [is_lawful_monad m] (α : Kleisli m)
    (β : Kleisli m) (γ : Kleisli m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    category_struct.comp xs ys a = xs a >>= ys :=
  rfl

end Mathlib