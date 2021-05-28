/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monad.basic
import Mathlib.category_theory.monad.kleisli
import Mathlib.category_theory.category.Kleisli
import Mathlib.category_theory.types
import PostPort

universes u 

namespace Mathlib

/-!

# Convert from `monad` (i.e. Lean's `Type`-based monads) to `category_theory.monad`

This allows us to use these monads in category theory.

-/

namespace category_theory


protected instance of_type_functor.monad (m : Type u → Type u) [Monad m] [is_lawful_monad m] : monad (of_type_functor m) :=
  monad.mk (nat_trans.mk pure) (nat_trans.mk mjoin)

/--
The `Kleisli` category of a `control.monad` is equivalent to the `kleisli` category of its
category-theoretic version, provided the monad is lawful.
-/
@[simp] theorem eq_unit_iso (m : Type u → Type u) [Monad m] [is_lawful_monad m] : equivalence.unit_iso (eq m) = nat_iso.of_components (fun (X : Kleisli m) => iso.refl X) (eq._proof_7 m) :=
  Eq.refl (equivalence.unit_iso (eq m))

