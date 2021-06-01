/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monad.basic
import Mathlib.category_theory.eq_to_hom
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Bundled Monads

We define bundled (co)monads as a structure consisting of a functor `func : C ⥤ C` endowed with
a term of type `(co)monad func`. See `category_theory.monad.basic` for the definition.
The type of bundled (co)monads on a category `C` is denoted `(Co)Monad C`.

We also define morphisms of bundled (co)monads as morphisms of their underlying (co)monads
in the sense of `category_theory.(co)monad_hom`. We construct a category instance on `(Co)Monad C`.
-/

namespace category_theory


/-- Bundled monads. -/
structure Monad (C : Type u) [category C] where
  func : C ⥤ C
  str :
    autoParam (monad func)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])

/-- Bundled comonads -/
structure Comonad (C : Type u) [category C] where
  func : C ⥤ C
  str :
    autoParam (comonad func)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.apply_instance")
        (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
          "apply_instance")
        [])

namespace Monad


/-- The initial monad. TODO: Prove it's initial. -/
def initial (C : Type u) [category C] : Monad C := mk 𝟭

protected instance inhabited {C : Type u} [category C] : Inhabited (Monad C) :=
  { default := initial C }

protected instance func.category_theory.monad {C : Type u} [category C] {M : Monad C} :
    monad (func M) :=
  str M

/-- Morphisms of bundled monads. -/
def hom {C : Type u} [category C] (M : Monad C) (N : Monad C) := monad_hom (func M) (func N)

namespace hom


end hom


protected instance hom.inhabited {C : Type u} [category C] {M : Monad C} : Inhabited (hom M M) :=
  { default := monad_hom.id (func M) }

protected instance category_theory.category {C : Type u} [category C] : category (Monad C) :=
  category.mk

/-- The forgetful functor from `Monad C` to `C ⥤ C`. -/
def forget (C : Type u) [category C] : Monad C ⥤ C ⥤ C :=
  functor.mk func fun (_x _x_1 : Monad C) (f : _x ⟶ _x_1) => monad_hom.to_nat_trans f

@[simp] theorem comp_to_nat_trans {C : Type u} [category C] {M : Monad C} {N : Monad C}
    {L : Monad C} (f : M ⟶ N) (g : N ⟶ L) :
    monad_hom.to_nat_trans (f ≫ g) =
        nat_trans.vcomp (monad_hom.to_nat_trans f) (monad_hom.to_nat_trans g) :=
  rfl

@[simp] theorem assoc_func_app {C : Type u} [category C] {M : Monad C} {X : C} :
    functor.map (func M) (nat_trans.app μ_ X) ≫ nat_trans.app μ_ X =
        nat_trans.app μ_ (functor.obj (func M) X) ≫ nat_trans.app μ_ X :=
  monad.assoc X

end Monad


namespace Comonad


/-- The terminal comonad. TODO: Prove it's terminal. -/
def terminal (C : Type u) [category C] : Comonad C := mk 𝟭

protected instance inhabited {C : Type u} [category C] : Inhabited (Comonad C) :=
  { default := terminal C }

protected instance func.category_theory.comonad {C : Type u} [category C] {M : Comonad C} :
    comonad (func M) :=
  str M

/-- Morphisms of bundled comonads. -/
def hom {C : Type u} [category C] (M : Comonad C) (N : Comonad C) := comonad_hom (func M) (func N)

namespace hom


end hom


protected instance hom.inhabited {C : Type u} [category C] {M : Comonad C} : Inhabited (hom M M) :=
  { default := comonad_hom.id (func M) }

protected instance category_theory.category {C : Type u} [category C] : category (Comonad C) :=
  category.mk

/-- The forgetful functor from `CoMonad C` to `C ⥤ C`. -/
def forget (C : Type u) [category C] : Comonad C ⥤ C ⥤ C :=
  functor.mk func fun (_x _x_1 : Comonad C) (f : _x ⟶ _x_1) => comonad_hom.to_nat_trans f

@[simp] theorem comp_to_nat_trans {C : Type u} [category C] {M : Comonad C} {N : Comonad C}
    {L : Comonad C} (f : M ⟶ N) (g : N ⟶ L) :
    comonad_hom.to_nat_trans (f ≫ g) =
        nat_trans.vcomp (comonad_hom.to_nat_trans f) (comonad_hom.to_nat_trans g) :=
  rfl

@[simp] theorem coassoc_func_app {C : Type u} [category C] {M : Comonad C} {X : C} :
    nat_trans.app δ_ X ≫ functor.map (func M) (nat_trans.app δ_ X) =
        nat_trans.app δ_ X ≫ nat_trans.app δ_ (functor.obj (func M) X) :=
  comonad.coassoc X

end Mathlib