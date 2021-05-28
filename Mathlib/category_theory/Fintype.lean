/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.fin
import Mathlib.category_theory.concrete_category.bundled
import Mathlib.category_theory.concrete_category.default
import Mathlib.category_theory.full_subcategory
import Mathlib.category_theory.skeletal
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# The category of finite types.

We define the category of finite types, denoted `Fintype` as
(bundled) types with a `fintype` instance.

We also define `Fintype.skeleton`, the standard skeleton of `Fintype` whose objects are `fin n`
for `n : ℕ`. We prove that the obvious inclusion functor `Fintype.skeleton ⥤ Fintype` is an
equivalence of categories in `Fintype.skeleton.equivalence`.
We prove that `Fintype.skeleton` is a skeleton of `Fintype` in `Fintype.is_skeleton`.
-/

/-- The category of finite types. -/
def Fintype  :=
  category_theory.bundled fintype

namespace Fintype


/-- Construct a bundled `Fintype` from the underlying type and typeclass. -/
def of (X : Type u_1) [fintype X] : Fintype :=
  category_theory.bundled.of X

protected instance inhabited : Inhabited Fintype :=
  { default := category_theory.bundled.mk pempty }

protected instance fintype {X : Fintype} : fintype ↥X :=
  category_theory.bundled.str X

protected instance category_theory.category : category_theory.category Fintype :=
  category_theory.induced_category.category category_theory.bundled.α

/-- The fully faithful embedding of `Fintype` into the category of types. -/
@[simp] theorem incl_map (x : category_theory.induced_category (Type u_1) category_theory.bundled.α) (y : category_theory.induced_category (Type u_1) category_theory.bundled.α) (f : x ⟶ y) : ∀ (ᾰ : category_theory.bundled.α x), category_theory.functor.map incl f ᾰ = f ᾰ :=
  fun (ᾰ : category_theory.bundled.α x) => Eq.refl (f ᾰ)

protected instance category_theory.concrete_category : category_theory.concrete_category Fintype :=
  category_theory.concrete_category.mk incl

/--
The "standard" skeleton for `Fintype`. This is the full subcategory of `Fintype` spanned by objects
of the form `fin n` for `n : ℕ`. We parameterize the objects of `Fintype.skeleton` directly as `ℕ`,
as the type `fin m ≃ fin n` is nonempty if and only if `n = m`.
-/
def skeleton  :=
  ℕ

namespace skeleton


/-- Given any natural number `n`, this creates the associated object of `Fintype.skeleton`. -/
def mk : ℕ → skeleton :=
  id

protected instance inhabited : Inhabited skeleton :=
  { default := mk 0 }

/-- Given any object of `Fintype.skeleton`, this returns the associated natural number. -/
def to_nat : skeleton → ℕ :=
  id

protected instance category_theory.category : category_theory.category skeleton :=
  category_theory.category.mk

theorem is_skeletal : category_theory.skeletal skeleton := sorry

/-- The canonical fully faithful embedding of `Fintype.skeleton` into `Fintype`. -/
def incl : skeleton ⥤ Fintype :=
  category_theory.functor.mk (fun (X : skeleton) => of (fin X)) fun (_x _x_1 : skeleton) (f : _x ⟶ _x_1) => f

protected instance incl.category_theory.full : category_theory.full incl :=
  category_theory.full.mk
    fun (_x _x_1 : skeleton) (f : category_theory.functor.obj incl _x ⟶ category_theory.functor.obj incl _x_1) => f

protected instance incl.category_theory.faithful : category_theory.faithful incl :=
  category_theory.faithful.mk

protected instance incl.category_theory.ess_surj : category_theory.ess_surj incl :=
  category_theory.ess_surj.mk
    fun (X : Fintype) =>
      let F : ↥X ≃ fin (fintype.card ↥X) := trunc.out (fintype.equiv_fin ↥X);
      Exists.intro (fintype.card ↥X) (Nonempty.intro (category_theory.iso.mk ⇑(equiv.symm F) ⇑F))

protected instance incl.category_theory.is_equivalence : category_theory.is_equivalence incl :=
  category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj incl

/-- The equivalence between `Fintype.skeleton` and `Fintype`. -/
def equivalence : skeleton ≌ Fintype :=
  category_theory.functor.as_equivalence incl

@[simp] theorem incl_mk_nat_card (n : ℕ) : fintype.card ↥(category_theory.functor.obj incl (mk n)) = n :=
  finset.card_fin n

end skeleton


/-- `Fintype.skeleton` is a skeleton of `Fintype`. -/
def is_skeleton : category_theory.is_skeleton_of Fintype skeleton skeleton.incl :=
  category_theory.is_skeleton_of.mk skeleton.is_skeletal skeleton.incl.category_theory.is_equivalence

