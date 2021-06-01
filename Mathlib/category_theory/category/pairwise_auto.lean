/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.category_theory.limits.lattice
import Mathlib.PostPort

universes v l 

namespace Mathlib

/-!
# The category of "pairwise intersections".

Given `ι : Type v`, we build the diagram category `pairwise ι`
with objects `single i` and `pair i j`, for `i j : ι`,
whose only non-identity morphisms are
`left : pair i j ⟶ single i` and `right : pair i j ⟶ single j`.

We use this later in describing (one formulation of) the sheaf condition.

Given any function `U : ι → α`, where `α` is some complete lattice (e.g. `(opens X)ᵒᵖ`),
we produce a functor `pairwise ι ⥤ α` in the obvious way,
and show that `supr U` provides a colimit cocone over this functor.
-/

namespace category_theory


/--
An inductive type representing either a single term of a type `ι`, or a pair of terms.
We use this as the objects of a category to describe the sheaf condition.
-/
inductive pairwise (ι : Type v) where
| single : ι → pairwise ι
| pair : ι → ι → pairwise ι

namespace pairwise


protected instance pairwise_inhabited {ι : Type v} [Inhabited ι] : Inhabited (pairwise ι) :=
  { default := single Inhabited.default }

/--
Morphisms in the category `pairwise ι`. The only non-identity morphisms are
`left i j : single i ⟶ pair i j` and `right i j : single j ⟶ pair i j`.
-/
inductive hom {ι : Type v} : pairwise ι → pairwise ι → Type v where
| id_single : (i : ι) → hom (single i) (single i)
| id_pair : (i j : ι) → hom (pair i j) (pair i j)
| left : (i j : ι) → hom (pair i j) (single i)
| right : (i j : ι) → hom (pair i j) (single j)

protected instance hom_inhabited {ι : Type v} [Inhabited ι] :
    Inhabited (hom (single Inhabited.default) (single Inhabited.default)) :=
  { default := hom.id_single Inhabited.default }

/--
The identity morphism in `pairwise ι`.
-/
def id {ι : Type v} (o : pairwise ι) : hom o o := sorry

/-- Composition of morphisms in `pairwise ι`. -/
def comp {ι : Type v} {o₁ : pairwise ι} {o₂ : pairwise ι} {o₃ : pairwise ι} (f : hom o₁ o₂)
    (g : hom o₂ o₃) : hom o₁ o₃ :=
  sorry

protected instance category_theory.category {ι : Type v} : category (pairwise ι) := category.mk

/-- Auxilliary definition for `diagram`. -/
@[simp] def diagram_obj {ι : Type v} {α : Type v} (U : ι → α) [semilattice_inf α] :
    pairwise ι → α :=
  sorry

/-- Auxilliary definition for `diagram`. -/
@[simp] def diagram_map {ι : Type v} {α : Type v} (U : ι → α) [semilattice_inf α] {o₁ : pairwise ι}
    {o₂ : pairwise ι} (f : o₁ ⟶ o₂) : diagram_obj U o₁ ⟶ diagram_obj U o₂ :=
  sorry

/--
Given a function `U : ι → α` for `[semilattice_inf α]`, we obtain a functor `pairwise ι ⥤ α`,
sending `single i` to `U i` and `pair i j` to `U i ⊓ U j`,
and the morphisms to the obvious inequalities.
-/
def diagram {ι : Type v} {α : Type v} (U : ι → α) [semilattice_inf α] : pairwise ι ⥤ α :=
  functor.mk (diagram_obj U) fun (X Y : pairwise ι) (f : X ⟶ Y) => diagram_map U f

-- `complete_lattice` is not really needed, as we only ever use `inf`,

-- but the appropriate structure has not been defined.

/-- Auxilliary definition for `cocone`. -/
def cocone_ι_app {ι : Type v} {α : Type v} (U : ι → α) [complete_lattice α] (o : pairwise ι) :
    diagram_obj U o ⟶ supr U :=
  sorry

/--
Given a function `U : ι → α` for `[complete_lattice α]`,
`supr U` provides a cocone over `diagram U`.
-/
@[simp] theorem cocone_X {ι : Type v} {α : Type v} (U : ι → α) [complete_lattice α] :
    limits.cocone.X (cocone U) = supr U :=
  Eq.refl (limits.cocone.X (cocone U))

/--
Given a function `U : ι → α` for `[complete_lattice α]`,
`infi U` provides a limit cone over `diagram U`.
-/
def cocone_is_colimit {ι : Type v} {α : Type v} (U : ι → α) [complete_lattice α] :
    limits.is_colimit (cocone U) :=
  limits.is_colimit.mk fun (s : limits.cocone (diagram U)) => hom_of_le sorry

end Mathlib