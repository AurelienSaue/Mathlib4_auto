/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.shift
import Mathlib.category_theory.concrete_category.default
import Mathlib.category_theory.pi.basic
import Mathlib.algebra.group.basic
import Mathlib.PostPort

universes w u v u_1 

namespace Mathlib

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`category_theory.pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `graded_object β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `graded_object β C`.
-/

namespace category_theory


/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
def graded_object (β : Type w) (C : Type u)  :=
  β → C

-- Satisfying the inhabited linter...

protected instance inhabited_graded_object (β : Type w) (C : Type u) [Inhabited C] : Inhabited (graded_object β C) :=
  { default := fun (b : β) => Inhabited.default }

/--
A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
def graded_object_with_shift {β : Type w} [add_comm_group β] (s : β) (C : Type u)  :=
  graded_object β C

namespace graded_object


protected instance category_of_graded_objects {C : Type u} [category C] (β : Type w) : category (graded_object β C) :=
  category_theory.pi fun (_x : β) => C

/--
The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
def comap_eq (C : Type u) [category C] {β : Type w} {γ : Type w} {f : β → γ} {g : β → γ} (h : f = g) : pi.comap (fun (i : γ) => C) f ≅ pi.comap (fun (i : γ) => C) g :=
  iso.mk (nat_trans.mk fun (X : γ → C) (b : β) => eq_to_hom sorry)
    (nat_trans.mk fun (X : γ → C) (b : β) => eq_to_hom sorry)

theorem comap_eq_symm (C : Type u) [category C] {β : Type w} {γ : Type w} {f : β → γ} {g : β → γ} (h : f = g) : comap_eq C (Eq.symm h) = iso.symm (comap_eq C h) :=
  Eq.refl (comap_eq C (Eq.symm h))

theorem comap_eq_trans (C : Type u) [category C] {β : Type w} {γ : Type w} {f : β → γ} {g : β → γ} {h : β → γ} (k : f = g) (l : g = h) : comap_eq C (Eq.trans k l) = comap_eq C k ≪≫ comap_eq C l := sorry

/--
The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
def comap_equiv (C : Type u) [category C] {β : Type w} {γ : Type w} (e : β ≃ γ) : graded_object β C ≌ graded_object γ C :=
  equivalence.mk' (pi.comap (fun (_x : β) => C) ⇑(equiv.symm e)) (pi.comap (fun (_x : γ) => C) ⇑e)
    (comap_eq C sorry ≪≫ iso.symm (pi.comap_comp (fun (_x : β) => C) ⇑e ⇑(equiv.symm e)))
    (pi.comap_comp (fun (_x : γ) => C) ⇑(equiv.symm e) ⇑e ≪≫ comap_eq C sorry)

protected instance has_shift {C : Type u} [category C] {β : Type u_1} [add_comm_group β] (s : β) : has_shift (graded_object_with_shift s C) :=
  has_shift.mk (comap_equiv C (equiv.mk (fun (b : β) => b - s) (fun (b : β) => b + s) sorry sorry))

@[simp] theorem shift_functor_obj_apply {C : Type u} [category C] {β : Type u_1} [add_comm_group β] (s : β) (X : β → C) (t : β) : functor.obj (equivalence.functor (shift (graded_object_with_shift s C))) X t = X (t + s) :=
  rfl

@[simp] theorem shift_functor_map_apply {C : Type u} [category C] {β : Type u_1} [add_comm_group β] (s : β) {X : graded_object_with_shift s C} {Y : graded_object_with_shift s C} (f : X ⟶ Y) (t : β) : functor.map (equivalence.functor (shift (graded_object_with_shift s C))) f t = f (t + s) :=
  rfl

protected instance has_zero_morphisms {C : Type u} [category C] [limits.has_zero_morphisms C] (β : Type w) : limits.has_zero_morphisms (graded_object β C) :=
  limits.has_zero_morphisms.mk

@[simp] theorem zero_apply {C : Type u} [category C] [limits.has_zero_morphisms C] (β : Type w) (X : graded_object β C) (Y : graded_object β C) (b : β) : HasZero.zero b = 0 :=
  rfl

protected instance has_zero_object {C : Type u} [category C] [limits.has_zero_object C] [limits.has_zero_morphisms C] (β : Type w) : limits.has_zero_object (graded_object β C) :=
  limits.has_zero_object.mk (fun (b : β) => 0)
    (fun (X : graded_object β C) => unique.mk { default := fun (b : β) => 0 } sorry)
    fun (X : graded_object β C) => unique.mk { default := fun (b : β) => 0 } sorry

end graded_object


namespace graded_object


-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.

-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.

-- If you're grading by things in higher universes, have fun!

/--
The total object of a graded object is the coproduct of the graded components.
-/
def total (β : Type) (C : Type u) [category C] [limits.has_coproducts C] : graded_object β C ⥤ C :=
  functor.mk (fun (X : graded_object β C) => ∐ fun (i : ulift β) => X (ulift.down i))
    fun (X Y : graded_object β C) (f : X ⟶ Y) => limits.sigma.map fun (i : ulift β) => f (ulift.down i)

/--
The `total` functor taking a graded object to the coproduct of its graded components is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms and decidable equality for the grading.
-/
protected instance total.category_theory.faithful (β : Type) (C : Type u) [category C] [limits.has_coproducts C] [limits.has_zero_morphisms C] : faithful (total β C) :=
  faithful.mk

end graded_object


namespace graded_object


protected instance category_theory.concrete_category (β : Type) (C : Type (u + 1)) [large_category C] [concrete_category C] [limits.has_coproducts C] [limits.has_zero_morphisms C] : concrete_category (graded_object β C) :=
  concrete_category.mk (total β C ⋙ forget C)

protected instance category_theory.has_forget₂ (β : Type) (C : Type (u + 1)) [large_category C] [concrete_category C] [limits.has_coproducts C] [limits.has_zero_morphisms C] : has_forget₂ (graded_object β C) C :=
  has_forget₂.mk (total β C)

