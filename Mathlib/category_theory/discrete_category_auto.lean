/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.eq_to_hom
import Mathlib.PostPort

universes u₁ u₂ v₂ v₁ 

namespace Mathlib

namespace category_theory


/--
A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def discrete (α : Type u₁) := α

/--
The "discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ulift (plift (X = Y))`.

See https://stacks.math.columbia.edu/tag/001A
-/
protected instance discrete_category (α : Type u₁) : small_category (discrete α) := category.mk

namespace discrete


protected instance inhabited {α : Type u₁} [Inhabited α] : Inhabited (discrete α) := id _inst_1

protected instance subsingleton {α : Type u₁} [subsingleton α] : subsingleton (discrete α) :=
  id _inst_1

/-- Extract the equation from a morphism in a discrete category. -/
theorem eq_of_hom {α : Type u₁} {X : discrete α} {Y : discrete α} (i : X ⟶ Y) : X = Y :=
  plift.down (ulift.down i)

@[simp] theorem id_def {α : Type u₁} (X : discrete α) : ulift.up (plift.up (Eq.refl X)) = 𝟙 := rfl

protected instance category_theory.is_iso {I : Type u₁} {i : discrete I} {j : discrete I}
    (f : i ⟶ j) : is_iso f :=
  is_iso.mk (eq_to_hom sorry)

/--
Any function `I → C` gives a functor `discrete I ⥤ C`.
-/
def functor {C : Type u₂} [category C] {I : Type u₁} (F : I → C) : discrete I ⥤ C :=
  functor.mk F
    fun (X Y : discrete I) (f : X ⟶ Y) =>
      ulift.cases_on f
        fun (f : plift (X = Y)) =>
          plift.cases_on f
            fun (f : X = Y) =>
              eq.dcases_on f
                (fun (H_1 : Y = X) => Eq._oldrec (fun (f : X = X) (H_2 : f == sorry) => 𝟙) sorry f)
                sorry sorry

@[simp] theorem functor_obj {C : Type u₂} [category C] {I : Type u₁} (F : I → C) (i : I) :
    functor.obj (functor F) i = F i :=
  rfl

theorem functor_map {C : Type u₂} [category C] {I : Type u₁} (F : I → C) {i : discrete I}
    (f : i ⟶ i) : functor.map (functor F) f = 𝟙 :=
  sorry

/--
For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
def nat_trans {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C} {G : discrete I ⥤ C}
    (f : (i : discrete I) → functor.obj F i ⟶ functor.obj G i) : F ⟶ G :=
  nat_trans.mk f

@[simp] theorem nat_trans_app {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C}
    {G : discrete I ⥤ C} (f : (i : discrete I) → functor.obj F i ⟶ functor.obj G i)
    (i : discrete I) : nat_trans.app (nat_trans f) i = f i :=
  rfl

/--
For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
def nat_iso {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C} {G : discrete I ⥤ C}
    (f : (i : discrete I) → functor.obj F i ≅ functor.obj G i) : F ≅ G :=
  nat_iso.of_components f sorry

@[simp] theorem nat_iso_hom_app {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C}
    {G : discrete I ⥤ C} (f : (i : discrete I) → functor.obj F i ≅ functor.obj G i) (i : I) :
    nat_trans.app (iso.hom (nat_iso f)) i = iso.hom (f i) :=
  rfl

@[simp] theorem nat_iso_inv_app {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C}
    {G : discrete I ⥤ C} (f : (i : discrete I) → functor.obj F i ≅ functor.obj G i) (i : I) :
    nat_trans.app (iso.inv (nat_iso f)) i = iso.inv (f i) :=
  rfl

@[simp] theorem nat_iso_app {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C}
    {G : discrete I ⥤ C} (f : (i : discrete I) → functor.obj F i ≅ functor.obj G i) (i : I) :
    iso.app (nat_iso f) i = f i :=
  iso.ext (Eq.refl (iso.hom (iso.app (nat_iso f) i)))

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `discrete.functor (F.obj)`. -/
def nat_iso_functor {C : Type u₂} [category C] {I : Type u₁} {F : discrete I ⥤ C} :
    F ≅ functor (functor.obj F) :=
  nat_iso fun (i : discrete I) => iso.refl (functor.obj F i)

/--
We can promote a type-level `equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simp] theorem equivalence_functor {I : Type u₁} {J : Type u₁} (e : I ≃ J) :
    equivalence.functor (equivalence e) = functor ⇑e :=
  Eq.refl (equivalence.functor (equivalence e))

/-- We can convert an equivalence of `discrete` categories to a type-level `equiv`. -/
@[simp] theorem equiv_of_equivalence_apply {α : Type u₁} {β : Type u₁}
    (h : discrete α ≌ discrete β) :
    ∀ (ᾰ : discrete α), coe_fn (equiv_of_equivalence h) ᾰ = functor.obj (equivalence.functor h) ᾰ :=
  fun (ᾰ : discrete α) => Eq.refl (coe_fn (equiv_of_equivalence h) ᾰ)

end discrete


namespace discrete


/-- A discrete category is equivalent to its opposite category. -/
protected def opposite (α : Type u₁) : discrete αᵒᵖ ≌ discrete α :=
  let F : discrete α ⥤ (discrete αᵒᵖ) := functor fun (x : α) => opposite.op x;
  equivalence.mk (functor.left_op F) F
    (nat_iso.of_components (fun (X : discrete αᵒᵖ) => eq.mpr sorry (iso.refl X)) sorry)
    (nat_iso fun (X : discrete α) => eq.mpr sorry (iso.refl X))

@[simp] theorem functor_map_id {J : Type v₁} {C : Type u₂} [category C] (F : discrete J ⥤ C)
    {j : discrete J} (f : j ⟶ j) : functor.map F f = 𝟙 :=
  sorry

end Mathlib