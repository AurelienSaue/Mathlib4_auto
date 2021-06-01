/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.types
import Mathlib.category_theory.epi_mono
import Mathlib.PostPort

universes w v u l u_1 u_2 v' u_3 

namespace Mathlib

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Type*`.  We define concrete categories using `class
concrete_category`.  In particular, we impose no restrictions on the
carrier type `C`, so `Type` is a concrete category with the identity
forgetful functor.

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Type*`.  We say that a concrete category `C` admits a
*forgetful functor* to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget C`,
see `class has_forget₂`.  Due to `faithful.div_comp`, it suffices
to verify that `forget₂.obj` and `forget₂.map` agree with the equality
above; then `forget₂` will satisfy the functor laws automatically, see
`has_forget₂.mk'`.

Two classes helping construct concrete categories in the two most
common cases are provided in the files `bundled_hom` and
`unbundled_hom`, see their documentation for details.

## References

See [Ahrens and Lumsdaine, *Displayed Categories*][ahrens2017] for
related work.
-/

namespace category_theory


/--
A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`.

Note that `concrete_category` potentially depends on three independent universe levels,
* the universe level `w` appearing in `forget : C ⥤ Type w`
* the universe level `v` of the morphisms (i.e. we have a `category.{v} C`)
* the universe level `u` of the objects (i.e `C : Type u`)
They are specified that order, to avoid unnecessary universe annotations.
-/
class concrete_category (C : Type u) [category C] where
  forget : C ⥤ Type w
  forget_faithful : faithful forget

/-- The forgetful functor from a concrete category to `Type u`. -/
def forget (C : Type v) [category C] [concrete_category C] : C ⥤ Type u :=
  concrete_category.forget C

/--
Provide a coercion to `Type u` for a concrete category. This is not marked as an instance
as it could potentially apply to every type, and so is too expensive in typeclass search.

You can use it on particular examples as:
```
instance : has_coe_to_sort X := concrete_category.has_coe_to_sort X
```
-/
def concrete_category.has_coe_to_sort (C : Type v) [category C] [concrete_category C] :
    has_coe_to_sort C :=
  has_coe_to_sort.mk (Type u) (functor.obj (concrete_category.forget C))

@[simp] theorem forget_obj_eq_coe {C : Type v} [category C] [concrete_category C] {X : C} :
    functor.obj (forget C) X = ↥X :=
  rfl

/-- Usually a bundled hom structure already has a coercion to function
that works with different universes. So we don't use this as a global instance. -/
def concrete_category.has_coe_to_fun {C : Type v} [category C] [concrete_category C] {X : C}
    {Y : C} : has_coe_to_fun (X ⟶ Y) :=
  has_coe_to_fun.mk (fun (f : X ⟶ Y) => ↥X → ↥Y) fun (f : X ⟶ Y) => functor.map (forget C) f

/-- In any concrete category, we can test equality of morphisms by pointwise evaluations.-/
theorem concrete_category.hom_ext {C : Type v} [category C] [concrete_category C] {X : C} {Y : C}
    (f : X ⟶ Y) (g : X ⟶ Y) (w : ∀ (x : ↥X), coe_fn f x = coe_fn g x) : f = g :=
  faithful.map_injective (forget C) (funext fun (x : functor.obj (forget C) X) => w x)

@[simp] theorem forget_map_eq_coe {C : Type v} [category C] [concrete_category C] {X : C} {Y : C}
    (f : X ⟶ Y) : functor.map (forget C) f = ⇑f :=
  rfl

@[simp] theorem coe_id {C : Type v} [category C] [concrete_category C] {X : C} (x : ↥X) :
    coe_fn 𝟙 x = x :=
  congr_fun (functor.map_id (forget C) X) x

@[simp] theorem coe_comp {C : Type v} [category C] [concrete_category C] {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) : coe_fn (f ≫ g) x = coe_fn g (coe_fn f x) :=
  congr_fun (functor.map_comp (forget C) f g) x

@[simp] theorem coe_hom_inv_id {C : Type v} [category C] [concrete_category C] {X : C} {Y : C}
    (f : X ≅ Y) (x : ↥X) : coe_fn (iso.inv f) (coe_fn (iso.hom f) x) = x :=
  congr_fun (iso.hom_inv_id (functor.map_iso (forget C) f)) x

@[simp] theorem coe_inv_hom_id {C : Type v} [category C] [concrete_category C] {X : C} {Y : C}
    (f : X ≅ Y) (y : ↥Y) : coe_fn (iso.hom f) (coe_fn (iso.inv f) y) = y :=
  congr_fun (iso.inv_hom_id (functor.map_iso (forget C) f)) y

/-- In any concrete category, injective morphisms are monomorphisms. -/
theorem concrete_category.mono_of_injective {C : Type v} [category C] [concrete_category C] {X : C}
    {Y : C} (f : X ⟶ Y) (i : function.injective ⇑f) : mono f :=
  faithful_reflects_mono (forget C) (iff.mpr (mono_iff_injective ⇑f) i)

/-- In any concrete category, surjective morphisms are epimorphisms. -/
theorem concrete_category.epi_of_surjective {C : Type v} [category C] [concrete_category C] {X : C}
    {Y : C} (f : X ⟶ Y) (s : function.surjective ⇑f) : epi f :=
  faithful_reflects_epi (forget C) (iff.mpr (epi_iff_surjective ⇑f) s)

protected instance concrete_category.types : concrete_category (Type u) := concrete_category.mk 𝟭

/--
`has_forget₂ C D`, where `C` and `D` are both concrete categories, provides a functor
`forget₂ C D : C ⥤ D` and a proof that `forget₂ ⋙ (forget D) = forget C`.
-/
class has_forget₂ (C : Type v) (D : Type v') [category C] [concrete_category C] [category D]
    [concrete_category D]
    where
  forget₂ : C ⥤ D
  forget_comp :
    autoParam (forget₂ ⋙ forget D = forget C)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/-- The forgetful functor `C ⥤ D` between concrete categories for which we have an instance
`has_forget₂ C `. -/
def forget₂ (C : Type v) (D : Type v') [category C] [concrete_category C] [category D]
    [concrete_category D] [has_forget₂ C D] : C ⥤ D :=
  has_forget₂.forget₂

protected instance forget_faithful (C : Type v) (D : Type v') [category C] [concrete_category C]
    [category D] [concrete_category D] [has_forget₂ C D] : faithful (forget₂ C D) :=
  eq.faithful_of_comp has_forget₂.forget_comp

protected instance induced_category.concrete_category {C : Type v} {D : Type v'} [category D]
    [concrete_category D] (f : C → D) : concrete_category (induced_category D f) :=
  concrete_category.mk (induced_functor f ⋙ forget D)

protected instance induced_category.has_forget₂ {C : Type v} {D : Type v'} [category D]
    [concrete_category D] (f : C → D) : has_forget₂ (induced_category D f) D :=
  has_forget₂.mk (induced_functor f)

/--
In order to construct a “partially forgetting” functor, we do not need to verify functor laws;
it suffices to ensure that compositions agree with `forget₂ C D ⋙ forget D = forget C`.
-/
def has_forget₂.mk' {C : Type v} {D : Type v'} [category C] [concrete_category C] [category D]
    [concrete_category D] (obj : C → D)
    (h_obj : ∀ (X : C), functor.obj (forget D) (obj X) = functor.obj (forget C) X)
    (map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y : C} {f : X ⟶ Y}, functor.map (forget D) (map f) == functor.map (forget C) f) :
    has_forget₂ C D :=
  has_forget₂.mk
    (faithful.div (forget C) (forget D) (fun (X : C) => obj X) h_obj
      (fun (X Y : C) (f : X ⟶ Y) => map f) h_map)

protected instance has_forget_to_Type (C : Type v) [category C] [concrete_category C] :
    has_forget₂ C (Type u) :=
  has_forget₂.mk (forget C)

end Mathlib