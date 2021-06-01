/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.fully_faithful
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes u v w u' u_1 u_2 

namespace Mathlib

/-!
# The category `Type`.

In this section we set up the theory so that Lean's types and functions between them
can be viewed as a `large_category` in our framework.

Lean can not transparently view a function as a morphism in this category,
and needs a hint in order to be able to type check.
We provide the abbreviation `as_hom f` to guide type checking,
as well as a corresponding notation `↾ f`. (Entered as `\upr `.)

We provide various simplification lemmas for functors and natural transformations valued in `Type`.

We define `ulift_functor`, from `Type u` to `Type (max u v)`, and show that it is fully faithful
(but not, of course, essentially surjective).

We prove some basic facts about the category `Type`:
*  epimorphisms are surjections and monomorphisms are injections,
* `iso` is both `iso` and `equiv` to `equiv` (at least within a fixed universe),
* every type level `is_lawful_functor` gives a categorical functor `Type ⥤ Type`
  (the corresponding fact about monads is in `src/category_theory/monad/types.lean`).
-/

namespace category_theory


protected instance types : large_category (Type u) := category.mk

theorem types_hom {α : Type u} {β : Type u} : (α ⟶ β) = (α → β) := rfl

theorem types_id (X : Type u) : 𝟙 = id := rfl

theorem types_comp {X : Type u} {Y : Type u} {Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f :=
  rfl

@[simp] theorem types_id_apply (X : Type u) (x : X) : 𝟙 = x := rfl

@[simp] theorem types_comp_apply {X : Type u} {Y : Type u} {Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X) : category_struct.comp f g x = g (f x) :=
  rfl

@[simp] theorem hom_inv_id_apply {X : Type u} {Y : Type u} (f : X ≅ Y) (x : X) :
    iso.inv f (iso.hom f x) = x :=
  congr_fun (iso.hom_inv_id f) x

@[simp] theorem inv_hom_id_apply {X : Type u} {Y : Type u} (f : X ≅ Y) (y : Y) :
    iso.hom f (iso.inv f y) = y :=
  congr_fun (iso.inv_hom_id f) y

/-- `as_hom f` helps Lean type check a function as a morphism in the category `Type`. -/
-- Unfortunately without this wrapper we can't use `category_theory` idioms, such as `is_iso f`.

-- If you don't mind some notation you can use fewer keystrokes:

def as_hom {α : Type u} {β : Type u} (f : α → β) : α ⟶ β := f

prefix:200 "↾" => Mathlib.category_theory.as_hom

namespace functor


/--
The sections of a functor `J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
def sections {J : Type u} [category J] (F : J ⥤ Type w) : set ((j : J) → obj F j) :=
  set_of fun (u : (j : J) → obj F j) => ∀ {j j' : J} (f : j ⟶ j'), map F f (u j) = u j'

end functor


namespace functor_to_types


@[simp] theorem map_comp_apply {C : Type u} [category C] (F : C ⥤ Type w) {X : C} {Y : C} {Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : functor.obj F X) :
    functor.map F (f ≫ g) a = functor.map F g (functor.map F f a) :=
  sorry

@[simp] theorem map_id_apply {C : Type u} [category C] (F : C ⥤ Type w) {X : C}
    (a : functor.obj F X) : functor.map F 𝟙 a = a :=
  sorry

theorem naturality {C : Type u} [category C] (F : C ⥤ Type w) (G : C ⥤ Type w) {X : C} {Y : C}
    (σ : F ⟶ G) (f : X ⟶ Y) (x : functor.obj F X) :
    nat_trans.app σ Y (functor.map F f x) = functor.map G f (nat_trans.app σ X x) :=
  congr_fun (nat_trans.naturality σ f) x

@[simp] theorem comp {C : Type u} [category C] (F : C ⥤ Type w) (G : C ⥤ Type w) (H : C ⥤ Type w)
    {X : C} (σ : F ⟶ G) (τ : G ⟶ H) (x : functor.obj F X) :
    nat_trans.app (σ ≫ τ) X x = nat_trans.app τ X (nat_trans.app σ X x) :=
  rfl

@[simp] theorem hcomp {C : Type u} [category C] (F : C ⥤ Type w) (G : C ⥤ Type w) (σ : F ⟶ G)
    {D : Type u'} [𝒟 : category D] (I : D ⥤ C) (J : D ⥤ C) (ρ : I ⟶ J) {W : D}
    (x : functor.obj (I ⋙ F) W) :
    nat_trans.app (ρ ◫ σ) W x =
        functor.map G (nat_trans.app ρ W) (nat_trans.app σ (functor.obj I W) x) :=
  rfl

@[simp] theorem map_inv_map_hom_apply {C : Type u} [category C] (F : C ⥤ Type w) {X : C} {Y : C}
    (f : X ≅ Y) (x : functor.obj F X) :
    functor.map F (iso.inv f) (functor.map F (iso.hom f) x) = x :=
  congr_fun (iso.hom_inv_id (functor.map_iso F f)) x

@[simp] theorem map_hom_map_inv_apply {C : Type u} [category C] (F : C ⥤ Type w) {X : C} {Y : C}
    (f : X ≅ Y) (y : functor.obj F Y) :
    functor.map F (iso.hom f) (functor.map F (iso.inv f) y) = y :=
  congr_fun (iso.inv_hom_id (functor.map_iso F f)) y

@[simp] theorem hom_inv_id_app_apply {C : Type u} [category C] (F : C ⥤ Type w) (G : C ⥤ Type w)
    (α : F ≅ G) (X : C) (x : functor.obj F X) :
    nat_trans.app (iso.inv α) X (nat_trans.app (iso.hom α) X x) = x :=
  congr_fun (iso.hom_inv_id_app α X) x

@[simp] theorem inv_hom_id_app_apply {C : Type u} [category C] (F : C ⥤ Type w) (G : C ⥤ Type w)
    (α : F ≅ G) (X : C) (x : functor.obj G X) :
    nat_trans.app (iso.hom α) X (nat_trans.app (iso.inv α) X x) = x :=
  congr_fun (iso.inv_hom_id_app α X) x

end functor_to_types


/--
The isomorphism between a `Type` which has been `ulift`ed to the same universe,
and the original type.
-/
def ulift_trivial (V : Type u) : ulift V ≅ V :=
  iso.mk (id fun (ᾰ : ulift V) => ulift.cases_on ᾰ fun (ᾰ : V) => ᾰ) ulift.up

/--
The functor embedding `Type u` into `Type (max u v)`.
Write this as `ulift_functor.{5 2}` to get `Type 2 ⥤ Type 5`.
-/
def ulift_functor : Type u ⥤ Type (max u v) :=
  functor.mk (fun (X : Type u) => ulift X)
    fun (X Y : Type u) (f : X ⟶ Y) (x : ulift X) => ulift.up (f (ulift.down x))

@[simp] theorem ulift_functor_map {X : Type u} {Y : Type u} (f : X ⟶ Y) (x : ulift X) :
    functor.map ulift_functor f x = ulift.up (f (ulift.down x)) :=
  rfl

protected instance ulift_functor_full : full ulift_functor :=
  full.mk
    fun (X Y : Type u) (f : functor.obj ulift_functor X ⟶ functor.obj ulift_functor Y) (x : X) =>
      ulift.down (f (ulift.up x))

protected instance ulift_functor_faithful : faithful ulift_functor := faithful.mk

/-- Any term `x` of a type `X` corresponds to a morphism `punit ⟶ X`. -/
-- TODO We should connect this to a general story about concrete categories

-- whose forgetful functor is representable.

def hom_of_element {X : Type u} (x : X) : PUnit ⟶ X := fun (_x : PUnit) => x

theorem hom_of_element_eq_iff {X : Type u} (x : X) (y : X) :
    hom_of_element x = hom_of_element y ↔ x = y :=
  sorry

/--
A morphism in `Type` is a monomorphism if and only if it is injective.

See https://stacks.math.columbia.edu/tag/003C.
-/
theorem mono_iff_injective {X : Type u} {Y : Type u} (f : X ⟶ Y) : mono f ↔ function.injective f :=
  sorry

/--
A morphism in `Type` is an epimorphism if and only if it is surjective.

See https://stacks.math.columbia.edu/tag/003C.
-/
theorem epi_iff_surjective {X : Type u} {Y : Type u} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
  sorry

/-- `of_type_functor m` converts from Lean's `Type`-based `category` to `category_theory`. This
allows us to use these functors in category theory. -/
def of_type_functor (m : Type u → Type v) [Functor m] [is_lawful_functor m] : Type u ⥤ Type v :=
  functor.mk m fun (α β : Type u) => Functor.map

@[simp] theorem of_type_functor_obj (m : Type u → Type v) [Functor m] [is_lawful_functor m] :
    functor.obj (of_type_functor m) = m :=
  rfl

@[simp] theorem of_type_functor_map (m : Type u → Type v) [Functor m] [is_lawful_functor m]
    {α : Type u} {β : Type u} (f : α → β) : functor.map (of_type_functor m) f = Functor.map f :=
  rfl

end category_theory


-- Isomorphisms in Type and equivalences.

namespace equiv


/--
Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
def to_iso {X : Type u} {Y : Type u} (e : X ≃ Y) : X ≅ Y :=
  category_theory.iso.mk (to_fun e) (inv_fun e)

@[simp] theorem to_iso_hom {X : Type u} {Y : Type u} {e : X ≃ Y} :
    category_theory.iso.hom (to_iso e) = ⇑e :=
  rfl

@[simp] theorem to_iso_inv {X : Type u} {Y : Type u} {e : X ≃ Y} :
    category_theory.iso.inv (to_iso e) = ⇑(equiv.symm e) :=
  rfl

end equiv


namespace category_theory.iso


/--
Any isomorphism between types gives an equivalence.
-/
def to_equiv {X : Type u} {Y : Type u} (i : X ≅ Y) : X ≃ Y := equiv.mk (hom i) (inv i) sorry sorry

@[simp] theorem to_equiv_fun {X : Type u} {Y : Type u} (i : X ≅ Y) : ⇑(to_equiv i) = hom i := rfl

@[simp] theorem to_equiv_symm_fun {X : Type u} {Y : Type u} (i : X ≅ Y) :
    ⇑(equiv.symm (to_equiv i)) = inv i :=
  rfl

@[simp] theorem to_equiv_id (X : Type u) : to_equiv (refl X) = equiv.refl X := rfl

@[simp] theorem to_equiv_comp {X : Type u} {Y : Type u} {Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) :
    to_equiv (f ≪≫ g) = equiv.trans (to_equiv f) (to_equiv g) :=
  rfl

end category_theory.iso


namespace category_theory


/-- A morphism in `Type u` is an isomorphism if and only if it is bijective. -/
def is_iso_equiv_bijective {X : Type u} {Y : Type u} (f : X ⟶ Y) :
    is_iso f ≃ function.bijective f :=
  equiv_of_subsingleton_of_subsingleton sorry
    fun (b : function.bijective f) => is_iso.mk (iso.inv (equiv.to_iso (equiv.of_bijective f b)))

end category_theory


-- We prove `equiv_iso_iso` and then use that to sneakily construct `equiv_equiv_iso`.

-- (In this order the proofs are handled by `obviously`.)

/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simp] theorem equiv_iso_iso_hom {X : Type u} {Y : Type u} (e : X ≃ Y) :
    category_theory.iso.hom equiv_iso_iso e = equiv.to_iso e :=
  Eq.refl (category_theory.iso.hom equiv_iso_iso e)

/-- Equivalences (between types in the same universe) are the same as (equivalent to) isomorphisms
of types. -/
-- We leave `X` and `Y` as explicit arguments here, because the coercions from `equiv` to a function

-- won't fire without them.

-- TODO: is it still true?

def equiv_equiv_iso (X : Type u) (Y : Type u) : X ≃ Y ≃ (X ≅ Y) :=
  category_theory.iso.to_equiv equiv_iso_iso

@[simp] theorem equiv_equiv_iso_hom {X : Type u} {Y : Type u} (e : X ≃ Y) :
    coe_fn (equiv_equiv_iso X Y) e = equiv.to_iso e :=
  rfl

@[simp] theorem equiv_equiv_iso_inv {X : Type u} {Y : Type u} (e : X ≅ Y) :
    coe_fn (equiv.symm (equiv_equiv_iso X Y)) e = category_theory.iso.to_equiv e :=
  rfl

end Mathlib