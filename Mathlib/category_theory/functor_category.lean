/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_transformation
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ v₃ u₃ 

namespace Mathlib

namespace category_theory


/--
`functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
protected instance functor.category (C : Type u₁) [category C] (D : Type u₂) [category D] : category (C ⥤ D) :=
  category.mk

namespace nat_trans


@[simp] theorem vcomp_eq_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β :=
  rfl

theorem vcomp_app' {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : app (α ≫ β) X = app α X ≫ app β X :=
  rfl

theorem congr_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {α : F ⟶ G} {β : F ⟶ G} (h : α = β) (X : C) : app α X = app β X :=
  eq.mpr (id (Eq._oldrec (Eq.refl (app α X = app β X)) h)) (Eq.refl (app β X))

@[simp] theorem id_app {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (X : C) : app 𝟙 X = 𝟙 :=
  rfl

@[simp] theorem comp_app {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : app (α ≫ β) X = app α X ≫ app β X :=
  rfl

theorem app_naturality {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D ⥤ E} {G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y : D} {Z : D} (f : Y ⟶ Z) : functor.map (functor.obj F X) f ≫ app (app T X) Z = app (app T X) Y ≫ functor.map (functor.obj G X) f :=
  naturality (app T X) f

theorem naturality_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D ⥤ E} {G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X : C} {Y : C} (f : X ⟶ Y) : app (functor.map F f) Z ≫ app (app T Y) Z = app (app T X) Z ≫ app (functor.map G f) Z :=
  congr_fun (congr_arg app (naturality T f)) Z

/-- A natural transformation is a monomorphism if each component is. -/
theorem mono_app_of_mono {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ⟶ G) [∀ (X : C), mono (app α X)] : mono α := sorry

/-- A natural transformation is an epimorphism if each component is. -/
theorem epi_app_of_epi {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : C ⥤ D} (α : F ⟶ G) [∀ (X : C), epi (app α X)] : epi α := sorry

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
def hcomp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} {I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I :=
  mk fun (X : C) => app β (functor.obj F X) ≫ functor.map I (app α X)

infixl:80 " ◫ " => Mathlib.category_theory.nat_trans.hcomp

@[simp] theorem hcomp_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} {I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) (X : C) : app (α ◫ β) X = app β (functor.obj F X) ≫ functor.map I (app α X) :=
  rfl

@[simp] theorem hcomp_id_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} (α : F ⟶ G) (X : C) : app (α ◫ 𝟙) X = functor.map H (app α X) := sorry

theorem id_hcomp_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : E ⥤ C} (α : F ⟶ G) (X : E) : app (𝟙 ◫ α) X = app α (functor.obj H X) := sorry

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we

-- need to use associativity of functor composition. (It's true without the explicit associator,

-- because functor composition is definitionally associative, but relying on the definitional equality

-- causes bad problems with elaboration later.)

theorem exchange {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : C ⥤ D} {I : D ⥤ E} {J : D ⥤ E} {K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) : (α ≫ β) ◫ (γ ≫ δ) = α ◫ γ ≫ β ◫ δ := sorry

end nat_trans


namespace functor


/-- Flip the arguments of a bifunctor. See also `currying.lean`. -/
protected def flip {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E :=
  mk (fun (k : D) => mk (fun (j : C) => obj (obj F j) k) fun (j j' : C) (f : j ⟶ j') => nat_trans.app (map F f) k)
    fun (c c' : D) (f : c ⟶ c') => nat_trans.mk fun (j : C) => map (obj F j) f

@[simp] theorem flip_obj_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D ⥤ E) (c : C) (d : D) : obj (obj (functor.flip F) d) c = obj (obj F c) d :=
  rfl

@[simp] theorem flip_obj_map {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D ⥤ E) {c : C} {c' : C} (f : c ⟶ c') (d : D) : map (obj (functor.flip F) d) f = nat_trans.app (map F f) d :=
  rfl

@[simp] theorem flip_map_app {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D ⥤ E) {d : D} {d' : D} (f : d ⟶ d') (c : C) : nat_trans.app (map (functor.flip F) f) c = map (obj F c) f :=
  rfl

