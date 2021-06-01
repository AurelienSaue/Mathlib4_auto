/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import Mathlib.data.equiv.basic
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l v₃ u₃ 

namespace Mathlib

namespace category_theory


/--
A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective.
In fact, we use a constructive definition, so the `full F` typeclass contains data,
specifying a particular preimage of each `f : F.obj X ⟶ F.obj Y`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class full {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) where
  preimage : {X Y : C} → (functor.obj F X ⟶ functor.obj F Y) → (X ⟶ Y)
  witness' :
    autoParam (∀ {X Y : C} (f : functor.obj F X ⟶ functor.obj F Y), functor.map F (preimage f) = f)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem full.witness {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    [c : full F] {X : C} {Y : C} (f : functor.obj F X ⟶ functor.obj F Y) :
    functor.map F (full.preimage f) = f :=
  sorry

/--
A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective.

See https://stacks.math.columbia.edu/tag/001C.
-/
class faithful {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) where
  map_injective' :
    autoParam (∀ {X Y : C}, function.injective (functor.map F))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem faithful.map_injective {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [c : faithful F] {X : C} {Y : C} : function.injective (functor.map F) :=
  sorry

namespace functor


theorem map_injective {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [faithful F]
    {X : C} {Y : C} : function.injective (map F) :=
  faithful.map_injective F

/-- The specified preimage of a morphism under a full functor. -/
def preimage {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [full F] {X : C}
    {Y : C} (f : obj F X ⟶ obj F Y) : X ⟶ Y :=
  full.preimage f

@[simp] theorem image_preimage {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [full F] {X : C} {Y : C} (f : obj F X ⟶ obj F Y) : map F (preimage F f) = f :=
  sorry

end functor


@[simp] theorem preimage_id {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    [full F] [faithful F] {X : C} : functor.preimage F 𝟙 = 𝟙 :=
  sorry

@[simp] theorem preimage_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    [full F] [faithful F] {X : C} {Y : C} {Z : C} (f : functor.obj F X ⟶ functor.obj F Y)
    (g : functor.obj F Y ⟶ functor.obj F Z) :
    functor.preimage F (f ≫ g) = functor.preimage F f ≫ functor.preimage F g :=
  sorry

@[simp] theorem preimage_map {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    [full F] [faithful F] {X : C} {Y : C} (f : X ⟶ Y) : functor.preimage F (functor.map F f) = f :=
  sorry

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
def preimage_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} [full F]
    [faithful F] {X : C} {Y : C} (f : functor.obj F X ≅ functor.obj F Y) : X ≅ Y :=
  iso.mk (functor.preimage F (iso.hom f)) (functor.preimage F (iso.inv f))

@[simp] theorem preimage_iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    [full F] [faithful F] {X : C} {Y : C} (f : functor.obj F X ≅ functor.obj F Y) :
    iso.hom (preimage_iso f) = functor.preimage F (iso.hom f) :=
  rfl

@[simp] theorem preimage_iso_inv {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    [full F] [faithful F] {X : C} {Y : C} (f : functor.obj F X ≅ functor.obj F Y) :
    iso.inv (preimage_iso f) = functor.preimage F (iso.inv f) :=
  rfl

@[simp] theorem preimage_iso_map_iso {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} [full F] [faithful F] {X : C} {Y : C} (f : X ≅ Y) :
    preimage_iso (functor.map_iso F f) = f :=
  sorry

/--
If the image of a morphism under a fully faithful functor in an isomorphism,
then the original morphisms is also an isomorphism.
-/
def is_iso_of_fully_faithful {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [full F] [faithful F] {X : C} {Y : C} (f : X ⟶ Y) [is_iso (functor.map F f)] : is_iso f :=
  is_iso.mk (functor.preimage F (inv (functor.map F f)))

/-- If `F` is fully faithful, we have an equivalence of hom-sets `X ⟶ Y` and `F X ⟶ F Y`. -/
def equiv_of_fully_faithful {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [full F] [faithful F] {X : C} {Y : C} : (X ⟶ Y) ≃ (functor.obj F X ⟶ functor.obj F Y) :=
  equiv.mk (fun (f : X ⟶ Y) => functor.map F f)
    (fun (f : functor.obj F X ⟶ functor.obj F Y) => functor.preimage F f) sorry sorry

@[simp] theorem equiv_of_fully_faithful_apply {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [full F] [faithful F] {X : C} {Y : C} (f : X ⟶ Y) :
    coe_fn (equiv_of_fully_faithful F) f = functor.map F f :=
  rfl

@[simp] theorem equiv_of_fully_faithful_symm_apply {C : Type u₁} [category C] {D : Type u₂}
    [category D] (F : C ⥤ D) [full F] [faithful F] {X : C} {Y : C}
    (f : functor.obj F X ⟶ functor.obj F Y) :
    coe_fn (equiv.symm (equiv_of_fully_faithful F)) f = functor.preimage F f :=
  rfl

end category_theory


namespace category_theory


protected instance full.id {C : Type u₁} [category C] : full 𝟭 :=
  full.mk fun (_x _x_1 : C) (f : functor.obj 𝟭 _x ⟶ functor.obj 𝟭 _x_1) => f

protected instance faithful.id {C : Type u₁} [category C] : faithful 𝟭 := faithful.mk

protected instance faithful.comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) (G : D ⥤ E) [faithful F] [faithful G] : faithful (F ⋙ G) :=
  faithful.mk

theorem faithful.of_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) (G : D ⥤ E) [faithful (F ⋙ G)] : faithful F :=
  faithful.mk

theorem faithful.of_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D}
    {F' : C ⥤ D} [faithful F] (α : F ≅ F') : faithful F' :=
  faithful.mk

theorem faithful.of_comp_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [ℋ : faithful H] (h : F ⋙ G ≅ H) :
    faithful F :=
  faithful.of_comp F G

theorem iso.faithful_of_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [ℋ : faithful H] (h : F ⋙ G ≅ H) :
    faithful F :=
  faithful.of_comp_iso

-- We could prove this from `faithful.of_comp_iso` using `eq_to_iso`,

-- but that would introduce a cyclic import.

theorem faithful.of_comp_eq {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [ℋ : faithful H] (h : F ⋙ G = H) :
    faithful F :=
  faithful.of_comp F G

theorem Mathlib.eq.faithful_of_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [ℋ : faithful H]
    (h : F ⋙ G = H) : faithful F :=
  faithful.of_comp_eq

/-- “Divide” a functor by a faithful functor. -/
protected def faithful.div {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ E) (G : D ⥤ E) [faithful G] (obj : C → D)
    (h_obj : ∀ (X : C), functor.obj G (obj X) = functor.obj F X)
    (map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y : C} {f : X ⟶ Y}, functor.map G (map f) == functor.map F f) : C ⥤ D :=
  functor.mk obj map

-- This follows immediately from `functor.hext` (`functor.hext h_obj @h_map`),

-- but importing `category_theory.eq_to_hom` causes an import loop:

-- category_theory.eq_to_hom → category_theory.opposites →

-- category_theory.equivalence → category_theory.fully_faithful

theorem faithful.div_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G] (obj : C → D)
    (h_obj : ∀ (X : C), functor.obj G (obj X) = functor.obj F X)
    (map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y : C} {f : X ⟶ Y}, functor.map G (map f) == functor.map F f) :
    faithful.div F G obj h_obj map h_map ⋙ G = F :=
  sorry

theorem faithful.div_faithful {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ E) [faithful F] (G : D ⥤ E) [faithful G] (obj : C → D)
    (h_obj : ∀ (X : C), functor.obj G (obj X) = functor.obj F X)
    (map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y))
    (h_map : ∀ {X Y : C} {f : X ⟶ Y}, functor.map G (map f) == functor.map F f) :
    faithful (faithful.div F G obj h_obj map h_map) :=
  eq.faithful_of_comp
    (faithful.div_comp F G (fun (X : C) => obj X) h_obj (fun (X Y : C) (f : X ⟶ Y) => map f) h_map)

protected instance full.comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (F : C ⥤ D) (G : D ⥤ E) [full F] [full G] : full (F ⋙ G) :=
  full.mk
    fun (_x _x_1 : C) (f : functor.obj (F ⋙ G) _x ⟶ functor.obj (F ⋙ G) _x_1) =>
      functor.preimage F (functor.preimage G f)

/--
Given a natural isomorphism between `F ⋙ H` and `G ⋙ H` for a fully faithful functor `H`, we
can 'cancel' it to give a natural iso between `F` and `G`.
-/
def fully_faithful_cancel_right {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] {F : C ⥤ D} {G : C ⥤ D} (H : D ⥤ E) [full H] [faithful H]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  nat_iso.of_components (fun (X : C) => preimage_iso (iso.app comp_iso X)) sorry

@[simp] theorem fully_faithful_cancel_right_hom_app {C : Type u₁} [category C] {D : Type u₂}
    [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} [full H]
    [faithful H] (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    nat_trans.app (iso.hom (fully_faithful_cancel_right H comp_iso)) X =
        functor.preimage H (nat_trans.app (iso.hom comp_iso) X) :=
  rfl

@[simp] theorem fully_faithful_cancel_right_inv_app {C : Type u₁} [category C] {D : Type u₂}
    [category D] {E : Type u₃} [category E] {F : C ⥤ D} {G : C ⥤ D} {H : D ⥤ E} [full H]
    [faithful H] (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    nat_trans.app (iso.inv (fully_faithful_cancel_right H comp_iso)) X =
        functor.preimage H (nat_trans.app (iso.inv comp_iso) X) :=
  rfl

end Mathlib