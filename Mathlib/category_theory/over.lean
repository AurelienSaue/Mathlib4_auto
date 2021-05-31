/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.comma
import Mathlib.category_theory.punit
import Mathlib.category_theory.reflects_isomorphisms
import Mathlib.category_theory.epi_mono
import Mathlib.PostPort

universes v₁ u₁ v₂ u₂ 

namespace Mathlib

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

comma, slice, coslice, over, under
-/

namespace category_theory


/--
The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles.

See https://stacks.math.columbia.edu/tag/001G.
-/
def over {T : Type u₁} [category T] (X : T) :=
  comma 𝟭 (functor.from_punit X)

-- Satisfying the inhabited linter

protected instance over.inhabited {T : Type u₁} [category T] [Inhabited T] : Inhabited (over Inhabited.default) :=
  { default := comma.mk 𝟙 }

namespace over


theorem over_morphism.ext {T : Type u₁} [category T] {X : T} {U : over X} {V : over X} {f : U ⟶ V} {g : U ⟶ V} (h : comma_morphism.left f = comma_morphism.left g) : f = g := sorry

@[simp] theorem over_right {T : Type u₁} [category T] {X : T} (U : over X) : comma.right U = PUnit.unit :=
  of_as_true trivial

@[simp] theorem id_left {T : Type u₁} [category T] {X : T} (U : over X) : comma_morphism.left 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_left {T : Type u₁} [category T] {X : T} (a : over X) (b : over X) (c : over X) (f : a ⟶ b) (g : b ⟶ c) : comma_morphism.left (f ≫ g) = comma_morphism.left f ≫ comma_morphism.left g :=
  rfl

@[simp] theorem w {T : Type u₁} [category T] {X : T} {A : over X} {B : over X} (f : A ⟶ B) : comma_morphism.left f ≫ comma.hom B = comma.hom A := sorry

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simp] theorem mk_left {T : Type u₁} [category T] {X : T} {Y : T} (f : Y ⟶ X) : comma.left (mk f) = Y :=
  Eq.refl (comma.left (mk f))

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
    be a global instance, but it is sometimes useful. -/
def coe_from_hom {T : Type u₁} [category T] {X : T} {Y : T} : has_coe (Y ⟶ X) (over X) :=
  has_coe.mk mk

@[simp] theorem coe_hom {T : Type u₁} [category T] {X : T} {Y : T} (f : Y ⟶ X) : comma.hom ↑f = f :=
  rfl

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
    triangle. -/
def hom_mk {T : Type u₁} [category T] {X : T} {U : over X} {V : over X} (f : comma.left U ⟶ comma.left V) (w : autoParam (f ≫ comma.hom V = comma.hom U)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) : U ⟶ V :=
  comma_morphism.mk

/--
Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simp] theorem iso_mk_inv_left {T : Type u₁} [category T] {X : T} {f : over X} {g : over X} (hl : comma.left f ≅ comma.left g) (hw : autoParam (iso.hom hl ≫ comma.hom g = comma.hom f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) : comma_morphism.left (iso.inv (iso_mk hl)) = iso.inv hl :=
  Eq.refl (iso.inv hl)

/--
The forgetful functor mapping an arrow to its domain.

See https://stacks.math.columbia.edu/tag/001G.
-/
def forget {T : Type u₁} [category T] (X : T) : over X ⥤ T :=
  comma.fst 𝟭 (functor.from_punit X)

@[simp] theorem forget_obj {T : Type u₁} [category T] {X : T} {U : over X} : functor.obj (forget X) U = comma.left U :=
  rfl

@[simp] theorem forget_map {T : Type u₁} [category T] {X : T} {U : over X} {V : over X} {f : U ⟶ V} : functor.map (forget X) f = comma_morphism.left f :=
  rfl

/--
A morphism `f : X ⟶ Y` induces a functor `over X ⥤ over Y` in the obvious way.

See https://stacks.math.columbia.edu/tag/001G.
-/
def map {T : Type u₁} [category T] {X : T} {Y : T} (f : X ⟶ Y) : over X ⥤ over Y :=
  comma.map_right 𝟭 (discrete.nat_trans fun (_x : discrete PUnit) => f)

@[simp] theorem map_obj_left {T : Type u₁} [category T] {X : T} {Y : T} {f : X ⟶ Y} {U : over X} : comma.left (functor.obj (map f) U) = comma.left U :=
  rfl

@[simp] theorem map_obj_hom {T : Type u₁} [category T] {X : T} {Y : T} {f : X ⟶ Y} {U : over X} : comma.hom (functor.obj (map f) U) = comma.hom U ≫ f :=
  rfl

@[simp] theorem map_map_left {T : Type u₁} [category T] {X : T} {Y : T} {f : X ⟶ Y} {U : over X} {V : over X} {g : U ⟶ V} : comma_morphism.left (functor.map (map f) g) = comma_morphism.left g :=
  rfl

/-- Mapping by the identity morphism is just the identity functor. -/
def map_id {T : Type u₁} [category T] {Y : T} : map 𝟙 ≅ 𝟭 :=
  nat_iso.of_components (fun (X : over Y) => iso_mk (iso.refl (comma.left (functor.obj (map 𝟙) X)))) sorry

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def map_comp {T : Type u₁} [category T] {X : T} {Y : T} {Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map f ⋙ map g :=
  nat_iso.of_components (fun (X_1 : over X) => iso_mk (iso.refl (comma.left (functor.obj (map (f ≫ g)) X_1)))) sorry

protected instance forget_reflects_iso {T : Type u₁} [category T] {X : T} : reflects_isomorphisms (forget X) :=
  reflects_isomorphisms.mk
    fun (Y Z : over X) (f : Y ⟶ Z) (t : is_iso (functor.map (forget X) f)) =>
      is_iso.mk (hom_mk (inv (functor.map (forget X) f)))

protected instance forget_faithful {T : Type u₁} [category T] {X : T} : faithful (forget X) :=
  faithful.mk

/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category.
-/
-- TODO: Show the converse holds if `T` has binary products or pushouts.

theorem epi_of_epi_left {T : Type u₁} [category T] {X : T} {f : over X} {g : over X} (k : f ⟶ g) [hk : epi (comma_morphism.left k)] : epi k :=
  faithful_reflects_epi (forget X) hk

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `over.forget X` reflects
monomorphisms.
The converse of `category_theory.over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem mono_of_mono_left {T : Type u₁} [category T] {X : T} {f : over X} {g : over X} (k : f ⟶ g) [hk : mono (comma_morphism.left k)] : mono k :=
  faithful_reflects_mono (forget X) hk

/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `over.forget X` preserves
monomorphisms.
The converse of `category_theory.over.mono_of_mono_left`.
-/
protected instance mono_left_of_mono {T : Type u₁} [category T] {X : T} {f : over X} {g : over X} (k : f ⟶ g) [mono k] : mono (comma_morphism.left k) :=
  mono.mk
    fun (Y : T) (l m : Y ⟶ comma.left f) (a : l ≫ comma_morphism.left k = m ≫ comma_morphism.left k) =>
      let l' : mk (m ≫ comma.hom f) ⟶ f := hom_mk l;
      congr_arg comma_morphism.left
        (eq.mpr (id (Eq._oldrec (Eq.refl (l' = hom_mk m)) (Eq.symm (propext (cancel_mono k))))) (over_morphism.ext a))

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simp] theorem iterated_slice_forward_obj {T : Type u₁} [category T] {X : T} (f : over X) (α : over f) : functor.obj (iterated_slice_forward f) α = mk (comma_morphism.left (comma.hom α)) :=
  Eq.refl (functor.obj (iterated_slice_forward f) α)

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simp] theorem iterated_slice_backward_map {T : Type u₁} [category T] {X : T} (f : over X) (g : over (comma.left f)) (h : over (comma.left f)) (α : g ⟶ h) : functor.map (iterated_slice_backward f) α = hom_mk (hom_mk (comma_morphism.left α)) :=
  Eq.refl (functor.map (iterated_slice_backward f) α)

/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simp] theorem iterated_slice_equiv_counit_iso {T : Type u₁} [category T] {X : T} (f : over X) : equivalence.counit_iso (iterated_slice_equiv f) =
  nat_iso.of_components
    (fun (g : over (comma.left f)) =>
      iso_mk (iso.refl (comma.left (functor.obj (iterated_slice_backward f ⋙ iterated_slice_forward f) g))))
    (iterated_slice_equiv._proof_5 f) :=
  Eq.refl (equivalence.counit_iso (iterated_slice_equiv f))

theorem iterated_slice_forward_forget {T : Type u₁} [category T] {X : T} (f : over X) : iterated_slice_forward f ⋙ forget (comma.left f) = forget f ⋙ forget X :=
  rfl

theorem iterated_slice_backward_forget_forget {T : Type u₁} [category T] {X : T} (f : over X) : iterated_slice_backward f ⋙ forget f ⋙ forget X = forget (comma.left f) :=
  rfl

/-- A functor `F : T ⥤ D` induces a functor `over X ⥤ over (F.obj X)` in the obvious way. -/
@[simp] theorem post_map_right {T : Type u₁} [category T] {X : T} {D : Type u₂} [category D] (F : T ⥤ D) (Y₁ : over X) (Y₂ : over X) (f : Y₁ ⟶ Y₂) : comma_morphism.right (functor.map (post F) f) =
  id (fun (F : T ⥤ D) (Y₁ Y₂ : over X) (f : Y₁ ⟶ Y₂) => ulift.up (eq.mpr post._proof_1 (plift.up (of_as_true trivial))))
    F Y₁ Y₂ f :=
  Eq.refl (comma_morphism.right (functor.map (post F) f))

end over


/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
def under {T : Type u₁} [category T] (X : T) :=
  comma (functor.from_punit X) 𝟭

-- Satisfying the inhabited linter

protected instance under.inhabited {T : Type u₁} [category T] [Inhabited T] : Inhabited (under Inhabited.default) :=
  { default := comma.mk 𝟙 }

namespace under


theorem under_morphism.ext {T : Type u₁} [category T] {X : T} {U : under X} {V : under X} {f : U ⟶ V} {g : U ⟶ V} (h : comma_morphism.right f = comma_morphism.right g) : f = g := sorry

@[simp] theorem under_left {T : Type u₁} [category T] {X : T} (U : under X) : comma.left U = PUnit.unit :=
  of_as_true trivial

@[simp] theorem id_right {T : Type u₁} [category T] {X : T} (U : under X) : comma_morphism.right 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_right {T : Type u₁} [category T] {X : T} (a : under X) (b : under X) (c : under X) (f : a ⟶ b) (g : b ⟶ c) : comma_morphism.right (f ≫ g) = comma_morphism.right f ≫ comma_morphism.right g :=
  rfl

@[simp] theorem w {T : Type u₁} [category T] {X : T} {A : under X} {B : under X} (f : A ⟶ B) : comma.hom A ≫ comma_morphism.right f = comma.hom B := sorry

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[simp] theorem mk_left {T : Type u₁} [category T] {X : T} {Y : T} (f : X ⟶ Y) : comma.left (mk f) = PUnit.unit :=
  Eq.refl (comma.left (mk f))

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simp] theorem hom_mk_left {T : Type u₁} [category T] {X : T} {U : under X} {V : under X} (f : comma.right U ⟶ comma.right V) (w : autoParam (comma.hom U ≫ f = comma.hom V)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) : comma_morphism.left (hom_mk f) =
  id
    (fun {X : T} {U V : under X} (f : comma.right U ⟶ comma.right V) (w : comma.hom U ≫ f = comma.hom V) =>
      eq.mpr hom_mk._proof_1 (ulift.up (eq.mpr hom_mk._proof_2 (plift.up (of_as_true trivial)))))
    X U V f w :=
  Eq.refl (comma_morphism.left (hom_mk f))

/--
Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def iso_mk {T : Type u₁} [category T] {X : T} {f : under X} {g : under X} (hr : comma.right f ≅ comma.right g) (hw : comma.hom f ≫ iso.hom hr = comma.hom g) : f ≅ g :=
  comma.iso_mk (eq_to_iso sorry) hr sorry

@[simp] theorem iso_mk_hom_right {T : Type u₁} [category T] {X : T} {f : under X} {g : under X} (hr : comma.right f ≅ comma.right g) (hw : comma.hom f ≫ iso.hom hr = comma.hom g) : comma_morphism.right (iso.hom (iso_mk hr hw)) = iso.hom hr :=
  rfl

@[simp] theorem iso_mk_inv_right {T : Type u₁} [category T] {X : T} {f : under X} {g : under X} (hr : comma.right f ≅ comma.right g) (hw : comma.hom f ≫ iso.hom hr = comma.hom g) : comma_morphism.right (iso.inv (iso_mk hr hw)) = iso.inv hr :=
  rfl

/-- The forgetful functor mapping an arrow to its domain. -/
def forget {T : Type u₁} [category T] (X : T) : under X ⥤ T :=
  comma.snd (functor.from_punit X) 𝟭

@[simp] theorem forget_obj {T : Type u₁} [category T] {X : T} {U : under X} : functor.obj (forget X) U = comma.right U :=
  rfl

@[simp] theorem forget_map {T : Type u₁} [category T] {X : T} {U : under X} {V : under X} {f : U ⟶ V} : functor.map (forget X) f = comma_morphism.right f :=
  rfl

/-- A morphism `X ⟶ Y` induces a functor `under Y ⥤ under X` in the obvious way. -/
def map {T : Type u₁} [category T] {X : T} {Y : T} (f : X ⟶ Y) : under Y ⥤ under X :=
  comma.map_left 𝟭 (discrete.nat_trans fun (_x : discrete PUnit) => f)

@[simp] theorem map_obj_right {T : Type u₁} [category T] {X : T} {Y : T} {f : X ⟶ Y} {U : under Y} : comma.right (functor.obj (map f) U) = comma.right U :=
  rfl

@[simp] theorem map_obj_hom {T : Type u₁} [category T] {X : T} {Y : T} {f : X ⟶ Y} {U : under Y} : comma.hom (functor.obj (map f) U) = f ≫ comma.hom U :=
  rfl

@[simp] theorem map_map_right {T : Type u₁} [category T] {X : T} {Y : T} {f : X ⟶ Y} {U : under Y} {V : under Y} {g : U ⟶ V} : comma_morphism.right (functor.map (map f) g) = comma_morphism.right g :=
  rfl

/-- Mapping by the identity morphism is just the identity functor. -/
def map_id {T : Type u₁} [category T] {Y : T} : map 𝟙 ≅ 𝟭 :=
  nat_iso.of_components (fun (X : under Y) => iso_mk (iso.refl (comma.right (functor.obj (map 𝟙) X))) sorry) sorry

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def map_comp {T : Type u₁} [category T] {X : T} {Y : T} {Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  nat_iso.of_components (fun (X_1 : under Z) => iso_mk (iso.refl (comma.right (functor.obj (map (f ≫ g)) X_1))) sorry)
    sorry

/-- A functor `F : T ⥤ D` induces a functor `under X ⥤ under (F.obj X)` in the obvious way. -/
@[simp] theorem post_map_left {T : Type u₁} [category T] {D : Type u₂} [category D] {X : T} (F : T ⥤ D) (Y₁ : under X) (Y₂ : under X) (f : Y₁ ⟶ Y₂) : comma_morphism.left (functor.map (post F) f) =
  id
    (fun {X : T} (F : T ⥤ D) (Y₁ Y₂ : under X) (f : Y₁ ⟶ Y₂) =>
      ulift.up (eq.mpr post._proof_1 (plift.up (of_as_true trivial))))
    X F Y₁ Y₂ f :=
  Eq.refl (comma_morphism.left (functor.map (post F) f))

