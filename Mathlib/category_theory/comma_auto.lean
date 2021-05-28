/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin, Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import PostPort

universes v₁ v₂ v₃ u₁ u₂ u₃ l 

namespace Mathlib

/-!
# Comma categories

A comma category is a construction in category theory, which builds a category out of two functors
with a common codomain. Specifically, for functors `L : A ⥤ T` and `R : B ⥤ T`, an object in
`comma L R` is a morphism `hom : L.obj left ⟶ R.obj right` for some objects `left : A` and
`right : B`, and a morphism in `comma L R` between `hom : L.obj left ⟶ R.obj right` and
`hom' : L.obj left' ⟶ R.obj right'` is a commutative square

```
L.obj left   ⟶   L.obj left'
      |               |
  hom |               | hom'
      ↓               ↓
R.obj right  ⟶   R.obj right',
```

where the top and bottom morphism come from morphisms `left ⟶ left'` and `right ⟶ right'`,
respectively.

## Main definitions

* `comma L R`: the comma category of the functors `L` and `R`.
* `over X`: the over category of the object `X` (developed in `over.lean`).
* `under X`: the under category of the object `X` (also developed in `over.lean`).
* `arrow T`: the arrow category of the category `T` (developed in `arrow.lean`).

## References

* <https://ncatlab.org/nlab/show/comma+category>

## Tags

comma, slice, coslice, over, under, arrow
-/

namespace category_theory


/-- The objects of the comma category are triples of an object `left : A`, an object
   `right : B` and a morphism `hom : L.obj left ⟶ R.obj right`.  -/
structure comma {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) (R : B ⥤ T) 
where
  left : autoParam A
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right : autoParam B
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  hom : functor.obj L left ⟶ functor.obj R right

-- Satisfying the inhabited linter

protected instance comma.inhabited {T : Type u₃} [category T] [Inhabited T] : Inhabited (comma 𝟭 𝟭) :=
  { default := comma.mk 𝟙 }

/-- A morphism between two objects in the comma category is a commutative square connecting the
    morphisms coming from the two objects using morphisms in the image of the functors `L` and `R`.
-/
structure comma_morphism {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} (X : comma L R) (Y : comma L R) 
where
  left : autoParam (comma.left X ⟶ comma.left Y)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right : autoParam (comma.right X ⟶ comma.right Y)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  w' : autoParam (functor.map L left ≫ comma.hom Y = comma.hom X ≫ functor.map R right)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- Satisfying the inhabited linter

protected instance comma_morphism.inhabited {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} [Inhabited (comma L R)] : Inhabited (comma_morphism Inhabited.default Inhabited.default) :=
  { default := comma_morphism.mk }

@[simp] theorem comma_morphism.w {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} {X : comma L R} {Y : comma L R} (c : comma_morphism X Y) : functor.map L (comma_morphism.left c) ≫ comma.hom Y = comma.hom X ≫ functor.map R (comma_morphism.right c) := sorry

@[simp] theorem comma_morphism.w_assoc {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} {X : comma L R} {Y : comma L R} (c : comma_morphism X Y) {X' : T} (f' : functor.obj R (comma.right Y) ⟶ X') : functor.map L (comma_morphism.left c) ≫ comma.hom Y ≫ f' = comma.hom X ≫ functor.map R (comma_morphism.right c) ≫ f' := sorry

protected instance comma_category {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} : category (comma L R) :=
  category.mk

namespace comma


@[simp] theorem id_left {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} {X : comma L R} : comma_morphism.left 𝟙 = 𝟙 :=
  rfl

@[simp] theorem id_right {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} {X : comma L R} : comma_morphism.right 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_left {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} {X : comma L R} {Y : comma L R} {Z : comma L R} {f : X ⟶ Y} {g : Y ⟶ Z} : comma_morphism.left (f ≫ g) = comma_morphism.left f ≫ comma_morphism.left g :=
  rfl

@[simp] theorem comp_right {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L : A ⥤ T} {R : B ⥤ T} {X : comma L R} {Y : comma L R} {Z : comma L R} {f : X ⟶ Y} {g : Y ⟶ Z} : comma_morphism.right (f ≫ g) = comma_morphism.right f ≫ comma_morphism.right g :=
  rfl

/-- The functor sending an object `X` in the comma category to `X.left`. -/
def fst {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) (R : B ⥤ T) : comma L R ⥤ A :=
  functor.mk (fun (X : comma L R) => left X) fun (_x _x_1 : comma L R) (f : _x ⟶ _x_1) => comma_morphism.left f

/-- The functor sending an object `X` in the comma category to `X.right`. -/
@[simp] theorem snd_map {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) (R : B ⥤ T) (_x : comma L R) : ∀ (_x_1 : comma L R) (f : _x ⟶ _x_1), functor.map (snd L R) f = comma_morphism.right f :=
  fun (_x_1 : comma L R) (f : _x ⟶ _x_1) => Eq.refl (functor.map (snd L R) f)

/-- We can interpret the commutative square constituting a morphism in the comma category as a
    natural transformation between the functors `fst ⋙ L` and `snd ⋙ R` from the comma category
    to `T`, where the components are given by the morphism that constitutes an object of the comma
    category. -/
@[simp] theorem nat_trans_app {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) (R : B ⥤ T) (X : comma L R) : nat_trans.app (nat_trans L R) X = hom X :=
  Eq.refl (nat_trans.app (nat_trans L R) X)

/--
Construct an isomorphism in the comma category given isomorphisms of the objects whose forward
directions give a commutative square.
-/
@[simp] theorem iso_mk_inv_left {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] {L₁ : A ⥤ T} {R₁ : B ⥤ T} {X : comma L₁ R₁} {Y : comma L₁ R₁} (l : left X ≅ left Y) (r : right X ≅ right Y) (h : functor.map L₁ (iso.hom l) ≫ hom Y = hom X ≫ functor.map R₁ (iso.hom r)) : comma_morphism.left (iso.inv (iso_mk l r h)) = iso.inv l :=
  Eq.refl (comma_morphism.left (iso.inv (iso_mk l r h)))

/-- A natural transformation `L₁ ⟶ L₂` induces a functor `comma L₂ R ⥤ comma L₁ R`. -/
@[simp] theorem map_left_obj_right {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (R : B ⥤ T) {L₁ : A ⥤ T} {L₂ : A ⥤ T} (l : L₁ ⟶ L₂) (X : comma L₂ R) : right (functor.obj (map_left R l) X) = right X :=
  Eq.refl (right (functor.obj (map_left R l) X))

/-- The functor `comma L R ⥤ comma L R` induced by the identity natural transformation on `L` is
    naturally isomorphic to the identity functor. -/
@[simp] theorem map_left_id_inv_app_right {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) (R : B ⥤ T) (X : comma L R) : comma_morphism.right (nat_trans.app (iso.inv (map_left_id L R)) X) = 𝟙 :=
  Eq.refl (comma_morphism.right (nat_trans.app (iso.inv (map_left_id L R)) X))

/-- The functor `comma L₁ R ⥤ comma L₃ R` induced by the composition of two natural transformations
    `l : L₁ ⟶ L₂` and `l' : L₂ ⟶ L₃` is naturally isomorphic to the composition of the two functors
    induced by these natural transformations. -/
@[simp] theorem map_left_comp_hom_app_left {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (R : B ⥤ T) {L₁ : A ⥤ T} {L₂ : A ⥤ T} {L₃ : A ⥤ T} (l : L₁ ⟶ L₂) (l' : L₂ ⟶ L₃) (X : comma L₃ R) : comma_morphism.left (nat_trans.app (iso.hom (map_left_comp R l l')) X) = 𝟙 :=
  Eq.refl (comma_morphism.left (nat_trans.app (iso.hom (map_left_comp R l l')) X))

/-- A natural transformation `R₁ ⟶ R₂` induces a functor `comma L R₁ ⥤ comma L R₂`. -/
def map_right {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) {R₁ : B ⥤ T} {R₂ : B ⥤ T} (r : R₁ ⟶ R₂) : comma L R₁ ⥤ comma L R₂ :=
  functor.mk (fun (X : comma L R₁) => mk (hom X ≫ nat_trans.app r (right X)))
    fun (X Y : comma L R₁) (f : X ⟶ Y) => comma_morphism.mk

/-- The functor `comma L R ⥤ comma L R` induced by the identity natural transformation on `R` is
    naturally isomorphic to the identity functor. -/
@[simp] theorem map_right_id_inv_app_left {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) (R : B ⥤ T) (X : comma L R) : comma_morphism.left (nat_trans.app (iso.inv (map_right_id L R)) X) = 𝟙 :=
  Eq.refl (comma_morphism.left (nat_trans.app (iso.inv (map_right_id L R)) X))

/-- The functor `comma L R₁ ⥤ comma L R₃` induced by the composition of the natural transformations
    `r : R₁ ⟶ R₂` and `r' : R₂ ⟶ R₃` is naturally isomorphic to the composition of the functors
    induced by these natural transformations. -/
@[simp] theorem map_right_comp_inv_app_right {A : Type u₁} [category A] {B : Type u₂} [category B] {T : Type u₃} [category T] (L : A ⥤ T) {R₁ : B ⥤ T} {R₂ : B ⥤ T} {R₃ : B ⥤ T} (r : R₁ ⟶ R₂) (r' : R₂ ⟶ R₃) (X : comma L R₁) : comma_morphism.right (nat_trans.app (iso.inv (map_right_comp L r r')) X) = 𝟙 :=
  Eq.refl (comma_morphism.right (nat_trans.app (iso.inv (map_right_comp L r r')) X))

