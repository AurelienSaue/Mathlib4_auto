/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.natural_isomorphism
import Mathlib.category_theory.eq_to_hom
import Mathlib.data.sigma.basic
import Mathlib.category_theory.pi.basic
import Mathlib.PostPort

universes w₁ v₁ u₁ l u₂ v₂ w₂ w₃ 

namespace Mathlib

/-!
# Disjoint union of categories

We define the category structure on a sigma-type (disjoint union) of categories.
-/

namespace category_theory


namespace sigma


/--
The type of morphisms of a disjoint union of categories: for `X : C i` and `Y : C j`, a morphism
`(i, X) ⟶ (j, Y)` if `i = j` is just a morphism `X ⟶ Y`, and if `i ≠ j` there are no such morphisms.
-/
inductive sigma_hom {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] : (sigma fun (i : I) => C i) → (sigma fun (i : I) => C i) → Type (max w₁ v₁ u₁)
where
| mk : {i : I} → {X Y : C i} → (X ⟶ Y) → sigma_hom (sigma.mk i X) (sigma.mk i Y)

namespace sigma_hom


/-- The identity morphism on an object. -/
def id {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (X : sigma fun (i : I) => C i) : sigma_hom X X :=
  sorry

protected instance inhabited {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (X : sigma fun (i : I) => C i) : Inhabited (sigma_hom X X) :=
  { default := id X }

/-- Composition of sigma homomorphisms. -/
def comp {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {X : sigma fun (i : I) => C i} {Y : sigma fun (i : I) => C i} {Z : sigma fun (i : I) => C i} : sigma_hom X Y → sigma_hom Y Z → sigma_hom X Z :=
  sorry

protected instance sigma.category_theory.category_struct {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] : category_struct (sigma fun (i : I) => C i) :=
  category_struct.mk id fun (X Y Z : sigma fun (i : I) => C i) (f : X ⟶ Y) (g : Y ⟶ Z) => comp f g

@[simp] theorem comp_def {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (i : I) (X : C i) (Y : C i) (Z : C i) (f : X ⟶ Y) (g : Y ⟶ Z) : comp (mk f) (mk g) = mk (f ≫ g) :=
  rfl

theorem assoc {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (X : sigma fun (i : I) => C i) (Y : sigma fun (i : I) => C i) (Z : sigma fun (i : I) => C i) (W : sigma fun (i : I) => C i) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) : (f ≫ g) ≫ h = f ≫ g ≫ h := sorry

theorem id_comp {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (X : sigma fun (i : I) => C i) (Y : sigma fun (i : I) => C i) (f : X ⟶ Y) : 𝟙 ≫ f = f := sorry

theorem comp_id {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (X : sigma fun (i : I) => C i) (Y : sigma fun (i : I) => C i) (f : X ⟶ Y) : f ≫ 𝟙 = f := sorry

end sigma_hom


protected instance sigma {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] : category (sigma fun (i : I) => C i) :=
  category.mk

/-- The inclusion functor into the disjoint union of categories. -/
@[simp] theorem incl_map {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (i : I) (X : C i) (Y : C i) : ∀ (ᾰ : X ⟶ Y), functor.map (incl i) ᾰ = sigma_hom.mk ᾰ :=
  fun (ᾰ : X ⟶ Y) => Eq.refl (functor.map (incl i) ᾰ)

@[simp] theorem incl_obj {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {i : I} (X : C i) : functor.obj (incl i) X = sigma.mk i X :=
  rfl

protected instance incl.category_theory.full {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (i : I) : full (incl i) :=
  full.mk fun (X Y : C i) (_x : functor.obj (incl i) X ⟶ functor.obj (incl i) Y) => sorry

protected instance incl.category_theory.faithful {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] (i : I) : faithful (incl i) :=
  faithful.mk

/--
To build a natural transformation over the sigma category, it suffices to specify it restricted to
each subcategory.
-/
def nat_trans {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] {F : (sigma fun (i : I) => C i) ⥤ D} {G : (sigma fun (i : I) => C i) ⥤ D} (h : (i : I) → incl i ⋙ F ⟶ incl i ⋙ G) : F ⟶ G :=
  nat_trans.mk fun (_x : sigma fun (i : I) => C i) => sorry

@[simp] theorem nat_trans_app {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] {F : (sigma fun (i : I) => C i) ⥤ D} {G : (sigma fun (i : I) => C i) ⥤ D} (h : (i : I) → incl i ⋙ F ⟶ incl i ⋙ G) (i : I) (X : C i) : nat_trans.app (nat_trans h) (sigma.mk i X) = nat_trans.app (h i) X :=
  rfl

/-- (Implementation). An auxiliary definition to build the functor `desc`. -/
def desc_map {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (X : sigma fun (i : I) => C i) (Y : sigma fun (i : I) => C i) : (X ⟶ Y) → (functor.obj (F (sigma.fst X)) (sigma.snd X) ⟶ functor.obj (F (sigma.fst Y)) (sigma.snd Y)) :=
  sorry

/--
Given a collection of functors `F i : C i ⥤ D`, we can produce a functor `(Σ i, C i) ⥤ D`.

The produced functor `desc F` satisfies: `incl i ⋙ desc F ≅ F i`, i.e. restricted to just the
subcategory `C i`, `desc F` agrees with `F i`, and it is unique (up to natural isomorphism) with
this property.

This witnesses that the sigma-type is the coproduct in Cat.
-/
@[simp] theorem desc_obj {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (X : sigma fun (i : I) => C i) : functor.obj (desc F) X = functor.obj (F (sigma.fst X)) (sigma.snd X) :=
  Eq.refl (functor.obj (desc F) X)

@[simp] theorem desc_map_mk {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) {i : I} (X : C i) (Y : C i) (f : X ⟶ Y) : functor.map (desc F) (sigma_hom.mk f) = functor.map (F i) f :=
  rfl

/--
This shows that when `desc F` is restricted to just the subcategory `C i`, `desc F` agrees with
`F i`.
-/
-- We hand-generate the simp lemmas about this since they come out cleaner.

def incl_desc {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (i : I) : incl i ⋙ desc F ≅ F i :=
  nat_iso.of_components (fun (X : C i) => iso.refl (functor.obj (incl i ⋙ desc F) X)) sorry

@[simp] theorem incl_desc_hom_app {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (i : I) (X : C i) : nat_trans.app (iso.hom (incl_desc F i)) X = 𝟙 :=
  rfl

@[simp] theorem incl_desc_inv_app {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (i : I) (X : C i) : nat_trans.app (iso.inv (incl_desc F i)) X = 𝟙 :=
  rfl

/--
If `q` when restricted to each subcategory `C i` agrees with `F i`, then `q` is isomorphic to
`desc F`.
-/
def desc_uniq {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (q : (sigma fun (i : I) => C i) ⥤ D) (h : (i : I) → incl i ⋙ q ≅ F i) : q ≅ desc F :=
  nat_iso.of_components (fun (_x : sigma fun (i : I) => C i) => sorry) sorry

@[simp] theorem desc_uniq_hom_app {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (q : (sigma fun (i : I) => C i) ⥤ D) (h : (i : I) → incl i ⋙ q ≅ F i) (i : I) (X : C i) : nat_trans.app (iso.hom (desc_uniq F q h)) (sigma.mk i X) = nat_trans.app (iso.hom (h i)) X :=
  rfl

@[simp] theorem desc_uniq_inv_app {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] (F : (i : I) → C i ⥤ D) (q : (sigma fun (i : I) => C i) ⥤ D) (h : (i : I) → incl i ⋙ q ≅ F i) (i : I) (X : C i) : nat_trans.app (iso.inv (desc_uniq F q h)) (sigma.mk i X) = nat_trans.app (iso.inv (h i)) X :=
  rfl

/--
If `q₁` and `q₂` when restricted to each subcategory `C i` agree, then `q₁` and `q₂` are isomorphic.
-/
@[simp] theorem nat_iso_inv {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : Type u₂} [category D] {q₁ : (sigma fun (i : I) => C i) ⥤ D} {q₂ : (sigma fun (i : I) => C i) ⥤ D} (h : (i : I) → incl i ⋙ q₁ ≅ incl i ⋙ q₂) : iso.inv (nat_iso h) = nat_trans fun (i : I) => iso.inv (h i) :=
  Eq.refl (iso.inv (nat_iso h))

/-- A function `J → I` induces a functor `Σ j, C (g j) ⥤ Σ i, C i`. -/
def map {I : Type w₁} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₂} (g : J → I) : (sigma fun (j : J) => C (g j)) ⥤ sigma fun (i : I) => C i :=
  desc fun (j : J) => incl (g j)

@[simp] theorem map_obj {I : Type w₁} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₂} (g : J → I) (j : J) (X : C (g j)) : functor.obj (map C g) (sigma.mk j X) = sigma.mk (g j) X :=
  rfl

@[simp] theorem map_map {I : Type w₁} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₂} (g : J → I) {j : J} {X : C (g j)} {Y : C (g j)} (f : X ⟶ Y) : functor.map (map C g) (sigma_hom.mk f) = sigma_hom.mk f :=
  rfl

/--
The functor `sigma.map C g` restricted to the subcategory `C j` acts as the inclusion of `g j`.
-/
@[simp] theorem incl_comp_map_hom_app {I : Type w₁} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₂} (g : J → I) (j : J) (X : C (g j)) : nat_trans.app (iso.hom (incl_comp_map C g j)) X = 𝟙 :=
  Eq.refl 𝟙

/-- The functor `sigma.map` applied to the identity function is just the identity functor. -/
@[simp] theorem map_id_hom_app (I : Type w₁) (C : I → Type u₁) [(i : I) → category (C i)] (_x : sigma fun (i : I) => (fun (i : I) => (fun (i : I) => C (id i)) i) i) : nat_trans.app (iso.hom (map_id I C)) _x =
  nat_trans._match_1
    (fun (i : I) => iso.hom (nat_iso.of_components (fun (X : C i) => iso.refl (sigma.mk i X)) (map_id._proof_1 I C i)))
    _x := sorry

/-- The functor `sigma.map` applied to a composition is a composition of functors. -/
@[simp] theorem map_comp_hom_app {I : Type w₁} (C : I → Type u₁) [(i : I) → category (C i)] {J : Type w₂} {K : Type w₃} (f : K → J) (g : J → I) (X : sigma fun (i : K) => (fun (j : K) => function.comp C g (f j)) i) : nat_trans.app (iso.hom (map_comp C f g)) X =
  iso.hom
    (desc_uniq._match_1 (fun (j : K) => incl (g (f j))) (map (C ∘ g) f ⋙ map C g)
      (fun (k : K) => iso_whisker_right (incl_comp_map (C ∘ g) f k) (map C g) ≪≫ incl_comp_map C g (f k)) X) := sorry

namespace functor


/--
Assemble an `I`-indexed family of functors into a functor between the sigma types.
-/
def sigma {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : I → Type u₁} [(i : I) → category (D i)] (F : (i : I) → C i ⥤ D i) : (sigma fun (i : I) => C i) ⥤ sigma fun (i : I) => D i :=
  desc fun (i : I) => F i ⋙ incl i

end functor


namespace nat_trans


/--
Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
def sigma {I : Type w₁} {C : I → Type u₁} [(i : I) → category (C i)] {D : I → Type u₁} [(i : I) → category (D i)] {F : (i : I) → C i ⥤ D i} {G : (i : I) → C i ⥤ D i} (α : (i : I) → F i ⟶ G i) : functor.sigma F ⟶ functor.sigma G :=
  nat_trans.mk fun (f : sigma fun (i : I) => C i) => sigma_hom.mk (nat_trans.app (α (sigma.fst f)) (sigma.snd f))

