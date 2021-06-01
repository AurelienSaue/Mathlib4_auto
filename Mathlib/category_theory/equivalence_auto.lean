/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.fully_faithful
import Mathlib.category_theory.whiskering
import Mathlib.category_theory.essential_image
import Mathlib.tactic.slice
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l u₃ v₃ 

namespace Mathlib

/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphims of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `equivalence`: bundled (half-)adjoint equivalences of categories
* `is_equivalence`: type class on a functor `F` containing the data of the inverse `G` as well as
  the natural isomorphisms `η` and `ε`.
* `ess_surj`: type class on a functor `F` containing the data of the preimages and the isomorphisms
  `F.obj (preimage d) ≅ d`.

## Main results

* `equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `equivalence_of_fully_faithfully_ess_surj`: a fully faithful essentially surjective functor is an
  equivalence.

## Notations

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

namespace category_theory


/-- We define an equivalence as a (half)-adjoint equivalence, a pair of functors with
  a unit and counit which are natural isomorphisms and the triangle law `Fη ≫ εF = 1`, or in other
  words the composite `F ⟶ FGF ⟶ F` is the identity.

  In `unit_inverse_comp`, we show that this is actually an adjoint equivalence, i.e., that the
  composite `G ⟶ GFG ⟶ G` is also the identity.

  The triangle equation is written as a family of equalities between morphisms, it is more
  complicated if we write it as an equality of natural transformations, because then we would have
  to insert natural transformations like `F ⟶ F1`.

See https://stacks.math.columbia.edu/tag/001J
-/
structure equivalence (C : Type u₁) [category C] (D : Type u₂) [category D] where
  mk' ::
    (functor : C ⥤ D)
    (inverse : D ⥤ C)
    (unit_iso : 𝟭 ≅ functor ⋙ inverse)
    (counit_iso : inverse ⋙ functor ≅ 𝟭)
    (functor_unit_iso_comp' :
      autoParam
        (∀ (X : C),
          functor.map functor (nat_trans.app (iso.hom unit_iso) X) ≫
              nat_trans.app (iso.hom counit_iso) (functor.obj functor X) =
            𝟙)
        (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
          (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") []))

theorem equivalence.functor_unit_iso_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    (c : equivalence C D) (X : C) :
    functor.map (equivalence.functor c) (nat_trans.app (iso.hom (equivalence.unit_iso c)) X) ≫
          nat_trans.app (iso.hom (equivalence.counit_iso c))
            (functor.obj (equivalence.functor c) X) =
        𝟙 :=
  sorry

infixr:10 " ≌ " => Mathlib.category_theory.equivalence

namespace equivalence


/-- The unit of an equivalence of categories. -/
/-- The counit of an equivalence of categories. -/
def unit {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) :
    𝟭 ⟶ functor e ⋙ inverse e :=
  iso.hom (unit_iso e)

/-- The inverse of the unit of an equivalence of categories. -/
def counit {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) :
    inverse e ⋙ functor e ⟶ 𝟭 :=
  iso.hom (counit_iso e)

/-- The inverse of the counit of an equivalence of categories. -/
def unit_inv {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) :
    functor e ⋙ inverse e ⟶ 𝟭 :=
  iso.inv (unit_iso e)

def counit_inv {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) :
    𝟭 ⟶ inverse e ⋙ functor e :=
  iso.inv (counit_iso e)

/- While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/

@[simp] theorem equivalence_mk'_unit {C : Type u₁} [category C] {D : Type u₂} [category D]
    (functor : C ⥤ D) (inverse : D ⥤ C) (unit_iso : 𝟭 ≅ functor ⋙ inverse)
    (counit_iso : inverse ⋙ functor ≅ 𝟭)
    (f :
      autoParam
        (∀ (X : C),
          functor.map functor (nat_trans.app (iso.hom unit_iso) X) ≫
              nat_trans.app (iso.hom counit_iso) (functor.obj functor X) =
            𝟙)
        (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
          (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) :
    unit (mk' functor inverse unit_iso counit_iso) = iso.hom unit_iso :=
  rfl

@[simp] theorem equivalence_mk'_counit {C : Type u₁} [category C] {D : Type u₂} [category D]
    (functor : C ⥤ D) (inverse : D ⥤ C) (unit_iso : 𝟭 ≅ functor ⋙ inverse)
    (counit_iso : inverse ⋙ functor ≅ 𝟭)
    (f :
      autoParam
        (∀ (X : C),
          functor.map functor (nat_trans.app (iso.hom unit_iso) X) ≫
              nat_trans.app (iso.hom counit_iso) (functor.obj functor X) =
            𝟙)
        (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
          (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) :
    counit (mk' functor inverse unit_iso counit_iso) = iso.hom counit_iso :=
  rfl

@[simp] theorem equivalence_mk'_unit_inv {C : Type u₁} [category C] {D : Type u₂} [category D]
    (functor : C ⥤ D) (inverse : D ⥤ C) (unit_iso : 𝟭 ≅ functor ⋙ inverse)
    (counit_iso : inverse ⋙ functor ≅ 𝟭)
    (f :
      autoParam
        (∀ (X : C),
          functor.map functor (nat_trans.app (iso.hom unit_iso) X) ≫
              nat_trans.app (iso.hom counit_iso) (functor.obj functor X) =
            𝟙)
        (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
          (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) :
    unit_inv (mk' functor inverse unit_iso counit_iso) = iso.inv unit_iso :=
  rfl

@[simp] theorem equivalence_mk'_counit_inv {C : Type u₁} [category C] {D : Type u₂} [category D]
    (functor : C ⥤ D) (inverse : D ⥤ C) (unit_iso : 𝟭 ≅ functor ⋙ inverse)
    (counit_iso : inverse ⋙ functor ≅ 𝟭)
    (f :
      autoParam
        (∀ (X : C),
          functor.map functor (nat_trans.app (iso.hom unit_iso) X) ≫
              nat_trans.app (iso.hom counit_iso) (functor.obj functor X) =
            𝟙)
        (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
          (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])) :
    counit_inv (mk' functor inverse unit_iso counit_iso) = iso.inv counit_iso :=
  rfl

@[simp] theorem functor_unit_comp {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (X : C) :
    functor.map (functor e) (nat_trans.app (unit e) X) ≫
          nat_trans.app (counit e) (functor.obj (functor e) X) =
        𝟙 :=
  functor_unit_iso_comp e X

@[simp] theorem counit_inv_functor_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) (X : C) :
    nat_trans.app (counit_inv e) (functor.obj (functor e) X) ≫
          functor.map (functor e) (nat_trans.app (unit_inv e) X) =
        𝟙 :=
  sorry

theorem counit_inv_app_functor {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (X : C) :
    nat_trans.app (counit_inv e) (functor.obj (functor e) X) =
        functor.map (functor e) (nat_trans.app (unit e) X) :=
  sorry

theorem counit_app_functor {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (X : C) :
    nat_trans.app (counit e) (functor.obj (functor e) X) =
        functor.map (functor e) (nat_trans.app (unit_inv e) X) :=
  sorry

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[simp] theorem unit_inverse_comp {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (Y : D) :
    nat_trans.app (unit e) (functor.obj (inverse e) Y) ≫
          functor.map (inverse e) (nat_trans.app (counit e) Y) =
        𝟙 :=
  sorry

@[simp] theorem inverse_counit_inv_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) (Y : D) :
    functor.map (inverse e) (nat_trans.app (counit_inv e) Y) ≫
          nat_trans.app (unit_inv e) (functor.obj (inverse e) Y) =
        𝟙 :=
  sorry

theorem unit_app_inverse {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) (Y : D) :
    nat_trans.app (unit e) (functor.obj (inverse e) Y) =
        functor.map (inverse e) (nat_trans.app (counit_inv e) Y) :=
  sorry

theorem unit_inv_app_inverse {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (Y : D) :
    nat_trans.app (unit_inv e) (functor.obj (inverse e) Y) =
        functor.map (inverse e) (nat_trans.app (counit e) Y) :=
  sorry

@[simp] theorem fun_inv_map {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (X : D) (Y : D) (f : X ⟶ Y) :
    functor.map (functor e) (functor.map (inverse e) f) =
        nat_trans.app (counit e) X ≫ f ≫ nat_trans.app (counit_inv e) Y :=
  Eq.symm (nat_iso.naturality_2 (counit_iso e) f)

@[simp] theorem inv_fun_map {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    (X : C) (Y : C) (f : X ⟶ Y) :
    functor.map (inverse e) (functor.map (functor e) f) =
        nat_trans.app (unit_inv e) X ≫ f ≫ nat_trans.app (unit e) Y :=
  Eq.symm (nat_iso.naturality_1 (unit_iso e) f)

-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.

/-- If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we can upgrade it
to a refined natural isomorphism `adjointify_η η : 𝟭 C ≅ F ⋙ G` which exhibits the properties
required for a half-adjoint equivalence. See `equivalence.mk`. -/
def adjointify_η {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C}
    (η : 𝟭 ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭) : 𝟭 ≅ F ⋙ G :=
  (((((η ≪≫ iso_whisker_left F (iso.symm (functor.left_unitor G))) ≪≫
            iso_whisker_left F (iso_whisker_right (iso.symm ε) G)) ≪≫
          iso_whisker_left F (functor.associator G F G)) ≪≫
        iso.symm (functor.associator F G (F ⋙ G))) ≪≫
      iso_whisker_right (iso.symm η) (F ⋙ G)) ≪≫
    functor.left_unitor (F ⋙ G)

theorem adjointify_η_ε {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} {G : D ⥤ C}
    (η : 𝟭 ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭) (X : C) :
    functor.map F (nat_trans.app (iso.hom (adjointify_η η ε)) X) ≫
          nat_trans.app (iso.hom ε) (functor.obj F X) =
        𝟙 :=
  sorry

/-- Every equivalence of categories consisting of functors `F` and `G` such that `F ⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed into a half-adjoint
    equivalence without changing `F` or `G`. -/
protected def mk {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (G : D ⥤ C)
    (η : 𝟭 ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭) : C ≌ D :=
  mk' F G (adjointify_η η ε) ε

/-- Equivalence of categories is reflexive. -/
@[simp] theorem refl_functor {C : Type u₁} [category C] : functor refl = 𝟭 := Eq.refl (functor refl)

protected instance inhabited {C : Type u₁} [category C] : Inhabited (C ≌ C) := { default := refl }

/-- Equivalence of categories is symmetric. -/
@[simp] theorem symm_counit_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D) :
    counit_iso (symm e) = iso.symm (unit_iso e) :=
  Eq.refl (counit_iso (symm e))

/-- Equivalence of categories is transitive. -/
@[simp] theorem trans_unit_iso {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (e : C ≌ D) (f : D ≌ E) :
    unit_iso (trans e f) =
        unit_iso e ≪≫ iso_whisker_left (functor e) (iso_whisker_right (unit_iso f) (inverse e)) :=
  Eq.refl (unit_iso (trans e f))

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic functor. -/
def fun_inv_id_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (e : C ≌ D) (F : C ⥤ E) : functor e ⋙ inverse e ⋙ F ≅ F :=
  iso.symm (functor.associator (functor e) (inverse e) F) ≪≫
    iso_whisker_right (iso.symm (unit_iso e)) F ≪≫ functor.left_unitor F

@[simp] theorem fun_inv_id_assoc_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (e : C ≌ D) (F : C ⥤ E) (X : C) :
    nat_trans.app (iso.hom (fun_inv_id_assoc e F)) X =
        functor.map F (nat_trans.app (unit_inv e) X) :=
  sorry

@[simp] theorem fun_inv_id_assoc_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (e : C ≌ D) (F : C ⥤ E) (X : C) :
    nat_trans.app (iso.inv (fun_inv_id_assoc e F)) X = functor.map F (nat_trans.app (unit e) X) :=
  sorry

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic functor. -/
def inv_fun_id_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃}
    [category E] (e : C ≌ D) (F : D ⥤ E) : inverse e ⋙ functor e ⋙ F ≅ F :=
  iso.symm (functor.associator (inverse e) (functor e) F) ≪≫
    iso_whisker_right (counit_iso e) F ≪≫ functor.left_unitor F

@[simp] theorem inv_fun_id_assoc_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (e : C ≌ D) (F : D ⥤ E) (X : D) :
    nat_trans.app (iso.hom (inv_fun_id_assoc e F)) X = functor.map F (nat_trans.app (counit e) X) :=
  sorry

@[simp] theorem inv_fun_id_assoc_inv_app {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (e : C ≌ D) (F : D ⥤ E) (X : D) :
    nat_trans.app (iso.inv (inv_fun_id_assoc e F)) X =
        functor.map F (nat_trans.app (counit_inv e) X) :=
  sorry

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simp] theorem congr_left_unit_iso {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (e : C ≌ D) :
    unit_iso (congr_left e) =
        adjointify_η
          (nat_iso.of_components (fun (F : C ⥤ E) => iso.symm (fun_inv_id_assoc e F))
            (congr_left._proof_1 e))
          (nat_iso.of_components (inv_fun_id_assoc e) (congr_left._proof_2 e)) :=
  Eq.refl
    (adjointify_η
      (nat_iso.of_components (fun (F : C ⥤ E) => iso.symm (fun_inv_id_assoc e F))
        (congr_left._proof_1 e))
      (nat_iso.of_components (inv_fun_id_assoc e) (congr_left._proof_2 e)))

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simp] theorem congr_right_functor {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (e : C ≌ D) :
    functor (congr_right e) = functor.obj (whiskering_right E C D) (functor e) :=
  Eq.refl (functor.obj (whiskering_right E C D) (functor e))

-- We need special forms of `cancel_nat_iso_hom_right(_assoc)` and `cancel_nat_iso_inv_right(_assoc)`

-- for units and counits, because neither `simp` or `rw` will apply those lemmas in this

-- setting without providing `e.unit_iso` (or similar) as an explicit argument.

-- We also provide the lemmas for length four compositions, since they're occasionally useful.

-- (e.g. in proving that equivalences take monos to monos)

@[simp] theorem cancel_unit_right {C : Type u₁} [category C] {D : Type u₂} [category D] (e : C ≌ D)
    {X : C} {Y : C} (f : X ⟶ Y) (f' : X ⟶ Y) :
    f ≫ nat_trans.app (unit e) Y = f' ≫ nat_trans.app (unit e) Y ↔ f = f' :=
  sorry

@[simp] theorem cancel_unit_inv_right {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {X : C} {Y : C} (f : X ⟶ functor.obj (inverse e) (functor.obj (functor e) Y))
    (f' : X ⟶ functor.obj (inverse e) (functor.obj (functor e) Y)) :
    f ≫ nat_trans.app (unit_inv e) Y = f' ≫ nat_trans.app (unit_inv e) Y ↔ f = f' :=
  sorry

@[simp] theorem cancel_counit_right {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {X : D} {Y : D} (f : X ⟶ functor.obj (functor e) (functor.obj (inverse e) Y))
    (f' : X ⟶ functor.obj (functor e) (functor.obj (inverse e) Y)) :
    f ≫ nat_trans.app (counit e) Y = f' ≫ nat_trans.app (counit e) Y ↔ f = f' :=
  sorry

@[simp] theorem cancel_counit_inv_right {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {X : D} {Y : D} (f : X ⟶ Y) (f' : X ⟶ Y) :
    f ≫ nat_trans.app (counit_inv e) Y = f' ≫ nat_trans.app (counit_inv e) Y ↔ f = f' :=
  sorry

@[simp] theorem cancel_unit_right_assoc {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {W : C} {X : C} {X' : C} {Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) :
    f ≫ g ≫ nat_trans.app (unit e) Y = f' ≫ g' ≫ nat_trans.app (unit e) Y ↔ f ≫ g = f' ≫ g' :=
  sorry

@[simp] theorem cancel_counit_inv_right_assoc {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {W : D} {X : D} {X' : D} {Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) :
    f ≫ g ≫ nat_trans.app (counit_inv e) Y = f' ≫ g' ≫ nat_trans.app (counit_inv e) Y ↔
        f ≫ g = f' ≫ g' :=
  sorry

@[simp] theorem cancel_unit_right_assoc' {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {W : C} {X : C} {X' : C} {Y : C} {Y' : C} {Z : C} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ nat_trans.app (unit e) Z = f' ≫ g' ≫ h' ≫ nat_trans.app (unit e) Z ↔
        f ≫ g ≫ h = f' ≫ g' ≫ h' :=
  sorry

@[simp] theorem cancel_counit_inv_right_assoc' {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {W : D} {X : D} {X' : D} {Y : D} {Y' : D} {Z : D} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ nat_trans.app (counit_inv e) Z = f' ≫ g' ≫ h' ≫ nat_trans.app (counit_inv e) Z ↔
        f ≫ g ≫ h = f' ≫ g' ≫ h' :=
  sorry

-- There's of course a monoid structure on `C ≌ C`,

-- but let's not encourage using it.

-- The power structure is nevertheless useful.

/-- Powers of an auto-equivalence. -/
def pow {C : Type u₁} [category C] (e : C ≌ C) : ℤ → (C ≌ C) := sorry

protected instance int.has_pow {C : Type u₁} [category C] : has_pow (C ≌ C) ℤ := has_pow.mk pow

@[simp] theorem pow_zero {C : Type u₁} [category C] (e : C ≌ C) : e ^ 0 = refl := rfl

@[simp] theorem pow_one {C : Type u₁} [category C] (e : C ≌ C) : e ^ 1 = e := rfl

@[simp] theorem pow_minus_one {C : Type u₁} [category C] (e : C ≌ C) : e ^ (-1) = symm e := rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.

-- At this point, we haven't even defined the category of equivalences.

end equivalence


/-- A functor that is part of a (half) adjoint equivalence -/
class is_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) where
  mk' ::
    (inverse : D ⥤ C)
    (unit_iso : 𝟭 ≅ F ⋙ inverse)
    (counit_iso : inverse ⋙ F ≅ 𝟭)
    (functor_unit_iso_comp' :
      autoParam
        (∀ (X : C),
          functor.map F (nat_trans.app (iso.hom unit_iso) X) ≫
              nat_trans.app (iso.hom counit_iso) (functor.obj F X) =
            𝟙)
        (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
          (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") []))

theorem is_equivalence.functor_unit_iso_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C ⥤ D} [c : is_equivalence F] (X : C) :
    functor.map F (nat_trans.app (iso.hom is_equivalence.unit_iso) X) ≫
          nat_trans.app (iso.hom is_equivalence.counit_iso) (functor.obj F X) =
        𝟙 :=
  sorry

namespace is_equivalence


protected instance of_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ≌ D) : is_equivalence (equivalence.functor F) :=
  mk' (equivalence.inverse F) (equivalence.unit_iso F) (equivalence.counit_iso F)

protected instance of_equivalence_inverse {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ≌ D) : is_equivalence (equivalence.inverse F) :=
  is_equivalence.of_equivalence (equivalence.symm F)

/-- To see that a functor is an equivalence, it suffices to provide an inverse functor `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors. -/
protected def mk {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C ⥤ D} (G : D ⥤ C)
    (η : 𝟭 ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭) : is_equivalence F :=
  mk' G (equivalence.adjointify_η η ε) ε

end is_equivalence


namespace functor


/-- Interpret a functor that is an equivalence as an equivalence. -/
def as_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] : C ≌ D :=
  equivalence.mk' F (is_equivalence.inverse F) is_equivalence.unit_iso is_equivalence.counit_iso

protected instance is_equivalence_refl {C : Type u₁} [category C] : is_equivalence 𝟭 :=
  is_equivalence.of_equivalence equivalence.refl

/-- The inverse functor of a functor that is an equivalence. -/
def inv {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) [is_equivalence F] :
    D ⥤ C :=
  is_equivalence.inverse F

protected instance is_equivalence_inv {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [is_equivalence F] : is_equivalence (inv F) :=
  is_equivalence.of_equivalence (equivalence.symm (as_equivalence F))

@[simp] theorem as_equivalence_functor {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [is_equivalence F] : equivalence.functor (as_equivalence F) = F :=
  rfl

@[simp] theorem as_equivalence_inverse {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [is_equivalence F] : equivalence.inverse (as_equivalence F) = inv F :=
  rfl

@[simp] theorem inv_inv {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] : inv (inv F) = F :=
  rfl

/-- The composition of functor that is an equivalence with its inverse is naturally isomorphic to
    the identity functor. -/
def fun_inv_id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] : F ⋙ inv F ≅ 𝟭 :=
  iso.symm is_equivalence.unit_iso

/-- The composition of functor that is an equivalence with its inverse is naturally isomorphic to
    the identity functor. -/
def inv_fun_id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] : inv F ⋙ F ≅ 𝟭 :=
  is_equivalence.counit_iso

protected instance is_equivalence_trans {C : Type u₁} [category C] {D : Type u₂} [category D]
    {E : Type u₃} [category E] (F : C ⥤ D) (G : D ⥤ E) [is_equivalence F] [is_equivalence G] :
    is_equivalence (F ⋙ G) :=
  is_equivalence.of_equivalence (equivalence.trans (as_equivalence F) (as_equivalence G))

end functor


namespace equivalence


@[simp] theorem functor_inv {C : Type u₁} [category C] {D : Type u₂} [category D] (E : C ≌ D) :
    functor.inv (functor E) = inverse E :=
  rfl

@[simp] theorem inverse_inv {C : Type u₁} [category C] {D : Type u₂} [category D] (E : C ≌ D) :
    functor.inv (inverse E) = functor E :=
  rfl

@[simp] theorem functor_as_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    (E : C ≌ D) : functor.as_equivalence (functor E) = E :=
  sorry

@[simp] theorem inverse_as_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    (E : C ≌ D) : functor.as_equivalence (inverse E) = symm E :=
  sorry

end equivalence


namespace is_equivalence


@[simp] theorem fun_inv_map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] (X : D) (Y : D) (f : X ⟶ Y) :
    functor.map F (functor.map (functor.inv F) f) =
        nat_trans.app (iso.hom (functor.inv_fun_id F)) X ≫
          f ≫ nat_trans.app (iso.inv (functor.inv_fun_id F)) Y :=
  sorry

@[simp] theorem inv_fun_map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] (X : C) (Y : C) (f : X ⟶ Y) :
    functor.map (functor.inv F) (functor.map F f) =
        nat_trans.app (iso.hom (functor.fun_inv_id F)) X ≫
          f ≫ nat_trans.app (iso.inv (functor.fun_inv_id F)) Y :=
  sorry

-- We should probably restate many of the lemmas about `equivalence` for `is_equivalence`,

-- but these are the only ones I need for now.

@[simp] theorem functor_unit_comp {C : Type u₁} [category C] {D : Type u₂} [category D] (E : C ⥤ D)
    [is_equivalence E] (Y : C) :
    functor.map E (nat_trans.app (iso.inv (functor.fun_inv_id E)) Y) ≫
          nat_trans.app (iso.hom (functor.inv_fun_id E)) (functor.obj E Y) =
        𝟙 :=
  equivalence.functor_unit_comp (functor.as_equivalence E) Y

@[simp] theorem inv_fun_id_inv_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    (E : C ⥤ D) [is_equivalence E] (Y : C) :
    nat_trans.app (iso.inv (functor.inv_fun_id E)) (functor.obj E Y) ≫
          functor.map E (nat_trans.app (iso.hom (functor.fun_inv_id E)) Y) =
        𝟙 :=
  eq_of_inv_eq_inv (functor_unit_comp E Y)

end is_equivalence


namespace equivalence


/--
An equivalence is essentially surjective.

See https://stacks.math.columbia.edu/tag/02C3.
-/
theorem ess_surj_of_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [is_equivalence F] : ess_surj F :=
  ess_surj.mk
    fun (Y : D) =>
      Exists.intro (functor.obj (functor.inv F) Y)
        (Nonempty.intro (iso.app (functor.inv_fun_id F) Y))

/--
An equivalence is faithful.

See https://stacks.math.columbia.edu/tag/02C3.
-/
protected instance faithful_of_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [is_equivalence F] : faithful F :=
  faithful.mk

/--
An equivalence is full.

See https://stacks.math.columbia.edu/tag/02C3.
-/
protected instance full_of_equivalence {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [is_equivalence F] : full F :=
  full.mk
    fun (X Y : C) (f : functor.obj F X ⟶ functor.obj F Y) =>
      nat_trans.app (iso.inv (functor.fun_inv_id F)) X ≫
        functor.map (functor.inv F) f ≫ nat_trans.app (iso.hom (functor.fun_inv_id F)) Y

/--
A functor which is full, faithful, and essentially surjective is an equivalence.

See https://stacks.math.columbia.edu/tag/02C3.
-/
def equivalence_of_fully_faithfully_ess_surj {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) [full F] [faithful F] [ess_surj F] : is_equivalence F :=
  is_equivalence.mk (equivalence_inverse F)
    (nat_iso.of_components
      (fun (X : C) => iso.symm (preimage_iso (functor.obj_obj_preimage_iso F (functor.obj F X))))
      sorry)
    (nat_iso.of_components (functor.obj_obj_preimage_iso F) sorry)

@[simp] theorem functor_map_inj_iff {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) :
    functor.map (functor e) f = functor.map (functor e) g ↔ f = g :=
  { mp :=
      fun (h : functor.map (functor e) f = functor.map (functor e) g) =>
        functor.map_injective (functor e) h,
    mpr := fun (h : f = g) => h ▸ rfl }

@[simp] theorem inverse_map_inj_iff {C : Type u₁} [category C] {D : Type u₂} [category D]
    (e : C ≌ D) {X : D} {Y : D} (f : X ⟶ Y) (g : X ⟶ Y) :
    functor.map (inverse e) f = functor.map (inverse e) g ↔ f = g :=
  functor_map_inj_iff (symm e) f g

end Mathlib