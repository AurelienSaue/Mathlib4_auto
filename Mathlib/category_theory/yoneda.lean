/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.hom_functor
import Mathlib.PostPort

universes u₁ v₁ l 

namespace Mathlib

/-!
# The Yoneda embedding

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `fully_faithful`.

Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

namespace category_theory


/--
The Yoneda embedding, as a functor from `C` into presheaves on `C`.

See https://stacks.math.columbia.edu/tag/001O.
-/
def yoneda {C : Type u₁} [category C] : C ⥤ Cᵒᵖ ⥤ Type v₁ :=
  functor.mk
    (fun (X : C) =>
      functor.mk (fun (Y : Cᵒᵖ) => opposite.unop Y ⟶ X)
        fun (Y Y' : Cᵒᵖ) (f : Y ⟶ Y') (g : opposite.unop Y ⟶ X) => has_hom.hom.unop f ≫ g)
    fun (X X' : C) (f : X ⟶ X') =>
      nat_trans.mk
        fun (Y : Cᵒᵖ)
          (g :
          functor.obj
            (functor.mk (fun (Y : Cᵒᵖ) => opposite.unop Y ⟶ X)
              fun (Y Y' : Cᵒᵖ) (f : Y ⟶ Y') (g : opposite.unop Y ⟶ X) => has_hom.hom.unop f ≫ g)
            Y) =>
          g ≫ f

/--
The co-Yoneda embedding, as a functor from `Cᵒᵖ` into co-presheaves on `C`.
-/
@[simp] theorem coyoneda_obj_map {C : Type u₁} [category C] (X : Cᵒᵖ) (Y : C) (Y' : C) (f : Y ⟶ Y') (g : opposite.unop X ⟶ Y) : functor.map (functor.obj coyoneda X) f g = g ≫ f :=
  Eq.refl (functor.map (functor.obj coyoneda X) f g)

namespace yoneda


theorem obj_map_id {C : Type u₁} [category C] {X : C} {Y : C} (f : opposite.op X ⟶ opposite.op Y) : functor.map (functor.obj yoneda X) f 𝟙 = nat_trans.app (functor.map yoneda (has_hom.hom.unop f)) (opposite.op Y) 𝟙 := sorry

@[simp] theorem naturality {C : Type u₁} [category C] {X : C} {Y : C} (α : functor.obj yoneda X ⟶ functor.obj yoneda Y) {Z : C} {Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : f ≫ nat_trans.app α (opposite.op Z') h = nat_trans.app α (opposite.op Z) (f ≫ h) :=
  Eq.symm (functor_to_types.naturality (functor.obj yoneda X) (functor.obj yoneda Y) α (has_hom.hom.op f) h)

/--
The Yoneda embedding is full.

See https://stacks.math.columbia.edu/tag/001P.
-/
protected instance yoneda_full {C : Type u₁} [category C] : full yoneda :=
  full.mk fun (X Y : C) (f : functor.obj yoneda X ⟶ functor.obj yoneda Y) => nat_trans.app f (opposite.op X) 𝟙

/--
The Yoneda embedding is faithful.

See https://stacks.math.columbia.edu/tag/001P.
-/
protected instance yoneda_faithful {C : Type u₁} [category C] : faithful yoneda :=
  faithful.mk

/-- Extensionality via Yoneda. The typical usage would be
```
-- Goal is `X ≅ Y`

-- Goal is `X ≅ Y`
apply yoneda.ext,
-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these

-- Goals are now functions `(Z ⟶ X) → (Z ⟶ Y)`, `(Z ⟶ Y) → (Z ⟶ X)`, and the fact that these
functions are inverses and natural in `Z`.
```
-/
def ext {C : Type u₁} [category C] (X : C) (Y : C) (p : {Z : C} → (Z ⟶ X) → (Z ⟶ Y)) (q : {Z : C} → (Z ⟶ Y) → (Z ⟶ X)) (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f) (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  preimage_iso (nat_iso.of_components (fun (Z : Cᵒᵖ) => iso.mk p q) sorry)

/--
If `yoneda.map f` is an isomorphism, so was `f`.
-/
def is_iso {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) [is_iso (functor.map yoneda f)] : is_iso f :=
  is_iso_of_fully_faithful yoneda f

end yoneda


namespace coyoneda


@[simp] theorem naturality {C : Type u₁} [category C] {X : Cᵒᵖ} {Y : Cᵒᵖ} (α : functor.obj coyoneda X ⟶ functor.obj coyoneda Y) {Z : C} {Z' : C} (f : Z' ⟶ Z) (h : opposite.unop X ⟶ Z') : nat_trans.app α Z' h ≫ f = nat_trans.app α Z (h ≫ f) := sorry

protected instance coyoneda_full {C : Type u₁} [category C] : full coyoneda :=
  full.mk
    fun (X Y : Cᵒᵖ) (f : functor.obj coyoneda X ⟶ functor.obj coyoneda Y) =>
      has_hom.hom.op (nat_trans.app f (opposite.unop X) 𝟙)

protected instance coyoneda_faithful {C : Type u₁} [category C] : faithful coyoneda :=
  faithful.mk

/--
If `coyoneda.map f` is an isomorphism, so was `f`.
-/
def is_iso {C : Type u₁} [category C] {X : Cᵒᵖ} {Y : Cᵒᵖ} (f : X ⟶ Y) [is_iso (functor.map coyoneda f)] : is_iso f :=
  is_iso_of_fully_faithful coyoneda f

-- No need to use Cᵒᵖ here, works with any category

/-- A Type-valued presheaf `P` is isomorphic to the composition of `P` with the
  coyoneda functor coming from `punit`. -/
@[simp] theorem iso_comp_punit_inv_app {C : Type u₁} [category C] (P : C ⥤ Type v₁) (X : C) (a : functor.obj P X) (_x : opposite.unop (opposite.op PUnit)) : nat_trans.app (iso.inv (iso_comp_punit P)) X a _x = a :=
  Eq.refl (nat_trans.app (iso.inv (iso_comp_punit P)) X a _x)

end coyoneda


/--
A presheaf `F` is representable if there is object `X` so `F ≅ yoneda.obj X`.

See https://stacks.math.columbia.edu/tag/001Q.
-/
-- TODO should we make this a Prop, merely asserting existence of such an object?

class representable {C : Type u₁} [category C] (F : Cᵒᵖ ⥤ Type v₁) 
where
  X : C
  w : functor.obj yoneda X ≅ F

end category_theory


namespace category_theory


-- For the rest of the file, we are using product categories,

-- so need to restrict to the case morphisms are in 'Type', not 'Sort'.

-- We need to help typeclass inference with some awkward universe levels here.

protected instance prod_category_instance_1 (C : Type u₁) [category C] : category ((Cᵒᵖ ⥤ Type v₁) × (Cᵒᵖ)) :=
  category_theory.prod (Cᵒᵖ ⥤ Type v₁) (Cᵒᵖ)

protected instance prod_category_instance_2 (C : Type u₁) [category C] : category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  category_theory.prod (Cᵒᵖ) (Cᵒᵖ ⥤ Type v₁)

/--
The "Yoneda evaluation" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `F.obj X`, functorially in both `X` and `F`.
-/
def yoneda_evaluation (C : Type u₁) [category C] : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  evaluation_uncurried (Cᵒᵖ) (Type v₁) ⋙ ulift_functor

@[simp] theorem yoneda_evaluation_map_down (C : Type u₁) [category C] (P : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (x : functor.obj (yoneda_evaluation C) P) : ulift.down (functor.map (yoneda_evaluation C) α x) =
  nat_trans.app (prod.snd α) (prod.fst Q) (functor.map (prod.snd P) (prod.fst α) (ulift.down x)) :=
  rfl

/--
The "Yoneda pairing" functor, which sends `X : Cᵒᵖ` and `F : Cᵒᵖ ⥤ Type`
to `yoneda.op.obj X ⟶ F`, functorially in both `X` and `F`.
-/
def yoneda_pairing (C : Type u₁) [category C] : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type (max u₁ v₁) :=
  functor.prod (functor.op yoneda) 𝟭 ⋙ functor.hom (Cᵒᵖ ⥤ Type v₁)

@[simp] theorem yoneda_pairing_map (C : Type u₁) [category C] (P : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : functor.obj (yoneda_pairing C) P) : functor.map (yoneda_pairing C) α β = functor.map yoneda (has_hom.hom.unop (prod.fst α)) ≫ β ≫ prod.snd α :=
  rfl

/--
The Yoneda lemma asserts that that the Yoneda pairing
`(X : Cᵒᵖ, F : Cᵒᵖ ⥤ Type) ↦ (yoneda.obj (unop X) ⟶ F)`
is naturally isomorphic to the evaluation `(X, F) ↦ F.obj X`.

See https://stacks.math.columbia.edu/tag/001P.
-/
def yoneda_lemma (C : Type u₁) [category C] : yoneda_pairing C ≅ yoneda_evaluation C :=
  iso.mk
    (nat_trans.mk
      fun (F : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (x : functor.obj (yoneda_pairing C) F) => ulift.up (nat_trans.app x (prod.fst F) 𝟙))
    (nat_trans.mk
      fun (F : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (x : functor.obj (yoneda_evaluation C) F) =>
        nat_trans.mk
          fun (X : Cᵒᵖ)
            (a : functor.obj (opposite.unop (prod.fst (functor.obj (functor.prod (functor.op yoneda) 𝟭) F))) X) =>
            functor.map (prod.snd F) (has_hom.hom.op a) (ulift.down x))

/--
The isomorphism between `yoneda.obj X ⟶ F` and `F.obj (op X)`
(we need to insert a `ulift` to get the universes right!)
given by the Yoneda lemma.
-/
@[simp] def yoneda_sections {C : Type u₁} [category C] (X : C) (F : Cᵒᵖ ⥤ Type v₁) : (functor.obj yoneda X ⟶ F) ≅ ulift (functor.obj F (opposite.op X)) :=
  iso.app (yoneda_lemma C) (opposite.op X, F)

/--
We have a type-level equivalence between natural transformations from the yoneda embedding
and elements of `F.obj X`, without any universe switching.
-/
def yoneda_equiv {C : Type u₁} [category C] {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (functor.obj yoneda X ⟶ F) ≃ functor.obj F (opposite.op X) :=
  equiv.trans (iso.to_equiv (yoneda_sections X F)) equiv.ulift

theorem yoneda_equiv_naturality {C : Type u₁} [category C] {X : C} {Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : functor.obj yoneda X ⟶ F) (g : Y ⟶ X) : functor.map F (has_hom.hom.op g) (coe_fn yoneda_equiv f) = coe_fn yoneda_equiv (functor.map yoneda g ≫ f) := sorry

@[simp] theorem yoneda_equiv_apply {C : Type u₁} [category C] {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : functor.obj yoneda X ⟶ F) : coe_fn yoneda_equiv f = nat_trans.app f (opposite.op X) 𝟙 :=
  rfl

@[simp] theorem yoneda_equiv_symm_app_apply {C : Type u₁} [category C] {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : functor.obj F (opposite.op X)) (Y : Cᵒᵖ) (f : opposite.unop Y ⟶ X) : nat_trans.app (coe_fn (equiv.symm yoneda_equiv) x) Y f = functor.map F (has_hom.hom.op f) x :=
  rfl

/--
When `C` is a small category, we can restate the isomorphism from `yoneda_sections`
without having to change universes.
-/
def yoneda_sections_small {C : Type u₁} [small_category C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) : (functor.obj yoneda X ⟶ F) ≅ functor.obj F (opposite.op X) :=
  yoneda_sections X F ≪≫ ulift_trivial (functor.obj F (opposite.op X))

@[simp] theorem yoneda_sections_small_hom {C : Type u₁} [small_category C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) (f : functor.obj yoneda X ⟶ F) : iso.hom (yoneda_sections_small X F) f = nat_trans.app f (opposite.op X) 𝟙 :=
  rfl

@[simp] theorem yoneda_sections_small_inv_app_apply {C : Type u₁} [small_category C] (X : C) (F : Cᵒᵖ ⥤ Type u₁) (t : functor.obj F (opposite.op X)) (Y : Cᵒᵖ) (f : opposite.unop Y ⟶ X) : nat_trans.app (iso.inv (yoneda_sections_small X F) t) Y f = functor.map F (has_hom.hom.op f) t :=
  rfl

