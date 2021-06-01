/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.products.basic
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Monoidal categories

A monoidal category is a category equipped with a tensor product, unitors, and an associator.
In the definition, we provide the tensor product as a pair of functions
* `tensor_obj : C → C → C`
* `tensor_hom : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → ((X₁ ⊗ X₂) ⟶ (Y₁ ⊗ Y₂))`
and allow use of the overloaded notation `⊗` for both.
The unitors and associator are provided componentwise.

The tensor product can be expressed as a functor via `tensor : C × C ⥤ C`.
The unitors and associator are gathered together as natural
isomorphisms in `left_unitor_nat_iso`, `right_unitor_nat_iso` and `associator_nat_iso`.

Some consequences of the definition are proved in other files,
e.g. `(λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom` in `category_theory.monoidal.unitors_equal`.

## Implementation
Dealing with unitors and associators is painful, and at this stage we do not have a useful
implementation of coherence for monoidal categories.

In an effort to lessen the pain, we put some effort into choosing the right `simp` lemmas.
Generally, the rule is that the component index of a natural transformation "weighs more"
in considering the complexity of an expression than does a structural isomorphism (associator, etc).

As an example when we prove Proposition 2.2.4 of
<http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
we state it as a `@[simp]` lemma as
```
(λ_ (X ⊗ Y)).hom = (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ⊗ (𝟙 Y)
```

This is far from completely effective, but seems to prove a useful principle.

## References
* Tensor categories, Etingof, Gelaki, Nikshych, Ostrik,
  http://www-math.mit.edu/~etingof/egnobookfinal.pdf
* https://stacks.math.columbia.edu/tag/0FFK.
-/

namespace category_theory


/--
In a monoidal category, we can take the tensor product of objects, `X ⊗ Y` and of morphisms `f ⊗ g`.
Tensor product does not need to be strictly associative on objects, but there is a
specified associator, `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. There is a tensor unit `𝟙_ C`,
with specified left and right unitor isomorphisms `λ_ X : 𝟙_ C ⊗ X ≅ X` and `ρ_ X : X ⊗ 𝟙_ C ≅ X`.
These associators and unitors satisfy the pentagon and triangle equations.

See https://stacks.math.columbia.edu/tag/0FFK.
-/
-- curried tensor product of objects:

class monoidal_category (C : Type u) [𝒞 : category C] where
  tensor_obj : C → C → C
  tensor_hom : {X₁ Y₁ X₂ Y₂ : C} → (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (tensor_obj X₁ X₂ ⟶ tensor_obj Y₁ Y₂)
  tensor_id' :
    autoParam (C → C → tensor_hom 𝟙 𝟙 = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  tensor_comp' :
    autoParam
      (∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
        tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom f₁ f₂ ≫ tensor_hom g₁ g₂)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  tensor_unit : C
  associator : (X Y Z : C) → tensor_obj (tensor_obj X Y) Z ≅ tensor_obj X (tensor_obj Y Z)
  associator_naturality' :
    autoParam
      (∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃),
        tensor_hom (tensor_hom f₁ f₂) f₃ ≫ iso.hom (associator Y₁ Y₂ Y₃) =
          iso.hom (associator X₁ X₂ X₃) ≫ tensor_hom f₁ (tensor_hom f₂ f₃))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  left_unitor : (X : C) → tensor_obj tensor_unit X ≅ X
  left_unitor_naturality' :
    autoParam
      (∀ {X Y : C} (f : X ⟶ Y),
        tensor_hom 𝟙 f ≫ iso.hom (left_unitor Y) = iso.hom (left_unitor X) ≫ f)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right_unitor : (X : C) → tensor_obj X tensor_unit ≅ X
  right_unitor_naturality' :
    autoParam
      (∀ {X Y : C} (f : X ⟶ Y),
        tensor_hom f 𝟙 ≫ iso.hom (right_unitor Y) = iso.hom (right_unitor X) ≫ f)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  pentagon' :
    autoParam
      (∀ (W X Y Z : C),
        tensor_hom (iso.hom (associator W X Y)) 𝟙 ≫
            iso.hom (associator W (tensor_obj X Y) Z) ≫ tensor_hom 𝟙 (iso.hom (associator X Y Z)) =
          iso.hom (associator (tensor_obj W X) Y Z) ≫ iso.hom (associator W X (tensor_obj Y Z)))
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  triangle' :
    autoParam
      (∀ (X Y : C),
        iso.hom (associator X tensor_unit Y) ≫ tensor_hom 𝟙 (iso.hom (left_unitor Y)) =
          tensor_hom (iso.hom (right_unitor X)) 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- curried tensor product of morphisms:

-- tensor product laws:

-- tensor unit:

-- associator:

-- left unitor:

-- right unitor:

-- pentagon identity:

-- triangle identity:

@[simp] theorem monoidal_category.tensor_id {C : Type u} [𝒞 : category C] [c : monoidal_category C]
    (X₁ : C) (X₂ : C) : monoidal_category.tensor_hom 𝟙 𝟙 = 𝟙 :=
  sorry

@[simp] theorem monoidal_category.tensor_comp {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X₁ : C} {Y₁ : C} {Z₁ : C} {X₂ : C} {Y₂ : C} {Z₂ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    monoidal_category.tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) =
        monoidal_category.tensor_hom f₁ f₂ ≫ monoidal_category.tensor_hom g₁ g₂ :=
  sorry

theorem monoidal_category.tensor_comp_assoc {C : Type u} [𝒞 : category C] [c : monoidal_category C]
    {X₁ : C} {Y₁ : C} {Z₁ : C} {X₂ : C} {Y₂ : C} {Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) {X' : C} (f' : monoidal_category.tensor_obj Z₁ Z₂ ⟶ X') :
    monoidal_category.tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) ≫ f' =
        monoidal_category.tensor_hom f₁ f₂ ≫ monoidal_category.tensor_hom g₁ g₂ ≫ f' :=
  sorry

theorem monoidal_category.associator_naturality {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X₁ : C} {X₂ : C} {X₃ : C} {Y₁ : C} {Y₂ : C} {Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    monoidal_category.tensor_hom (monoidal_category.tensor_hom f₁ f₂) f₃ ≫
          iso.hom (monoidal_category.associator Y₁ Y₂ Y₃) =
        iso.hom (monoidal_category.associator X₁ X₂ X₃) ≫
          monoidal_category.tensor_hom f₁ (monoidal_category.tensor_hom f₂ f₃) :=
  sorry

theorem monoidal_category.associator_naturality_assoc {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X₁ : C} {X₂ : C} {X₃ : C} {Y₁ : C} {Y₂ : C} {Y₃ : C} (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) {X' : C}
    (f' : monoidal_category.tensor_obj Y₁ (monoidal_category.tensor_obj Y₂ Y₃) ⟶ X') :
    monoidal_category.tensor_hom (monoidal_category.tensor_hom f₁ f₂) f₃ ≫
          iso.hom (monoidal_category.associator Y₁ Y₂ Y₃) ≫ f' =
        iso.hom (monoidal_category.associator X₁ X₂ X₃) ≫
          monoidal_category.tensor_hom f₁ (monoidal_category.tensor_hom f₂ f₃) ≫ f' :=
  sorry

theorem monoidal_category.left_unitor_naturality {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X : C} {Y : C} (f : X ⟶ Y) :
    monoidal_category.tensor_hom 𝟙 f ≫ iso.hom (monoidal_category.left_unitor Y) =
        iso.hom (monoidal_category.left_unitor X) ≫ f :=
  sorry

theorem monoidal_category.left_unitor_naturality_assoc {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X : C} {Y : C} (f : X ⟶ Y) {X' : C} (f' : Y ⟶ X') :
    monoidal_category.tensor_hom 𝟙 f ≫ iso.hom (monoidal_category.left_unitor Y) ≫ f' =
        iso.hom (monoidal_category.left_unitor X) ≫ f ≫ f' :=
  sorry

theorem monoidal_category.right_unitor_naturality {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X : C} {Y : C} (f : X ⟶ Y) :
    monoidal_category.tensor_hom f 𝟙 ≫ iso.hom (monoidal_category.right_unitor Y) =
        iso.hom (monoidal_category.right_unitor X) ≫ f :=
  sorry

theorem monoidal_category.right_unitor_naturality_assoc {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] {X : C} {Y : C} (f : X ⟶ Y) {X' : C} (f' : Y ⟶ X') :
    monoidal_category.tensor_hom f 𝟙 ≫ iso.hom (monoidal_category.right_unitor Y) ≫ f' =
        iso.hom (monoidal_category.right_unitor X) ≫ f ≫ f' :=
  sorry

theorem monoidal_category.pentagon {C : Type u} [𝒞 : category C] [c : monoidal_category C] (W : C)
    (X : C) (Y : C) (Z : C) :
    monoidal_category.tensor_hom (iso.hom (monoidal_category.associator W X Y)) 𝟙 ≫
          iso.hom (monoidal_category.associator W (monoidal_category.tensor_obj X Y) Z) ≫
            monoidal_category.tensor_hom 𝟙 (iso.hom (monoidal_category.associator X Y Z)) =
        iso.hom (monoidal_category.associator (monoidal_category.tensor_obj W X) Y Z) ≫
          iso.hom (monoidal_category.associator W X (monoidal_category.tensor_obj Y Z)) :=
  sorry

@[simp] theorem monoidal_category.triangle {C : Type u} [𝒞 : category C] [c : monoidal_category C]
    (X : C) (Y : C) :
    iso.hom (monoidal_category.associator X (monoidal_category.tensor_unit C) Y) ≫
          monoidal_category.tensor_hom 𝟙 (iso.hom (monoidal_category.left_unitor Y)) =
        monoidal_category.tensor_hom (iso.hom (monoidal_category.right_unitor X)) 𝟙 :=
  sorry

@[simp] theorem monoidal_category.triangle_assoc {C : Type u} [𝒞 : category C]
    [c : monoidal_category C] (X : C) (Y : C) {X' : C}
    (f' : monoidal_category.tensor_obj X Y ⟶ X') :
    iso.hom (monoidal_category.associator X (monoidal_category.tensor_unit C) Y) ≫
          monoidal_category.tensor_hom 𝟙 (iso.hom (monoidal_category.left_unitor Y)) ≫ f' =
        monoidal_category.tensor_hom (iso.hom (monoidal_category.right_unitor X)) 𝟙 ≫ f' :=
  sorry

infixr:70 " ⊗ " => Mathlib.category_theory.monoidal_category.tensor_obj

infixr:70 " ⊗ " => Mathlib.category_theory.monoidal_category.tensor_hom

notation:1024 "𝟙_" => Mathlib.category_theory.monoidal_category.tensor_unit

notation:1024 "α_" => Mathlib.category_theory.monoidal_category.associator

notation:1024 "λ_" => Mathlib.category_theory.monoidal_category.left_unitor

notation:1024 "ρ_" => Mathlib.category_theory.monoidal_category.right_unitor

/-- The tensor product of two isomorphisms is an isomorphism. -/
def tensor_iso {C : Type u} {X : C} {Y : C} {X' : C} {Y' : C} [category C] [monoidal_category C]
    (f : X ≅ Y) (g : X' ≅ Y') : X ⊗ X' ≅ Y ⊗ Y' :=
  iso.mk (iso.hom f ⊗ iso.hom g) (iso.inv f ⊗ iso.inv g)

infixr:70 " ⊗ " => Mathlib.category_theory.tensor_iso

namespace monoidal_category


protected instance tensor_is_iso {C : Type u} [category C] [monoidal_category C] {W : C} {X : C}
    {Y : C} {Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] : is_iso (f ⊗ g) :=
  is_iso.mk (iso.inv (as_iso f ⊗ as_iso g))

@[simp] theorem inv_tensor {C : Type u} [category C] [monoidal_category C] {W : C} {X : C} {Y : C}
    {Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] : inv (f ⊗ g) = inv f ⊗ inv g :=
  rfl

-- When `rewrite_search` lands, add @[search] attributes to

-- monoidal_category.tensor_id monoidal_category.tensor_comp monoidal_category.associator_naturality

-- monoidal_category.left_unitor_naturality monoidal_category.right_unitor_naturality

-- monoidal_category.pentagon monoidal_category.triangle

-- tensor_comp_id tensor_id_comp comp_id_tensor_tensor_id

-- triangle_assoc_comp_left triangle_assoc_comp_right

-- triangle_assoc_comp_left_inv triangle_assoc_comp_right_inv

-- left_unitor_tensor left_unitor_tensor_inv

-- right_unitor_tensor right_unitor_tensor_inv

-- pentagon_inv

-- associator_inv_naturality

-- left_unitor_inv_naturality

-- right_unitor_inv_naturality

@[simp] theorem comp_tensor_id {C : Type u} [category C] [monoidal_category C] {W : C} {X : C}
    {Y : C} {Z : C} (f : W ⟶ X) (g : X ⟶ Y) : f ≫ g ⊗ 𝟙 = (f ⊗ 𝟙) ≫ (g ⊗ 𝟙) :=
  sorry

@[simp] theorem id_tensor_comp {C : Type u} [category C] [monoidal_category C] {W : C} {X : C}
    {Y : C} {Z : C} (f : W ⟶ X) (g : X ⟶ Y) : 𝟙 ⊗ f ≫ g = (𝟙 ⊗ f) ≫ (𝟙 ⊗ g) :=
  sorry

@[simp] theorem id_tensor_comp_tensor_id {C : Type u} [category C] [monoidal_category C] {W : C}
    {X : C} {Y : C} {Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : (𝟙 ⊗ f) ≫ (g ⊗ 𝟙) = g ⊗ f :=
  sorry

@[simp] theorem tensor_id_comp_id_tensor_assoc {C : Type u} [category C] [monoidal_category C]
    {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ X) (g : Y ⟶ Z) {X' : C} (f' : Z ⊗ X ⟶ X') :
    (g ⊗ 𝟙) ≫ (𝟙 ⊗ f) ≫ f' = (g ⊗ f) ≫ f' :=
  sorry

theorem left_unitor_inv_naturality {C : Type u} [category C] [monoidal_category C] {X : C} {X' : C}
    (f : X ⟶ X') : f ≫ iso.inv λ_ = iso.inv λ_ ≫ (𝟙 ⊗ f) :=
  sorry

theorem right_unitor_inv_naturality {C : Type u} [category C] [monoidal_category C] {X : C} {X' : C}
    (f : X ⟶ X') : f ≫ iso.inv ρ_ = iso.inv ρ_ ≫ (f ⊗ 𝟙) :=
  sorry

@[simp] theorem right_unitor_conjugation {C : Type u} [category C] [monoidal_category C] {X : C}
    {Y : C} (f : X ⟶ Y) : iso.inv ρ_ ≫ (f ⊗ 𝟙) ≫ iso.hom ρ_ = f :=
  sorry

@[simp] theorem left_unitor_conjugation {C : Type u} [category C] [monoidal_category C] {X : C}
    {Y : C} (f : X ⟶ Y) : iso.inv λ_ ≫ (𝟙 ⊗ f) ≫ iso.hom λ_ = f :=
  sorry

@[simp] theorem tensor_left_iff {C : Type u} [category C] [monoidal_category C] {X : C} {Y : C}
    (f : X ⟶ Y) (g : X ⟶ Y) : 𝟙 ⊗ f = 𝟙 ⊗ g ↔ f = g :=
  sorry

@[simp] theorem tensor_right_iff {C : Type u} [category C] [monoidal_category C] {X : C} {Y : C}
    (f : X ⟶ Y) (g : X ⟶ Y) : f ⊗ 𝟙 = g ⊗ 𝟙 ↔ f = g :=
  sorry

-- We now prove:

--   ((α_ (𝟙_ C) X Y).hom) ≫

--     ((λ_ (X ⊗ Y)).hom)

--   = ((λ_ X).hom ⊗ (𝟙 Y))

-- (and the corresponding fact for right unitors)

-- following the proof on nLab:

-- Lemma 2.2 at <https://ncatlab.org/nlab/revision/monoidal+category/115>

theorem left_unitor_product_aux_perimeter {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) :
    (iso.hom α_ ⊗ 𝟙) ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.hom α_) ≫ (𝟙 ⊗ iso.hom λ_) =
        ((iso.hom ρ_ ⊗ 𝟙) ⊗ 𝟙) ≫ iso.hom α_ :=
  sorry

theorem left_unitor_product_aux_triangle {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : (iso.hom α_ ⊗ 𝟙) ≫ ((𝟙 ⊗ iso.hom λ_) ⊗ 𝟙) = (iso.hom ρ_ ⊗ 𝟙) ⊗ 𝟙 :=
  sorry

theorem left_unitor_product_aux_square {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : iso.hom α_ ≫ (𝟙 ⊗ iso.hom λ_ ⊗ 𝟙) = ((𝟙 ⊗ iso.hom λ_) ⊗ 𝟙) ≫ iso.hom α_ :=
  sorry

theorem left_unitor_product_aux {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    (𝟙 ⊗ iso.hom α_) ≫ (𝟙 ⊗ iso.hom λ_) = 𝟙 ⊗ iso.hom λ_ ⊗ 𝟙 :=
  sorry

theorem right_unitor_product_aux_perimeter {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) :
    (iso.hom α_ ⊗ 𝟙) ≫ iso.hom α_ ≫ (𝟙 ⊗ iso.hom α_) ≫ (𝟙 ⊗ 𝟙 ⊗ iso.hom λ_) =
        (iso.hom ρ_ ⊗ 𝟙) ≫ iso.hom α_ :=
  sorry

theorem right_unitor_product_aux_triangle {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : (𝟙 ⊗ iso.hom α_) ≫ (𝟙 ⊗ 𝟙 ⊗ iso.hom λ_) = 𝟙 ⊗ iso.hom ρ_ ⊗ 𝟙 :=
  sorry

theorem right_unitor_product_aux_square {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : iso.hom α_ ≫ (𝟙 ⊗ iso.hom ρ_ ⊗ 𝟙) = ((𝟙 ⊗ iso.hom ρ_) ⊗ 𝟙) ≫ iso.hom α_ :=
  sorry

theorem right_unitor_product_aux {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    (iso.hom α_ ⊗ 𝟙) ≫ ((𝟙 ⊗ iso.hom ρ_) ⊗ 𝟙) = iso.hom ρ_ ⊗ 𝟙 :=
  sorry

-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>

theorem left_unitor_tensor' {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    iso.hom α_ ≫ iso.hom λ_ = iso.hom λ_ ⊗ 𝟙 :=
  sorry

@[simp] theorem left_unitor_tensor {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    iso.hom λ_ = iso.inv α_ ≫ (iso.hom λ_ ⊗ 𝟙) :=
  sorry

theorem left_unitor_tensor_inv' {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    iso.inv λ_ ≫ iso.inv α_ = iso.inv λ_ ⊗ 𝟙 :=
  sorry

@[simp] theorem left_unitor_tensor_inv {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : iso.inv λ_ = (iso.inv λ_ ⊗ 𝟙) ≫ iso.hom α_ :=
  sorry

@[simp] theorem right_unitor_tensor {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : iso.hom ρ_ = iso.hom α_ ≫ (𝟙 ⊗ iso.hom ρ_) :=
  sorry

@[simp] theorem right_unitor_tensor_inv {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : iso.inv ρ_ = (𝟙 ⊗ iso.inv ρ_) ≫ iso.inv α_ :=
  sorry

theorem associator_inv_naturality {C : Type u} [category C] [monoidal_category C] {X : C} {Y : C}
    {Z : C} {X' : C} {Y' : C} {Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    (f ⊗ g ⊗ h) ≫ iso.inv α_ = iso.inv α_ ≫ ((f ⊗ g) ⊗ h) :=
  sorry

theorem pentagon_inv {C : Type u} [category C] [monoidal_category C] (W : C) (X : C) (Y : C)
    (Z : C) : (𝟙 ⊗ iso.inv α_) ≫ iso.inv α_ ≫ (iso.inv α_ ⊗ 𝟙) = iso.inv α_ ≫ iso.inv α_ :=
  sorry

theorem triangle_assoc_comp_left {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    iso.hom α_ ≫ (𝟙 ⊗ iso.hom λ_) = iso.hom ρ_ ⊗ 𝟙 :=
  triangle X Y

@[simp] theorem triangle_assoc_comp_right {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : iso.inv α_ ≫ (iso.hom ρ_ ⊗ 𝟙) = 𝟙 ⊗ iso.hom λ_ :=
  sorry

@[simp] theorem triangle_assoc_comp_right_inv {C : Type u} [category C] [monoidal_category C]
    (X : C) (Y : C) : (iso.inv ρ_ ⊗ 𝟙) ≫ iso.hom α_ = 𝟙 ⊗ iso.inv λ_ :=
  sorry

@[simp] theorem triangle_assoc_comp_left_inv {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) : (𝟙 ⊗ iso.inv λ_) ≫ iso.inv α_ = iso.inv ρ_ ⊗ 𝟙 :=
  sorry

/-- The tensor product expressed as a functor. -/
def tensor (C : Type u) [category C] [monoidal_category C] : C × C ⥤ C :=
  functor.mk (fun (X : C × C) => prod.fst X ⊗ prod.snd X)
    fun {X Y : C × C} (f : X ⟶ Y) => prod.fst f ⊗ prod.snd f

/-- The left-associated triple tensor product as a functor. -/
def left_assoc_tensor (C : Type u) [category C] [monoidal_category C] : C × C × C ⥤ C :=
  functor.mk (fun (X : C × C × C) => (prod.fst X ⊗ prod.fst (prod.snd X)) ⊗ prod.snd (prod.snd X))
    fun {X Y : C × C × C} (f : X ⟶ Y) =>
      (prod.fst f ⊗ prod.fst (prod.snd f)) ⊗ prod.snd (prod.snd f)

@[simp] theorem left_assoc_tensor_obj (C : Type u) [category C] [monoidal_category C]
    (X : C × C × C) :
    functor.obj (left_assoc_tensor C) X =
        (prod.fst X ⊗ prod.fst (prod.snd X)) ⊗ prod.snd (prod.snd X) :=
  rfl

@[simp] theorem left_assoc_tensor_map (C : Type u) [category C] [monoidal_category C]
    {X : C × C × C} {Y : C × C × C} (f : X ⟶ Y) :
    functor.map (left_assoc_tensor C) f =
        (prod.fst f ⊗ prod.fst (prod.snd f)) ⊗ prod.snd (prod.snd f) :=
  rfl

/-- The right-associated triple tensor product as a functor. -/
def right_assoc_tensor (C : Type u) [category C] [monoidal_category C] : C × C × C ⥤ C :=
  functor.mk (fun (X : C × C × C) => prod.fst X ⊗ prod.fst (prod.snd X) ⊗ prod.snd (prod.snd X))
    fun {X Y : C × C × C} (f : X ⟶ Y) => prod.fst f ⊗ prod.fst (prod.snd f) ⊗ prod.snd (prod.snd f)

@[simp] theorem right_assoc_tensor_obj (C : Type u) [category C] [monoidal_category C]
    (X : C × C × C) :
    functor.obj (right_assoc_tensor C) X =
        prod.fst X ⊗ prod.fst (prod.snd X) ⊗ prod.snd (prod.snd X) :=
  rfl

@[simp] theorem right_assoc_tensor_map (C : Type u) [category C] [monoidal_category C]
    {X : C × C × C} {Y : C × C × C} (f : X ⟶ Y) :
    functor.map (right_assoc_tensor C) f =
        prod.fst f ⊗ prod.fst (prod.snd f) ⊗ prod.snd (prod.snd f) :=
  rfl

/-- The functor `λ X, 𝟙_ C ⊗ X`. -/
def tensor_unit_left (C : Type u) [category C] [monoidal_category C] : C ⥤ C :=
  functor.mk (fun (X : C) => 𝟙_ ⊗ X) fun {X Y : C} (f : X ⟶ Y) => 𝟙 ⊗ f

/-- The functor `λ X, X ⊗ 𝟙_ C`. -/
def tensor_unit_right (C : Type u) [category C] [monoidal_category C] : C ⥤ C :=
  functor.mk (fun (X : C) => X ⊗ 𝟙_) fun {X Y : C} (f : X ⟶ Y) => f ⊗ 𝟙

-- We can express the associator and the unitors, given componentwise above,

-- as natural isomorphisms.

/-- The associator as a natural isomorphism. -/
@[simp] theorem associator_nat_iso_hom_app (C : Type u) [category C] [monoidal_category C]
    (X : C × C × C) : nat_trans.app (iso.hom (associator_nat_iso C)) X = iso.hom α_ :=
  Eq.refl (iso.hom α_)

/-- The left unitor as a natural isomorphism. -/
@[simp] theorem left_unitor_nat_iso_inv_app (C : Type u) [category C] [monoidal_category C]
    (X : C) : nat_trans.app (iso.inv (left_unitor_nat_iso C)) X = iso.inv λ_ :=
  Eq.refl (iso.inv λ_)

/-- The right unitor as a natural isomorphism. -/
@[simp] theorem right_unitor_nat_iso_inv_app (C : Type u) [category C] [monoidal_category C]
    (X : C) : nat_trans.app (iso.inv (right_unitor_nat_iso C)) X = iso.inv ρ_ :=
  Eq.refl (iso.inv ρ_)

/-- Tensoring on the left with a fixed object, as a functor. -/
@[simp] theorem tensor_left_map {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C)
    (Y' : C) (f : Y ⟶ Y') : functor.map (tensor_left X) f = 𝟙 ⊗ f :=
  Eq.refl (functor.map (tensor_left X) f)

/--
Tensoring on the left with `X ⊗ Y` is naturally isomorphic to
tensoring on the left with `Y`, and then again with `X`.
-/
def tensor_left_tensor {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    tensor_left (X ⊗ Y) ≅ tensor_left Y ⋙ tensor_left X :=
  nat_iso.of_components α_ sorry

@[simp] theorem tensor_left_tensor_hom_app {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) (Z : C) : nat_trans.app (iso.hom (tensor_left_tensor X Y)) Z = iso.hom α_ :=
  rfl

@[simp] theorem tensor_left_tensor_inv_app {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) (Z : C) : nat_trans.app (iso.inv (tensor_left_tensor X Y)) Z = iso.inv α_ :=
  rfl

/-- Tensoring on the right with a fixed object, as a functor. -/
@[simp] theorem tensor_right_obj {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    functor.obj (tensor_right X) Y = Y ⊗ X :=
  Eq.refl (functor.obj (tensor_right X) Y)

/--
Tensoring on the right, as a functor from `C` into endofunctors of `C`.

We later show this is a monoidal functor.
-/
def tensoring_right (C : Type u) [category C] [monoidal_category C] : C ⥤ C ⥤ C :=
  functor.mk tensor_right fun (X Y : C) (f : X ⟶ Y) => nat_trans.mk fun (Z : C) => 𝟙 ⊗ f

protected instance tensoring_right.category_theory.faithful (C : Type u) [category C]
    [monoidal_category C] : faithful (tensoring_right C) :=
  faithful.mk

/--
Tensoring on the right with `X ⊗ Y` is naturally isomorphic to
tensoring on the right with `X`, and then again with `Y`.
-/
def tensor_right_tensor {C : Type u} [category C] [monoidal_category C] (X : C) (Y : C) :
    tensor_right (X ⊗ Y) ≅ tensor_right X ⋙ tensor_right Y :=
  nat_iso.of_components (fun (Z : C) => iso.symm α_) sorry

@[simp] theorem tensor_right_tensor_hom_app {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) (Z : C) : nat_trans.app (iso.hom (tensor_right_tensor X Y)) Z = iso.inv α_ :=
  rfl

@[simp] theorem tensor_right_tensor_inv_app {C : Type u} [category C] [monoidal_category C] (X : C)
    (Y : C) (Z : C) : nat_trans.app (iso.inv (tensor_right_tensor X Y)) Z = iso.hom α_ :=
  rfl

end Mathlib