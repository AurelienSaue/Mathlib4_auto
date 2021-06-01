/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.braided
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.category_theory.pempty
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# The monoidal structure on a category with chosen finite products.

This is a variant of the development in `category_theory.monoidal.of_has_finite_products`,
which uses specified choices of the terminal object and binary product,
enabling the construction of a cartesian category with specific definitions of the tensor unit
and tensor product.

(Because the construction in `category_theory.monoidal.of_has_finite_products` uses `has_limit`
classes, the actual definitions there are opaque behind `classical.choice`.)

We use this in `category_theory.monoidal.types` to construct the monoidal category of types
so that the tensor product is the usual cartesian product of types.

For now we only do the construction from products, and not from coproducts,
which seems less often useful.
-/

namespace category_theory


namespace limits


/-- Swap the two sides of a `binary_fan`. -/
def binary_fan.swap {C : Type u} [category C] {P : C} {Q : C} (t : binary_fan P Q) :
    binary_fan Q P :=
  binary_fan.mk (binary_fan.snd t) (binary_fan.fst t)

@[simp] theorem binary_fan.swap_fst {C : Type u} [category C] {P : C} {Q : C} (t : binary_fan P Q) :
    binary_fan.fst (binary_fan.swap t) = binary_fan.snd t :=
  rfl

@[simp] theorem binary_fan.swap_snd {C : Type u} [category C] {P : C} {Q : C} (t : binary_fan P Q) :
    binary_fan.snd (binary_fan.swap t) = binary_fan.fst t :=
  rfl

/--
If a cone `t` over `P Q` is a limit cone, then `t.swap` is a limit cone over `Q P`.
-/
@[simp] theorem is_limit.swap_binary_fan_lift {C : Type u} [category C] {P : C} {Q : C}
    {t : binary_fan P Q} (I : is_limit t) (s : cone (pair Q P)) :
    is_limit.lift (is_limit.swap_binary_fan I) s = is_limit.lift I (binary_fan.swap s) :=
  Eq.refl (is_limit.lift (is_limit.swap_binary_fan I) s)

/--
Construct `has_binary_product Q P` from `has_binary_product P Q`.
This can't be an instance, as it would cause a loop in typeclass search.
-/
theorem has_binary_product.swap {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q] :
    has_binary_product Q P :=
  has_limit.mk
    (limit_cone.mk (binary_fan.swap (limit.cone (pair P Q)))
      (is_limit.swap_binary_fan (limit.is_limit (pair P Q))))

/--
Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we can construct
an isomorphism between the cone points. Relative to some fixed choice of limits cones for every pair,
these isomorphisms constitute a braiding.
-/
def binary_fan.braiding {C : Type u} [category C] {X : C} {Y : C} {s : binary_fan X Y}
    (P : is_limit s) {t : binary_fan Y X} (Q : is_limit t) : cone.X s ≅ cone.X t :=
  is_limit.cone_point_unique_up_to_iso P (is_limit.swap_binary_fan Q)

/--
Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a cartesian category.
-/
def binary_fan.assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {sXY : binary_fan X Y}
    {sYZ : binary_fan Y Z} (Q : is_limit sYZ) (s : binary_fan (cone.X sXY) Z) :
    binary_fan X (cone.X sYZ) :=
  binary_fan.mk (binary_fan.fst s ≫ binary_fan.fst sXY)
    (is_limit.lift Q (binary_fan.mk (binary_fan.fst s ≫ binary_fan.snd sXY) (binary_fan.snd s)))

@[simp] theorem binary_fan.assoc_fst {C : Type u} [category C] {X : C} {Y : C} {Z : C}
    {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ)
    (s : binary_fan (cone.X sXY) Z) :
    binary_fan.fst (binary_fan.assoc Q s) = binary_fan.fst s ≫ binary_fan.fst sXY :=
  rfl

@[simp] theorem binary_fan.assoc_snd {C : Type u} [category C] {X : C} {Y : C} {Z : C}
    {sXY : binary_fan X Y} {sYZ : binary_fan Y Z} (Q : is_limit sYZ)
    (s : binary_fan (cone.X sXY) Z) :
    binary_fan.snd (binary_fan.assoc Q s) =
        is_limit.lift Q
          (binary_fan.mk (binary_fan.fst s ≫ binary_fan.snd sXY) (binary_fan.snd s)) :=
  rfl

/--
Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a cartesian category.
-/
def binary_fan.assoc_inv {C : Type u} [category C] {X : C} {Y : C} {Z : C} {sXY : binary_fan X Y}
    (P : is_limit sXY) {sYZ : binary_fan Y Z} (s : binary_fan X (cone.X sYZ)) :
    binary_fan (cone.X sXY) Z :=
  binary_fan.mk
    (is_limit.lift P (binary_fan.mk (binary_fan.fst s) (binary_fan.snd s ≫ binary_fan.fst sYZ)))
    (binary_fan.snd s ≫ binary_fan.snd sYZ)

@[simp] theorem binary_fan.assoc_inv_fst {C : Type u} [category C] {X : C} {Y : C} {Z : C}
    {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z}
    (s : binary_fan X (cone.X sYZ)) :
    binary_fan.fst (binary_fan.assoc_inv P s) =
        is_limit.lift P
          (binary_fan.mk (binary_fan.fst s) (binary_fan.snd s ≫ binary_fan.fst sYZ)) :=
  rfl

@[simp] theorem binary_fan.assoc_inv_snd {C : Type u} [category C] {X : C} {Y : C} {Z : C}
    {sXY : binary_fan X Y} (P : is_limit sXY) {sYZ : binary_fan Y Z}
    (s : binary_fan X (cone.X sYZ)) :
    binary_fan.snd (binary_fan.assoc_inv P s) = binary_fan.snd s ≫ binary_fan.snd sYZ :=
  rfl

/--
If all the binary fans involved a limit cones, `binary_fan.assoc` produces another limit cone.
-/
def is_limit.assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {sXY : binary_fan X Y}
    (P : is_limit sXY) {sYZ : binary_fan Y Z} (Q : is_limit sYZ) {s : binary_fan (cone.X sXY) Z}
    (R : is_limit s) : is_limit (binary_fan.assoc Q s) :=
  is_limit.mk fun (t : cone (pair X (cone.X sYZ))) => is_limit.lift R (binary_fan.assoc_inv P t)

/--
Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`,
we obtain an isomorphism between the cone points.
-/
def binary_fan.associator {C : Type u} [category C] {X : C} {Y : C} {Z : C} {sXY : binary_fan X Y}
    (P : is_limit sXY) {sYZ : binary_fan Y Z} (Q : is_limit sYZ) {s : binary_fan (cone.X sXY) Z}
    (R : is_limit s) {t : binary_fan X (cone.X sYZ)} (S : is_limit t) : cone.X s ≅ cone.X t :=
  is_limit.cone_point_unique_up_to_iso (is_limit.assoc P Q R) S

/--
Given a fixed family of limit data for every pair `X Y`, we obtain an associator.
-/
def binary_fan.associator_of_limit_cone {C : Type u} [category C]
    (L : (X Y : C) → limit_cone (pair X Y)) (X : C) (Y : C) (Z : C) :
    cone.X (limit_cone.cone (L (cone.X (limit_cone.cone (L X Y))) Z)) ≅
        cone.X (limit_cone.cone (L X (cone.X (limit_cone.cone (L Y Z))))) :=
  binary_fan.associator (limit_cone.is_limit (L X Y)) (limit_cone.is_limit (L Y Z))
    (limit_cone.is_limit (L (cone.X (limit_cone.cone (L X Y))) Z))
    (limit_cone.is_limit (L X (cone.X (limit_cone.cone (L Y Z)))))

/--
Construct a left unitor from specified limit cones.
-/
def binary_fan.left_unitor {C : Type u} [category C] {X : C} {s : cone (functor.empty C)}
    (P : is_limit s) {t : binary_fan (cone.X s) X} (Q : is_limit t) : cone.X t ≅ X :=
  iso.mk (binary_fan.snd t)
    (is_limit.lift Q
      (binary_fan.mk
        (is_limit.lift P
          (cone.mk X
            (nat_trans.mk
              (pempty.rec
                fun (n : pempty) =>
                  functor.obj (functor.obj (functor.const (discrete pempty)) X) n ⟶
                    functor.obj (functor.empty C) n))))
        𝟙))

/--
Construct a right unitor from specified limit cones.
-/
def binary_fan.right_unitor {C : Type u} [category C] {X : C} {s : cone (functor.empty C)}
    (P : is_limit s) {t : binary_fan X (cone.X s)} (Q : is_limit t) : cone.X t ≅ X :=
  iso.mk (binary_fan.fst t)
    (is_limit.lift Q
      (binary_fan.mk 𝟙
        (is_limit.lift P
          (cone.mk X
            (nat_trans.mk
              (pempty.rec
                fun (n : pempty) =>
                  functor.obj (functor.obj (functor.const (discrete pempty)) X) n ⟶
                    functor.obj (functor.empty C) n))))))

end limits


namespace monoidal_of_chosen_finite_products


/-- Implementation of the tensor product for `monoidal_of_chosen_finite_products`. -/
def tensor_obj {C : Type u} [category C] (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y))
    (X : C) (Y : C) : C :=
  limits.cone.X (limits.limit_cone.cone (ℬ X Y))

/-- Implementation of the tensor product of morphisms for `monoidal_of_chosen_finite_products`. -/
def tensor_hom {C : Type u} [category C] (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y))
    {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : tensor_obj ℬ W Y ⟶ tensor_obj ℬ X Z :=
  subtype.val
    (limits.binary_fan.is_limit.lift' (limits.limit_cone.is_limit (ℬ X Z))
      (nat_trans.app (limits.cone.π (limits.limit_cone.cone (ℬ W Y))) limits.walking_pair.left ≫ f)
      (nat_trans.app (limits.cone.π (limits.limit_cone.cone (ℬ W Y))) limits.walking_pair.right ≫
        g))

theorem tensor_id {C : Type u} [category C] (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y))
    (X₁ : C) (X₂ : C) : tensor_hom ℬ 𝟙 𝟙 = 𝟙 :=
  sorry

theorem tensor_comp {C : Type u} [category C] (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y))
    {X₁ : C} {Y₁ : C} {Z₁ : C} {X₂ : C} {Y₂ : C} {Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensor_hom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) = tensor_hom ℬ f₁ f₂ ≫ tensor_hom ℬ g₁ g₂ :=
  sorry

theorem pentagon {C : Type u} [category C] (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y))
    (W : C) (X : C) (Y : C) (Z : C) :
    tensor_hom ℬ (iso.hom (limits.binary_fan.associator_of_limit_cone ℬ W X Y)) 𝟙 ≫
          iso.hom (limits.binary_fan.associator_of_limit_cone ℬ W (tensor_obj ℬ X Y) Z) ≫
            tensor_hom ℬ 𝟙 (iso.hom (limits.binary_fan.associator_of_limit_cone ℬ X Y Z)) =
        iso.hom (limits.binary_fan.associator_of_limit_cone ℬ (tensor_obj ℬ W X) Y Z) ≫
          iso.hom (limits.binary_fan.associator_of_limit_cone ℬ W X (tensor_obj ℬ Y Z)) :=
  sorry

theorem triangle {C : Type u} [category C] (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) (X : C) (Y : C) :
    iso.hom
            (limits.binary_fan.associator_of_limit_cone ℬ X
              (limits.cone.X (limits.limit_cone.cone 𝒯)) Y) ≫
          tensor_hom ℬ 𝟙
            (iso.hom
              (limits.binary_fan.left_unitor (limits.limit_cone.is_limit 𝒯)
                (limits.limit_cone.is_limit (ℬ (limits.cone.X (limits.limit_cone.cone 𝒯)) Y)))) =
        tensor_hom ℬ
          (iso.hom
            (limits.binary_fan.right_unitor (limits.limit_cone.is_limit 𝒯)
              (limits.limit_cone.is_limit (ℬ X (limits.cone.X (limits.limit_cone.cone 𝒯))))))
          𝟙 :=
  sorry

theorem left_unitor_naturality {C : Type u} [category C] (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) {X₁ : C} {X₂ : C} (f : X₁ ⟶ X₂) :
    tensor_hom ℬ 𝟙 f ≫
          iso.hom
            (limits.binary_fan.left_unitor (limits.limit_cone.is_limit 𝒯)
              (limits.limit_cone.is_limit (ℬ (limits.cone.X (limits.limit_cone.cone 𝒯)) X₂))) =
        iso.hom
            (limits.binary_fan.left_unitor (limits.limit_cone.is_limit 𝒯)
              (limits.limit_cone.is_limit (ℬ (limits.cone.X (limits.limit_cone.cone 𝒯)) X₁))) ≫
          f :=
  sorry

theorem right_unitor_naturality {C : Type u} [category C] (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) {X₁ : C} {X₂ : C} (f : X₁ ⟶ X₂) :
    tensor_hom ℬ f 𝟙 ≫
          iso.hom
            (limits.binary_fan.right_unitor (limits.limit_cone.is_limit 𝒯)
              (limits.limit_cone.is_limit (ℬ X₂ (limits.cone.X (limits.limit_cone.cone 𝒯))))) =
        iso.hom
            (limits.binary_fan.right_unitor (limits.limit_cone.is_limit 𝒯)
              (limits.limit_cone.is_limit (ℬ X₁ (limits.cone.X (limits.limit_cone.cone 𝒯))))) ≫
          f :=
  sorry

theorem associator_naturality {C : Type u} [category C]
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) {X₁ : C} {X₂ : C} {X₃ : C} {Y₁ : C}
    {Y₂ : C} {Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensor_hom ℬ (tensor_hom ℬ f₁ f₂) f₃ ≫
          iso.hom (limits.binary_fan.associator_of_limit_cone ℬ Y₁ Y₂ Y₃) =
        iso.hom (limits.binary_fan.associator_of_limit_cone ℬ X₁ X₂ X₃) ≫
          tensor_hom ℬ f₁ (tensor_hom ℬ f₂ f₃) :=
  sorry

end monoidal_of_chosen_finite_products


/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidal_of_chosen_finite_products {C : Type u} [category C]
    (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) : monoidal_category C :=
  monoidal_category.mk (fun (X Y : C) => sorry)
    (fun (_x _x_1 _x_2 _x_3 : C) (f : _x ⟶ _x_1) (g : _x_2 ⟶ _x_3) => sorry)
    (limits.cone.X (limits.limit_cone.cone 𝒯))
    (fun (X Y Z : C) => limits.binary_fan.associator_of_limit_cone ℬ X Y Z)
    (fun (X : C) =>
      limits.binary_fan.left_unitor (limits.limit_cone.is_limit 𝒯)
        (limits.limit_cone.is_limit (ℬ (limits.cone.X (limits.limit_cone.cone 𝒯)) X)))
    fun (X : C) =>
      limits.binary_fan.right_unitor (limits.limit_cone.is_limit 𝒯)
        (limits.limit_cone.is_limit (ℬ X (limits.cone.X (limits.limit_cone.cone 𝒯))))

namespace monoidal_of_chosen_finite_products


/--
A type synonym for `C` carrying a monoidal category structure corresponding to
a fixed choice of limit data for the empty functor, and for `pair X Y` for every `X Y : C`.

This is an implementation detail for `symmetric_of_chosen_finite_products`.
-/
def monoidal_of_chosen_finite_products_synonym {C : Type u} [category C]
    (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) :=
  C

protected instance monoidal_of_chosen_finite_products_synonym.category_theory.monoidal_category
    {C : Type u} [category C] (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) :
    monoidal_category (monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
  monoidal_of_chosen_finite_products 𝒯 ℬ

theorem braiding_naturality {C : Type u} [category C]
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) {X : C} {X' : C} {Y : C} {Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    tensor_hom ℬ f g ≫
          iso.hom
            (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ Y Y'))
              (limits.limit_cone.is_limit (ℬ Y' Y))) =
        iso.hom
            (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ X X'))
              (limits.limit_cone.is_limit (ℬ X' X))) ≫
          tensor_hom ℬ g f :=
  sorry

theorem hexagon_forward {C : Type u} [category C]
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) (X : C) (Y : C) (Z : C) :
    iso.hom (limits.binary_fan.associator_of_limit_cone ℬ X Y Z) ≫
          iso.hom
              (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ X (tensor_obj ℬ Y Z)))
                (limits.limit_cone.is_limit (ℬ (tensor_obj ℬ Y Z) X))) ≫
            iso.hom (limits.binary_fan.associator_of_limit_cone ℬ Y Z X) =
        tensor_hom ℬ
            (iso.hom
              (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ X Y))
                (limits.limit_cone.is_limit (ℬ Y X))))
            𝟙 ≫
          iso.hom (limits.binary_fan.associator_of_limit_cone ℬ Y X Z) ≫
            tensor_hom ℬ 𝟙
              (iso.hom
                (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ X Z))
                  (limits.limit_cone.is_limit (ℬ Z X)))) :=
  sorry

theorem hexagon_reverse {C : Type u} [category C]
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) (X : C) (Y : C) (Z : C) :
    iso.inv (limits.binary_fan.associator_of_limit_cone ℬ X Y Z) ≫
          iso.hom
              (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ (tensor_obj ℬ X Y) Z))
                (limits.limit_cone.is_limit (ℬ Z (tensor_obj ℬ X Y)))) ≫
            iso.inv (limits.binary_fan.associator_of_limit_cone ℬ Z X Y) =
        tensor_hom ℬ 𝟙
            (iso.hom
              (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ Y Z))
                (limits.limit_cone.is_limit (ℬ Z Y)))) ≫
          iso.inv (limits.binary_fan.associator_of_limit_cone ℬ X Z Y) ≫
            tensor_hom ℬ
              (iso.hom
                (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ X Z))
                  (limits.limit_cone.is_limit (ℬ Z X))))
              𝟙 :=
  sorry

theorem symmetry {C : Type u} [category C] (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y))
    (X : C) (Y : C) :
    iso.hom
            (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ X Y))
              (limits.limit_cone.is_limit (ℬ Y X))) ≫
          iso.hom
            (limits.binary_fan.braiding (limits.limit_cone.is_limit (ℬ Y X))
              (limits.limit_cone.is_limit (ℬ X Y))) =
        𝟙 :=
  sorry

end monoidal_of_chosen_finite_products


/--
The monoidal structure coming from finite products is symmetric.
-/
def symmetric_of_chosen_finite_products {C : Type u} [category C]
    (𝒯 : limits.limit_cone (functor.empty C))
    (ℬ : (X Y : C) → limits.limit_cone (limits.pair X Y)) :
    symmetric_category
        (monoidal_of_chosen_finite_products.monoidal_of_chosen_finite_products_synonym 𝒯 ℬ) :=
  symmetric_category.mk

end Mathlib