/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.finite_products
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.preadditive.default
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

We treat first the case of a general category with zero morphisms,
and subsequently the case of a preadditive category.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit cocone.

In a preadditive category,
* any `binary_biproduct` satisfies `total : fst ≫ inl + snd ≫ inr = 𝟙 X`
* any `binary_product` is a `binary_biproduct`
* any `binary_coproduct` is a `binary_biproduct`

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

In a preadditive category,
* any `biproduct` satisfies `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
* any `product` is a `biproduct`
* any `coproduct` is a `biproduct`

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.
-/

namespace category_theory.limits


/--
A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
structure bicone {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C)
    where
  X : C
  π : (j : J) → X ⟶ F j
  ι : (j : J) → F j ⟶ X
  ι_π :
    ∀ (j j' : J),
      ι j ≫ π j' =
        dite (j = j') (fun (h : j = j') => eq_to_hom (congr_arg F h)) fun (h : ¬j = j') => 0

@[simp] theorem bicone_ι_π_self {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {F : J → C} (B : bicone F) (j : J) : bicone.ι B j ≫ bicone.π B j = 𝟙 :=
  sorry

@[simp] theorem bicone_ι_π_ne {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {F : J → C} (B : bicone F) {j : J} {j' : J} (h : j ≠ j') :
    bicone.ι B j ≫ bicone.π B j' = 0 :=
  sorry

namespace bicone


/-- Extract the cone from a bicone. -/
def to_cone {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    {F : J → C} (B : bicone F) : cone (discrete.functor F) :=
  cone.mk (X B) (nat_trans.mk fun (j : discrete J) => π B j)

/-- Extract the cocone from a bicone. -/
def to_cocone {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    {F : J → C} (B : bicone F) : cocone (discrete.functor F) :=
  cocone.mk (X B) (nat_trans.mk fun (j : discrete J) => ι B j)

end bicone


/--
A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
structure limit_bicone {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C)
    where
  bicone : bicone F
  is_limit : is_limit (bicone.to_cone bicone)
  is_colimit : is_colimit (bicone.to_cocone bicone)

/--
`has_biproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class has_biproduct {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C)
    where
  mk' :: (exists_biproduct : Nonempty (limit_bicone F))

theorem has_biproduct.mk {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {F : J → C} (d : limit_bicone F) : has_biproduct F :=
  has_biproduct.mk' (Nonempty.intro d)

/-- Use the axiom of choice to extract explicit `biproduct_data F` from `has_biproduct F`. -/
def get_biproduct_data {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C) [has_biproduct F] : limit_bicone F :=
  Classical.choice sorry

/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
def biproduct.bicone {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C) [has_biproduct F] : bicone F :=
  limit_bicone.bicone (get_biproduct_data F)

/-- `biproduct.bicone F` is a limit cone. -/
def biproduct.is_limit {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C) [has_biproduct F] : is_limit (bicone.to_cone (biproduct.bicone F)) :=
  limit_bicone.is_limit (get_biproduct_data F)

/-- `biproduct.bicone F` is a colimit cocone. -/
def biproduct.is_colimit {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (F : J → C) [has_biproduct F] :
    is_colimit (bicone.to_cocone (biproduct.bicone F)) :=
  limit_bicone.is_colimit (get_biproduct_data F)

protected instance has_product_of_has_biproduct {J : Type v} [DecidableEq J] {C : Type u}
    [category C] [has_zero_morphisms C] {F : J → C} [has_biproduct F] :
    has_limit (discrete.functor F) :=
  has_limit.mk (limit_cone.mk (bicone.to_cone (biproduct.bicone F)) (biproduct.is_limit F))

protected instance has_coproduct_of_has_biproduct {J : Type v} [DecidableEq J] {C : Type u}
    [category C] [has_zero_morphisms C] {F : J → C} [has_biproduct F] :
    has_colimit (discrete.functor F) :=
  has_colimit.mk
    (colimit_cocone.mk (bicone.to_cocone (biproduct.bicone F)) (biproduct.is_colimit F))

/--
`C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class has_biproducts_of_shape (J : Type v) [DecidableEq J] (C : Type u) [category C]
    [has_zero_morphisms C]
    where
  has_biproduct : ∀ (F : J → C), has_biproduct F

/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type with decidable equality. -/
class has_finite_biproducts (C : Type u) [category C] [has_zero_morphisms C] where
  has_biproducts_of_shape :
    ∀ (J : Type v) [_inst_4 : DecidableEq J] [_inst_5 : fintype J], has_biproducts_of_shape J C

protected instance has_finite_products_of_has_finite_biproducts (C : Type u) [category C]
    [has_zero_morphisms C] [has_finite_biproducts C] : has_finite_products C :=
  fun (J : Type v) (_x : DecidableEq J) (_x_1 : fintype J) =>
    has_limits_of_shape.mk
      fun (F : discrete J ⥤ C) => has_limit_of_iso (iso.symm discrete.nat_iso_functor)

protected instance has_finite_coproducts_of_has_finite_biproducts (C : Type u) [category C]
    [has_zero_morphisms C] [has_finite_biproducts C] : has_finite_coproducts C :=
  fun (J : Type v) (_x : DecidableEq J) (_x_1 : fintype J) =>
    has_colimits_of_shape.mk fun (F : discrete J ⥤ C) => has_colimit_of_iso discrete.nat_iso_functor

/--
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproduct_iso {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (F : J → C) [has_biproduct F] : ∏ F ≅ ∐ F :=
  is_limit.cone_point_unique_up_to_iso (limit.is_limit (discrete.functor F))
      (biproduct.is_limit F) ≪≫
    is_colimit.cocone_point_unique_up_to_iso (biproduct.is_colimit F)
      (colimit.is_colimit (discrete.functor F))

end category_theory.limits


namespace category_theory.limits


/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
def biproduct {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (f : J → C) [has_biproduct f] : C :=
  bicone.X sorry

prefix:20 "⨁ " => Mathlib.category_theory.limits.biproduct

/-- The projection onto a summand of a biproduct. -/
def biproduct.π {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (f : J → C) [has_biproduct f] (b : J) : ⨁ f ⟶ f b :=
  bicone.π (biproduct.bicone f) b

@[simp] theorem biproduct.bicone_π {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (f : J → C) [has_biproduct f] (b : J) :
    bicone.π (biproduct.bicone f) b = biproduct.π f b :=
  rfl

/-- The inclusion into a summand of a biproduct. -/
def biproduct.ι {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (f : J → C) [has_biproduct f] (b : J) : f b ⟶ ⨁ f :=
  bicone.ι (biproduct.bicone f) b

@[simp] theorem biproduct.bicone_ι {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (f : J → C) [has_biproduct f] (b : J) :
    bicone.ι (biproduct.bicone f) b = biproduct.ι f b :=
  rfl

theorem biproduct.ι_π {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    (f : J → C) [has_biproduct f] (j : J) (j' : J) :
    biproduct.ι f j ≫ biproduct.π f j' =
        dite (j = j') (fun (h : j = j') => eq_to_hom (congr_arg f h)) fun (h : ¬j = j') => 0 :=
  bicone.ι_π (biproduct.bicone f) j j'

@[simp] theorem biproduct.ι_π_self {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (f : J → C) [has_biproduct f] (j : J) :
    biproduct.ι f j ≫ biproduct.π f j = 𝟙 :=
  sorry

@[simp] theorem biproduct.ι_π_ne {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (f : J → C) [has_biproduct f] {j : J} {j' : J} (h : j ≠ j') :
    biproduct.ι f j ≫ biproduct.π f j' = 0 :=
  sorry

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
def biproduct.lift {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    {f : J → C} [has_biproduct f] {P : C} (p : (b : J) → P ⟶ f b) : P ⟶ ⨁ f :=
  is_limit.lift (biproduct.is_limit f) (fan.mk P p)

/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
def biproduct.desc {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    {f : J → C} [has_biproduct f] {P : C} (p : (b : J) → f b ⟶ P) : ⨁ f ⟶ P :=
  is_colimit.desc (biproduct.is_colimit f) (cofan.mk P p)

@[simp] theorem biproduct.lift_π {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {f : J → C} [has_biproduct f] {P : C} (p : (b : J) → P ⟶ f b) (j : J) :
    biproduct.lift p ≫ biproduct.π f j = p j :=
  is_limit.fac (biproduct.is_limit f) (fan.mk P p) j

@[simp] theorem biproduct.ι_desc_assoc {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {f : J → C} [has_biproduct f] {P : C} (p : (b : J) → f b ⟶ P) (j : J)
    {X' : C} (f' : P ⟶ X') : biproduct.ι f j ≫ biproduct.desc p ≫ f' = p j ≫ f' :=
  sorry

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
def biproduct.map {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    [fintype J] {f : J → C} {g : J → C} [has_finite_biproducts C] (p : (b : J) → f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  is_limit.map (bicone.to_cone (biproduct.bicone f)) (biproduct.is_limit g) (discrete.nat_trans p)

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
def biproduct.map' {J : Type v} [DecidableEq J] {C : Type u} [category C] [has_zero_morphisms C]
    [fintype J] {f : J → C} {g : J → C} [has_finite_biproducts C] (p : (b : J) → f b ⟶ g b) :
    ⨁ f ⟶ ⨁ g :=
  is_colimit.map (biproduct.is_colimit f) (bicone.to_cocone (biproduct.bicone g))
    (discrete.nat_trans p)

theorem biproduct.hom_ext {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {f : J → C} [has_biproduct f] {Z : C} (g : Z ⟶ ⨁ f) (h : Z ⟶ ⨁ f)
    (w : ∀ (j : J), g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
  is_limit.hom_ext (biproduct.is_limit f) w

theorem biproduct.hom_ext' {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] {f : J → C} [has_biproduct f] {Z : C} (g : ⨁ f ⟶ Z) (h : ⨁ f ⟶ Z)
    (w : ∀ (j : J), biproduct.ι f j ≫ g = biproduct.ι f j ≫ h) : g = h :=
  is_colimit.hom_ext (biproduct.is_colimit f) w

theorem biproduct.map_eq_map' {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] [fintype J] {f : J → C} {g : J → C} [has_finite_biproducts C]
    (p : (b : J) → f b ⟶ g b) : biproduct.map p = biproduct.map' p :=
  sorry

protected instance biproduct.ι_mono {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (f : J → C) [has_biproduct f] (b : J) : split_mono (biproduct.ι f b) :=
  split_mono.mk
    (biproduct.desc
      fun (b' : J) =>
        dite (b' = b) (fun (h : b' = b) => eq_to_hom (congr_arg f h))
          fun (h : ¬b' = b) => biproduct.ι f b' ≫ biproduct.π f b)

protected instance biproduct.π_epi {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] (f : J → C) [has_biproduct f] (b : J) : split_epi (biproduct.π f b) :=
  split_epi.mk
    (biproduct.lift
      fun (b' : J) =>
        dite (b = b') (fun (h : b = b') => eq_to_hom (congr_arg f h))
          fun (h : ¬b = b') => biproduct.ι f b ≫ biproduct.π f b')

@[simp] theorem biproduct.map_π_assoc {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] [fintype J] {f : J → C} {g : J → C} [has_finite_biproducts C]
    (p : (j : J) → f j ⟶ g j) (j : J) {X' : C} (f' : g j ⟶ X') :
    biproduct.map p ≫ biproduct.π g j ≫ f' = biproduct.π f j ≫ p j ≫ f' :=
  sorry

@[simp] theorem biproduct.ι_map {J : Type v} [DecidableEq J] {C : Type u} [category C]
    [has_zero_morphisms C] [fintype J] {f : J → C} {g : J → C} [has_finite_biproducts C]
    (p : (j : J) → f j ⟶ g j) (j : J) : biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j :=
  sorry

/--
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
structure binary_bicone {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C) where
  X : C
  fst : X ⟶ P
  snd : X ⟶ Q
  inl : P ⟶ X
  inr : Q ⟶ X
  inl_fst' :
    autoParam (inl ≫ fst = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  inl_snd' :
    autoParam (inl ≫ snd = 0)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  inr_fst' :
    autoParam (inr ≫ fst = 0)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  inr_snd' :
    autoParam (inr ≫ snd = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem binary_bicone.inl_fst {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) : binary_bicone.inl c ≫ binary_bicone.fst c = 𝟙 :=
  sorry

@[simp] theorem binary_bicone.inl_snd {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) : binary_bicone.inl c ≫ binary_bicone.snd c = 0 :=
  sorry

@[simp] theorem binary_bicone.inr_fst {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) : binary_bicone.inr c ≫ binary_bicone.fst c = 0 :=
  sorry

@[simp] theorem binary_bicone.inr_snd {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) : binary_bicone.inr c ≫ binary_bicone.snd c = 𝟙 :=
  sorry

@[simp] theorem binary_bicone.inr_fst_assoc {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) {X' : C} (f' : P ⟶ X') :
    binary_bicone.inr c ≫ binary_bicone.fst c ≫ f' = 0 ≫ f' :=
  sorry

namespace binary_bicone


/-- Extract the cone from a binary bicone. -/
def to_cone {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (c : binary_bicone P Q) : cone (pair P Q) :=
  binary_fan.mk (fst c) (snd c)

@[simp] theorem to_cone_X {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (c : binary_bicone P Q) : cone.X (to_cone c) = X c :=
  rfl

@[simp] theorem to_cone_π_app_left {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (c : binary_bicone P Q) : nat_trans.app (cone.π (to_cone c)) walking_pair.left = fst c :=
  rfl

@[simp] theorem to_cone_π_app_right {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (c : binary_bicone P Q) : nat_trans.app (cone.π (to_cone c)) walking_pair.right = snd c :=
  rfl

/-- Extract the cocone from a binary bicone. -/
def to_cocone {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (c : binary_bicone P Q) : cocone (pair P Q) :=
  binary_cofan.mk (inl c) (inr c)

@[simp] theorem to_cocone_X {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (c : binary_bicone P Q) : cocone.X (to_cocone c) = X c :=
  rfl

@[simp] theorem to_cocone_ι_app_left {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) :
    nat_trans.app (cocone.ι (to_cocone c)) walking_pair.left = inl c :=
  rfl

@[simp] theorem to_cocone_ι_app_right {C : Type u} [category C] [has_zero_morphisms C] {P : C}
    {Q : C} (c : binary_bicone P Q) :
    nat_trans.app (cocone.ι (to_cocone c)) walking_pair.right = inr c :=
  rfl

end binary_bicone


namespace bicone


/-- Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simp] theorem to_binary_bicone_snd {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} (b : bicone (functor.obj (pair X Y))) :
    binary_bicone.snd (to_binary_bicone b) = π b walking_pair.right :=
  Eq.refl (binary_bicone.snd (to_binary_bicone b))

/--
If the cone obtained from a bicone over `pair X Y` is a limit cone,
so is the cone obtained by converting that bicone to a binary_bicone, then to a cone.
-/
def to_binary_bicone_is_limit {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {b : bicone (functor.obj (pair X Y))} (c : is_limit (to_cone b)) :
    is_limit (binary_bicone.to_cone (to_binary_bicone b)) :=
  is_limit.mk fun (s : cone (pair X Y)) => is_limit.lift c s

/--
If the cocone obtained from a bicone over `pair X Y` is a colimit cocone,
so is the cocone obtained by converting that bicone to a binary_bicone, then to a cocone.
-/
def to_binary_bicone_is_colimit {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    {b : bicone (functor.obj (pair X Y))} (c : is_colimit (to_cocone b)) :
    is_colimit (binary_bicone.to_cocone (to_binary_bicone b)) :=
  is_colimit.mk fun (s : cocone (pair X Y)) => is_colimit.desc c s

end bicone


/--
A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
structure binary_biproduct_data {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C)
    where
  bicone : binary_bicone P Q
  is_limit : is_limit (binary_bicone.to_cone bicone)
  is_colimit : is_colimit (binary_bicone.to_cocone bicone)

/--
`has_binary_biproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class has_binary_biproduct {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C) where
  mk' :: (exists_binary_biproduct : Nonempty (binary_biproduct_data P Q))

theorem has_binary_biproduct.mk {C : Type u} [category C] [has_zero_morphisms C] {P : C} {Q : C}
    (d : binary_biproduct_data P Q) : has_binary_biproduct P Q :=
  has_binary_biproduct.mk' (Nonempty.intro d)

/--
Use the axiom of choice to extract explicit `binary_biproduct_data F` from `has_binary_biproduct F`.
-/
def get_binary_biproduct_data {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C)
    [has_binary_biproduct P Q] : binary_biproduct_data P Q :=
  Classical.choice has_binary_biproduct.exists_binary_biproduct

/-- A bicone for `P Q ` which is both a limit cone and a colimit cocone. -/
def binary_biproduct.bicone {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C)
    [has_binary_biproduct P Q] : binary_bicone P Q :=
  binary_biproduct_data.bicone (get_binary_biproduct_data P Q)

/-- `binary_biproduct.bicone P Q` is a limit cone. -/
def binary_biproduct.is_limit {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C)
    [has_binary_biproduct P Q] : is_limit (binary_bicone.to_cone (binary_biproduct.bicone P Q)) :=
  binary_biproduct_data.is_limit (get_binary_biproduct_data P Q)

/-- `binary_biproduct.bicone P Q` is a colimit cocone. -/
def binary_biproduct.is_colimit {C : Type u} [category C] [has_zero_morphisms C] (P : C) (Q : C)
    [has_binary_biproduct P Q] :
    is_colimit (binary_bicone.to_cocone (binary_biproduct.bicone P Q)) :=
  binary_biproduct_data.is_colimit (get_binary_biproduct_data P Q)

/--
`has_binary_biproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class has_binary_biproducts (C : Type u) [category C] [has_zero_morphisms C] where
  has_binary_biproduct : ∀ (P Q : C), has_binary_biproduct P Q

/--
A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
theorem has_binary_biproducts_of_finite_biproducts (C : Type u) [category C] [has_zero_morphisms C]
    [has_finite_biproducts C] : has_binary_biproducts C :=
  sorry

protected instance has_binary_biproduct.has_limit_pair {C : Type u} [category C]
    [has_zero_morphisms C] {P : C} {Q : C} [has_binary_biproduct P Q] : has_limit (pair P Q) :=
  has_limit.mk
    (limit_cone.mk (binary_bicone.to_cone (binary_biproduct.bicone P Q))
      (binary_biproduct.is_limit P Q))

protected instance has_binary_biproduct.has_colimit_pair {C : Type u} [category C]
    [has_zero_morphisms C] {P : C} {Q : C} [has_binary_biproduct P Q] : has_colimit (pair P Q) :=
  has_colimit.mk
    (colimit_cocone.mk (binary_bicone.to_cocone (binary_biproduct.bicone P Q))
      (binary_biproduct.is_colimit P Q))

protected instance has_binary_products_of_has_binary_biproducts {C : Type u} [category C]
    [has_zero_morphisms C] [has_binary_biproducts C] : has_binary_products C :=
  has_limits_of_shape.mk
    fun (F : discrete walking_pair ⥤ C) => has_limit_of_iso (iso.symm (diagram_iso_pair F))

protected instance has_binary_coproducts_of_has_binary_biproducts {C : Type u} [category C]
    [has_zero_morphisms C] [has_binary_biproducts C] : has_binary_coproducts C :=
  has_colimits_of_shape.mk
    fun (F : discrete walking_pair ⥤ C) => has_colimit_of_iso (diagram_iso_pair F)

/--
The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprod_iso {C : Type u} [category C] [has_zero_morphisms C] (X : C) (Y : C)
    [has_binary_biproduct X Y] : X ⨯ Y ≅ X ⨿ Y :=
  is_limit.cone_point_unique_up_to_iso (limit.is_limit (pair X Y))
      (binary_biproduct.is_limit X Y) ≪≫
    is_colimit.cocone_point_unique_up_to_iso (binary_biproduct.is_colimit X Y)
      (colimit.is_colimit (pair X Y))

/-- An arbitrary choice of biproduct of a pair of objects. -/
def biprod {C : Type u} [category C] [has_zero_morphisms C] (X : C) (Y : C)
    [has_binary_biproduct X Y] : C :=
  binary_bicone.X (binary_biproduct.bicone X Y)

infixl:20 " ⊞ " => Mathlib.category_theory.limits.biprod

/-- The projection onto the first summand of a binary biproduct. -/
def biprod.fst {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : X ⊞ Y ⟶ X :=
  binary_bicone.fst (binary_biproduct.bicone X Y)

/-- The projection onto the second summand of a binary biproduct. -/
def biprod.snd {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : X ⊞ Y ⟶ Y :=
  binary_bicone.snd (binary_biproduct.bicone X Y)

/-- The inclusion into the first summand of a binary biproduct. -/
def biprod.inl {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : X ⟶ X ⊞ Y :=
  binary_bicone.inl (binary_biproduct.bicone X Y)

/-- The inclusion into the second summand of a binary biproduct. -/
def biprod.inr {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : Y ⟶ X ⊞ Y :=
  binary_bicone.inr (binary_biproduct.bicone X Y)

@[simp] theorem binary_biproduct.bicone_fst {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_binary_biproduct X Y] :
    binary_bicone.fst (binary_biproduct.bicone X Y) = biprod.fst :=
  rfl

@[simp] theorem binary_biproduct.bicone_snd {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_binary_biproduct X Y] :
    binary_bicone.snd (binary_biproduct.bicone X Y) = biprod.snd :=
  rfl

@[simp] theorem binary_biproduct.bicone_inl {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_binary_biproduct X Y] :
    binary_bicone.inl (binary_biproduct.bicone X Y) = biprod.inl :=
  rfl

@[simp] theorem binary_biproduct.bicone_inr {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_binary_biproduct X Y] :
    binary_bicone.inr (binary_biproduct.bicone X Y) = biprod.inr :=
  rfl

@[simp] theorem biprod.inl_fst {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : biprod.inl ≫ biprod.fst = 𝟙 :=
  binary_bicone.inl_fst (binary_biproduct.bicone X Y)

@[simp] theorem biprod.inl_snd {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : biprod.inl ≫ biprod.snd = 0 :=
  binary_bicone.inl_snd (binary_biproduct.bicone X Y)

@[simp] theorem biprod.inr_fst_assoc {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_binary_biproduct X Y] {X' : C} (f' : X ⟶ X') :
    biprod.inr ≫ biprod.fst ≫ f' = 0 ≫ f' :=
  sorry

@[simp] theorem biprod.inr_snd_assoc {C : Type u} [category C] [has_zero_morphisms C] {X : C}
    {Y : C} [has_binary_biproduct X Y] {X' : C} (f' : Y ⟶ X') : biprod.inr ≫ biprod.snd ≫ f' = f' :=
  sorry

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
def biprod.lift {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C} {Y : C}
    [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  is_limit.lift (binary_biproduct.is_limit X Y) (binary_fan.mk f g)

/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
def biprod.desc {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C} {Y : C}
    [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  is_colimit.desc (binary_biproduct.is_colimit X Y) (binary_cofan.mk f g)

@[simp] theorem biprod.lift_fst_assoc {C : Type u} [category C] [has_zero_morphisms C] {W : C}
    {X : C} {Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) {X' : C} (f' : X ⟶ X') :
    biprod.lift f g ≫ biprod.fst ≫ f' = f ≫ f' :=
  sorry

@[simp] theorem biprod.lift_snd_assoc {C : Type u} [category C] [has_zero_morphisms C] {W : C}
    {X : C} {Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) {X' : C} (f' : Y ⟶ X') :
    biprod.lift f g ≫ biprod.snd ≫ f' = g ≫ f' :=
  sorry

@[simp] theorem biprod.inl_desc_assoc {C : Type u} [category C] [has_zero_morphisms C] {W : C}
    {X : C} {Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) {X' : C} (f' : W ⟶ X') :
    biprod.inl ≫ biprod.desc f g ≫ f' = f ≫ f' :=
  sorry

@[simp] theorem biprod.inr_desc_assoc {C : Type u} [category C] [has_zero_morphisms C] {W : C}
    {X : C} {Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) {X' : C} (f' : W ⟶ X') :
    biprod.inr ≫ biprod.desc f g ≫ f' = g ≫ f' :=
  sorry

protected instance biprod.mono_lift_of_mono_left {C : Type u} [category C] [has_zero_morphisms C]
    {W : C} {X : C} {Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [mono f] :
    mono (biprod.lift f g) :=
  mono_of_mono_fac (biprod.lift_fst f g)

protected instance biprod.mono_lift_of_mono_right {C : Type u} [category C] [has_zero_morphisms C]
    {W : C} {X : C} {Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) [mono g] :
    mono (biprod.lift f g) :=
  mono_of_mono_fac (biprod.lift_snd f g)

protected instance biprod.epi_desc_of_epi_left {C : Type u} [category C] [has_zero_morphisms C]
    {W : C} {X : C} {Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [epi f] :
    epi (biprod.desc f g) :=
  epi_of_epi_fac (biprod.inl_desc f g)

protected instance biprod.epi_desc_of_epi_right {C : Type u} [category C] [has_zero_morphisms C]
    {W : C} {X : C} {Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [epi g] :
    epi (biprod.desc f g) :=
  epi_of_epi_fac (biprod.inr_desc f g)

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
def biprod.map {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  is_limit.map (binary_bicone.to_cone (binary_biproduct.bicone W X)) (binary_biproduct.is_limit Y Z)
    (map_pair f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
def biprod.map' {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  is_colimit.map (binary_biproduct.is_colimit W X)
    (binary_bicone.to_cocone (binary_biproduct.bicone Y Z)) (map_pair f g)

theorem biprod.hom_ext {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    [has_binary_biproduct X Y] (f : Z ⟶ X ⊞ Y) (g : Z ⟶ X ⊞ Y)
    (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  binary_fan.is_limit.hom_ext (binary_biproduct.is_limit X Y) h₀ h₁

theorem biprod.hom_ext' {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C} {Z : C}
    [has_binary_biproduct X Y] (f : X ⊞ Y ⟶ Z) (g : X ⊞ Y ⟶ Z)
    (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  binary_cofan.is_colimit.hom_ext (binary_biproduct.is_colimit X Y) h₀ h₁

theorem biprod.map_eq_map' {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C} {Y : C}
    {Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g = biprod.map' f g :=
  sorry

protected instance biprod.inl_mono {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : split_mono biprod.inl :=
  split_mono.mk (biprod.desc 𝟙 (biprod.inr ≫ biprod.fst))

protected instance biprod.inr_mono {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : split_mono biprod.inr :=
  split_mono.mk (biprod.desc (biprod.inl ≫ biprod.snd) 𝟙)

protected instance biprod.fst_epi {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : split_epi biprod.fst :=
  split_epi.mk (biprod.lift 𝟙 (biprod.inl ≫ biprod.snd))

protected instance biprod.snd_epi {C : Type u} [category C] [has_zero_morphisms C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : split_epi biprod.snd :=
  split_epi.mk (biprod.lift (biprod.inr ≫ biprod.fst) 𝟙)

@[simp] theorem biprod.map_fst {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C}
    {Y : C} {Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  is_limit.map_π (binary_bicone.to_cone (binary_biproduct.bicone W X))
    (binary_biproduct.is_limit Y Z) (map_pair f g) walking_pair.left

@[simp] theorem biprod.map_snd_assoc {C : Type u} [category C] [has_zero_morphisms C] {W : C}
    {X : C} {Y : C} {Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) {X' : C} (f' : Z ⟶ X') : biprod.map f g ≫ biprod.snd ≫ f' = biprod.snd ≫ g ≫ f' :=
  sorry

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,

-- we need to provide additional `simp` lemmas.

@[simp] theorem biprod.inl_map_assoc {C : Type u} [category C] [has_zero_morphisms C] {W : C}
    {X : C} {Y : C} {Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) {X' : C} (f' : Y ⊞ Z ⟶ X') :
    biprod.inl ≫ biprod.map f g ≫ f' = f ≫ biprod.inl ≫ f' :=
  sorry

@[simp] theorem biprod.inr_map {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C}
    {Y : C} {Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    biprod.inr ≫ biprod.map f g = g ≫ biprod.inr :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (biprod.inr ≫ biprod.map f g = g ≫ biprod.inr))
        (biprod.map_eq_map' f g)))
    (is_colimit.ι_map (binary_biproduct.is_colimit W X)
      (binary_bicone.to_cocone (binary_biproduct.bicone Y Z)) (map_pair f g) walking_pair.right)

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simp] theorem biprod.map_iso_hom {C : Type u} [category C] [has_zero_morphisms C] {W : C} {X : C}
    {Y : C} {Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    iso.hom (biprod.map_iso f g) = biprod.map (iso.hom f) (iso.hom g) :=
  Eq.refl (iso.hom (biprod.map_iso f g))

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simp] theorem biprod.braiding_hom {C : Type u} [category C] [has_zero_morphisms C]
    [has_binary_biproducts C] (P : C) (Q : C) :
    iso.hom (biprod.braiding P Q) = biprod.lift biprod.snd biprod.fst :=
  Eq.refl (iso.hom (biprod.braiding P Q))

/--
An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
def biprod.braiding' {C : Type u} [category C] [has_zero_morphisms C] [has_binary_biproducts C]
    (P : C) (Q : C) : P ⊞ Q ≅ Q ⊞ P :=
  iso.mk (biprod.desc biprod.inr biprod.inl) (biprod.desc biprod.inr biprod.inl)

theorem biprod.braiding'_eq_braiding {C : Type u} [category C] [has_zero_morphisms C]
    [has_binary_biproducts C] {P : C} {Q : C} : biprod.braiding' P Q = biprod.braiding P Q :=
  sorry

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
theorem biprod.braid_natural_assoc {C : Type u} [category C] [has_zero_morphisms C]
    [has_binary_biproducts C] {W : C} {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Z ⟶ W) {X' : C}
    (f' : W ⊞ Y ⟶ X') :
    biprod.map f g ≫ iso.hom (biprod.braiding Y W) ≫ f' =
        iso.hom (biprod.braiding X Z) ≫ biprod.map g f ≫ f' :=
  sorry

theorem biprod.braiding_map_braiding {C : Type u} [category C] [has_zero_morphisms C]
    [has_binary_biproducts C] {W : C} {X : C} {Y : C} {Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    iso.hom (biprod.braiding X W) ≫ biprod.map f g ≫ iso.hom (biprod.braiding Y Z) =
        biprod.map g f :=
  sorry

@[simp] theorem biprod.symmetry'_assoc {C : Type u} [category C] [has_zero_morphisms C]
    [has_binary_biproducts C] (P : C) (Q : C) {X' : C} (f' : P ⊞ Q ⟶ X') :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst ≫ f' = f' :=
  sorry

/-- The braiding isomorphism is symmetric. -/
theorem biprod.symmetry_assoc {C : Type u} [category C] [has_zero_morphisms C]
    [has_binary_biproducts C] (P : C) (Q : C) {X' : C} (f' : P ⊞ Q ⟶ X') :
    iso.hom (biprod.braiding P Q) ≫ iso.hom (biprod.braiding Q P) ≫ f' = f' :=
  sorry

-- TODO:

-- If someone is interested, they could provide the constructions:

--   has_binary_biproducts ↔ has_finite_biproducts

end category_theory.limits


namespace category_theory.limits


/--
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem has_biproduct_of_total {C : Type u} [category C] [preadditive C] {J : Type v}
    [DecidableEq J] [fintype J] {f : J → C} (b : bicone f)
    (total : (finset.sum finset.univ fun (j : J) => bicone.π b j ≫ bicone.ι b j) = 𝟙) :
    has_biproduct f :=
  sorry

/-- In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem has_biproduct.of_has_product {C : Type u} [category C] [preadditive C] {J : Type v}
    [DecidableEq J] [fintype J] (f : J → C) [has_product f] : has_biproduct f :=
  sorry

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
theorem has_biproduct.of_has_coproduct {C : Type u} [category C] [preadditive C] {J : Type v}
    [DecidableEq J] [fintype J] (f : J → C) [has_coproduct f] : has_biproduct f :=
  sorry

/-- A preadditive category with finite products has finite biproducts. -/
theorem has_finite_biproducts.of_has_finite_products {C : Type u} [category C] [preadditive C]
    [has_finite_products C] : has_finite_biproducts C :=
  has_finite_biproducts.mk
    fun (J : Type v) (_x : DecidableEq J) (_x_1 : fintype J) =>
      has_biproducts_of_shape.mk fun (F : J → C) => has_biproduct.of_has_product F

/-- A preadditive category with finite coproducts has finite biproducts. -/
theorem has_finite_biproducts.of_has_finite_coproducts {C : Type u} [category C] [preadditive C]
    [has_finite_coproducts C] : has_finite_biproducts C :=
  has_finite_biproducts.mk
    fun (J : Type v) (_x : DecidableEq J) (_x_1 : fintype J) =>
      has_biproducts_of_shape.mk fun (F : J → C) => has_biproduct.of_has_coproduct F

/--
In any preadditive category, any biproduct satsifies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp] theorem biproduct.total {C : Type u} [category C] [preadditive C] {J : Type v}
    [DecidableEq J] [fintype J] {f : J → C} [has_biproduct f] :
    (finset.sum finset.univ fun (j : J) => biproduct.π f j ≫ biproduct.ι f j) = 𝟙 :=
  sorry

theorem biproduct.lift_eq {C : Type u} [category C] [preadditive C] {J : Type v} [DecidableEq J]
    [fintype J] {f : J → C} [has_biproduct f] {T : C} {g : (j : J) → T ⟶ f j} :
    biproduct.lift g = finset.sum finset.univ fun (j : J) => g j ≫ biproduct.ι f j :=
  sorry

theorem biproduct.desc_eq {C : Type u} [category C] [preadditive C] {J : Type v} [DecidableEq J]
    [fintype J] {f : J → C} [has_biproduct f] {T : C} {g : (j : J) → f j ⟶ T} :
    biproduct.desc g = finset.sum finset.univ fun (j : J) => biproduct.π f j ≫ g j :=
  sorry

@[simp] theorem biproduct.lift_desc {C : Type u} [category C] [preadditive C] {J : Type v}
    [DecidableEq J] [fintype J] {f : J → C} [has_biproduct f] {T : C} {U : C}
    {g : (j : J) → T ⟶ f j} {h : (j : J) → f j ⟶ U} :
    biproduct.lift g ≫ biproduct.desc h = finset.sum finset.univ fun (j : J) => g j ≫ h j :=
  sorry

theorem biproduct.map_eq {C : Type u} [category C] [preadditive C] {J : Type v} [DecidableEq J]
    [fintype J] [has_finite_biproducts C] {f : J → C} {g : J → C} {h : (j : J) → f j ⟶ g j} :
    biproduct.map h =
        finset.sum finset.univ fun (j : J) => biproduct.π f j ≫ h j ≫ biproduct.ι g j :=
  sorry

/--
In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
theorem has_binary_biproduct_of_total {C : Type u} [category C] [preadditive C] {X : C} {Y : C}
    (b : binary_bicone X Y)
    (total :
      binary_bicone.fst b ≫ binary_bicone.inl b + binary_bicone.snd b ≫ binary_bicone.inr b = 𝟙) :
    has_binary_biproduct X Y :=
  sorry

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem has_binary_biproduct.of_has_binary_product {C : Type u} [category C] [preadditive C] (X : C)
    (Y : C) [has_binary_product X Y] : has_binary_biproduct X Y :=
  sorry

/-- In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
theorem has_binary_biproducts.of_has_binary_products {C : Type u} [category C] [preadditive C]
    [has_binary_products C] : has_binary_biproducts C :=
  has_binary_biproducts.mk fun (X Y : C) => has_binary_biproduct.of_has_binary_product X Y

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
theorem has_binary_biproduct.of_has_binary_coproduct {C : Type u} [category C] [preadditive C]
    (X : C) (Y : C) [has_binary_coproduct X Y] : has_binary_biproduct X Y :=
  sorry

/-- In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
theorem has_binary_biproducts.of_has_binary_coproducts {C : Type u} [category C] [preadditive C]
    [has_binary_coproducts C] : has_binary_biproducts C :=
  has_binary_biproducts.mk fun (X Y : C) => has_binary_biproduct.of_has_binary_coproduct X Y

/--
In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp] theorem biprod.total {C : Type u} [category C] [preadditive C] {X : C} {Y : C}
    [has_binary_biproduct X Y] : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 :=
  sorry

theorem biprod.lift_eq {C : Type u} [category C] [preadditive C] {X : C} {Y : C}
    [has_binary_biproduct X Y] {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
    biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr :=
  sorry

theorem biprod.desc_eq {C : Type u} [category C] [preadditive C] {X : C} {Y : C}
    [has_binary_biproduct X Y] {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
    biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g :=
  sorry

@[simp] theorem biprod.lift_desc {C : Type u} [category C] [preadditive C] {X : C} {Y : C}
    [has_binary_biproduct X Y] {T : C} {U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
    biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i :=
  sorry

theorem biprod.map_eq {C : Type u} [category C] [preadditive C] [has_binary_biproducts C] {W : C}
    {X : C} {Y : C} {Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
    biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr :=
  sorry

end Mathlib