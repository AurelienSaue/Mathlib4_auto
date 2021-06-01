/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.category_theory.discrete_category
import Mathlib.category_theory.epi_mono
import Mathlib.PostPort

universes v l u_1 u_2 u u₂ 

namespace Mathlib

/-!
# Binary (co)products

We define a category `walking_pair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `has_binary_products` and `has_binary_coproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.

## References
* [Stacks: Products of pairs](https://stacks.math.columbia.edu/tag/001R)
* [Stacks: coproducts of pairs](https://stacks.math.columbia.edu/tag/04AN)
-/

namespace category_theory.limits


/-- The type of objects for the diagram indexing a binary (co)product. -/
inductive walking_pair where
| left : walking_pair
| right : walking_pair

/--
The equivalence swapping left and right.
-/
def walking_pair.swap : walking_pair ≃ walking_pair :=
  equiv.mk (fun (j : walking_pair) => walking_pair.rec_on j walking_pair.right walking_pair.left)
    (fun (j : walking_pair) => walking_pair.rec_on j walking_pair.right walking_pair.left) sorry
    sorry

@[simp] theorem walking_pair.swap_apply_left :
    coe_fn walking_pair.swap walking_pair.left = walking_pair.right :=
  rfl

@[simp] theorem walking_pair.swap_apply_right :
    coe_fn walking_pair.swap walking_pair.right = walking_pair.left :=
  rfl

@[simp] theorem walking_pair.swap_symm_apply_tt :
    coe_fn (equiv.symm walking_pair.swap) walking_pair.left = walking_pair.right :=
  rfl

@[simp] theorem walking_pair.swap_symm_apply_ff :
    coe_fn (equiv.symm walking_pair.swap) walking_pair.right = walking_pair.left :=
  rfl

/--
An equivalence from `walking_pair` to `bool`, sometimes useful when reindexing limits.
-/
def walking_pair.equiv_bool : walking_pair ≃ Bool :=
  equiv.mk (fun (j : walking_pair) => walking_pair.rec_on j tt false)
    (fun (b : Bool) => bool.rec_on b walking_pair.right walking_pair.left) sorry sorry

@[simp] theorem walking_pair.equiv_bool_apply_left :
    coe_fn walking_pair.equiv_bool walking_pair.left = tt :=
  rfl

@[simp] theorem walking_pair.equiv_bool_apply_right :
    coe_fn walking_pair.equiv_bool walking_pair.right = false :=
  rfl

@[simp] theorem walking_pair.equiv_bool_symm_apply_tt :
    coe_fn (equiv.symm walking_pair.equiv_bool) tt = walking_pair.left :=
  rfl

@[simp] theorem walking_pair.equiv_bool_symm_apply_ff :
    coe_fn (equiv.symm walking_pair.equiv_bool) false = walking_pair.right :=
  rfl

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair {C : Type u} [category C] (X : C) (Y : C) : discrete walking_pair ⥤ C :=
  discrete.functor fun (j : walking_pair) => walking_pair.cases_on j X Y

@[simp] theorem pair_obj_left {C : Type u} [category C] (X : C) (Y : C) :
    functor.obj (pair X Y) walking_pair.left = X :=
  rfl

@[simp] theorem pair_obj_right {C : Type u} [category C] (X : C) (Y : C) :
    functor.obj (pair X Y) walking_pair.right = Y :=
  rfl

/-- The natural transformation between two functors out of the walking pair, specified by its components. -/
def map_pair {C : Type u} [category C] {F : discrete walking_pair ⥤ C}
    {G : discrete walking_pair ⥤ C}
    (f : functor.obj F walking_pair.left ⟶ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ⟶ functor.obj G walking_pair.right) : F ⟶ G :=
  nat_trans.mk fun (j : discrete walking_pair) => walking_pair.cases_on j f g

@[simp] theorem map_pair_left {C : Type u} [category C] {F : discrete walking_pair ⥤ C}
    {G : discrete walking_pair ⥤ C}
    (f : functor.obj F walking_pair.left ⟶ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ⟶ functor.obj G walking_pair.right) :
    nat_trans.app (map_pair f g) walking_pair.left = f :=
  rfl

@[simp] theorem map_pair_right {C : Type u} [category C] {F : discrete walking_pair ⥤ C}
    {G : discrete walking_pair ⥤ C}
    (f : functor.obj F walking_pair.left ⟶ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ⟶ functor.obj G walking_pair.right) :
    nat_trans.app (map_pair f g) walking_pair.right = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its components. -/
def map_pair_iso {C : Type u} [category C] {F : discrete walking_pair ⥤ C}
    {G : discrete walking_pair ⥤ C}
    (f : functor.obj F walking_pair.left ≅ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ≅ functor.obj G walking_pair.right) : F ≅ G :=
  nat_iso.of_components (fun (j : discrete walking_pair) => walking_pair.cases_on j f g) sorry

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simp] theorem diagram_iso_pair_inv_app {C : Type u} [category C] (F : discrete walking_pair ⥤ C)
    (X : discrete walking_pair) :
    nat_trans.app (iso.inv (diagram_iso_pair F)) X =
        iso.inv
          (walking_pair.rec (iso.refl (functor.obj F walking_pair.left))
            (iso.refl (functor.obj F walking_pair.right)) X) :=
  Eq.refl
    (iso.inv
      (walking_pair.rec (iso.refl (functor.obj F walking_pair.left))
        (iso.refl (functor.obj F walking_pair.right)) X))

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
def pair_comp {C : Type u} [category C] {D : Type u} [category D] (X : C) (Y : C) (F : C ⥤ D) :
    pair X Y ⋙ F ≅ pair (functor.obj F X) (functor.obj F Y) :=
  diagram_iso_pair (pair X Y ⋙ F)

/-- A binary fan is just a cone on a diagram indexing a product. -/
def binary_fan {C : Type u} [category C] (X : C) (Y : C) := cone (pair X Y)

/-- The first projection of a binary fan. -/
def binary_fan.fst {C : Type u} [category C] {X : C} {Y : C} (s : binary_fan X Y) :
    functor.obj (functor.obj (functor.const (discrete walking_pair)) (cone.X s)) walking_pair.left ⟶
        functor.obj (pair X Y) walking_pair.left :=
  nat_trans.app (cone.π s) walking_pair.left

/-- The second projection of a binary fan. -/
def binary_fan.snd {C : Type u} [category C] {X : C} {Y : C} (s : binary_fan X Y) :
    functor.obj (functor.obj (functor.const (discrete walking_pair)) (cone.X s))
          walking_pair.right ⟶
        functor.obj (pair X Y) walking_pair.right :=
  nat_trans.app (cone.π s) walking_pair.right

@[simp] theorem binary_fan.π_app_left {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_fan X Y) : nat_trans.app (cone.π s) walking_pair.left = binary_fan.fst s :=
  rfl

@[simp] theorem binary_fan.π_app_right {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_fan X Y) : nat_trans.app (cone.π s) walking_pair.right = binary_fan.snd s :=
  rfl

theorem binary_fan.is_limit.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_fan X Y} (h : is_limit s) {f : W ⟶ cone.X s} {g : W ⟶ cone.X s}
    (h₁ : f ≫ binary_fan.fst s = g ≫ binary_fan.fst s)
    (h₂ : f ≫ binary_fan.snd s = g ≫ binary_fan.snd s) : f = g :=
  is_limit.hom_ext h fun (j : discrete walking_pair) => walking_pair.cases_on j h₁ h₂

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
def binary_cofan {C : Type u} [category C] (X : C) (Y : C) := cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
def binary_cofan.inl {C : Type u} [category C] {X : C} {Y : C} (s : binary_cofan X Y) :
    functor.obj (pair X Y) walking_pair.left ⟶
        functor.obj (functor.obj (functor.const (discrete walking_pair)) (cocone.X s))
          walking_pair.left :=
  nat_trans.app (cocone.ι s) walking_pair.left

/-- The second inclusion of a binary cofan. -/
def binary_cofan.inr {C : Type u} [category C] {X : C} {Y : C} (s : binary_cofan X Y) :
    functor.obj (pair X Y) walking_pair.right ⟶
        functor.obj (functor.obj (functor.const (discrete walking_pair)) (cocone.X s))
          walking_pair.right :=
  nat_trans.app (cocone.ι s) walking_pair.right

@[simp] theorem binary_cofan.ι_app_left {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_cofan X Y) : nat_trans.app (cocone.ι s) walking_pair.left = binary_cofan.inl s :=
  rfl

@[simp] theorem binary_cofan.ι_app_right {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_cofan X Y) : nat_trans.app (cocone.ι s) walking_pair.right = binary_cofan.inr s :=
  rfl

theorem binary_cofan.is_colimit.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_cofan X Y} (h : is_colimit s) {f : cocone.X s ⟶ W} {g : cocone.X s ⟶ W}
    (h₁ : binary_cofan.inl s ≫ f = binary_cofan.inl s ≫ g)
    (h₂ : binary_cofan.inr s ≫ f = binary_cofan.inr s ≫ g) : f = g :=
  is_colimit.hom_ext h fun (j : discrete walking_pair) => walking_pair.cases_on j h₁ h₂

/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
def binary_fan.mk {C : Type u} [category C] {X : C} {Y : C} {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
    binary_fan X Y :=
  cone.mk P (nat_trans.mk fun (j : discrete walking_pair) => walking_pair.cases_on j π₁ π₂)

/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
def binary_cofan.mk {C : Type u} [category C] {X : C} {Y : C} {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    binary_cofan X Y :=
  cocone.mk P (nat_trans.mk fun (j : discrete walking_pair) => walking_pair.cases_on j ι₁ ι₂)

@[simp] theorem binary_fan.mk_π_app_left {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
    nat_trans.app (cone.π (binary_fan.mk π₁ π₂)) walking_pair.left = π₁ :=
  rfl

@[simp] theorem binary_fan.mk_π_app_right {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
    nat_trans.app (cone.π (binary_fan.mk π₁ π₂)) walking_pair.right = π₂ :=
  rfl

@[simp] theorem binary_cofan.mk_ι_app_left {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    nat_trans.app (cocone.ι (binary_cofan.mk ι₁ ι₂)) walking_pair.left = ι₁ :=
  rfl

@[simp] theorem binary_cofan.mk_ι_app_right {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
    nat_trans.app (cocone.ι (binary_cofan.mk ι₁ ι₂)) walking_pair.right = ι₂ :=
  rfl

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
    `g : W ⟶ Y` induces a morphism `l : W ⟶ s.X` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
    -/
@[simp] theorem binary_fan.is_limit.lift'_coe {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_fan X Y} (h : is_limit s) (f : W ⟶ X) (g : W ⟶ Y) :
    ↑(binary_fan.is_limit.lift' h f g) = is_limit.lift h (binary_fan.mk f g) :=
  Eq.refl ↑(binary_fan.is_limit.lift' h f g)

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : s.X ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
    -/
@[simp] theorem binary_cofan.is_colimit.desc'_coe {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_cofan X Y} (h : is_colimit s) (f : X ⟶ W) (g : Y ⟶ W) :
    ↑(binary_cofan.is_colimit.desc' h f g) = is_colimit.desc h (binary_cofan.mk f g) :=
  Eq.refl ↑(binary_cofan.is_colimit.desc' h f g)

/-- An abbreviation for `has_limit (pair X Y)`. -/
/-- An abbreviation for `has_colimit (pair X Y)`. -/
def has_binary_product {C : Type u} [category C] (X : C) (Y : C) := has_limit (pair X Y)

def has_binary_coproduct {C : Type u} [category C] (X : C) (Y : C) := has_colimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or
    `X ⨯ Y`. -/
def prod {C : Type u} [category C] (X : C) (Y : C) [has_binary_product X Y] : C := limit (pair X Y)

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y ` or
    `X ⨿ Y`. -/
def coprod {C : Type u} [category C] (X : C) (Y : C) [has_binary_coproduct X Y] : C :=
  colimit (pair X Y)

infixl:20 " ⨯ " => Mathlib.category_theory.limits.prod

infixl:20 " ⨿ " => Mathlib.category_theory.limits.coprod

/-- The projection map to the first component of the product. -/
def prod.fst {C : Type u} [category C] {X : C} {Y : C} [has_binary_product X Y] : X ⨯ Y ⟶ X :=
  limit.π (pair X Y) walking_pair.left

/-- The projecton map to the second component of the product. -/
def prod.snd {C : Type u} [category C] {X : C} {Y : C} [has_binary_product X Y] : X ⨯ Y ⟶ Y :=
  limit.π (pair X Y) walking_pair.right

/-- The inclusion map from the first component of the coproduct. -/
def coprod.inl {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X Y] : X ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) walking_pair.left

/-- The inclusion map from the second component of the coproduct. -/
def coprod.inr {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X Y] : Y ⟶ X ⨿ Y :=
  colimit.ι (pair X Y) walking_pair.right

/-- The binary fan constructed from the projection maps is a limit. -/
def prod_is_prod {C : Type u} [category C] (X : C) (Y : C) [has_binary_product X Y] :
    is_limit (binary_fan.mk prod.fst prod.snd) :=
  is_limit.of_iso_limit (limit.is_limit (pair X Y))
    (cones.ext (iso.refl (cone.X (limit.cone (pair X Y)))) sorry)

/-- The binary cofan constructed from the coprojection maps is a colimit. -/
def coprod_is_coprod {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X Y] :
    is_colimit (binary_cofan.mk coprod.inl coprod.inr) :=
  is_colimit.of_iso_colimit (colimit.is_colimit (pair X Y))
    (cocones.ext (iso.refl (cocone.X (colimit.cocone (pair X Y)))) sorry)

theorem prod.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_product X Y]
    {f : W ⟶ X ⨯ Y} {g : W ⟶ X ⨯ Y} (h₁ : f ≫ prod.fst = g ≫ prod.fst)
    (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
  binary_fan.is_limit.hom_ext (limit.is_limit (pair X Y)) h₁ h₂

theorem coprod.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_coproduct X Y]
    {f : X ⨿ Y ⟶ W} {g : X ⨿ Y ⟶ W} (h₁ : coprod.inl ≫ f = coprod.inl ≫ g)
    (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
  binary_cofan.is_colimit.hom_ext (colimit.is_colimit (pair X Y)) h₁ h₂

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
def prod.lift {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_product X Y] (f : W ⟶ X)
    (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
  limit.lift (pair X Y) (binary_fan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
def diag {C : Type u} [category C] (X : C) [has_binary_product X X] : X ⟶ X ⨯ X := prod.lift 𝟙 𝟙

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/
def coprod.desc {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_coproduct X Y]
    (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
  colimit.desc (pair X Y) (binary_cofan.mk f g)

/-- codiagonal arrow of the binary coproduct -/
def codiag {C : Type u} [category C] (X : C) [has_binary_coproduct X X] : X ⨿ X ⟶ X :=
  coprod.desc 𝟙 𝟙

@[simp] theorem prod.lift_fst_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) {X' : C} (f' : X ⟶ X') :
    prod.lift f g ≫ prod.fst ≫ f' = f ≫ f' :=
  sorry

@[simp] theorem prod.lift_snd {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) : prod.lift f g ≫ prod.snd = g :=
  limit.lift_π (binary_fan.mk f g) walking_pair.right

-- The simp linter says simp can prove the reassoc version of this lemma.

theorem coprod.inl_desc_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) {X' : C} (f' : W ⟶ X') :
    coprod.inl ≫ coprod.desc f g ≫ f' = f ≫ f' :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

theorem coprod.inr_desc_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) {X' : C} (f' : W ⟶ X') :
    coprod.inr ≫ coprod.desc f g ≫ f' = g ≫ f' :=
  sorry

protected instance prod.mono_lift_of_mono_left {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) [mono f] : mono (prod.lift f g) :=
  mono_of_mono_fac (prod.lift_fst f g)

protected instance prod.mono_lift_of_mono_right {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) [mono g] : mono (prod.lift f g) :=
  mono_of_mono_fac (prod.lift_snd f g)

protected instance coprod.epi_desc_of_epi_left {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [epi f] : epi (coprod.desc f g) :=
  epi_of_epi_fac (coprod.inl_desc f g)

protected instance coprod.epi_desc_of_epi_right {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) [epi g] : epi (coprod.desc f g) :=
  epi_of_epi_fac (coprod.inr_desc f g)

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ prod.fst = f` and `l ≫ prod.snd = g`. -/
def prod.lift' {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_product X Y]
    (f : W ⟶ X) (g : W ⟶ Y) : Subtype fun (l : W ⟶ X ⨯ Y) => l ≫ prod.fst = f ∧ l ≫ prod.snd = g :=
  { val := prod.lift f g, property := sorry }

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
    `coprod.inr ≫ l = g`. -/
def coprod.desc' {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_coproduct X Y]
    (f : X ⟶ W) (g : Y ⟶ W) :
    Subtype fun (l : X ⨿ Y ⟶ W) => coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g :=
  { val := coprod.desc f g, property := sorry }

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
def prod.map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} [has_binary_product W X]
    [has_binary_product Y Z] (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
  lim_map (map_pair f g)

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/
def coprod.map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} [has_binary_coproduct W X]
    [has_binary_coproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
  colim_map (map_pair f g)

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.

theorem prod.comp_lift_assoc {C : Type u} [category C] {V : C} {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) {X' : C} (f' : X ⨯ Y ⟶ X') :
    f ≫ prod.lift g h ≫ f' = prod.lift (f ≫ g) (f ≫ h) ≫ f' :=
  sorry

theorem prod.comp_diag {C : Type u} [category C] {X : C} {Y : C} [has_binary_product Y Y]
    (f : X ⟶ Y) : f ≫ diag Y = prod.lift f f :=
  sorry

@[simp] theorem prod.map_fst {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    prod.map f g ≫ prod.fst = prod.fst ≫ f :=
  lim_map_π (map_pair f g) walking_pair.left

@[simp] theorem prod.map_snd_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ⟶ Y) (g : X ⟶ Z) {X' : C}
    (f' : Z ⟶ X') : prod.map f g ≫ prod.snd ≫ f' = prod.snd ≫ g ≫ f' :=
  sorry

@[simp] theorem prod.map_id_id {C : Type u} [category C] {X : C} {Y : C} [has_binary_product X Y] :
    prod.map 𝟙 𝟙 = 𝟙 :=
  sorry

@[simp] theorem prod.lift_fst_snd {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_product X Y] : prod.lift prod.fst prod.snd = 𝟙 :=
  sorry

@[simp] theorem prod.lift_map {C : Type u} [category C] {V : C} {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y)
    (k : X ⟶ Z) : prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) :=
  sorry

@[simp] theorem prod.lift_fst_comp_snd_comp {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {Z : C} [has_binary_product W Y] [has_binary_product X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    prod.lift (prod.fst ≫ g) (prod.snd ≫ g') = prod.map g g' :=
  sorry

-- We take the right hand side here to be simp normal form, as this way composition lemmas for

-- `f ≫ h` and `g ≫ k` can fire (eg `id_comp`) , while `map_fst` and `map_snd` can still work just

-- as well.

@[simp] theorem prod.map_map_assoc {C : Type u} [category C] {A₁ : C} {A₂ : C} {A₃ : C} {B₁ : C}
    {B₂ : C} {B₃ : C} [has_binary_product A₁ B₁] [has_binary_product A₂ B₂]
    [has_binary_product A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) {X' : C}
    (f' : A₃ ⨯ B₃ ⟶ X') : prod.map f g ≫ prod.map h k ≫ f' = prod.map (f ≫ h) (g ≫ k) ≫ f' :=
  sorry

-- TODO: is it necessary to weaken the assumption here?

theorem prod.map_swap {C : Type u} [category C] {A : C} {B : C} {X : C} {Y : C} (f : A ⟶ B)
    (g : X ⟶ Y) [has_limits_of_shape (discrete walking_pair) C] :
    prod.map 𝟙 f ≫ prod.map g 𝟙 = prod.map g 𝟙 ≫ prod.map 𝟙 f :=
  sorry

theorem prod.map_comp_id {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [has_binary_product X W] [has_binary_product Z W] [has_binary_product Y W] :
    prod.map (f ≫ g) 𝟙 = prod.map f 𝟙 ≫ prod.map g 𝟙 :=
  sorry

theorem prod.map_id_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [has_binary_product W X] [has_binary_product W Y] [has_binary_product W Z] :
    prod.map 𝟙 (f ≫ g) = prod.map 𝟙 f ≫ prod.map 𝟙 g :=
  sorry

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : X ≅ Z` induces an isomorphism `prod.map_iso f g : W ⨯ X ≅ Y ⨯ Z`. -/
@[simp] theorem prod.map_iso_inv {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    iso.inv (prod.map_iso f g) = prod.map (iso.inv f) (iso.inv g) :=
  Eq.refl (iso.inv (prod.map_iso f g))

protected instance is_iso_prod {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ⟶ Y) (g : X ⟶ Z) [is_iso f]
    [is_iso g] : is_iso (prod.map f g) :=
  is_iso.of_iso (prod.map_iso (as_iso f) (as_iso g))

@[simp] theorem prod.diag_map {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_binary_product X X] [has_binary_product Y Y] : diag X ≫ prod.map f f = f ≫ diag Y :=
  sorry

@[simp] theorem prod.diag_map_fst_snd_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_product X Y] [has_binary_product (X ⨯ Y) (X ⨯ Y)] {X' : C} (f' : X ⨯ Y ⟶ X') :
    diag (X ⨯ Y) ≫ prod.map prod.fst prod.snd ≫ f' = f' :=
  sorry

@[simp] theorem prod.diag_map_fst_snd_comp_assoc {C : Type u} [category C]
    [has_limits_of_shape (discrete walking_pair) C] {X : C} {X' : C} {Y : C} {Y' : C} (g : X ⟶ Y)
    (g' : X' ⟶ Y') :
    ∀ {X'_1 : C} (f' : Y ⨯ Y' ⟶ X'_1),
        diag (X ⨯ X') ≫ prod.map (prod.fst ≫ g) (prod.snd ≫ g') ≫ f' = prod.map g g' ≫ f' :=
  sorry

protected instance diag.category_theory.split_mono {C : Type u} [category C] {X : C}
    [has_binary_product X X] : split_mono (diag X) :=
  split_mono.mk prod.fst

@[simp] theorem coprod.desc_comp_assoc {C : Type u} [category C] {V : C} {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : V ⟶ W) (g : X ⟶ V) (h : Y ⟶ V) {X' : C} (f' : W ⟶ X') :
    coprod.desc g h ≫ f ≫ f' = coprod.desc (g ≫ f) (h ≫ f) ≫ f' :=
  sorry

theorem coprod.diag_comp {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X X]
    (f : X ⟶ Y) : codiag X ≫ f = coprod.desc f f :=
  sorry

@[simp] theorem coprod.inl_map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    coprod.inl ≫ coprod.map f g = f ≫ coprod.inl :=
  ι_colim_map (map_pair f g) walking_pair.left

@[simp] theorem coprod.inr_map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) :
    coprod.inr ≫ coprod.map f g = g ≫ coprod.inr :=
  ι_colim_map (map_pair f g) walking_pair.right

@[simp] theorem coprod.map_id_id {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_coproduct X Y] : coprod.map 𝟙 𝟙 = 𝟙 :=
  sorry

@[simp] theorem coprod.desc_inl_inr {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_coproduct X Y] : coprod.desc coprod.inl coprod.inr = 𝟙 :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

@[simp] theorem coprod.map_desc {C : Type u} [category C] {S : C} {T : C} {U : C} {V : C} {W : C}
    [has_binary_coproduct U W] [has_binary_coproduct T V] (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U)
    (k : V ⟶ W) : coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) :=
  sorry

@[simp] theorem coprod.desc_comp_inl_comp_inr {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {Z : C} [has_binary_coproduct W Y] [has_binary_coproduct X Z] (g : W ⟶ X) (g' : Y ⟶ Z) :
    coprod.desc (g ≫ coprod.inl) (g' ≫ coprod.inr) = coprod.map g g' :=
  sorry

-- We take the right hand side here to be simp normal form, as this way composition lemmas for

-- `f ≫ h` and `g ≫ k` can fire (eg `id_comp`) , while `inl_map` and `inr_map` can still work just

-- as well.

@[simp] theorem coprod.map_map {C : Type u} [category C] {A₁ : C} {A₂ : C} {A₃ : C} {B₁ : C}
    {B₂ : C} {B₃ : C} [has_binary_coproduct A₁ B₁] [has_binary_coproduct A₂ B₂]
    [has_binary_coproduct A₃ B₃] (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    coprod.map f g ≫ coprod.map h k = coprod.map (f ≫ h) (g ≫ k) :=
  sorry

-- I don't think it's a good idea to make any of the following three simp lemmas.

theorem coprod.map_swap_assoc {C : Type u} [category C] {A : C} {B : C} {X : C} {Y : C} (f : A ⟶ B)
    (g : X ⟶ Y) [has_colimits_of_shape (discrete walking_pair) C] {X' : C} (f' : Y ⨿ B ⟶ X') :
    coprod.map 𝟙 f ≫ coprod.map g 𝟙 ≫ f' = coprod.map g 𝟙 ≫ coprod.map 𝟙 f ≫ f' :=
  sorry

theorem coprod.map_comp_id {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [has_binary_coproduct Z W] [has_binary_coproduct Y W] [has_binary_coproduct X W] :
    coprod.map (f ≫ g) 𝟙 = coprod.map f 𝟙 ≫ coprod.map g 𝟙 :=
  sorry

theorem coprod.map_id_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) [has_binary_coproduct W X] [has_binary_coproduct W Y] [has_binary_coproduct W Z] :
    coprod.map 𝟙 (f ≫ g) = coprod.map 𝟙 f ≫ coprod.map 𝟙 g :=
  sorry

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : W ≅ Z` induces a isomorphism `coprod.map_iso f g : W ⨿ X ≅ Y ⨿ Z`. -/
@[simp] theorem coprod.map_iso_hom {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ≅ Y) (g : X ≅ Z) :
    iso.hom (coprod.map_iso f g) = coprod.map (iso.hom f) (iso.hom g) :=
  Eq.refl (iso.hom (coprod.map_iso f g))

protected instance is_iso_coprod {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ⟶ Y) (g : X ⟶ Z) [is_iso f]
    [is_iso g] : is_iso (coprod.map f g) :=
  is_iso.of_iso (coprod.map_iso (as_iso f) (as_iso g))

-- The simp linter says simp can prove the reassoc version of this lemma.

@[simp] theorem coprod.map_codiag {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y)
    [has_binary_coproduct X X] [has_binary_coproduct Y Y] :
    coprod.map f f ≫ codiag Y = codiag X ≫ f :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

theorem coprod.map_inl_inr_codiag_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_coproduct X Y] [has_binary_coproduct (X ⨿ Y) (X ⨿ Y)] {X' : C} (f' : X ⨿ Y ⟶ X') :
    coprod.map coprod.inl coprod.inr ≫ codiag (X ⨿ Y) ≫ f' = f' :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

@[simp] theorem coprod.map_comp_inl_inr_codiag {C : Type u} [category C]
    [has_colimits_of_shape (discrete walking_pair) C] {X : C} {X' : C} {Y : C} {Y' : C} (g : X ⟶ Y)
    (g' : X' ⟶ Y') :
    coprod.map (g ≫ coprod.inl) (g' ≫ coprod.inr) ≫ codiag (Y ⨿ Y') = coprod.map g g' :=
  sorry

/--
`has_binary_products` represents a choice of product for every pair of objects.

See https://stacks.math.columbia.edu/tag/001T.
-/
def has_binary_products (C : Type u) [category C] := has_limits_of_shape (discrete walking_pair) C

/--
`has_binary_coproducts` represents a choice of coproduct for every pair of objects.

See https://stacks.math.columbia.edu/tag/04AP.
-/
def has_binary_coproducts (C : Type u) [category C] :=
  has_colimits_of_shape (discrete walking_pair) C

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
theorem has_binary_products_of_has_limit_pair (C : Type u) [category C]
    [∀ {X Y : C}, has_limit (pair X Y)] : has_binary_products C :=
  has_limits_of_shape.mk
    fun (F : discrete walking_pair ⥤ C) => has_limit_of_iso (iso.symm (diagram_iso_pair F))

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
theorem has_binary_coproducts_of_has_colimit_pair (C : Type u) [category C]
    [∀ {X Y : C}, has_colimit (pair X Y)] : has_binary_coproducts C :=
  has_colimits_of_shape.mk
    fun (F : discrete walking_pair ⥤ C) => has_colimit_of_iso (diagram_iso_pair F)

/-- The braiding isomorphism which swaps a binary product. -/
@[simp] theorem prod.braiding_hom {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q]
    [has_binary_product Q P] : iso.hom (prod.braiding P Q) = prod.lift prod.snd prod.fst :=
  Eq.refl (iso.hom (prod.braiding P Q))

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
theorem braid_natural {C : Type u} [category C] [has_binary_products C] {W : C} {X : C} {Y : C}
    {Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    prod.map f g ≫ iso.hom (prod.braiding Y W) = iso.hom (prod.braiding X Z) ≫ prod.map g f :=
  sorry

theorem prod.symmetry'_assoc {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q]
    [has_binary_product Q P] {X' : C} (f' : P ⨯ Q ⟶ X') :
    prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst ≫ f' = f' :=
  sorry

/-- The braiding isomorphism is symmetric. -/
theorem prod.symmetry_assoc {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q]
    [has_binary_product Q P] {X' : C} (f' : P ⨯ Q ⟶ X') :
    iso.hom (prod.braiding P Q) ≫ iso.hom (prod.braiding Q P) ≫ f' = f' :=
  sorry

/-- The associator isomorphism for binary products. -/
@[simp] theorem prod.associator_hom {C : Type u} [category C] [has_binary_products C] (P : C)
    (Q : C) (R : C) :
    iso.hom (prod.associator P Q R) =
        prod.lift (prod.fst ≫ prod.fst) (prod.lift (prod.fst ≫ prod.snd) prod.snd) :=
  Eq.refl (iso.hom (prod.associator P Q R))

theorem prod.pentagon_assoc {C : Type u} [category C] [has_binary_products C] (W : C) (X : C)
    (Y : C) (Z : C) {X' : C} (f' : W ⨯ (X ⨯ (Y ⨯ Z)) ⟶ X') :
    prod.map (iso.hom (prod.associator W X Y)) 𝟙 ≫
          iso.hom (prod.associator W (X ⨯ Y) Z) ≫
            prod.map 𝟙 (iso.hom (prod.associator X Y Z)) ≫ f' =
        iso.hom (prod.associator (W ⨯ X) Y Z) ≫ iso.hom (prod.associator W X (Y ⨯ Z)) ≫ f' :=
  sorry

theorem prod.associator_naturality_assoc {C : Type u} [category C] [has_binary_products C] {X₁ : C}
    {X₂ : C} {X₃ : C} {Y₁ : C} {Y₂ : C} {Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    {X' : C} (f' : Y₁ ⨯ (Y₂ ⨯ Y₃) ⟶ X') :
    prod.map (prod.map f₁ f₂) f₃ ≫ iso.hom (prod.associator Y₁ Y₂ Y₃) ≫ f' =
        iso.hom (prod.associator X₁ X₂ X₃) ≫ prod.map f₁ (prod.map f₂ f₃) ≫ f' :=
  sorry

/-- The left unitor isomorphism for binary products with the terminal object. -/
def prod.left_unitor {C : Type u} [category C] [has_terminal C] (P : C)
    [has_binary_product (⊤_C) P] : (⊤_C) ⨯ P ≅ P :=
  iso.mk prod.snd (prod.lift (terminal.from P) 𝟙)

/-- The right unitor isomorphism for binary products with the terminal object. -/
def prod.right_unitor {C : Type u} [category C] [has_terminal C] (P : C)
    [has_binary_product P (⊤_C)] : P ⨯ (⊤_C) ≅ P :=
  iso.mk prod.fst (prod.lift 𝟙 (terminal.from P))

theorem prod.left_unitor_hom_naturality_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_terminal C] [has_binary_products C] (f : X ⟶ Y) {X' : C} (f' : Y ⟶ X') :
    prod.map 𝟙 f ≫ iso.hom (prod.left_unitor Y) ≫ f' = iso.hom (prod.left_unitor X) ≫ f ≫ f' :=
  sorry

theorem prod.left_unitor_inv_naturality {C : Type u} [category C] {X : C} {Y : C} [has_terminal C]
    [has_binary_products C] (f : X ⟶ Y) :
    iso.inv (prod.left_unitor X) ≫ prod.map 𝟙 f = f ≫ iso.inv (prod.left_unitor Y) :=
  sorry

theorem prod.right_unitor_hom_naturality_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_terminal C] [has_binary_products C] (f : X ⟶ Y) {X' : C} (f' : Y ⟶ X') :
    prod.map f 𝟙 ≫ iso.hom (prod.right_unitor Y) ≫ f' = iso.hom (prod.right_unitor X) ≫ f ≫ f' :=
  sorry

theorem prod_right_unitor_inv_naturality {C : Type u} [category C] {X : C} {Y : C} [has_terminal C]
    [has_binary_products C] (f : X ⟶ Y) :
    iso.inv (prod.right_unitor X) ≫ prod.map f 𝟙 = f ≫ iso.inv (prod.right_unitor Y) :=
  sorry

theorem prod.triangle {C : Type u} [category C] [has_terminal C] [has_binary_products C] (X : C)
    (Y : C) :
    iso.hom (prod.associator X (⊤_C) Y) ≫ prod.map 𝟙 (iso.hom (prod.left_unitor Y)) =
        prod.map (iso.hom (prod.right_unitor X)) 𝟙 :=
  sorry

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simp] theorem coprod.braiding_hom {C : Type u} [category C] [has_binary_coproducts C] (P : C)
    (Q : C) : iso.hom (coprod.braiding P Q) = coprod.desc coprod.inr coprod.inl :=
  Eq.refl (iso.hom (coprod.braiding P Q))

theorem coprod.symmetry'_assoc {C : Type u} [category C] [has_binary_coproducts C] (P : C) (Q : C)
    {X' : C} (f' : P ⨿ Q ⟶ X') :
    coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl ≫ f' = f' :=
  sorry

/-- The braiding isomorphism is symmetric. -/
theorem coprod.symmetry {C : Type u} [category C] [has_binary_coproducts C] (P : C) (Q : C) :
    iso.hom (coprod.braiding P Q) ≫ iso.hom (coprod.braiding Q P) = 𝟙 :=
  coprod.symmetry' P Q

/-- The associator isomorphism for binary coproducts. -/
@[simp] theorem coprod.associator_inv {C : Type u} [category C] [has_binary_coproducts C] (P : C)
    (Q : C) (R : C) :
    iso.inv (coprod.associator P Q R) =
        coprod.desc (coprod.inl ≫ coprod.inl) (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) :=
  Eq.refl (iso.inv (coprod.associator P Q R))

theorem coprod.pentagon {C : Type u} [category C] [has_binary_coproducts C] (W : C) (X : C) (Y : C)
    (Z : C) :
    coprod.map (iso.hom (coprod.associator W X Y)) 𝟙 ≫
          iso.hom (coprod.associator W (X ⨿ Y) Z) ≫
            coprod.map 𝟙 (iso.hom (coprod.associator X Y Z)) =
        iso.hom (coprod.associator (W ⨿ X) Y Z) ≫ iso.hom (coprod.associator W X (Y ⨿ Z)) :=
  sorry

theorem coprod.associator_naturality {C : Type u} [category C] [has_binary_coproducts C] {X₁ : C}
    {X₂ : C} {X₃ : C} {Y₁ : C} {Y₂ : C} {Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    coprod.map (coprod.map f₁ f₂) f₃ ≫ iso.hom (coprod.associator Y₁ Y₂ Y₃) =
        iso.hom (coprod.associator X₁ X₂ X₃) ≫ coprod.map f₁ (coprod.map f₂ f₃) :=
  sorry

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simp] theorem coprod.left_unitor_inv {C : Type u} [category C] [has_binary_coproducts C]
    [has_initial C] (P : C) : iso.inv (coprod.left_unitor P) = coprod.inr :=
  Eq.refl (iso.inv (coprod.left_unitor P))

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simp] theorem coprod.right_unitor_hom {C : Type u} [category C] [has_binary_coproducts C]
    [has_initial C] (P : C) : iso.hom (coprod.right_unitor P) = coprod.desc 𝟙 (initial.to P) :=
  Eq.refl (iso.hom (coprod.right_unitor P))

theorem coprod.triangle {C : Type u} [category C] [has_binary_coproducts C] [has_initial C] (X : C)
    (Y : C) :
    iso.hom (coprod.associator X (⊥_C) Y) ≫ coprod.map 𝟙 (iso.hom (coprod.left_unitor Y)) =
        coprod.map (iso.hom (coprod.right_unitor X)) 𝟙 :=
  sorry

/-- The binary product functor. -/
@[simp] theorem prod.functor_obj_map {C : Type u} [category C] [has_binary_products C] (X : C)
    (Y : C) (Z : C) (g : Y ⟶ Z) : functor.map (functor.obj prod.functor X) g = prod.map 𝟙 g :=
  Eq.refl (functor.map (functor.obj prod.functor X) g)

/-- The product functor can be decomposed. -/
def prod.functor_left_comp {C : Type u} [category C] [has_binary_products C] (X : C) (Y : C) :
    functor.obj prod.functor (X ⨯ Y) ≅ functor.obj prod.functor Y ⋙ functor.obj prod.functor X :=
  nat_iso.of_components (prod.associator X Y) sorry

/-- The binary coproduct functor. -/
@[simp] theorem coprod.functor_obj_map {C : Type u} [category C] [has_binary_coproducts C] (X : C)
    (Y : C) (Z : C) (g : Y ⟶ Z) : functor.map (functor.obj coprod.functor X) g = coprod.map 𝟙 g :=
  Eq.refl (functor.map (functor.obj coprod.functor X) g)

/-- The coproduct functor can be decomposed. -/
def coprod.functor_left_comp {C : Type u} [category C] [has_binary_coproducts C] (X : C) (Y : C) :
    functor.obj coprod.functor (X ⨿ Y) ≅
        functor.obj coprod.functor Y ⋙ functor.obj coprod.functor X :=
  nat_iso.of_components (coprod.associator X Y) sorry

/--
The product comparison morphism.

In `category_theory/limits/preserves` we show this is always an iso iff F preserves binary products.
-/
def prod_comparison {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D) (A : C) (B : C)
    [has_binary_product A B] [has_binary_product (functor.obj F A) (functor.obj F B)] :
    functor.obj F (A ⨯ B) ⟶ functor.obj F A ⨯ functor.obj F B :=
  prod.lift (functor.map F prod.fst) (functor.map F prod.snd)

@[simp] theorem prod_comparison_fst_assoc {C : Type u} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] {X' : D} (f' : functor.obj F A ⟶ X') :
    prod_comparison F A B ≫ prod.fst ≫ f' = functor.map F prod.fst ≫ f' :=
  sorry

@[simp] theorem prod_comparison_snd_assoc {C : Type u} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] {X' : D} (f' : functor.obj F B ⟶ X') :
    prod_comparison F A B ≫ prod.snd ≫ f' = functor.map F prod.snd ≫ f' :=
  sorry

/-- Naturality of the prod_comparison morphism in both arguments. -/
theorem prod_comparison_natural_assoc {C : Type u} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) {A : C} {A' : C} {B : C} {B' : C} [has_binary_product A B]
    [has_binary_product A' B'] [has_binary_product (functor.obj F A) (functor.obj F B)]
    [has_binary_product (functor.obj F A') (functor.obj F B')] (f : A ⟶ A') (g : B ⟶ B') {X' : D}
    (f' : functor.obj F A' ⨯ functor.obj F B' ⟶ X') :
    functor.map F (prod.map f g) ≫ prod_comparison F A' B' ≫ f' =
        prod_comparison F A B ≫ prod.map (functor.map F f) (functor.map F g) ≫ f' :=
  sorry

/--
The product comparison morphism from `F(A ⨯ -)` to `FA ⨯ F-`, whose components are given by
`prod_comparison`.
-/
def prod_comparison_nat_trans {C : Type u} [category C] {D : Type u₂} [category D]
    [has_binary_products C] [has_binary_products D] (F : C ⥤ D) (A : C) :
    functor.obj prod.functor A ⋙ F ⟶ F ⋙ functor.obj prod.functor (functor.obj F A) :=
  nat_trans.mk fun (B : C) => prod_comparison F A B

theorem inv_prod_comparison_map_fst_assoc {C : Type u} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] [is_iso (prod_comparison F A B)]
    {X' : D} (f' : functor.obj F A ⟶ X') :
    inv (prod_comparison F A B) ≫ functor.map F prod.fst ≫ f' = prod.fst ≫ f' :=
  sorry

theorem inv_prod_comparison_map_snd_assoc {C : Type u} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] [is_iso (prod_comparison F A B)]
    {X' : D} (f' : functor.obj F B ⟶ X') :
    inv (prod_comparison F A B) ≫ functor.map F prod.snd ≫ f' = prod.snd ≫ f' :=
  sorry

/-- If the product comparison morphism is an iso, its inverse is natural. -/
theorem prod_comparison_inv_natural {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    {A : C} {A' : C} {B : C} {B' : C} [has_binary_product A B] [has_binary_product A' B']
    [has_binary_product (functor.obj F A) (functor.obj F B)]
    [has_binary_product (functor.obj F A') (functor.obj F B')] (f : A ⟶ A') (g : B ⟶ B')
    [is_iso (prod_comparison F A B)] [is_iso (prod_comparison F A' B')] :
    inv (prod_comparison F A B) ≫ functor.map F (prod.map f g) =
        prod.map (functor.map F f) (functor.map F g) ≫ inv (prod_comparison F A' B') :=
  sorry

/--
The natural isomorphism `F(A ⨯ -) ≅ FA ⨯ F-`, provided each `prod_comparison F A B` is an
isomorphism (as `B` changes).
-/
def prod_comparison_nat_iso {C : Type u} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    [has_binary_products C] [has_binary_products D] (A : C)
    [(B : C) → is_iso (prod_comparison F A B)] :
    functor.obj prod.functor A ⋙ F ≅ F ⋙ functor.obj prod.functor (functor.obj F A) :=
  iso.mk (prod_comparison_nat_trans F A) (inv (nat_trans.mk fun (B : C) => prod_comparison F A B))

end Mathlib