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

universes v l u_1 u_2 u uā 

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
def walking_pair.swap : walking_pair ā walking_pair :=
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
def walking_pair.equiv_bool : walking_pair ā Bool :=
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
def pair {C : Type u} [category C] (X : C) (Y : C) : discrete walking_pair ā„¤ C :=
  discrete.functor fun (j : walking_pair) => walking_pair.cases_on j X Y

@[simp] theorem pair_obj_left {C : Type u} [category C] (X : C) (Y : C) :
    functor.obj (pair X Y) walking_pair.left = X :=
  rfl

@[simp] theorem pair_obj_right {C : Type u} [category C] (X : C) (Y : C) :
    functor.obj (pair X Y) walking_pair.right = Y :=
  rfl

/-- The natural transformation between two functors out of the walking pair, specified by its components. -/
def map_pair {C : Type u} [category C] {F : discrete walking_pair ā„¤ C}
    {G : discrete walking_pair ā„¤ C}
    (f : functor.obj F walking_pair.left ā¶ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ā¶ functor.obj G walking_pair.right) : F ā¶ G :=
  nat_trans.mk fun (j : discrete walking_pair) => walking_pair.cases_on j f g

@[simp] theorem map_pair_left {C : Type u} [category C] {F : discrete walking_pair ā„¤ C}
    {G : discrete walking_pair ā„¤ C}
    (f : functor.obj F walking_pair.left ā¶ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ā¶ functor.obj G walking_pair.right) :
    nat_trans.app (map_pair f g) walking_pair.left = f :=
  rfl

@[simp] theorem map_pair_right {C : Type u} [category C] {F : discrete walking_pair ā„¤ C}
    {G : discrete walking_pair ā„¤ C}
    (f : functor.obj F walking_pair.left ā¶ functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ā¶ functor.obj G walking_pair.right) :
    nat_trans.app (map_pair f g) walking_pair.right = g :=
  rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its components. -/
def map_pair_iso {C : Type u} [category C] {F : discrete walking_pair ā„¤ C}
    {G : discrete walking_pair ā„¤ C}
    (f : functor.obj F walking_pair.left ā functor.obj G walking_pair.left)
    (g : functor.obj F walking_pair.right ā functor.obj G walking_pair.right) : F ā G :=
  nat_iso.of_components (fun (j : discrete walking_pair) => walking_pair.cases_on j f g) sorry

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
@[simp] theorem diagram_iso_pair_inv_app {C : Type u} [category C] (F : discrete walking_pair ā„¤ C)
    (X : discrete walking_pair) :
    nat_trans.app (iso.inv (diagram_iso_pair F)) X =
        iso.inv
          (walking_pair.rec (iso.refl (functor.obj F walking_pair.left))
            (iso.refl (functor.obj F walking_pair.right)) X) :=
  Eq.refl
    (iso.inv
      (walking_pair.rec (iso.refl (functor.obj F walking_pair.left))
        (iso.refl (functor.obj F walking_pair.right)) X))

/-- The natural isomorphism between `pair X Y ā F` and `pair (F.obj X) (F.obj Y)`. -/
def pair_comp {C : Type u} [category C] {D : Type u} [category D] (X : C) (Y : C) (F : C ā„¤ D) :
    pair X Y ā F ā pair (functor.obj F X) (functor.obj F Y) :=
  diagram_iso_pair (pair X Y ā F)

/-- A binary fan is just a cone on a diagram indexing a product. -/
def binary_fan {C : Type u} [category C] (X : C) (Y : C) := cone (pair X Y)

/-- The first projection of a binary fan. -/
def binary_fan.fst {C : Type u} [category C] {X : C} {Y : C} (s : binary_fan X Y) :
    functor.obj (functor.obj (functor.const (discrete walking_pair)) (cone.X s)) walking_pair.left ā¶
        functor.obj (pair X Y) walking_pair.left :=
  nat_trans.app (cone.Ļ s) walking_pair.left

/-- The second projection of a binary fan. -/
def binary_fan.snd {C : Type u} [category C] {X : C} {Y : C} (s : binary_fan X Y) :
    functor.obj (functor.obj (functor.const (discrete walking_pair)) (cone.X s))
          walking_pair.right ā¶
        functor.obj (pair X Y) walking_pair.right :=
  nat_trans.app (cone.Ļ s) walking_pair.right

@[simp] theorem binary_fan.Ļ_app_left {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_fan X Y) : nat_trans.app (cone.Ļ s) walking_pair.left = binary_fan.fst s :=
  rfl

@[simp] theorem binary_fan.Ļ_app_right {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_fan X Y) : nat_trans.app (cone.Ļ s) walking_pair.right = binary_fan.snd s :=
  rfl

theorem binary_fan.is_limit.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_fan X Y} (h : is_limit s) {f : W ā¶ cone.X s} {g : W ā¶ cone.X s}
    (hā : f ā« binary_fan.fst s = g ā« binary_fan.fst s)
    (hā : f ā« binary_fan.snd s = g ā« binary_fan.snd s) : f = g :=
  is_limit.hom_ext h fun (j : discrete walking_pair) => walking_pair.cases_on j hā hā

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
def binary_cofan {C : Type u} [category C] (X : C) (Y : C) := cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
def binary_cofan.inl {C : Type u} [category C] {X : C} {Y : C} (s : binary_cofan X Y) :
    functor.obj (pair X Y) walking_pair.left ā¶
        functor.obj (functor.obj (functor.const (discrete walking_pair)) (cocone.X s))
          walking_pair.left :=
  nat_trans.app (cocone.Ī¹ s) walking_pair.left

/-- The second inclusion of a binary cofan. -/
def binary_cofan.inr {C : Type u} [category C] {X : C} {Y : C} (s : binary_cofan X Y) :
    functor.obj (pair X Y) walking_pair.right ā¶
        functor.obj (functor.obj (functor.const (discrete walking_pair)) (cocone.X s))
          walking_pair.right :=
  nat_trans.app (cocone.Ī¹ s) walking_pair.right

@[simp] theorem binary_cofan.Ī¹_app_left {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_cofan X Y) : nat_trans.app (cocone.Ī¹ s) walking_pair.left = binary_cofan.inl s :=
  rfl

@[simp] theorem binary_cofan.Ī¹_app_right {C : Type u} [category C] {X : C} {Y : C}
    (s : binary_cofan X Y) : nat_trans.app (cocone.Ī¹ s) walking_pair.right = binary_cofan.inr s :=
  rfl

theorem binary_cofan.is_colimit.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_cofan X Y} (h : is_colimit s) {f : cocone.X s ā¶ W} {g : cocone.X s ā¶ W}
    (hā : binary_cofan.inl s ā« f = binary_cofan.inl s ā« g)
    (hā : binary_cofan.inr s ā« f = binary_cofan.inr s ā« g) : f = g :=
  is_colimit.hom_ext h fun (j : discrete walking_pair) => walking_pair.cases_on j hā hā

/-- A binary fan with vertex `P` consists of the two projections `Ļā : P ā¶ X` and `Ļā : P ā¶ Y`. -/
def binary_fan.mk {C : Type u} [category C] {X : C} {Y : C} {P : C} (Ļā : P ā¶ X) (Ļā : P ā¶ Y) :
    binary_fan X Y :=
  cone.mk P (nat_trans.mk fun (j : discrete walking_pair) => walking_pair.cases_on j Ļā Ļā)

/-- A binary cofan with vertex `P` consists of the two inclusions `Ī¹ā : X ā¶ P` and `Ī¹ā : Y ā¶ P`. -/
def binary_cofan.mk {C : Type u} [category C] {X : C} {Y : C} {P : C} (Ī¹ā : X ā¶ P) (Ī¹ā : Y ā¶ P) :
    binary_cofan X Y :=
  cocone.mk P (nat_trans.mk fun (j : discrete walking_pair) => walking_pair.cases_on j Ī¹ā Ī¹ā)

@[simp] theorem binary_fan.mk_Ļ_app_left {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (Ļā : P ā¶ X) (Ļā : P ā¶ Y) :
    nat_trans.app (cone.Ļ (binary_fan.mk Ļā Ļā)) walking_pair.left = Ļā :=
  rfl

@[simp] theorem binary_fan.mk_Ļ_app_right {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (Ļā : P ā¶ X) (Ļā : P ā¶ Y) :
    nat_trans.app (cone.Ļ (binary_fan.mk Ļā Ļā)) walking_pair.right = Ļā :=
  rfl

@[simp] theorem binary_cofan.mk_Ī¹_app_left {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (Ī¹ā : X ā¶ P) (Ī¹ā : Y ā¶ P) :
    nat_trans.app (cocone.Ī¹ (binary_cofan.mk Ī¹ā Ī¹ā)) walking_pair.left = Ī¹ā :=
  rfl

@[simp] theorem binary_cofan.mk_Ī¹_app_right {C : Type u} [category C] {X : C} {Y : C} {P : C}
    (Ī¹ā : X ā¶ P) (Ī¹ā : Y ā¶ P) :
    nat_trans.app (cocone.Ī¹ (binary_cofan.mk Ī¹ā Ī¹ā)) walking_pair.right = Ī¹ā :=
  rfl

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ā¶ X` and
    `g : W ā¶ Y` induces a morphism `l : W ā¶ s.X` satisfying `l ā« s.fst = f` and `l ā« s.snd = g`.
    -/
@[simp] theorem binary_fan.is_limit.lift'_coe {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_fan X Y} (h : is_limit s) (f : W ā¶ X) (g : W ā¶ Y) :
    ā(binary_fan.is_limit.lift' h f g) = is_limit.lift h (binary_fan.mk f g) :=
  Eq.refl ā(binary_fan.is_limit.lift' h f g)

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ā¶ W` and
    `g : Y ā¶ W` induces a morphism `l : s.X ā¶ W` satisfying `s.inl ā« l = f` and `s.inr ā« l = g`.
    -/
@[simp] theorem binary_cofan.is_colimit.desc'_coe {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {s : binary_cofan X Y} (h : is_colimit s) (f : X ā¶ W) (g : Y ā¶ W) :
    ā(binary_cofan.is_colimit.desc' h f g) = is_colimit.desc h (binary_cofan.mk f g) :=
  Eq.refl ā(binary_cofan.is_colimit.desc' h f g)

/-- An abbreviation for `has_limit (pair X Y)`. -/
/-- An abbreviation for `has_colimit (pair X Y)`. -/
def has_binary_product {C : Type u} [category C] (X : C) (Y : C) := has_limit (pair X Y)

def has_binary_coproduct {C : Type u} [category C] (X : C) (Y : C) := has_colimit (pair X Y)

/-- If we have a product of `X` and `Y`, we can access it using `prod X Y` or
    `X āØÆ Y`. -/
def prod {C : Type u} [category C] (X : C) (Y : C) [has_binary_product X Y] : C := limit (pair X Y)

/-- If we have a coproduct of `X` and `Y`, we can access it using `coprod X Y ` or
    `X āØæ Y`. -/
def coprod {C : Type u} [category C] (X : C) (Y : C) [has_binary_coproduct X Y] : C :=
  colimit (pair X Y)

infixl:20 " āØÆ " => Mathlib.category_theory.limits.prod

infixl:20 " āØæ " => Mathlib.category_theory.limits.coprod

/-- The projection map to the first component of the product. -/
def prod.fst {C : Type u} [category C] {X : C} {Y : C} [has_binary_product X Y] : X āØÆ Y ā¶ X :=
  limit.Ļ (pair X Y) walking_pair.left

/-- The projecton map to the second component of the product. -/
def prod.snd {C : Type u} [category C] {X : C} {Y : C} [has_binary_product X Y] : X āØÆ Y ā¶ Y :=
  limit.Ļ (pair X Y) walking_pair.right

/-- The inclusion map from the first component of the coproduct. -/
def coprod.inl {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X Y] : X ā¶ X āØæ Y :=
  colimit.Ī¹ (pair X Y) walking_pair.left

/-- The inclusion map from the second component of the coproduct. -/
def coprod.inr {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X Y] : Y ā¶ X āØæ Y :=
  colimit.Ī¹ (pair X Y) walking_pair.right

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
    {f : W ā¶ X āØÆ Y} {g : W ā¶ X āØÆ Y} (hā : f ā« prod.fst = g ā« prod.fst)
    (hā : f ā« prod.snd = g ā« prod.snd) : f = g :=
  binary_fan.is_limit.hom_ext (limit.is_limit (pair X Y)) hā hā

theorem coprod.hom_ext {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_coproduct X Y]
    {f : X āØæ Y ā¶ W} {g : X āØæ Y ā¶ W} (hā : coprod.inl ā« f = coprod.inl ā« g)
    (hā : coprod.inr ā« f = coprod.inr ā« g) : f = g :=
  binary_cofan.is_colimit.hom_ext (colimit.is_colimit (pair X Y)) hā hā

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ā¶ X` and `g : W ā¶ Y`
    induces a morphism `prod.lift f g : W ā¶ X āØÆ Y`. -/
def prod.lift {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_product X Y] (f : W ā¶ X)
    (g : W ā¶ Y) : W ā¶ X āØÆ Y :=
  limit.lift (pair X Y) (binary_fan.mk f g)

/-- diagonal arrow of the binary product in the category `fam I` -/
def diag {C : Type u} [category C] (X : C) [has_binary_product X X] : X ā¶ X āØÆ X := prod.lift š š

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ā¶ W` and
    `g : Y ā¶ W` induces a morphism `coprod.desc f g : X āØæ Y ā¶ W`. -/
def coprod.desc {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_coproduct X Y]
    (f : X ā¶ W) (g : Y ā¶ W) : X āØæ Y ā¶ W :=
  colimit.desc (pair X Y) (binary_cofan.mk f g)

/-- codiagonal arrow of the binary coproduct -/
def codiag {C : Type u} [category C] (X : C) [has_binary_coproduct X X] : X āØæ X ā¶ X :=
  coprod.desc š š

@[simp] theorem prod.lift_fst_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ā¶ X) (g : W ā¶ Y) {X' : C} (f' : X ā¶ X') :
    prod.lift f g ā« prod.fst ā« f' = f ā« f' :=
  sorry

@[simp] theorem prod.lift_snd {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ā¶ X) (g : W ā¶ Y) : prod.lift f g ā« prod.snd = g :=
  limit.lift_Ļ (binary_fan.mk f g) walking_pair.right

-- The simp linter says simp can prove the reassoc version of this lemma.

theorem coprod.inl_desc_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) {X' : C} (f' : W ā¶ X') :
    coprod.inl ā« coprod.desc f g ā« f' = f ā« f' :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

theorem coprod.inr_desc_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) {X' : C} (f' : W ā¶ X') :
    coprod.inr ā« coprod.desc f g ā« f' = g ā« f' :=
  sorry

protected instance prod.mono_lift_of_mono_left {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ā¶ X) (g : W ā¶ Y) [mono f] : mono (prod.lift f g) :=
  mono_of_mono_fac (prod.lift_fst f g)

protected instance prod.mono_lift_of_mono_right {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : W ā¶ X) (g : W ā¶ Y) [mono g] : mono (prod.lift f g) :=
  mono_of_mono_fac (prod.lift_snd f g)

protected instance coprod.epi_desc_of_epi_left {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) [epi f] : epi (coprod.desc f g) :=
  epi_of_epi_fac (coprod.inl_desc f g)

protected instance coprod.epi_desc_of_epi_right {C : Type u} [category C] {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : X ā¶ W) (g : Y ā¶ W) [epi g] : epi (coprod.desc f g) :=
  epi_of_epi_fac (coprod.inr_desc f g)

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ā¶ X` and `g : W ā¶ Y`
    induces a morphism `l : W ā¶ X āØÆ Y` satisfying `l ā« prod.fst = f` and `l ā« prod.snd = g`. -/
def prod.lift' {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_product X Y]
    (f : W ā¶ X) (g : W ā¶ Y) : Subtype fun (l : W ā¶ X āØÆ Y) => l ā« prod.fst = f ā§ l ā« prod.snd = g :=
  { val := prod.lift f g, property := sorry }

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ā¶ W` and
    `g : Y ā¶ W` induces a morphism `l : X āØæ Y ā¶ W` satisfying `coprod.inl ā« l = f` and
    `coprod.inr ā« l = g`. -/
def coprod.desc' {C : Type u} [category C] {W : C} {X : C} {Y : C} [has_binary_coproduct X Y]
    (f : X ā¶ W) (g : Y ā¶ W) :
    Subtype fun (l : X āØæ Y ā¶ W) => coprod.inl ā« l = f ā§ coprod.inr ā« l = g :=
  { val := coprod.desc f g, property := sorry }

/-- If the products `W āØÆ X` and `Y āØÆ Z` exist, then every pair of morphisms `f : W ā¶ Y` and
    `g : X ā¶ Z` induces a morphism `prod.map f g : W āØÆ X ā¶ Y āØÆ Z`. -/
def prod.map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} [has_binary_product W X]
    [has_binary_product Y Z] (f : W ā¶ Y) (g : X ā¶ Z) : W āØÆ X ā¶ Y āØÆ Z :=
  lim_map (map_pair f g)

/-- If the coproducts `W āØæ X` and `Y āØæ Z` exist, then every pair of morphisms `f : W ā¶ Y` and
    `g : W ā¶ Z` induces a morphism `coprod.map f g : W āØæ X ā¶ Y āØæ Z`. -/
def coprod.map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} [has_binary_coproduct W X]
    [has_binary_coproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) : W āØæ X ā¶ Y āØæ Z :=
  colim_map (map_pair f g)

-- Making the reassoc version of this a simp lemma seems to be more harmful than helpful.

theorem prod.comp_lift_assoc {C : Type u} [category C] {V : C} {W : C} {X : C} {Y : C}
    [has_binary_product X Y] (f : V ā¶ W) (g : W ā¶ X) (h : W ā¶ Y) {X' : C} (f' : X āØÆ Y ā¶ X') :
    f ā« prod.lift g h ā« f' = prod.lift (f ā« g) (f ā« h) ā« f' :=
  sorry

theorem prod.comp_diag {C : Type u} [category C] {X : C} {Y : C} [has_binary_product Y Y]
    (f : X ā¶ Y) : f ā« diag Y = prod.lift f f :=
  sorry

@[simp] theorem prod.map_fst {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    prod.map f g ā« prod.fst = prod.fst ā« f :=
  lim_map_Ļ (map_pair f g) walking_pair.left

@[simp] theorem prod.map_snd_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ā¶ Y) (g : X ā¶ Z) {X' : C}
    (f' : Z ā¶ X') : prod.map f g ā« prod.snd ā« f' = prod.snd ā« g ā« f' :=
  sorry

@[simp] theorem prod.map_id_id {C : Type u} [category C] {X : C} {Y : C} [has_binary_product X Y] :
    prod.map š š = š :=
  sorry

@[simp] theorem prod.lift_fst_snd {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_product X Y] : prod.lift prod.fst prod.snd = š :=
  sorry

@[simp] theorem prod.lift_map {C : Type u} [category C] {V : C} {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : V ā¶ W) (g : V ā¶ X) (h : W ā¶ Y)
    (k : X ā¶ Z) : prod.lift f g ā« prod.map h k = prod.lift (f ā« h) (g ā« k) :=
  sorry

@[simp] theorem prod.lift_fst_comp_snd_comp {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {Z : C} [has_binary_product W Y] [has_binary_product X Z] (g : W ā¶ X) (g' : Y ā¶ Z) :
    prod.lift (prod.fst ā« g) (prod.snd ā« g') = prod.map g g' :=
  sorry

-- We take the right hand side here to be simp normal form, as this way composition lemmas for

-- `f ā« h` and `g ā« k` can fire (eg `id_comp`) , while `map_fst` and `map_snd` can still work just

-- as well.

@[simp] theorem prod.map_map_assoc {C : Type u} [category C] {Aā : C} {Aā : C} {Aā : C} {Bā : C}
    {Bā : C} {Bā : C} [has_binary_product Aā Bā] [has_binary_product Aā Bā]
    [has_binary_product Aā Bā] (f : Aā ā¶ Aā) (g : Bā ā¶ Bā) (h : Aā ā¶ Aā) (k : Bā ā¶ Bā) {X' : C}
    (f' : Aā āØÆ Bā ā¶ X') : prod.map f g ā« prod.map h k ā« f' = prod.map (f ā« h) (g ā« k) ā« f' :=
  sorry

-- TODO: is it necessary to weaken the assumption here?

theorem prod.map_swap {C : Type u} [category C] {A : C} {B : C} {X : C} {Y : C} (f : A ā¶ B)
    (g : X ā¶ Y) [has_limits_of_shape (discrete walking_pair) C] :
    prod.map š f ā« prod.map g š = prod.map g š ā« prod.map š f :=
  sorry

theorem prod.map_comp_id {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ā¶ Y)
    (g : Y ā¶ Z) [has_binary_product X W] [has_binary_product Z W] [has_binary_product Y W] :
    prod.map (f ā« g) š = prod.map f š ā« prod.map g š :=
  sorry

theorem prod.map_id_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ā¶ Y)
    (g : Y ā¶ Z) [has_binary_product W X] [has_binary_product W Y] [has_binary_product W Z] :
    prod.map š (f ā« g) = prod.map š f ā« prod.map š g :=
  sorry

/-- If the products `W āØÆ X` and `Y āØÆ Z` exist, then every pair of isomorphisms `f : W ā Y` and
    `g : X ā Z` induces an isomorphism `prod.map_iso f g : W āØÆ X ā Y āØÆ Z`. -/
@[simp] theorem prod.map_iso_inv {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ā Y) (g : X ā Z) :
    iso.inv (prod.map_iso f g) = prod.map (iso.inv f) (iso.inv g) :=
  Eq.refl (iso.inv (prod.map_iso f g))

protected instance is_iso_prod {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_product W X] [has_binary_product Y Z] (f : W ā¶ Y) (g : X ā¶ Z) [is_iso f]
    [is_iso g] : is_iso (prod.map f g) :=
  is_iso.of_iso (prod.map_iso (as_iso f) (as_iso g))

@[simp] theorem prod.diag_map {C : Type u} [category C] {X : C} {Y : C} (f : X ā¶ Y)
    [has_binary_product X X] [has_binary_product Y Y] : diag X ā« prod.map f f = f ā« diag Y :=
  sorry

@[simp] theorem prod.diag_map_fst_snd_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_product X Y] [has_binary_product (X āØÆ Y) (X āØÆ Y)] {X' : C} (f' : X āØÆ Y ā¶ X') :
    diag (X āØÆ Y) ā« prod.map prod.fst prod.snd ā« f' = f' :=
  sorry

@[simp] theorem prod.diag_map_fst_snd_comp_assoc {C : Type u} [category C]
    [has_limits_of_shape (discrete walking_pair) C] {X : C} {X' : C} {Y : C} {Y' : C} (g : X ā¶ Y)
    (g' : X' ā¶ Y') :
    ā {X'_1 : C} (f' : Y āØÆ Y' ā¶ X'_1),
        diag (X āØÆ X') ā« prod.map (prod.fst ā« g) (prod.snd ā« g') ā« f' = prod.map g g' ā« f' :=
  sorry

protected instance diag.category_theory.split_mono {C : Type u} [category C] {X : C}
    [has_binary_product X X] : split_mono (diag X) :=
  split_mono.mk prod.fst

@[simp] theorem coprod.desc_comp_assoc {C : Type u} [category C] {V : C} {W : C} {X : C} {Y : C}
    [has_binary_coproduct X Y] (f : V ā¶ W) (g : X ā¶ V) (h : Y ā¶ V) {X' : C} (f' : W ā¶ X') :
    coprod.desc g h ā« f ā« f' = coprod.desc (g ā« f) (h ā« f) ā« f' :=
  sorry

theorem coprod.diag_comp {C : Type u} [category C] {X : C} {Y : C} [has_binary_coproduct X X]
    (f : X ā¶ Y) : codiag X ā« f = coprod.desc f f :=
  sorry

@[simp] theorem coprod.inl_map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    coprod.inl ā« coprod.map f g = f ā« coprod.inl :=
  Ī¹_colim_map (map_pair f g) walking_pair.left

@[simp] theorem coprod.inr_map {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) :
    coprod.inr ā« coprod.map f g = g ā« coprod.inr :=
  Ī¹_colim_map (map_pair f g) walking_pair.right

@[simp] theorem coprod.map_id_id {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_coproduct X Y] : coprod.map š š = š :=
  sorry

@[simp] theorem coprod.desc_inl_inr {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_coproduct X Y] : coprod.desc coprod.inl coprod.inr = š :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

@[simp] theorem coprod.map_desc {C : Type u} [category C] {S : C} {T : C} {U : C} {V : C} {W : C}
    [has_binary_coproduct U W] [has_binary_coproduct T V] (f : U ā¶ S) (g : W ā¶ S) (h : T ā¶ U)
    (k : V ā¶ W) : coprod.map h k ā« coprod.desc f g = coprod.desc (h ā« f) (k ā« g) :=
  sorry

@[simp] theorem coprod.desc_comp_inl_comp_inr {C : Type u} [category C] {W : C} {X : C} {Y : C}
    {Z : C} [has_binary_coproduct W Y] [has_binary_coproduct X Z] (g : W ā¶ X) (g' : Y ā¶ Z) :
    coprod.desc (g ā« coprod.inl) (g' ā« coprod.inr) = coprod.map g g' :=
  sorry

-- We take the right hand side here to be simp normal form, as this way composition lemmas for

-- `f ā« h` and `g ā« k` can fire (eg `id_comp`) , while `inl_map` and `inr_map` can still work just

-- as well.

@[simp] theorem coprod.map_map {C : Type u} [category C] {Aā : C} {Aā : C} {Aā : C} {Bā : C}
    {Bā : C} {Bā : C} [has_binary_coproduct Aā Bā] [has_binary_coproduct Aā Bā]
    [has_binary_coproduct Aā Bā] (f : Aā ā¶ Aā) (g : Bā ā¶ Bā) (h : Aā ā¶ Aā) (k : Bā ā¶ Bā) :
    coprod.map f g ā« coprod.map h k = coprod.map (f ā« h) (g ā« k) :=
  sorry

-- I don't think it's a good idea to make any of the following three simp lemmas.

theorem coprod.map_swap_assoc {C : Type u} [category C] {A : C} {B : C} {X : C} {Y : C} (f : A ā¶ B)
    (g : X ā¶ Y) [has_colimits_of_shape (discrete walking_pair) C] {X' : C} (f' : Y āØæ B ā¶ X') :
    coprod.map š f ā« coprod.map g š ā« f' = coprod.map g š ā« coprod.map š f ā« f' :=
  sorry

theorem coprod.map_comp_id {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ā¶ Y)
    (g : Y ā¶ Z) [has_binary_coproduct Z W] [has_binary_coproduct Y W] [has_binary_coproduct X W] :
    coprod.map (f ā« g) š = coprod.map f š ā« coprod.map g š :=
  sorry

theorem coprod.map_id_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} {W : C} (f : X ā¶ Y)
    (g : Y ā¶ Z) [has_binary_coproduct W X] [has_binary_coproduct W Y] [has_binary_coproduct W Z] :
    coprod.map š (f ā« g) = coprod.map š f ā« coprod.map š g :=
  sorry

/-- If the coproducts `W āØæ X` and `Y āØæ Z` exist, then every pair of isomorphisms `f : W ā Y` and
    `g : W ā Z` induces a isomorphism `coprod.map_iso f g : W āØæ X ā Y āØæ Z`. -/
@[simp] theorem coprod.map_iso_hom {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ā Y) (g : X ā Z) :
    iso.hom (coprod.map_iso f g) = coprod.map (iso.hom f) (iso.hom g) :=
  Eq.refl (iso.hom (coprod.map_iso f g))

protected instance is_iso_coprod {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C}
    [has_binary_coproduct W X] [has_binary_coproduct Y Z] (f : W ā¶ Y) (g : X ā¶ Z) [is_iso f]
    [is_iso g] : is_iso (coprod.map f g) :=
  is_iso.of_iso (coprod.map_iso (as_iso f) (as_iso g))

-- The simp linter says simp can prove the reassoc version of this lemma.

@[simp] theorem coprod.map_codiag {C : Type u} [category C] {X : C} {Y : C} (f : X ā¶ Y)
    [has_binary_coproduct X X] [has_binary_coproduct Y Y] :
    coprod.map f f ā« codiag Y = codiag X ā« f :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

theorem coprod.map_inl_inr_codiag_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_binary_coproduct X Y] [has_binary_coproduct (X āØæ Y) (X āØæ Y)] {X' : C} (f' : X āØæ Y ā¶ X') :
    coprod.map coprod.inl coprod.inr ā« codiag (X āØæ Y) ā« f' = f' :=
  sorry

-- The simp linter says simp can prove the reassoc version of this lemma.

@[simp] theorem coprod.map_comp_inl_inr_codiag {C : Type u} [category C]
    [has_colimits_of_shape (discrete walking_pair) C] {X : C} {X' : C} {Y : C} {Y' : C} (g : X ā¶ Y)
    (g' : X' ā¶ Y') :
    coprod.map (g ā« coprod.inl) (g' ā« coprod.inr) ā« codiag (Y āØæ Y') = coprod.map g g' :=
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
    [ā {X Y : C}, has_limit (pair X Y)] : has_binary_products C :=
  has_limits_of_shape.mk
    fun (F : discrete walking_pair ā„¤ C) => has_limit_of_iso (iso.symm (diagram_iso_pair F))

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
theorem has_binary_coproducts_of_has_colimit_pair (C : Type u) [category C]
    [ā {X Y : C}, has_colimit (pair X Y)] : has_binary_coproducts C :=
  has_colimits_of_shape.mk
    fun (F : discrete walking_pair ā„¤ C) => has_colimit_of_iso (diagram_iso_pair F)

/-- The braiding isomorphism which swaps a binary product. -/
@[simp] theorem prod.braiding_hom {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q]
    [has_binary_product Q P] : iso.hom (prod.braiding P Q) = prod.lift prod.snd prod.fst :=
  Eq.refl (iso.hom (prod.braiding P Q))

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
theorem braid_natural {C : Type u} [category C] [has_binary_products C] {W : C} {X : C} {Y : C}
    {Z : C} (f : X ā¶ Y) (g : Z ā¶ W) :
    prod.map f g ā« iso.hom (prod.braiding Y W) = iso.hom (prod.braiding X Z) ā« prod.map g f :=
  sorry

theorem prod.symmetry'_assoc {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q]
    [has_binary_product Q P] {X' : C} (f' : P āØÆ Q ā¶ X') :
    prod.lift prod.snd prod.fst ā« prod.lift prod.snd prod.fst ā« f' = f' :=
  sorry

/-- The braiding isomorphism is symmetric. -/
theorem prod.symmetry_assoc {C : Type u} [category C] (P : C) (Q : C) [has_binary_product P Q]
    [has_binary_product Q P] {X' : C} (f' : P āØÆ Q ā¶ X') :
    iso.hom (prod.braiding P Q) ā« iso.hom (prod.braiding Q P) ā« f' = f' :=
  sorry

/-- The associator isomorphism for binary products. -/
@[simp] theorem prod.associator_hom {C : Type u} [category C] [has_binary_products C] (P : C)
    (Q : C) (R : C) :
    iso.hom (prod.associator P Q R) =
        prod.lift (prod.fst ā« prod.fst) (prod.lift (prod.fst ā« prod.snd) prod.snd) :=
  Eq.refl (iso.hom (prod.associator P Q R))

theorem prod.pentagon_assoc {C : Type u} [category C] [has_binary_products C] (W : C) (X : C)
    (Y : C) (Z : C) {X' : C} (f' : W āØÆ (X āØÆ (Y āØÆ Z)) ā¶ X') :
    prod.map (iso.hom (prod.associator W X Y)) š ā«
          iso.hom (prod.associator W (X āØÆ Y) Z) ā«
            prod.map š (iso.hom (prod.associator X Y Z)) ā« f' =
        iso.hom (prod.associator (W āØÆ X) Y Z) ā« iso.hom (prod.associator W X (Y āØÆ Z)) ā« f' :=
  sorry

theorem prod.associator_naturality_assoc {C : Type u} [category C] [has_binary_products C] {Xā : C}
    {Xā : C} {Xā : C} {Yā : C} {Yā : C} {Yā : C} (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā)
    {X' : C} (f' : Yā āØÆ (Yā āØÆ Yā) ā¶ X') :
    prod.map (prod.map fā fā) fā ā« iso.hom (prod.associator Yā Yā Yā) ā« f' =
        iso.hom (prod.associator Xā Xā Xā) ā« prod.map fā (prod.map fā fā) ā« f' :=
  sorry

/-- The left unitor isomorphism for binary products with the terminal object. -/
def prod.left_unitor {C : Type u} [category C] [has_terminal C] (P : C)
    [has_binary_product (ā¤_C) P] : (ā¤_C) āØÆ P ā P :=
  iso.mk prod.snd (prod.lift (terminal.from P) š)

/-- The right unitor isomorphism for binary products with the terminal object. -/
def prod.right_unitor {C : Type u} [category C] [has_terminal C] (P : C)
    [has_binary_product P (ā¤_C)] : P āØÆ (ā¤_C) ā P :=
  iso.mk prod.fst (prod.lift š (terminal.from P))

theorem prod.left_unitor_hom_naturality_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_terminal C] [has_binary_products C] (f : X ā¶ Y) {X' : C} (f' : Y ā¶ X') :
    prod.map š f ā« iso.hom (prod.left_unitor Y) ā« f' = iso.hom (prod.left_unitor X) ā« f ā« f' :=
  sorry

theorem prod.left_unitor_inv_naturality {C : Type u} [category C] {X : C} {Y : C} [has_terminal C]
    [has_binary_products C] (f : X ā¶ Y) :
    iso.inv (prod.left_unitor X) ā« prod.map š f = f ā« iso.inv (prod.left_unitor Y) :=
  sorry

theorem prod.right_unitor_hom_naturality_assoc {C : Type u} [category C] {X : C} {Y : C}
    [has_terminal C] [has_binary_products C] (f : X ā¶ Y) {X' : C} (f' : Y ā¶ X') :
    prod.map f š ā« iso.hom (prod.right_unitor Y) ā« f' = iso.hom (prod.right_unitor X) ā« f ā« f' :=
  sorry

theorem prod_right_unitor_inv_naturality {C : Type u} [category C] {X : C} {Y : C} [has_terminal C]
    [has_binary_products C] (f : X ā¶ Y) :
    iso.inv (prod.right_unitor X) ā« prod.map f š = f ā« iso.inv (prod.right_unitor Y) :=
  sorry

theorem prod.triangle {C : Type u} [category C] [has_terminal C] [has_binary_products C] (X : C)
    (Y : C) :
    iso.hom (prod.associator X (ā¤_C) Y) ā« prod.map š (iso.hom (prod.left_unitor Y)) =
        prod.map (iso.hom (prod.right_unitor X)) š :=
  sorry

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simp] theorem coprod.braiding_hom {C : Type u} [category C] [has_binary_coproducts C] (P : C)
    (Q : C) : iso.hom (coprod.braiding P Q) = coprod.desc coprod.inr coprod.inl :=
  Eq.refl (iso.hom (coprod.braiding P Q))

theorem coprod.symmetry'_assoc {C : Type u} [category C] [has_binary_coproducts C] (P : C) (Q : C)
    {X' : C} (f' : P āØæ Q ā¶ X') :
    coprod.desc coprod.inr coprod.inl ā« coprod.desc coprod.inr coprod.inl ā« f' = f' :=
  sorry

/-- The braiding isomorphism is symmetric. -/
theorem coprod.symmetry {C : Type u} [category C] [has_binary_coproducts C] (P : C) (Q : C) :
    iso.hom (coprod.braiding P Q) ā« iso.hom (coprod.braiding Q P) = š :=
  coprod.symmetry' P Q

/-- The associator isomorphism for binary coproducts. -/
@[simp] theorem coprod.associator_inv {C : Type u} [category C] [has_binary_coproducts C] (P : C)
    (Q : C) (R : C) :
    iso.inv (coprod.associator P Q R) =
        coprod.desc (coprod.inl ā« coprod.inl) (coprod.desc (coprod.inr ā« coprod.inl) coprod.inr) :=
  Eq.refl (iso.inv (coprod.associator P Q R))

theorem coprod.pentagon {C : Type u} [category C] [has_binary_coproducts C] (W : C) (X : C) (Y : C)
    (Z : C) :
    coprod.map (iso.hom (coprod.associator W X Y)) š ā«
          iso.hom (coprod.associator W (X āØæ Y) Z) ā«
            coprod.map š (iso.hom (coprod.associator X Y Z)) =
        iso.hom (coprod.associator (W āØæ X) Y Z) ā« iso.hom (coprod.associator W X (Y āØæ Z)) :=
  sorry

theorem coprod.associator_naturality {C : Type u} [category C] [has_binary_coproducts C] {Xā : C}
    {Xā : C} {Xā : C} {Yā : C} {Yā : C} {Yā : C} (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) (fā : Xā ā¶ Yā) :
    coprod.map (coprod.map fā fā) fā ā« iso.hom (coprod.associator Yā Yā Yā) =
        iso.hom (coprod.associator Xā Xā Xā) ā« coprod.map fā (coprod.map fā fā) :=
  sorry

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simp] theorem coprod.left_unitor_inv {C : Type u} [category C] [has_binary_coproducts C]
    [has_initial C] (P : C) : iso.inv (coprod.left_unitor P) = coprod.inr :=
  Eq.refl (iso.inv (coprod.left_unitor P))

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simp] theorem coprod.right_unitor_hom {C : Type u} [category C] [has_binary_coproducts C]
    [has_initial C] (P : C) : iso.hom (coprod.right_unitor P) = coprod.desc š (initial.to P) :=
  Eq.refl (iso.hom (coprod.right_unitor P))

theorem coprod.triangle {C : Type u} [category C] [has_binary_coproducts C] [has_initial C] (X : C)
    (Y : C) :
    iso.hom (coprod.associator X (ā„_C) Y) ā« coprod.map š (iso.hom (coprod.left_unitor Y)) =
        coprod.map (iso.hom (coprod.right_unitor X)) š :=
  sorry

/-- The binary product functor. -/
@[simp] theorem prod.functor_obj_map {C : Type u} [category C] [has_binary_products C] (X : C)
    (Y : C) (Z : C) (g : Y ā¶ Z) : functor.map (functor.obj prod.functor X) g = prod.map š g :=
  Eq.refl (functor.map (functor.obj prod.functor X) g)

/-- The product functor can be decomposed. -/
def prod.functor_left_comp {C : Type u} [category C] [has_binary_products C] (X : C) (Y : C) :
    functor.obj prod.functor (X āØÆ Y) ā functor.obj prod.functor Y ā functor.obj prod.functor X :=
  nat_iso.of_components (prod.associator X Y) sorry

/-- The binary coproduct functor. -/
@[simp] theorem coprod.functor_obj_map {C : Type u} [category C] [has_binary_coproducts C] (X : C)
    (Y : C) (Z : C) (g : Y ā¶ Z) : functor.map (functor.obj coprod.functor X) g = coprod.map š g :=
  Eq.refl (functor.map (functor.obj coprod.functor X) g)

/-- The coproduct functor can be decomposed. -/
def coprod.functor_left_comp {C : Type u} [category C] [has_binary_coproducts C] (X : C) (Y : C) :
    functor.obj coprod.functor (X āØæ Y) ā
        functor.obj coprod.functor Y ā functor.obj coprod.functor X :=
  nat_iso.of_components (coprod.associator X Y) sorry

/--
The product comparison morphism.

In `category_theory/limits/preserves` we show this is always an iso iff F preserves binary products.
-/
def prod_comparison {C : Type u} [category C] {D : Type uā} [category D] (F : C ā„¤ D) (A : C) (B : C)
    [has_binary_product A B] [has_binary_product (functor.obj F A) (functor.obj F B)] :
    functor.obj F (A āØÆ B) ā¶ functor.obj F A āØÆ functor.obj F B :=
  prod.lift (functor.map F prod.fst) (functor.map F prod.snd)

@[simp] theorem prod_comparison_fst_assoc {C : Type u} [category C] {D : Type uā} [category D]
    (F : C ā„¤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] {X' : D} (f' : functor.obj F A ā¶ X') :
    prod_comparison F A B ā« prod.fst ā« f' = functor.map F prod.fst ā« f' :=
  sorry

@[simp] theorem prod_comparison_snd_assoc {C : Type u} [category C] {D : Type uā} [category D]
    (F : C ā„¤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] {X' : D} (f' : functor.obj F B ā¶ X') :
    prod_comparison F A B ā« prod.snd ā« f' = functor.map F prod.snd ā« f' :=
  sorry

/-- Naturality of the prod_comparison morphism in both arguments. -/
theorem prod_comparison_natural_assoc {C : Type u} [category C] {D : Type uā} [category D]
    (F : C ā„¤ D) {A : C} {A' : C} {B : C} {B' : C} [has_binary_product A B]
    [has_binary_product A' B'] [has_binary_product (functor.obj F A) (functor.obj F B)]
    [has_binary_product (functor.obj F A') (functor.obj F B')] (f : A ā¶ A') (g : B ā¶ B') {X' : D}
    (f' : functor.obj F A' āØÆ functor.obj F B' ā¶ X') :
    functor.map F (prod.map f g) ā« prod_comparison F A' B' ā« f' =
        prod_comparison F A B ā« prod.map (functor.map F f) (functor.map F g) ā« f' :=
  sorry

/--
The product comparison morphism from `F(A āØÆ -)` to `FA āØÆ F-`, whose components are given by
`prod_comparison`.
-/
def prod_comparison_nat_trans {C : Type u} [category C] {D : Type uā} [category D]
    [has_binary_products C] [has_binary_products D] (F : C ā„¤ D) (A : C) :
    functor.obj prod.functor A ā F ā¶ F ā functor.obj prod.functor (functor.obj F A) :=
  nat_trans.mk fun (B : C) => prod_comparison F A B

theorem inv_prod_comparison_map_fst_assoc {C : Type u} [category C] {D : Type uā} [category D]
    (F : C ā„¤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] [is_iso (prod_comparison F A B)]
    {X' : D} (f' : functor.obj F A ā¶ X') :
    inv (prod_comparison F A B) ā« functor.map F prod.fst ā« f' = prod.fst ā« f' :=
  sorry

theorem inv_prod_comparison_map_snd_assoc {C : Type u} [category C] {D : Type uā} [category D]
    (F : C ā„¤ D) {A : C} {B : C} [has_binary_product A B]
    [has_binary_product (functor.obj F A) (functor.obj F B)] [is_iso (prod_comparison F A B)]
    {X' : D} (f' : functor.obj F B ā¶ X') :
    inv (prod_comparison F A B) ā« functor.map F prod.snd ā« f' = prod.snd ā« f' :=
  sorry

/-- If the product comparison morphism is an iso, its inverse is natural. -/
theorem prod_comparison_inv_natural {C : Type u} [category C] {D : Type uā} [category D] (F : C ā„¤ D)
    {A : C} {A' : C} {B : C} {B' : C} [has_binary_product A B] [has_binary_product A' B']
    [has_binary_product (functor.obj F A) (functor.obj F B)]
    [has_binary_product (functor.obj F A') (functor.obj F B')] (f : A ā¶ A') (g : B ā¶ B')
    [is_iso (prod_comparison F A B)] [is_iso (prod_comparison F A' B')] :
    inv (prod_comparison F A B) ā« functor.map F (prod.map f g) =
        prod.map (functor.map F f) (functor.map F g) ā« inv (prod_comparison F A' B') :=
  sorry

/--
The natural isomorphism `F(A āØÆ -) ā FA āØÆ F-`, provided each `prod_comparison F A B` is an
isomorphism (as `B` changes).
-/
def prod_comparison_nat_iso {C : Type u} [category C] {D : Type uā} [category D] (F : C ā„¤ D)
    [has_binary_products C] [has_binary_products D] (A : C)
    [(B : C) ā is_iso (prod_comparison F A B)] :
    functor.obj prod.functor A ā F ā F ā functor.obj prod.functor (functor.obj F A) :=
  iso.mk (prod_comparison_nat_trans F A) (inv (nat_trans.mk fun (B : C) => prod_comparison F A B))

end Mathlib