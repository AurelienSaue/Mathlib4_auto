/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.wide_pullbacks
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.PostPort

universes v u_1 u u₂ 

namespace Mathlib

/-!
# Pullbacks

We define a category `walking_cospan` (resp. `walking_span`), which is the index category
for the given data for a pullback (resp. pushout) diagram. Convenience methods `cospan f g`
and `span f g` construct functors from the walking (co)span, hitting the given morphisms.

We define `pullback f g` and `pushout f g` as limits and colimits of such functors.

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

namespace category_theory.limits


/--
The type of objects for the diagram indexing a pullback, defined as a special case of
`wide_pullback_shape`.
-/
def walking_cospan  :=
  wide_pullback_shape walking_pair

/-- The left point of the walking cospan. -/
/-- The right point of the walking cospan. -/
def walking_cospan.left : walking_cospan :=
  some walking_pair.left

/-- The central point of the walking cospan. -/
def walking_cospan.right : walking_cospan :=
  some walking_pair.right

def walking_cospan.one : walking_cospan :=
  none

/--
The type of objects for the diagram indexing a pushout, defined as a special case of
`wide_pushout_shape`.
-/
def walking_span  :=
  wide_pushout_shape walking_pair

/-- The left point of the walking span. -/
/-- The right point of the walking span. -/
def walking_span.left : walking_span :=
  some walking_pair.left

/-- The central point of the walking span. -/
def walking_span.right : walking_span :=
  some walking_pair.right

def walking_span.zero : walking_span :=
  none

namespace walking_cospan


/-- The type of arrows for the diagram indexing a pullback. -/
def hom : walking_cospan → walking_cospan → Type v :=
  wide_pullback_shape.hom

/-- The left arrow of the walking cospan. -/
/-- The right arrow of the walking cospan. -/
def hom.inl : left ⟶ one :=
  wide_pullback_shape.hom.term walking_pair.left

/-- The identity arrows of the walking cospan. -/
def hom.inr : right ⟶ one :=
  wide_pullback_shape.hom.term walking_pair.right

def hom.id (X : walking_cospan) : X ⟶ X :=
  wide_pullback_shape.hom.id X

protected instance category_theory.has_hom.hom.subsingleton (X : walking_cospan) (Y : walking_cospan) : subsingleton (X ⟶ Y) :=
  subsingleton.intro fun (a b : X ⟶ Y) => eq.mpr (id (propext (eq_iff_true_of_subsingleton a b))) trivial

end walking_cospan


namespace walking_span


/-- The type of arrows for the diagram indexing a pushout. -/
def hom : walking_span → walking_span → Type v :=
  wide_pushout_shape.hom

/-- The left arrow of the walking span. -/
/-- The right arrow of the walking span. -/
def hom.fst : zero ⟶ left :=
  wide_pushout_shape.hom.init walking_pair.left

/-- The identity arrows of the walking span. -/
def hom.snd : zero ⟶ right :=
  wide_pushout_shape.hom.init walking_pair.right

def hom.id (X : walking_span) : X ⟶ X :=
  wide_pushout_shape.hom.id X

protected instance category_theory.has_hom.hom.subsingleton (X : walking_span) (Y : walking_span) : subsingleton (X ⟶ Y) :=
  subsingleton.intro fun (a b : X ⟶ Y) => eq.mpr (id (propext (eq_iff_true_of_subsingleton a b))) trivial

end walking_span


/-- `cospan f g` is the functor from the walking cospan hitting `f` and `g`. -/
def cospan {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : walking_cospan ⥤ C :=
  wide_pullback_shape.wide_cospan Z (fun (j : walking_pair) => walking_pair.cases_on j X Y)
    fun (j : walking_pair) => walking_pair.cases_on j f g

/-- `span f g` is the functor from the walking span hitting `f` and `g`. -/
def span {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : walking_span ⥤ C :=
  wide_pushout_shape.wide_span X (fun (j : walking_pair) => walking_pair.cases_on j Y Z)
    fun (j : walking_pair) => walking_pair.cases_on j f g

@[simp] theorem cospan_left {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : functor.obj (cospan f g) walking_cospan.left = X :=
  rfl

@[simp] theorem span_left {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : functor.obj (span f g) walking_span.left = Y :=
  rfl

@[simp] theorem cospan_right {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : functor.obj (cospan f g) walking_cospan.right = Y :=
  rfl

@[simp] theorem span_right {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : functor.obj (span f g) walking_span.right = Z :=
  rfl

@[simp] theorem cospan_one {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : functor.obj (cospan f g) walking_cospan.one = Z :=
  rfl

@[simp] theorem span_zero {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : functor.obj (span f g) walking_span.zero = X :=
  rfl

@[simp] theorem cospan_map_inl {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : functor.map (cospan f g) walking_cospan.hom.inl = f :=
  rfl

@[simp] theorem span_map_fst {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : functor.map (span f g) walking_span.hom.fst = f :=
  rfl

@[simp] theorem cospan_map_inr {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : functor.map (cospan f g) walking_cospan.hom.inr = g :=
  rfl

@[simp] theorem span_map_snd {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : functor.map (span f g) walking_span.hom.snd = g :=
  rfl

theorem cospan_map_id {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (w : walking_cospan) : functor.map (cospan f g) (walking_cospan.hom.id w) = 𝟙 :=
  rfl

theorem span_map_id {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (w : walking_span) : functor.map (span f g) (walking_span.hom.id w) = 𝟙 :=
  rfl

/-- Every diagram indexing an pullback is naturally isomorphic (actually, equal) to a `cospan` -/
def diagram_iso_cospan {C : Type u} [category C] (F : walking_cospan ⥤ C) : F ≅ cospan (functor.map F walking_cospan.hom.inl) (functor.map F walking_cospan.hom.inr) :=
  nat_iso.of_components (fun (j : walking_cospan) => eq_to_iso sorry) sorry

/-- Every diagram indexing a pushout is naturally isomorphic (actually, equal) to a `span` -/
def diagram_iso_span {C : Type u} [category C] (F : walking_span ⥤ C) : F ≅ span (functor.map F walking_span.hom.fst) (functor.map F walking_span.hom.snd) :=
  nat_iso.of_components (fun (j : walking_span) => eq_to_iso sorry) sorry

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
    `g : Y ⟶ Z`.-/
def pullback_cone {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)  :=
  cone (cospan f g)

namespace pullback_cone


/-- The first projection of a pullback cone. -/
def fst {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : pullback_cone f g) : cone.X t ⟶ X :=
  nat_trans.app (cone.π t) walking_cospan.left

/-- The second projection of a pullback cone. -/
def snd {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : pullback_cone f g) : cone.X t ⟶ Y :=
  nat_trans.app (cone.π t) walking_cospan.right

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def is_limit_aux {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : pullback_cone f g) (lift : (s : cone (cospan f g)) → cone.X s ⟶ cone.X t) (fac_left : ∀ (s : pullback_cone f g), lift s ≫ fst t = fst s) (fac_right : ∀ (s : pullback_cone f g), lift s ≫ snd t = snd s) (uniq : ∀ (s : pullback_cone f g) (m : cone.X s ⟶ cone.X t),
  (∀ (j : walking_cospan), m ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j) → m = lift s) : is_limit t :=
  is_limit.mk lift

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def is_limit_aux' {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : pullback_cone f g) (create : (s : pullback_cone f g) →
  Subtype
    fun (l : cone.X s ⟶ cone.X t) =>
      l ≫ fst t = fst s ∧ l ≫ snd t = snd s ∧ ∀ {m : cone.X s ⟶ cone.X t}, m ≫ fst t = fst s → m ≫ snd t = snd s → m = l) : is_limit t :=
  is_limit_aux t (fun (s : cone (cospan f g)) => subtype.val (create s)) sorry sorry sorry

/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
    such that `fst ≫ f = snd ≫ g`. -/
@[simp] theorem mk_π_app {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) (j : walking_cospan) : nat_trans.app (cone.π (mk fst snd eq)) j =
  option.cases_on j (fst ≫ f) fun (j' : walking_pair) => walking_pair.cases_on j' fst snd :=
  Eq.refl (nat_trans.app (cone.π (mk fst snd eq)) j)

@[simp] theorem mk_π_app_left {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : nat_trans.app (cone.π (mk fst snd eq)) walking_cospan.left = fst :=
  rfl

@[simp] theorem mk_π_app_right {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : nat_trans.app (cone.π (mk fst snd eq)) walking_cospan.right = snd :=
  rfl

@[simp] theorem mk_π_app_one {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : nat_trans.app (cone.π (mk fst snd eq)) walking_cospan.one = fst ≫ f :=
  rfl

@[simp] theorem mk_fst {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : fst (mk fst snd eq) = fst :=
  rfl

@[simp] theorem mk_snd {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : snd (mk fst snd eq) = snd :=
  rfl

theorem condition_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : pullback_cone f g) {X' : C} (f' : Z ⟶ X') : fst t ≫ f ≫ f' = snd t ≫ g ≫ f' := sorry

/-- To check whether a morphism is equalized by the maps of a pullback cone, it suffices to check
  it for `fst t` and `snd t` -/
theorem equalizer_ext {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (t : pullback_cone f g) {W : C} {k : W ⟶ cone.X t} {l : W ⟶ cone.X t} (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) (j : walking_cospan) : k ≫ nat_trans.app (cone.π t) j = l ≫ nat_trans.app (cone.π t) j := sorry

theorem is_limit.hom_ext {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : pullback_cone f g} (ht : is_limit t) {W : C} {k : W ⟶ cone.X t} {l : W ⟶ cone.X t} (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  is_limit.hom_ext ht (equalizer_ext t h₀ h₁)

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
    `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.X` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
    -/
def is_limit.lift' {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : pullback_cone f g} (ht : is_limit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : Subtype fun (l : W ⟶ cone.X t) => l ≫ fst t = h ∧ l ≫ snd t = k :=
  { val := is_limit.lift ht (mk h k w), property := sorry }

/--
This is a more convenient formulation to show that a `pullback_cone` constructed using
`pullback_cone.mk` is a limit cone.
-/
def is_limit.mk {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g) (lift : (s : pullback_cone f g) → cone.X s ⟶ W) (fac_left : ∀ (s : pullback_cone f g), lift s ≫ fst = fst s) (fac_right : ∀ (s : pullback_cone f g), lift s ≫ snd = snd s) (uniq : ∀ (s : pullback_cone f g) (m : cone.X s ⟶ W), m ≫ fst = fst s → m ≫ snd = snd s → m = lift s) : is_limit (mk fst snd eq) :=
  is_limit_aux (mk fst snd eq) lift fac_left fac_right sorry

/-- The flip of a pullback square is a pullback square. -/
def flip_is_limit {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} {h : W ⟶ X} {k : W ⟶ Y} {comm : h ≫ f = k ≫ g} (t : is_limit (mk k h flip_is_limit._proof_1)) : is_limit (mk h k comm) :=
  is_limit_aux' (mk h k comm)
    fun (s : pullback_cone f g) => { val := subtype.val (is_limit.lift' t (snd s) (fst s) sorry), property := sorry }

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def is_limit_mk_id_id {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] : is_limit (mk 𝟙 𝟙 (is_limit_mk_id_id._proof_1 f)) :=
  is_limit.mk sorry (fun (s : pullback_cone f f) => fst s) sorry sorry sorry

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `pullback_cone.is_id_of_mono`.
-/
theorem mono_of_is_limit_mk_id_id {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (t : is_limit (mk 𝟙 𝟙 rfl)) : mono f := sorry

end pullback_cone


/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
    `g : X ⟶ Z`.-/
def pushout_cocone {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  :=
  cocone (span f g)

namespace pushout_cocone


/-- The first inclusion of a pushout cocone. -/
def inl {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : pushout_cocone f g) : Y ⟶ cocone.X t :=
  nat_trans.app (cocone.ι t) walking_span.left

/-- The second inclusion of a pushout cocone. -/
def inr {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : pushout_cocone f g) : Z ⟶ cocone.X t :=
  nat_trans.app (cocone.ι t) walking_span.right

/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
    It only asks for a proof of facts that carry any mathematical content -/
def is_colimit_aux {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : pushout_cocone f g) (desc : (s : pushout_cocone f g) → cocone.X t ⟶ cocone.X s) (fac_left : ∀ (s : pushout_cocone f g), inl t ≫ desc s = inl s) (fac_right : ∀ (s : pushout_cocone f g), inr t ≫ desc s = inr s) (uniq : ∀ (s : pushout_cocone f g) (m : cocone.X t ⟶ cocone.X s),
  (∀ (j : walking_span), nat_trans.app (cocone.ι t) j ≫ m = nat_trans.app (cocone.ι s) j) → m = desc s) : is_colimit t :=
  is_colimit.mk desc

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def is_colimit_aux' {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : pushout_cocone f g) (create : (s : pushout_cocone f g) →
  Subtype
    fun (l : cocone.X t ⟶ cocone.X s) =>
      inl t ≫ l = inl s ∧
        inr t ≫ l = inr s ∧ ∀ {m : cocone.X t ⟶ cocone.X s}, inl t ≫ m = inl s → inr t ≫ m = inr s → m = l) : is_colimit t :=
  is_colimit_aux t (fun (s : pushout_cocone f g) => subtype.val (create s)) sorry sorry sorry

/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
    that `f ≫ inl = g ↠ inr`. -/
def mk {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : pushout_cocone f g :=
  cocone.mk W
    (nat_trans.mk
      fun (j : walking_span) => option.cases_on j (f ≫ inl) fun (j' : walking_pair) => walking_pair.cases_on j' inl inr)

@[simp] theorem mk_ι_app_left {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : nat_trans.app (cocone.ι (mk inl inr eq)) walking_span.left = inl :=
  rfl

@[simp] theorem mk_ι_app_right {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : nat_trans.app (cocone.ι (mk inl inr eq)) walking_span.right = inr :=
  rfl

@[simp] theorem mk_ι_app_zero {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : nat_trans.app (cocone.ι (mk inl inr eq)) walking_span.zero = f ≫ inl :=
  rfl

@[simp] theorem mk_inl {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : inl (mk inl inr eq) = inl :=
  rfl

@[simp] theorem mk_inr {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : inr (mk inl inr eq) = inr :=
  rfl

theorem condition_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : pushout_cocone f g) {X' : C} (f' : cocone.X t ⟶ X') : f ≫ inl t ≫ f' = g ≫ inr t ≫ f' := sorry

/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
theorem coequalizer_ext {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} (t : pushout_cocone f g) {W : C} {k : cocone.X t ⟶ W} {l : cocone.X t ⟶ W} (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) (j : walking_span) : nat_trans.app (cocone.ι t) j ≫ k = nat_trans.app (cocone.ι t) j ≫ l := sorry

theorem is_colimit.hom_ext {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {t : pushout_cocone f g} (ht : is_colimit t) {W : C} {k : cocone.X t ⟶ W} {l : cocone.X t ⟶ W} (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  is_colimit.hom_ext ht (coequalizer_ext t h₀ h₁)

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
    morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.X ⟶ W` such that
    `inl t ≫ l = h` and `inr t ≫ l = k`. -/
def is_colimit.desc' {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {t : pushout_cocone f g} (ht : is_colimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : Subtype fun (l : cocone.X t ⟶ W) => inl t ≫ l = h ∧ inr t ≫ l = k :=
  { val := is_colimit.desc ht (mk h k w), property := sorry }

/--
This is a more convenient formulation to show that a `pushout_cocone` constructed using
`pushout_cocone.mk` is a colimit cocone.
-/
def is_colimit.mk {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr) (desc : (s : pushout_cocone f g) → W ⟶ cocone.X s) (fac_left : ∀ (s : pushout_cocone f g), inl ≫ desc s = inl s) (fac_right : ∀ (s : pushout_cocone f g), inr ≫ desc s = inr s) (uniq : ∀ (s : pushout_cocone f g) (m : W ⟶ cocone.X s), inl ≫ m = inl s → inr ≫ m = inr s → m = desc s) : is_colimit (mk inl inr eq) :=
  is_colimit_aux (mk inl inr eq) desc fac_left fac_right sorry

/-- The flip of a pushout square is a pushout square. -/
def flip_is_colimit {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} {h : Y ⟶ W} {k : Z ⟶ W} {comm : f ≫ h = g ≫ k} (t : is_colimit (mk k h flip_is_colimit._proof_1)) : is_colimit (mk h k comm) :=
  is_colimit_aux' (mk h k comm)
    fun (s : pushout_cocone f g) => { val := subtype.val (is_colimit.desc' t (inr s) (inl s) sorry), property := sorry }

end pushout_cocone


/-- This is a helper construction that can be useful when verifying that a category has all
    pullbacks. Given `F : walking_cospan ⥤ C`, which is really the same as
    `cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
    get a cone on `F`.

    If you're thinking about using this, have a look at `has_pullbacks_of_has_limit_cospan`,
    which you may find to be an easier way of achieving your goal. -/
@[simp] theorem cone.of_pullback_cone_π {C : Type u} [category C] {F : walking_cospan ⥤ C} (t : pullback_cone (functor.map F walking_cospan.hom.inl) (functor.map F walking_cospan.hom.inr)) : cone.π (cone.of_pullback_cone t) = cone.π t ≫ iso.inv (diagram_iso_cospan F) :=
  Eq.refl (cone.π (cone.of_pullback_cone t))

/-- This is a helper construction that can be useful when verifying that a category has all
    pushout. Given `F : walking_span ⥤ C`, which is really the same as
    `span (F.map fst) (F.mal snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at `has_pushouts_of_has_colimit_span`, which
    you may find to be an easiery way of achieving your goal.  -/
@[simp] theorem cocone.of_pushout_cocone_X {C : Type u} [category C] {F : walking_span ⥤ C} (t : pushout_cocone (functor.map F walking_span.hom.fst) (functor.map F walking_span.hom.snd)) : cocone.X (cocone.of_pushout_cocone t) = cocone.X t :=
  Eq.refl (cocone.X (cocone.of_pushout_cocone t))

/-- Given `F : walking_cospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
    and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simp] theorem pullback_cone.of_cone_X {C : Type u} [category C] {F : walking_cospan ⥤ C} (t : cone F) : cone.X (pullback_cone.of_cone t) = cone.X t :=
  Eq.refl (cone.X (pullback_cone.of_cone t))

/-- Given `F : walking_span ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
    and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
def pushout_cocone.of_cocone {C : Type u} [category C] {F : walking_span ⥤ C} (t : cocone F) : pushout_cocone (functor.map F walking_span.hom.fst) (functor.map F walking_span.hom.snd) :=
  cocone.mk (cocone.X t) (iso.inv (diagram_iso_span F) ≫ cocone.ι t)

/--
`has_pullback f g` represents a particular choice of limiting cone
for the pair of morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`.
-/
/--
def has_pullback {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)  :=
  has_limit (cospan f g)

`has_pushout f g` represents a particular choice of colimiting cocone
for the pair of morphisms `f : X ⟶ Y` and `g : X ⟶ Z`.
-/
def has_pushout {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z)  :=
  has_colimit (span f g)

/-- `pullback f g` computes the pullback of a pair of morphisms with the same target. -/
def pullback {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] : C :=
  limit (cospan f g)

/-- `pushout f g` computes the pushout of a pair of morphisms with the same source. -/
def pushout {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [has_pushout f g] : C :=
  colimit (span f g)

/-- The first projection of the pullback of `f` and `g`. -/
def pullback.fst {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] : pullback f g ⟶ X :=
  limit.π (cospan f g) walking_cospan.left

/-- The second projection of the pullback of `f` and `g`. -/
def pullback.snd {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] : pullback f g ⟶ Y :=
  limit.π (cospan f g) walking_cospan.right

/-- The first inclusion into the pushout of `f` and `g`. -/
def pushout.inl {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] : Y ⟶ pushout f g :=
  colimit.ι (span f g) walking_span.left

/-- The second inclusion into the pushout of `f` and `g`. -/
def pushout.inr {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] : Z ⟶ pushout f g :=
  colimit.ι (span f g) walking_span.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `pullback.lift : W ⟶ pullback f g`. -/
def pullback.lift {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : W ⟶ pullback f g :=
  limit.lift (cospan f g) (pullback_cone.mk h k w)

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `pushout.desc : pushout f g ⟶ W`. -/
def pushout.desc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : pushout f g ⟶ W :=
  colimit.desc (span f g) (pushout_cocone.mk h k w)

@[simp] theorem pullback.lift_fst_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) {X' : C} (f' : X ⟶ X') : pullback.lift h k w ≫ pullback.fst ≫ f' = h ≫ f' := sorry

@[simp] theorem pullback.lift_snd_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) {X' : C} (f' : Y ⟶ X') : pullback.lift h k w ≫ pullback.snd ≫ f' = k ≫ f' := sorry

@[simp] theorem pushout.inl_desc_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {X' : C} (f' : W ⟶ X') : pushout.inl ≫ pushout.desc h k w ≫ f' = h ≫ f' := sorry

@[simp] theorem pushout.inr_desc_assoc {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) {X' : C} (f' : W ⟶ X') : pushout.inr ≫ pushout.desc h k w ≫ f' = k ≫ f' := sorry

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
    `l : W ⟶ pullback f g` such that `l ≫ pullback.fst = h` and `l ≫ pullback.snd = k`. -/
def pullback.lift' {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : Subtype fun (l : W ⟶ pullback f g) => l ≫ pullback.fst = h ∧ l ≫ pullback.snd = k :=
  { val := pullback.lift h k w, property := sorry }

/-- A pair of morphisms `h : Y ⟶ W` and `k : Z ⟶ W` satisfying `f ≫ h = g ≫ k` induces a morphism
    `l : pushout f g ⟶ W` such that `pushout.inl ≫ l = h` and `pushout.inr ≫ l = k`. -/
def pullback.desc' {C : Type u} [category C] {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] (h : Y ⟶ W) (k : Z ⟶ W) (w : f ≫ h = g ≫ k) : Subtype fun (l : pushout f g ⟶ W) => pushout.inl ≫ l = h ∧ pushout.inr ≫ l = k :=
  { val := pushout.desc h k w, property := sorry }

theorem pullback.condition {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] : pullback.fst ≫ f = pullback.snd ≫ g :=
  pullback_cone.condition (limit.cone (cospan f g))

theorem pushout.condition_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] {X' : C} (f' : pushout f g ⟶ X') : f ≫ pushout.inl ≫ f' = g ≫ pushout.inr ≫ f' := sorry

/-- Two morphisms into a pullback are equal if their compositions with the pullback morphisms are
    equal -/
theorem pullback.hom_ext {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] {W : C} {k : W ⟶ pullback f g} {l : W ⟶ pullback f g} (h₀ : k ≫ pullback.fst = l ≫ pullback.fst) (h₁ : k ≫ pullback.snd = l ≫ pullback.snd) : k = l :=
  limit.hom_ext (pullback_cone.equalizer_ext (limit.cone (cospan f g)) h₀ h₁)

/-- The pullback cone built from the pullback projections is a pullback. -/
def pullback_is_pullback {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] : is_limit (pullback_cone.mk pullback.fst pullback.snd pullback.condition) :=
  pullback_cone.is_limit.mk pullback.condition
    (fun (s : pullback_cone f g) => pullback.lift (pullback_cone.fst s) (pullback_cone.snd s) (pullback_cone.condition s))
    sorry sorry sorry

/-- The pullback of a monomorphism is a monomorphism -/
protected instance pullback.fst_of_mono {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] [mono g] : mono pullback.fst := sorry

/-- The pullback of a monomorphism is a monomorphism -/
protected instance pullback.snd_of_mono {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] [mono f] : mono pullback.snd := sorry

/-- Two morphisms out of a pushout are equal if their compositions with the pushout morphisms are
    equal -/
theorem pushout.hom_ext {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] {W : C} {k : pushout f g ⟶ W} {l : pushout f g ⟶ W} (h₀ : pushout.inl ≫ k = pushout.inl ≫ l) (h₁ : pushout.inr ≫ k = pushout.inr ≫ l) : k = l :=
  colimit.hom_ext (pushout_cocone.coequalizer_ext (colimit.cocone (span f g)) h₀ h₁)

/-- The pushout of an epimorphism is an epimorphism -/
protected instance pushout.inl_of_epi {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi g] : epi pushout.inl :=
  epi.mk
    fun (W : C) (u v : pushout f g ⟶ W) (h : pushout.inl ≫ u = pushout.inl ≫ v) =>
      pushout.hom_ext h
        (iff.mp (cancel_epi g)
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : X ⟶ W) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ W) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                  (g ≫ pushout.inr ≫ u) (f ≫ pushout.inl ≫ v)
                  (Eq.trans (Eq.symm (pushout.condition_assoc u))
                    ((fun (ᾰ ᾰ_1 : X ⟶ Y) (e_1 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : Y ⟶ W) (e_2 : ᾰ_2 = ᾰ_3) =>
                        congr (congr_arg category_struct.comp e_1) e_2)
                      f f (Eq.refl f) (pushout.inl ≫ u) (pushout.inl ≫ v) h))
                  (g ≫ pushout.inr ≫ v) (f ≫ pushout.inl ≫ v) (Eq.symm (pushout.condition_assoc v)))
                (propext (eq_self_iff_true (f ≫ pushout.inl ≫ v)))))
            trivial))

/-- The pushout of an epimorphism is an epimorphism -/
protected instance pushout.inr_of_epi {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [has_pushout f g] [epi f] : epi pushout.inr :=
  epi.mk
    fun (W : C) (u v : pushout f g ⟶ W) (h : pushout.inr ≫ u = pushout.inr ≫ v) =>
      pushout.hom_ext
        (iff.mp (cancel_epi f)
          (eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : X ⟶ W) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ W) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                  (f ≫ pushout.inl ≫ u) (g ≫ pushout.inr ≫ v)
                  (Eq.trans (pushout.condition_assoc u)
                    ((fun (ᾰ ᾰ_1 : X ⟶ Z) (e_1 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : Z ⟶ W) (e_2 : ᾰ_2 = ᾰ_3) =>
                        congr (congr_arg category_struct.comp e_1) e_2)
                      g g (Eq.refl g) (pushout.inr ≫ u) (pushout.inr ≫ v) h))
                  (f ≫ pushout.inl ≫ v) (g ≫ pushout.inr ≫ v) (pushout.condition_assoc v))
                (propext (eq_self_iff_true (g ≫ pushout.inr ≫ v)))))
            trivial))
        h

/--
The comparison morphism for the pullback of `f,g`.
This is an isomorphism iff `G` preserves the pullback of `f,g`; see
`category_theory/limits/preserves/shapes/pullbacks.lean`
-/
def pullback_comparison {C : Type u} [category C] {X : C} {Y : C} {Z : C} {D : Type u₂} [category D] (G : C ⥤ D) (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] : functor.obj G (pullback f g) ⟶ pullback (functor.map G f) (functor.map G g) :=
  pullback.lift (functor.map G pullback.fst) (functor.map G pullback.snd) sorry

@[simp] theorem pullback_comparison_comp_fst_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {D : Type u₂} [category D] (G : C ⥤ D) (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] {X' : D} (f' : functor.obj G X ⟶ X') : pullback_comparison G f g ≫ pullback.fst ≫ f' = functor.map G pullback.fst ≫ f' := sorry

@[simp] theorem pullback_comparison_comp_snd_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {D : Type u₂} [category D] (G : C ⥤ D) (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] {X' : D} (f' : functor.obj G Y ⟶ X') : pullback_comparison G f g ≫ pullback.snd ≫ f' = functor.map G pullback.snd ≫ f' := sorry

@[simp] theorem map_lift_pullback_comparison_assoc {C : Type u} [category C] {X : C} {Y : C} {Z : C} {D : Type u₂} [category D] (G : C ⥤ D) (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] {W : C} {h : W ⟶ X} {k : W ⟶ Y} (w : h ≫ f = k ≫ g) {X' : D} (f' : pullback (functor.map G f) (functor.map G g) ⟶ X') : functor.map G (pullback.lift h k w) ≫ pullback_comparison G f g ≫ f' =
  pullback.lift (functor.map G h) (functor.map G k)
      (eq.mpr
        (id
          ((fun (a a_1 : functor.obj G W ⟶ functor.obj G Z) (e_1 : a = a_1) (ᾰ ᾰ_1 : functor.obj G W ⟶ functor.obj G Z)
              (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
            (functor.map G h ≫ functor.map G f) (functor.map G (k ≫ g))
            (Eq.trans (Eq.symm (functor.map_comp G h f))
              ((fun (c : C ⥤ D) {X Y : C} (ᾰ ᾰ_1 : X ⟶ Y) (e_4 : ᾰ = ᾰ_1) => congr_arg (functor.map c) e_4) G (h ≫ f)
                (k ≫ g) w))
            (functor.map G k ≫ functor.map G g) (functor.map G (k ≫ g)) (Eq.symm (functor.map_comp G k g))))
        (Eq.refl (functor.map G (k ≫ g)))) ≫
    f' := sorry

/--
`has_pullbacks` represents a choice of pullback for every pair of morphisms

See https://stacks.math.columbia.edu/tag/001W.
-/
def has_pullbacks (C : Type u) [category C]  :=
  has_limits_of_shape walking_cospan C

/-- `has_pushouts` represents a choice of pushout for every pair of morphisms -/
def has_pushouts (C : Type u) [category C]  :=
  has_colimits_of_shape walking_span C

/-- If `C` has all limits of diagrams `cospan f g`, then it has all pullbacks -/
theorem has_pullbacks_of_has_limit_cospan (C : Type u) [category C] [∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}, has_limit (cospan f g)] : has_pullbacks C :=
  has_limits_of_shape.mk fun (F : walking_cospan ⥤ C) => has_limit_of_iso (iso.symm (diagram_iso_cospan F))

/-- If `C` has all colimits of diagrams `span f g`, then it has all pushouts -/
theorem has_pushouts_of_has_colimit_span (C : Type u) [category C] [∀ {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}, has_colimit (span f g)] : has_pushouts C :=
  has_colimits_of_shape.mk fun (F : walking_span ⥤ C) => has_colimit_of_iso (diagram_iso_span F)

