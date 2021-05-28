/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.PostPort

universes v u l u₂ 

namespace Mathlib

/-!
# Split coequalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split
coequalizer: there is a section `s` of `π` and a section `t` of `g`, which additionally satisfy
`t ≫ f = π ≫ s`.

In addition, we show that every split coequalizer is a coequalizer
(`category_theory.is_split_coequalizer.is_coequalizer`) and absolute
(`category_theory.is_split_coequalizer.map`)

A pair `f g : X ⟶ Y` has a split coequalizer if there is a `Z` and `π : Y ⟶ Z` making `f,g,π` a
split coequalizer.
A pair `f g : X ⟶ Y` has a `G`-split coequalizer if `G f, G g` has a split coequalizer.

These definitions and constructions are useful in particular for the monadicity theorems.

## TODO

Dualise to split equalizers.
-/

namespace category_theory


/--
A split coequalizer diagram consists of morphisms

      f   π
    X ⇉ Y → Z
      g

satisfying `f ≫ π = g ≫ π` together with morphisms

      t   s
    X ← Y ← Z

satisfying `s ≫ π = 𝟙 Z`, `t ≫ g = 𝟙 Y` and `t ≫ f = π ≫ s`.

The name "coequalizer" is appropriate, since any split coequalizer is a coequalizer, see
`category_theory.is_split_coequalizer.is_coequalizer`.
Split coequalizers are also absolute, since a functor preserves all the structure above.
-/
structure is_split_coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {Z : C} (π : Y ⟶ Z) 
where
  right_section : Z ⟶ Y
  left_section : Y ⟶ X
  condition : f ≫ π = g ≫ π
  right_section_π : right_section ≫ π = 𝟙
  left_section_bottom : left_section ≫ g = 𝟙
  left_section_top : left_section ≫ f = π ≫ right_section

protected instance is_split_coequalizer.inhabited {C : Type u} [category C] {X : C} : Inhabited (is_split_coequalizer 𝟙 𝟙 𝟙) :=
  { default := is_split_coequalizer.mk 𝟙 𝟙 sorry sorry sorry sorry }

theorem is_split_coequalizer.condition_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {Z : C} {π : Y ⟶ Z} (c : is_split_coequalizer f g π) {X' : C} (f' : Z ⟶ X') : f ≫ π ≫ f' = g ≫ π ≫ f' := sorry

@[simp] theorem is_split_coequalizer.right_section_π_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {Z : C} {π : Y ⟶ Z} (c : is_split_coequalizer f g π) {X' : C} (f' : Z ⟶ X') : is_split_coequalizer.right_section c ≫ π ≫ f' = f' := sorry

/-- Split coequalizers are absolute: they are preserved by any functor. -/
@[simp] theorem is_split_coequalizer.map_left_section {C : Type u} [category C] {D : Type u₂} [category D] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {Z : C} {π : Y ⟶ Z} (q : is_split_coequalizer f g π) (F : C ⥤ D) : is_split_coequalizer.left_section (is_split_coequalizer.map q F) = functor.map F (is_split_coequalizer.left_section q) :=
  Eq.refl (is_split_coequalizer.left_section (is_split_coequalizer.map q F))

/-- A split coequalizer clearly induces a cofork. -/
@[simp] theorem is_split_coequalizer.as_cofork_X {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) : limits.cocone.X (is_split_coequalizer.as_cofork t) = Z :=
  Eq.refl Z

/--
The cofork induced by a split coequalizer is a coequalizer, justifying the name. In some cases it
is more convenient to show a given cofork is a coequalizer by showing it is split.
-/
def is_split_coequalizer.is_coequalizer {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {Z : C} {h : Y ⟶ Z} (t : is_split_coequalizer f g h) : limits.is_colimit (is_split_coequalizer.as_cofork t) :=
  limits.cofork.is_colimit.mk' (is_split_coequalizer.as_cofork t)
    fun (s : limits.cofork f g) => { val := is_split_coequalizer.right_section t ≫ limits.cofork.π s, property := sorry }

/--
The pair `f,g` is a split pair if there is a `h : Y ⟶ Z` so that `f, g, h` forms a split coequalizer
in `C`.
-/
class has_split_coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) 
where
  splittable : Exists fun {Z : C} => ∃ (h : Y ⟶ Z), Nonempty (is_split_coequalizer f g h)

/--
The pair `f,g` is a `G`-split pair if there is a `h : G Y ⟶ Z` so that `G f, G g, h` forms a split
coequalizer in `D`.
-/
def functor.is_split_pair {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y)  :=
  has_split_coequalizer (functor.map G f) (functor.map G g)

/-- Get the coequalizer object from the typeclass `is_split_pair`. -/
def has_split_coequalizer.coequalizer_of_split {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_split_coequalizer f g] : C :=
  Exists.some (has_split_coequalizer.splittable f g)

/-- Get the coequalizer morphism from the typeclass `is_split_pair`. -/
def has_split_coequalizer.coequalizer_π {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_split_coequalizer f g] : Y ⟶ has_split_coequalizer.coequalizer_of_split f g :=
  Exists.some sorry

/-- The coequalizer morphism `coequalizer_ι` gives a split coequalizer on `f,g`. -/
def has_split_coequalizer.is_split_coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_split_coequalizer f g] : is_split_coequalizer f g (has_split_coequalizer.coequalizer_π f g) :=
  Classical.choice sorry

/-- If `f, g` is split, then `G f, G g` is split. -/
protected instance map_is_split_pair {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_split_coequalizer f g] : has_split_coequalizer (functor.map G f) (functor.map G g) :=
  has_split_coequalizer.mk
    (Exists.intro (functor.obj G (has_split_coequalizer.coequalizer_of_split f g))
      (Exists.intro (functor.map G (has_split_coequalizer.coequalizer_π f g))
        (Nonempty.intro (is_split_coequalizer.map (has_split_coequalizer.is_split_coequalizer f g) G))))

namespace limits


/-- If a pair has a split coequalizer, it has a coequalizer. -/
protected instance has_coequalizer_of_has_split_coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_split_coequalizer f g] : has_coequalizer f g :=
  has_colimit.mk
    (colimit_cocone.mk (is_split_coequalizer.as_cofork (has_split_coequalizer.is_split_coequalizer f g))
      (is_split_coequalizer.is_coequalizer (has_split_coequalizer.is_split_coequalizer f g)))

