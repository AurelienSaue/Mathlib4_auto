/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.PostPort

universes v u l u' 

namespace Mathlib

/-!
# Categories

Defines a category, as a type class parametrised by the type of objects.

## Notations

Introduces notations
* `X ⟶ Y` for the morphism spaces,
* `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```lean
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

-- The order in this declaration matters: v often needs to be explicitly specified while u often

-- can be omitted

namespace category_theory


/-- A 'notation typeclass' on the way to defining a category. -/
class has_hom (obj : Type u) 
where
  hom : obj → obj → Type v

infixr:10 " ⟶ " => Mathlib.category_theory.has_hom.hom

/-- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
class category_struct (obj : Type u) 
extends has_hom obj
where
  id : (X : obj) → X ⟶ X
  comp : {X Y Z : obj} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

notation:1024 "𝟙" => Mathlib.category_theory.category_struct.id

infixr:80 " ≫ " => Mathlib.category_theory.category_struct.comp

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{v} C`. (See also `large_category` and `small_category`.)

See https://stacks.math.columbia.edu/tag/0014.
-/
class category (obj : Type u) 
extends category_struct obj
where
  id_comp' : autoParam (∀ {X Y : obj} (f : X ⟶ Y), 𝟙 ≫ f = f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  comp_id' : autoParam (∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 = f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  assoc' : autoParam (∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- `restate_axiom` is a command that creates a lemma from a structure field,

-- discarding any auto_param wrappers from the type.

-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)

@[simp] theorem category.id_comp {obj : Type u} [c : category obj] {X : obj} {Y : obj} (f : X ⟶ Y) : 𝟙 ≫ f = f := sorry

@[simp] theorem category.comp_id {obj : Type u} [c : category obj] {X : obj} {Y : obj} (f : X ⟶ Y) : f ≫ 𝟙 = f := sorry

@[simp] theorem category.assoc {obj : Type u} [c : category obj] {W : obj} {X : obj} {Y : obj} {Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : (f ≫ g) ≫ h = f ≫ g ≫ h := sorry

/--
A `large_category` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
/--
def large_category (C : Type (u + 1)) :=
  category C

A `small_category` has objects and morphisms in the same universe level.
-/
def small_category (C : Type u) :=
  category C

/-- postcompose an equation between morphisms by another morphism -/
theorem eq_whisker {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} (w : f = g) (h : Y ⟶ Z) : f ≫ h = g ≫ h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f ≫ h = g ≫ h)) w)) (Eq.refl (g ≫ h))

/-- precompose an equation between morphisms by another morphism -/
theorem whisker_eq {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} {h : Y ⟶ Z} (w : g = h) : f ≫ g = f ≫ h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f ≫ g = f ≫ h)) w)) (Eq.refl (f ≫ h))

infixr:80 " =≫ " => Mathlib.category_theory.eq_whisker

infixr:80 " ≫= " => Mathlib.category_theory.whisker_eq

theorem eq_of_comp_left_eq {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (w : ∀ {Z : C} (h : Y ⟶ Z), f ≫ h = g ≫ h) : f = g := sorry

theorem eq_of_comp_right_eq {C : Type u} [category C] {Y : C} {Z : C} {f : Y ⟶ Z} {g : Y ⟶ Z} (w : ∀ {X : C} (h : X ⟶ Y), h ≫ f = h ≫ g) : f = g := sorry

theorem eq_of_comp_left_eq' {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) (w : (fun {Z : C} (h : Y ⟶ Z) => f ≫ h) = fun {Z : C} (h : Y ⟶ Z) => g ≫ h) : f = g := sorry

theorem eq_of_comp_right_eq' {C : Type u} [category C] {Y : C} {Z : C} (f : Y ⟶ Z) (g : Y ⟶ Z) (w : (fun {X : C} (h : X ⟶ Y) => h ≫ f) = fun {X : C} (h : X ⟶ Y) => h ≫ g) : f = g := sorry

theorem id_of_comp_left_id {C : Type u} [category C] {X : C} (f : X ⟶ X) (w : ∀ {Y : C} (g : X ⟶ Y), f ≫ g = g) : f = 𝟙 := sorry

theorem id_of_comp_right_id {C : Type u} [category C] {X : C} (f : X ⟶ X) (w : ∀ {Y : C} (g : Y ⟶ X), g ≫ f = g) : f = 𝟙 := sorry

theorem comp_dite {C : Type u} [category C] {P : Prop} [Decidable P] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : P → (Y ⟶ Z)) (g' : ¬P → (Y ⟶ Z)) : (f ≫ dite P (fun (h : P) => g h) fun (h : ¬P) => g' h) = dite P (fun (h : P) => f ≫ g h) fun (h : ¬P) => f ≫ g' h := sorry

theorem dite_comp {C : Type u} [category C] {P : Prop} [Decidable P] {X : C} {Y : C} {Z : C} (f : P → (X ⟶ Y)) (f' : ¬P → (X ⟶ Y)) (g : Y ⟶ Z) : (dite P (fun (h : P) => f h) fun (h : ¬P) => f' h) ≫ g = dite P (fun (h : P) => f h ≫ g) fun (h : ¬P) => f' h ≫ g := sorry

/--
A morphism `f` is an epimorphism if it can be "cancelled" when precomposed:
`f ≫ g = f ≫ h` implies `g = h`.

See https://stacks.math.columbia.edu/tag/003B.
-/
class epi {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) 
where
  left_cancellation : ∀ {Z : C} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h

/--
A morphism `f` is a monomorphism if it can be "cancelled" when postcomposed:
`g ≫ f = h ≫ f` implies `g = h`.

See https://stacks.math.columbia.edu/tag/003B.
-/
class mono {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) 
where
  right_cancellation : ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h

protected instance category_struct.id.epi {C : Type u} [category C] (X : C) : epi 𝟙 :=
  epi.mk
    fun (Z : C) (g h : X ⟶ Z) (w : 𝟙 ≫ g = 𝟙 ≫ h) =>
      eq.mpr (id (Eq.refl (g = h)))
        (eq.mp
          ((fun (a a_1 : X ⟶ Z) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ Z) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (𝟙 ≫ g) g
            (category.id_comp g) (𝟙 ≫ h) h (category.id_comp h))
          w)

protected instance category_struct.id.mono {C : Type u} [category C] (X : C) : mono 𝟙 :=
  mono.mk
    fun (Z : C) (g h : Z ⟶ X) (w : g ≫ 𝟙 = h ≫ 𝟙) =>
      eq.mpr (id (Eq.refl (g = h)))
        (eq.mp
          ((fun (a a_1 : Z ⟶ X) (e_1 : a = a_1) (ᾰ ᾰ_1 : Z ⟶ X) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (g ≫ 𝟙) g
            (category.comp_id g) (h ≫ 𝟙) h (category.comp_id h))
          w)

theorem cancel_epi {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) [epi f] {g : Y ⟶ Z} {h : Y ⟶ Z} : f ≫ g = f ≫ h ↔ g = h :=
  { mp := fun (p : f ≫ g = f ≫ h) => epi.left_cancellation g h p,
    mpr := fun (a : g = h) => Eq._oldrec (Eq.refl (f ≫ g)) a }

theorem cancel_mono {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) [mono f] {g : Z ⟶ X} {h : Z ⟶ X} : g ≫ f = h ≫ f ↔ g = h :=
  { mp := fun (p : g ≫ f = h ≫ f) => mono.right_cancellation g h p,
    mpr := fun (a : g = h) => Eq._oldrec (Eq.refl (g ≫ f)) a }

theorem cancel_epi_id {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [epi f] {h : Y ⟶ Y} : f ≫ h = f ↔ h = 𝟙 := sorry

theorem cancel_mono_id {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [mono f] {g : X ⟶ X} : g ≫ f = f ↔ g = 𝟙 := sorry

theorem epi_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [epi g] : epi (f ≫ g) := sorry

theorem mono_comp {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) [mono f] (g : Y ⟶ Z) [mono g] : mono (f ≫ g) := sorry

theorem mono_of_mono {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [mono (f ≫ g)] : mono f := sorry

theorem mono_of_mono_fac {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [mono h] (w : f ≫ g = h) : mono f :=
  Eq._oldrec (mono_of_mono f g) w _inst_2

theorem epi_of_epi {C : Type u} [category C] {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [epi (f ≫ g)] : epi g := sorry

theorem epi_of_epi_fac {C : Type u} [category C] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} [epi h] (w : f ≫ g = h) : epi g :=
  Eq._oldrec (epi_of_epi f g) w _inst_2

protected instance ulift_category (C : Type u) [category C] : category (ulift C) :=
  category.mk

-- We verify that this previous instance can lift small categories to large categories.

end category_theory


/-!
We now put a category instance on any preorder.

Because we do not allow the morphisms of a category to live in `Prop`,
unfortunately we need to use `plift` and `ulift` when defining the morphisms.

As convenience functions, we provide `hom_of_le` and `le_of_hom` to wrap and unwrap inequalities.
-/

namespace preorder


/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ulift (plift (X ≤ Y))`.
See `category_theory.hom_of_le` and `category_theory.le_of_hom`.

See https://stacks.math.columbia.edu/tag/00D3.
-/
protected instance small_category (α : Type u) [preorder α] : category_theory.small_category α :=
  category_theory.category.mk

end preorder


namespace category_theory


/--
Express an inequality as a morphism in the corresponding preorder category.
-/
def hom_of_le {α : Type u} [preorder α] {U : α} {V : α} (h : U ≤ V) : U ⟶ V :=
  ulift.up (plift.up h)

/--
Extract the underlying inequality from a morphism in a preorder category.
-/
theorem le_of_hom {α : Type u} [preorder α] {U : α} {V : α} (h : U ⟶ V) : U ≤ V :=
  plift.down (ulift.down h)

end category_theory


/--
Many proofs in the category theory library use the `dsimp, simp` pattern,
