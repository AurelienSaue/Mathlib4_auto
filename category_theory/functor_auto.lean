/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

Defines a functor between categories.

(As it is a 'bundled' object rather than the `is_functorial` typeclass parametrised
by the underlying function on objects, the name is capitalised.)

Introduces notations
  `C ⥤ D` for the type of all functors from `C` to `D`.
    (I would like a better arrow here, unfortunately ⇒ (`\functor`) is taken by core.)
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.reassoc_axiom
import PostPort

universes v₁ v₂ u₁ u₂ l u₃ v₃ 

namespace Mathlib

namespace category_theory


/--
`functor C D` represents a functor between categories `C` and `D`.

To apply a functor `F` to an object use `F.obj X`, and to a morphism use `F.map f`.

The axiom `map_id` expresses preservation of identities, and
`map_comp` expresses functoriality.

See https://stacks.math.columbia.edu/tag/001B.
-/
structure functor (C : Type u₁) [category C] (D : Type u₂) [category D] 
where
  obj : C → D
  map : {X Y : C} → (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id' : autoParam (C → map 𝟙 = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  map_comp' : autoParam (∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

infixr:26 " ⥤ " => Mathlib.category_theory.functor

-- A functor is basically a function, so give ⥤ a similar precedence to → (25).

-- For example, `C × D ⥤ E` should parse as `(C × D) ⥤ E` not `C × (D ⥤ E)`.

@[simp] theorem functor.map_id {C : Type u₁} [category C] {D : Type u₂} [category D] (c : C ⥤ D) (X : C) : functor.map c 𝟙 = 𝟙 := sorry

@[simp] theorem functor.map_comp {C : Type u₁} [category C] {D : Type u₂} [category D] (c : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : functor.map c (f ≫ g) = functor.map c f ≫ functor.map c g := sorry

theorem functor.map_comp_assoc {C : Type u₁} [category C] {D : Type u₂} [category D] (c : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) {X' : D} (f' : functor.obj c Z ⟶ X') : functor.map c (f ≫ g) ≫ f' = functor.map c f ≫ functor.map c g ≫ f' := sorry

namespace functor


/-- `𝟭 C` is the identity functor on a category `C`. -/
protected def id (C : Type u₁) [category C] : C ⥤ C :=
  mk (fun (X : C) => X) fun (_x _x_1 : C) (f : _x ⟶ _x_1) => f

notation:1024 "𝟭" => Mathlib.category_theory.functor.id

protected instance inhabited (C : Type u₁) [category C] : Inhabited (C ⥤ C) :=
  { default := 𝟭 }

@[simp] theorem id_obj {C : Type u₁} [category C] (X : C) : obj 𝟭 X = X :=
  rfl

@[simp] theorem id_map {C : Type u₁} [category C] {X : C} {Y : C} (f : X ⟶ Y) : map 𝟭 f = f :=
  rfl

/--
`F ⋙ G` is the composition of a functor `F` and a functor `G` (`F` first, then `G`).
-/
def comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E :=
  mk (fun (X : C) => obj G (obj F X)) fun (_x _x_1 : C) (f : _x ⟶ _x_1) => map G (map F f)

infixr:80 " ⋙ " => Mathlib.category_theory.functor.comp

@[simp] theorem comp_obj {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D) (G : D ⥤ E) (X : C) : obj (F ⋙ G) X = obj G (obj F X) :=
  rfl

@[simp] theorem comp_map {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E] (F : C ⥤ D) (G : D ⥤ E) {X : C} {Y : C} (f : X ⟶ Y) : map (F ⋙ G) f = map G (map F f) :=
  rfl

-- These are not simp lemmas because rewriting along equalities between functors

-- is not necessarily a good idea.

-- Natural isomorphisms are also provided in `whiskering.lean`.

protected theorem comp_id {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : F ⋙ 𝟭 = F := sorry

protected theorem id_comp {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D) : 𝟭 ⋙ F = F := sorry

