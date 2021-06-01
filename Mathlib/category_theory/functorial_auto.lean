/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.functor
import Mathlib.PostPort

universes v₁ v₂ u₁ u₂ l u₃ v₃ 

namespace Mathlib

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

namespace category_theory


/-- A unbundled functor. -/
-- Perhaps in the future we could redefine `functor` in terms of this, but that isn't the

-- immediate plan.

class functorial {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C → D) where
  map : {X Y : C} → (X ⟶ Y) → (F X ⟶ F Y)
  map_id' :
    autoParam (C → map 𝟙 = 𝟙)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  map_comp' :
    autoParam (∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/--
If `F : C → D` (just a function) has `[functorial F]`,
we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`.
-/
def map {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C → D) [functorial F] {X : C}
    {Y : C} (f : X ⟶ Y) : F X ⟶ F Y :=
  functorial.map f

@[simp] theorem map_as_map {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C → D}
    [functorial F] {X : C} {Y : C} {f : X ⟶ Y} : functorial.map f = map F f :=
  rfl

@[simp] theorem functorial.map_id {C : Type u₁} [category C] {D : Type u₂} [category D] {F : C → D}
    [functorial F] {X : C} : map F 𝟙 = 𝟙 :=
  functorial.map_id' X

@[simp] theorem functorial.map_comp {C : Type u₁} [category C] {D : Type u₂} [category D]
    {F : C → D} [functorial F] {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
    map F (f ≫ g) = map F f ≫ map F g :=
  functorial.map_comp' f g

namespace functor


/--
Bundle a functorial function as a functor.
-/
def of {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C → D) [I : functorial F] :
    C ⥤ D :=
  mk F functorial.map

end functor


protected instance functor.obj.functorial {C : Type u₁} [category C] {D : Type u₂} [category D]
    (F : C ⥤ D) : functorial (functor.obj F) :=
  functorial.mk (functor.map F)

@[simp] theorem map_functorial_obj {C : Type u₁} [category C] {D : Type u₂} [category D] (F : C ⥤ D)
    {X : C} {Y : C} (f : X ⟶ Y) : map (functor.obj F) f = functor.map F f :=
  rfl

protected instance functorial_id {C : Type u₁} [category C] : functorial id :=
  functorial.mk fun (X Y : C) (f : X ⟶ Y) => f

/--
`G ∘ F` is a functorial if both `F` and `G` are.
-/
-- This is no longer viable as an instance in Lean 3.7,

-- #lint reports an instance loop

-- Will this be a problem?

def functorial_comp {C : Type u₁} [category C] {D : Type u₂} [category D] {E : Type u₃} [category E]
    (F : C → D) [functorial F] (G : D → E) [functorial G] : functorial (G ∘ F) :=
  functorial.mk (functor.map (functor.of F ⋙ functor.of G))

end Mathlib