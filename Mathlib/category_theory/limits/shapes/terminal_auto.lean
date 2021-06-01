/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.pempty
import Mathlib.category_theory.limits.limits
import Mathlib.PostPort

universes u v u₂ 

namespace Mathlib

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

namespace category_theory.limits


/-- Construct a cone for the empty diagram given an object. -/
/-- Construct a cocone for the empty diagram given an object. -/
@[simp] theorem as_empty_cone_π_app {C : Type u} [category C] (X : C) :
    ∀ (X_1 : discrete pempty),
        nat_trans.app (cone.π (as_empty_cone X)) X_1 = as_empty_cone._aux_1 X X_1 :=
  fun (X_1 : discrete pempty) => Eq.refl (nat_trans.app (cone.π (as_empty_cone X)) X_1)

@[simp] theorem as_empty_cocone_ι_app {C : Type u} [category C] (X : C) :
    ∀ (X_1 : discrete pempty),
        nat_trans.app (cocone.ι (as_empty_cocone X)) X_1 = as_empty_cocone._aux_1 X X_1 :=
  fun (X_1 : discrete pempty) => Eq.refl (nat_trans.app (cocone.ι (as_empty_cocone X)) X_1)

/-- `X` is terminal if the cone it induces on the empty diagram is limiting. -/
/-- `X` is initial if the cocone it induces on the empty diagram is colimiting. -/
def is_terminal {C : Type u} [category C] (X : C) := is_limit (as_empty_cone X)

def is_initial {C : Type u} [category C] (X : C) := is_colimit (as_empty_cocone X)

/-- Give the morphism to a terminal object from any other. -/
def is_terminal.from {C : Type u} [category C] {X : C} (t : is_terminal X) (Y : C) : Y ⟶ X :=
  is_limit.lift t (as_empty_cone Y)

/-- Any two morphisms to a terminal object are equal. -/
theorem is_terminal.hom_ext {C : Type u} [category C] {X : C} {Y : C} (t : is_terminal X)
    (f : Y ⟶ X) (g : Y ⟶ X) : f = g :=
  sorry

/-- Give the morphism from an initial object to any other. -/
def is_initial.to {C : Type u} [category C] {X : C} (t : is_initial X) (Y : C) : X ⟶ Y :=
  is_colimit.desc t (as_empty_cocone Y)

/-- Any two morphisms from an initial object are equal. -/
theorem is_initial.hom_ext {C : Type u} [category C] {X : C} {Y : C} (t : is_initial X) (f : X ⟶ Y)
    (g : X ⟶ Y) : f = g :=
  sorry

/-- Any morphism from a terminal object is mono. -/
theorem is_terminal.mono_from {C : Type u} [category C] {X : C} {Y : C} (t : is_terminal X)
    (f : X ⟶ Y) : mono f :=
  mono.mk fun (Z : C) (g h : Z ⟶ X) (eq : g ≫ f = h ≫ f) => is_terminal.hom_ext t g h

/-- Any morphism to an initial object is epi. -/
theorem is_initial.epi_to {C : Type u} [category C] {X : C} {Y : C} (t : is_initial X) (f : Y ⟶ X) :
    epi f :=
  epi.mk fun (Z : C) (g h : X ⟶ Z) (eq : f ≫ g = f ≫ h) => is_initial.hom_ext t g h

/--
A category has a terminal object if it has a limit over the empty diagram.
Use `has_terminal_of_unique` to construct instances.
-/
/--
def has_terminal (C : Type u) [category C] := has_limits_of_shape (discrete pempty) C

A category has an initial object if it has a colimit over the empty diagram.
Use `has_initial_of_unique` to construct instances.
-/
def has_initial (C : Type u) [category C] := has_colimits_of_shape (discrete pempty) C

/--
An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
/--
def terminal (C : Type u) [category C] [has_terminal C] : C := limit (functor.empty C)

An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
def initial (C : Type u) [category C] [has_initial C] : C := colimit (functor.empty C)

prefix:20 "⊤_" => Mathlib.category_theory.limits.terminal

prefix:20 "⊥_" => Mathlib.category_theory.limits.initial

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
theorem has_terminal_of_unique {C : Type u} [category C] (X : C) [h : (Y : C) → unique (Y ⟶ X)] :
    has_terminal C :=
  sorry

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
theorem has_initial_of_unique {C : Type u} [category C] (X : C) [h : (Y : C) → unique (X ⟶ Y)] :
    has_initial C :=
  sorry

/-- The map from an object to the terminal object. -/
def terminal.from {C : Type u} [category C] [has_terminal C] (P : C) : P ⟶ ⊤_C :=
  limit.lift (functor.empty C) (as_empty_cone P)

/-- The map to an object from the initial object. -/
def initial.to {C : Type u} [category C] [has_initial C] (P : C) : ⊥_C ⟶ P :=
  colimit.desc (functor.empty C) (as_empty_cocone P)

protected instance unique_to_terminal {C : Type u} [category C] [has_terminal C] (P : C) :
    unique (P ⟶ ⊤_C) :=
  unique.mk { default := terminal.from P } sorry

protected instance unique_from_initial {C : Type u} [category C] [has_initial C] (P : C) :
    unique (⊥_C ⟶ P) :=
  unique.mk { default := initial.to P } sorry

/-- A terminal object is terminal. -/
def terminal_is_terminal {C : Type u} [category C] [has_terminal C] : is_terminal (⊤_C) :=
  is_limit.mk fun (s : cone (functor.empty C)) => terminal.from (cone.X s)

/-- An initial object is initial. -/
def initial_is_initial {C : Type u} [category C] [has_initial C] : is_initial (⊥_C) :=
  is_colimit.mk fun (s : cocone (functor.empty C)) => initial.to (cocone.X s)

/-- Any morphism from a terminal object is mono. -/
protected instance terminal.mono_from {C : Type u} [category C] {Y : C} [has_terminal C]
    (f : ⊤_C ⟶ Y) : mono f :=
  is_terminal.mono_from terminal_is_terminal f

/-- Any morphism to an initial object is epi. -/
protected instance initial.epi_to {C : Type u} [category C] {Y : C} [has_initial C] (f : Y ⟶ ⊥_C) :
    epi f :=
  is_initial.epi_to initial_is_initial f

/-- An initial object is terminal in the opposite category. -/
def terminal_op_of_initial {C : Type u} [category C] {X : C} (t : is_initial X) :
    is_terminal (opposite.op X) :=
  is_limit.mk
    fun (s : cone (functor.empty (Cᵒᵖ))) =>
      has_hom.hom.op (is_initial.to t (opposite.unop (cone.X s)))

/-- An initial object in the opposite category is terminal in the original category. -/
def terminal_unop_of_initial {C : Type u} [category C] {X : Cᵒᵖ} (t : is_initial X) :
    is_terminal (opposite.unop X) :=
  is_limit.mk
    fun (s : cone (functor.empty C)) => has_hom.hom.unop (is_initial.to t (opposite.op (cone.X s)))

/-- A terminal object is initial in the opposite category. -/
def initial_op_of_terminal {C : Type u} [category C] {X : C} (t : is_terminal X) :
    is_initial (opposite.op X) :=
  is_colimit.mk
    fun (s : cocone (functor.empty (Cᵒᵖ))) =>
      has_hom.hom.op (is_terminal.from t (opposite.unop (cocone.X s)))

/-- A terminal object in the opposite category is initial in the original category. -/
def initial_unop_of_terminal {C : Type u} [category C] {X : Cᵒᵖ} (t : is_terminal X) :
    is_initial (opposite.unop X) :=
  is_colimit.mk
    fun (s : cocone (functor.empty C)) =>
      has_hom.hom.unop (is_terminal.from t (opposite.op (cocone.X s)))

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, construct a cone for `J`.
In `limit_of_diagram_initial` we show it is a limit cone. -/
@[simp] theorem cone_of_diagram_initial_π_app {C : Type u} [category C] {J : Type v}
    [small_category J] {X : J} (tX : is_initial X) (F : J ⥤ C) (j : J) :
    nat_trans.app (cone.π (cone_of_diagram_initial tX F)) j = functor.map F (is_initial.to tX j) :=
  Eq.refl (nat_trans.app (cone.π (cone_of_diagram_initial tX F)) j)

/-- From a functor `F : J ⥤ C`, given an initial object of `J`, show the cone
`cone_of_diagram_initial` is a limit. -/
def limit_of_diagram_initial {C : Type u} [category C] {J : Type v} [small_category J] {X : J}
    (tX : is_initial X) (F : J ⥤ C) : is_limit (cone_of_diagram_initial tX F) :=
  is_limit.mk fun (s : cone F) => nat_trans.app (cone.π s) X

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.

/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
def limit_of_initial {C : Type u} [category C] {J : Type v} [small_category J] (F : J ⥤ C)
    [has_initial J] [has_limit F] : limit F ≅ functor.obj F (⊥_J) :=
  is_limit.cone_point_unique_up_to_iso (limit.is_limit F)
    (limit_of_diagram_initial initial_is_initial F)

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, construct a cocone for `J`.
In `colimit_of_diagram_terminal` we show it is a colimit cocone. -/
@[simp] theorem cocone_of_diagram_terminal_X {C : Type u} [category C] {J : Type v}
    [small_category J] {X : J} (tX : is_terminal X) (F : J ⥤ C) :
    cocone.X (cocone_of_diagram_terminal tX F) = functor.obj F X :=
  Eq.refl (cocone.X (cocone_of_diagram_terminal tX F))

/-- From a functor `F : J ⥤ C`, given a terminal object of `J`, show the cocone
`cocone_of_diagram_terminal` is a colimit. -/
def colimit_of_diagram_terminal {C : Type u} [category C] {J : Type v} [small_category J] {X : J}
    (tX : is_terminal X) (F : J ⥤ C) : is_colimit (cocone_of_diagram_terminal tX F) :=
  is_colimit.mk fun (s : cocone F) => nat_trans.app (cocone.ι s) X

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.

/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
def colimit_of_terminal {C : Type u} [category C] {J : Type v} [small_category J] (F : J ⥤ C)
    [has_terminal J] [has_colimit F] : colimit F ≅ functor.obj F (⊤_J) :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F)
    (colimit_of_diagram_terminal terminal_is_terminal F)

/--
The comparison morphism from the image of a terminal object to the terminal object in the target
category.
-/
-- TODO: Show this is an isomorphism if and only if `G` preserves terminal objects.

def terminal_comparison {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D)
    [has_terminal C] [has_terminal D] : functor.obj G (⊤_C) ⟶ ⊤_D :=
  terminal.from (functor.obj G (⊤_C))

/--
The comparison morphism from the initial object in the target category to the image of the initial
object.
-/
-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.

def initial_comparison {C : Type u} [category C] {D : Type u₂} [category D] (G : C ⥤ D)
    [has_initial C] [has_initial D] : ⊥_D ⟶ functor.obj G (⊥_C) :=
  initial.to (functor.obj G (⊥_C))

end Mathlib