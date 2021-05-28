/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.arrow
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`, such
that for every commutative square with `f` at the top and a monomorphism at the bottom, there is
a diagonal morphism making the two triangles commute. This lift is necessarily unique (as shown in
`comma.lean`).

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

## Future work

There is also the dual notion of strong monomorphism.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

namespace category_theory


/-- A strong epimorphism `f` is an epimorphism such that every commutative square with `f` at the
    top and a monomorphism at the bottom has a lift. -/
class strong_epi {C : Type u} [category C] {P : C} {Q : C} (f : P ⟶ Q) 
where
  epi : epi f
  has_lift : ∀ {X Y : C} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y} [_inst_2 : mono z] (h : u ≫ z = f ≫ v), arrow.has_lift (arrow.hom_mk' h)

protected instance epi_of_strong_epi {C : Type u} [category C] {P : C} {Q : C} (f : P ⟶ Q) [strong_epi f] : epi f :=
  strong_epi.epi

/-- The composition of two strong epimorphisms is a strong epimorphism. -/
theorem strong_epi_comp {C : Type u} [category C] {P : C} {Q : C} {R : C} (f : P ⟶ Q) (g : Q ⟶ R) [strong_epi f] [strong_epi g] : strong_epi (f ≫ g) := sorry

/-- If `f ≫ g` is a strong epimorphism, then so is g. -/
theorem strong_epi_of_strong_epi {C : Type u} [category C] {P : C} {Q : C} {R : C} (f : P ⟶ Q) (g : Q ⟶ R) [strong_epi (f ≫ g)] : strong_epi g := sorry

/-- An isomorphism is in particular a strong epimorphism. -/
protected instance strong_epi_of_is_iso {C : Type u} [category C] {P : C} {Q : C} (f : P ⟶ Q) [is_iso f] : strong_epi f := sorry

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
def is_iso_of_mono_of_strong_epi {C : Type u} [category C] {P : C} {Q : C} (f : P ⟶ Q) [mono f] [strong_epi f] : is_iso f :=
  is_iso.mk (arrow.lift (arrow.hom_mk' sorry))

