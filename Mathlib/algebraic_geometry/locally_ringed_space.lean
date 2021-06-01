/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.sheafed_space
import Mathlib.algebra.category.CommRing.limits
import Mathlib.algebra.category.CommRing.colimits
import Mathlib.algebraic_geometry.stalks
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u_1 l u 

namespace Mathlib

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces
(as `SheafedSpace CommRing` along with the fact that the stalks are local rings),
and morphisms between these (morphisms in `SheafedSpace` with `is_local_ring_hom` on the stalk maps).

## Future work
* Define the restriction along an open embedding
-/

namespace algebraic_geometry


/-- A `LocallyRingedSpace` is a topological space equipped with a sheaf of commutative rings
such that all the stalks are local rings.

A morphism of locally ringed spaces is a morphism of ringed spaces
such that the morphims induced on stalks are local ring homomorphisms. -/
structure LocallyRingedSpace 
extends SheafedSpace CommRing
where
  local_ring : ∀ (x : ↥(PresheafedSpace.carrier (SheafedSpace.to_PresheafedSpace _to_SheafedSpace))),
  local_ring ↥(Top.presheaf.stalk (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace _to_SheafedSpace)) x)

namespace LocallyRingedSpace


/-- The underlying topological space of a locally ringed space. -/
def to_Top (X : LocallyRingedSpace) : Top :=
  PresheafedSpace.carrier (SheafedSpace.to_PresheafedSpace (to_SheafedSpace X))

protected instance has_coe_to_sort : has_coe_to_sort LocallyRingedSpace :=
  has_coe_to_sort.mk (Type u) fun (X : LocallyRingedSpace) => ↥(to_Top X)

-- PROJECT: how about a typeclass "has_structure_sheaf" to mediate the 𝒪 notation, rather

-- than defining it over and over for PresheafedSpace, LRS, Scheme, etc.

/-- The structure sheaf of a locally ringed space. -/
def 𝒪 (X : LocallyRingedSpace) : Top.sheaf CommRing (to_Top X) :=
  SheafedSpace.sheaf (to_SheafedSpace X)

/-- A morphism of locally ringed spaces is a morphism of ringed spaces
 such that the morphims induced on stalks are local ring homomorphisms. -/
def hom (X : LocallyRingedSpace) (Y : LocallyRingedSpace) :=
  Subtype
    fun (f : to_SheafedSpace X ⟶ to_SheafedSpace Y) =>
      ∀ (x : ↥(SheafedSpace.to_PresheafedSpace (to_SheafedSpace X))), is_local_ring_hom (PresheafedSpace.stalk_map f x)

protected instance category_theory.has_hom : category_theory.has_hom LocallyRingedSpace :=
  category_theory.has_hom.mk hom

theorem hom_ext {X : LocallyRingedSpace} {Y : LocallyRingedSpace} (f : hom X Y) (g : hom X Y) (w : subtype.val f = subtype.val g) : f = g :=
  subtype.eq w

/--
The stalk of a locally ringed space, just as a `CommRing`.
-/
-- TODO perhaps we should make a bundled `LocalRing` and return one here?

-- TODO define `sheaf.stalk` so we can write `X.𝒪.stalk` here?

def stalk (X : LocallyRingedSpace) (x : ↥X) : CommRing :=
  Top.presheaf.stalk (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (to_SheafedSpace X))) x

/--
A morphism of locally ringed spaces `f : X ⟶ Y` induces
a local ring homomorphism from `Y.stalk (f x)` to `X.stalk x` for any `x : X`.
-/
def stalk_map {X : LocallyRingedSpace} {Y : LocallyRingedSpace} (f : X ⟶ Y) (x : ↥X) : stalk Y (coe_fn (PresheafedSpace.hom.base (subtype.val f)) x) ⟶ stalk X x :=
  PresheafedSpace.stalk_map (subtype.val f) x

protected instance stalk_map.is_local_ring_hom {X : LocallyRingedSpace} {Y : LocallyRingedSpace} (f : X ⟶ Y) (x : ↥X) : is_local_ring_hom (stalk_map f x) :=
  subtype.property f x

/-- The identity morphism on a locally ringed space. -/
def id (X : LocallyRingedSpace) : hom X X :=
  { val := 𝟙, property := sorry }

protected instance hom.inhabited (X : LocallyRingedSpace) : Inhabited (hom X X) :=
  { default := id X }

/-- Composition of morphisms of locally ringed spaces. -/
def comp {X : LocallyRingedSpace} {Y : LocallyRingedSpace} {Z : LocallyRingedSpace} (f : hom X Y) (g : hom Y Z) : hom X Z :=
  { val := subtype.val f ≫ subtype.val g, property := sorry }

/-- The category of locally ringed spaces. -/
protected instance category_theory.category : category_theory.category LocallyRingedSpace :=
  category_theory.category.mk

/-- The forgetful functor from `LocallyRingedSpace` to `SheafedSpace CommRing`. -/
def forget_to_SheafedSpace : LocallyRingedSpace ⥤ SheafedSpace CommRing :=
  category_theory.functor.mk (fun (X : LocallyRingedSpace) => to_SheafedSpace X)
    fun (X Y : LocallyRingedSpace) (f : X ⟶ Y) => subtype.val f

protected instance forget_to_SheafedSpace.category_theory.faithful : category_theory.faithful forget_to_SheafedSpace :=
  category_theory.faithful.mk

-- PROJECT: once we have `PresheafedSpace.restrict_stalk_iso`

-- (that restriction doesn't change stalks) we can uncomment this.

/-
def restrict {U : Top} (X : LocallyRingedSpace)
  (f : U ⟶ X.to_Top) (h : open_embedding f) : LocallyRingedSpace :=
{ local_ring :=
  begin
    intro x,
    dsimp at *,
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    have := X.to_SheafedSpace.to_PresheafedSpace.restrict_stalk_iso f h x,
    -- and then transfer `local_ring` across the ring equivalence.
    apply (this.CommRing_iso_to_ring_equiv).local_ring, -- import data.equiv.transfer_instance
    apply X.local_ring,
  end,
  .. X.to_SheafedSpace.restrict _ f h }
-/

/--
The global sections, notated Gamma.
-/
def Γ : LocallyRingedSpaceᵒᵖ ⥤ CommRing :=
  category_theory.functor.op forget_to_SheafedSpace ⋙ SheafedSpace.Γ

theorem Γ_def : Γ = category_theory.functor.op forget_to_SheafedSpace ⋙ SheafedSpace.Γ :=
  rfl

@[simp] theorem Γ_obj (X : LocallyRingedSpaceᵒᵖ) : category_theory.functor.obj Γ X =
  category_theory.functor.obj
    (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (to_SheafedSpace (opposite.unop X)))) (opposite.op ⊤) :=
  rfl

theorem Γ_obj_op (X : LocallyRingedSpace) : category_theory.functor.obj Γ (opposite.op X) =
  category_theory.functor.obj (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (to_SheafedSpace X)))
    (opposite.op ⊤) :=
  rfl

@[simp] theorem Γ_map {X : LocallyRingedSpaceᵒᵖ} {Y : LocallyRingedSpaceᵒᵖ} (f : X ⟶ Y) : category_theory.functor.map Γ f =
  category_theory.nat_trans.app (PresheafedSpace.hom.c (subtype.val (category_theory.has_hom.hom.unop f)))
      (opposite.op ⊤) ≫
    category_theory.functor.map
      (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (to_SheafedSpace (opposite.unop Y))))
      (category_theory.has_hom.hom.op
        (topological_space.opens.le_map_top
          (PresheafedSpace.hom.base (subtype.val (category_theory.has_hom.hom.unop f))) ⊤)) :=
  rfl

theorem Γ_map_op {X : LocallyRingedSpace} {Y : LocallyRingedSpace} (f : X ⟶ Y) : category_theory.functor.map Γ (category_theory.has_hom.hom.op f) =
  category_theory.nat_trans.app (PresheafedSpace.hom.c (subtype.val f)) (opposite.op ⊤) ≫
    category_theory.functor.map (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (to_SheafedSpace X)))
      (category_theory.has_hom.hom.op (topological_space.opens.le_map_top (PresheafedSpace.hom.base (subtype.val f)) ⊤)) :=
  rfl

