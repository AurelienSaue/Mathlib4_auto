/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.Spec
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# The category of schemes

A scheme is a locally ringed space such that every point is contained in some open set
where there is an isomorphism of presheaves between the restriction to that open set,
and the structure sheaf of `Spec R`, for some commutative ring `R`.

A morphism is schemes is just a morphism of the underlying locally ringed spaces.

-/

namespace algebraic_geometry


/--
We define `Scheme` as a `X : LocallyRingedSpace`,
along with a proof that every point has an open neighbourhood `U`
so that that the restriction of `X` to `U` is isomorphic, as a space with a presheaf of commutative
rings, to `Spec.PresheafedSpace R` for some `R : CommRing`.

(Note we're not asking in the definition that this is an isomorphism as locally ringed spaces,
although that is a consequence.)
-/
structure Scheme 
where
  local_affine : ∀ (x : ↥(PresheafedSpace.carrier (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace _X)))),
  ∃ (U :
    topological_space.opens
      ↥(PresheafedSpace.carrier (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace _X)))),
    ∃ (m : x ∈ U),
      ∃ (R : CommRing),
        ∃ (i :
          PresheafedSpace.restrict (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace _X))
              (topological_space.opens.inclusion U) (topological_space.opens.inclusion_open_embedding U) ≅
            Spec.PresheafedSpace R),
          True

-- PROJECT

-- In fact, we can make the isomorphism `i` above an isomorphism in `LocallyRingedSpace`.

-- However this is a consequence of the above definition, and not necessary for defining schemes.

-- We haven't done this yet because we haven't shown that you can restrict a `LocallyRingedSpace`

-- along an open embedding.

-- We can do this already for `SheafedSpace` (as above), but we need to know that

-- the stalks of the restriction are still local rings, which we follow if we knew that

-- the stalks didn't change.

-- This will follow if we define cofinal functors, and show precomposing with a cofinal functor

-- doesn't change colimits, because open neighbourhoods of `x` within `U` are cofinal in

-- all open neighbourhoods of `x`.

namespace Scheme


/--
Every `Scheme` is a `LocallyRingedSpace`.
-/
-- (This parent projection is apparently not automatically generated because

-- we used the `extends X : LocallyRingedSpace` syntax.)

def to_LocallyRingedSpace (S : Scheme) : LocallyRingedSpace :=
  LocallyRingedSpace.mk (LocallyRingedSpace.to_SheafedSpace (X S)) sorry

/--
`Spec R` as a `Scheme`.
-/
def Spec (R : CommRing) : Scheme :=
  mk (LocallyRingedSpace.mk (LocallyRingedSpace.to_SheafedSpace (Spec.LocallyRingedSpace R)) sorry) sorry

/--
The empty scheme, as `Spec 0`.
-/
def empty : Scheme :=
  Spec (CommRing.of PUnit)

protected instance has_emptyc : has_emptyc Scheme :=
  has_emptyc.mk empty

protected instance inhabited : Inhabited Scheme :=
  { default := ∅ }

/--
Schemes are a full subcategory of locally ringed spaces.
-/
protected instance category_theory.category : category_theory.category Scheme :=
  category_theory.induced_category.category to_LocallyRingedSpace

/--
The global sections, notated Gamma.
-/
def Γ : Schemeᵒᵖ ⥤ CommRing :=
  category_theory.functor.op (category_theory.induced_functor to_LocallyRingedSpace) ⋙ LocallyRingedSpace.Γ

theorem Γ_def : Γ = category_theory.functor.op (category_theory.induced_functor to_LocallyRingedSpace) ⋙ LocallyRingedSpace.Γ :=
  rfl

@[simp] theorem Γ_obj (X : Schemeᵒᵖ) : category_theory.functor.obj Γ X =
  category_theory.functor.obj
    (PresheafedSpace.presheaf
      (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace (X (opposite.unop X)))))
    (opposite.op ⊤) :=
  rfl

theorem Γ_obj_op (X : Scheme) : category_theory.functor.obj Γ (opposite.op X) =
  category_theory.functor.obj
    (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace (X X))))
    (opposite.op ⊤) :=
  rfl

@[simp] theorem Γ_map {X : Schemeᵒᵖ} {Y : Schemeᵒᵖ} (f : X ⟶ Y) : category_theory.functor.map Γ f =
  category_theory.nat_trans.app (PresheafedSpace.hom.c (subtype.val (category_theory.has_hom.hom.unop f)))
      (opposite.op ⊤) ≫
    category_theory.functor.map
      (PresheafedSpace.presheaf
        (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace (X (opposite.unop Y)))))
      (category_theory.has_hom.hom.op
        (topological_space.opens.le_map_top
          (PresheafedSpace.hom.base (subtype.val (category_theory.has_hom.hom.unop f))) ⊤)) :=
  rfl

theorem Γ_map_op {X : Scheme} {Y : Scheme} (f : X ⟶ Y) : category_theory.functor.map Γ (category_theory.has_hom.hom.op f) =
  category_theory.nat_trans.app (PresheafedSpace.hom.c (subtype.val f)) (opposite.op ⊤) ≫
    category_theory.functor.map
      (PresheafedSpace.presheaf (SheafedSpace.to_PresheafedSpace (LocallyRingedSpace.to_SheafedSpace (X X))))
      (category_theory.has_hom.hom.op (topological_space.opens.le_map_top (PresheafedSpace.hom.base (subtype.val f)) ⊤)) :=
  rfl

