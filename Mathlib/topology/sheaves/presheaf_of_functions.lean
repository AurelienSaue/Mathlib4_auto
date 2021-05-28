/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.yoneda
import Mathlib.topology.sheaves.presheaf
import Mathlib.topology.category.TopCommRing
import Mathlib.topology.algebra.continuous_functions
import Mathlib.PostPort

universes v u_1 u 

namespace Mathlib

/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheaf_to_Type X f`, where `f : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheaf_to_Type X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheaf_to_Top X T`, where `T : Top`,
  is the presheaf of continuous functions into a topological space `T`
* `presheaf_To_TopCommRing X R`, where `R : TopCommRing`
  is the presheaf valued in `CommRing` of functions functions into a topological ring `R`
* as an example of the previous construction,
  `presheaf_to_TopCommRing X (TopCommRing.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/

namespace Top


/--
The presheaf of dependently typed functions on `X`, with fibres given by a type family `f`.
There is no requirement that the functions are continuous, here.
-/
def presheaf_to_Types (X : Top) (T : ↥X → Type v) : presheaf (Type v) X :=
  category_theory.functor.mk (fun (U : topological_space.opens ↥Xᵒᵖ) => (x : ↥(opposite.unop U)) → T ↑x)
    fun (U V : topological_space.opens ↥Xᵒᵖ) (i : U ⟶ V) (g : (x : ↥(opposite.unop U)) → T ↑x) (x : ↥(opposite.unop V)) =>
      g (coe_fn (category_theory.has_hom.hom.unop i) x)

@[simp] theorem presheaf_to_Types_obj (X : Top) {T : ↥X → Type v} {U : topological_space.opens ↥Xᵒᵖ} : category_theory.functor.obj (presheaf_to_Types X T) U = ((x : ↥(opposite.unop U)) → T ↑x) :=
  rfl

@[simp] theorem presheaf_to_Types_map (X : Top) {T : ↥X → Type v} {U : topological_space.opens ↥Xᵒᵖ} {V : topological_space.opens ↥Xᵒᵖ} {i : U ⟶ V} {f : category_theory.functor.obj (presheaf_to_Types X T) U} : category_theory.functor.map (presheaf_to_Types X T) i f =
  fun (x : ↥(opposite.unop V)) => f (coe_fn (category_theory.has_hom.hom.unop i) x) :=
  rfl

/--
The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
-- We don't just define this in terms of `presheaf_to_Types`,

-- as it's helpful later to see (at a syntactic level) that `(presheaf_to_Type X T).obj U`

-- is a non-dependent function.

-- We don't use `@[simps]` to generate the projection lemmas here,

-- as it turns out to be useful to have `presheaf_to_Type_map`

-- written as an equality of functions (rather than being applied to some argument).

def presheaf_to_Type (X : Top) (T : Type v) : presheaf (Type v) X :=
  category_theory.functor.mk (fun (U : topological_space.opens ↥Xᵒᵖ) => ↥(opposite.unop U) → T)
    fun (U V : topological_space.opens ↥Xᵒᵖ) (i : U ⟶ V) (g : ↥(opposite.unop U) → T) =>
      g ∘ ⇑(category_theory.has_hom.hom.unop i)

@[simp] theorem presheaf_to_Type_obj (X : Top) {T : Type v} {U : topological_space.opens ↥Xᵒᵖ} : category_theory.functor.obj (presheaf_to_Type X T) U = (↥(opposite.unop U) → T) :=
  rfl

@[simp] theorem presheaf_to_Type_map (X : Top) {T : Type v} {U : topological_space.opens ↥Xᵒᵖ} {V : topological_space.opens ↥Xᵒᵖ} {i : U ⟶ V} {f : category_theory.functor.obj (presheaf_to_Type X T) U} : category_theory.functor.map (presheaf_to_Type X T) i f = f ∘ ⇑(category_theory.has_hom.hom.unop i) :=
  rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space `T`. -/
def presheaf_to_Top (X : Top) (T : Top) : presheaf (Type v) X :=
  category_theory.functor.op (topological_space.opens.to_Top X) ⋙ category_theory.functor.obj category_theory.yoneda T

@[simp] theorem presheaf_to_Top_obj (X : Top) (T : Top) (U : topological_space.opens ↥Xᵒᵖ) : category_theory.functor.obj (presheaf_to_Top X T) U =
  (category_theory.functor.obj (topological_space.opens.to_Top X) (opposite.unop U) ⟶ T) :=
  rfl

/-- The (bundled) commutative ring of continuous functions from a topological space
to a topological commutative ring, with pointwise multiplication. -/
-- TODO upgrade the result to TopCommRing?

def continuous_functions (X : Topᵒᵖ) (R : TopCommRing) : CommRing :=
  CommRing.of (opposite.unop X ⟶ category_theory.functor.obj (category_theory.forget₂ TopCommRing Top) R)

namespace continuous_functions


/-- Pulling back functions into a topological ring along a continuous map is a ring homomorphism. -/
def pullback {X : Topᵒᵖ} {Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) : continuous_functions X R ⟶ continuous_functions Y R :=
  ring_hom.mk (fun (g : ↥(continuous_functions X R)) => category_theory.has_hom.hom.unop f ≫ g) sorry sorry sorry sorry

/-- A homomorphism of topological rings can be postcomposed with functions from a source space `X`;
this is a ring homomorphism (with respect to the pointwise ring operations on functions). -/
def map (X : Topᵒᵖ) {R : TopCommRing} {S : TopCommRing} (φ : R ⟶ S) : continuous_functions X R ⟶ continuous_functions X S :=
  ring_hom.mk
    (fun (g : ↥(continuous_functions X R)) => g ≫ category_theory.functor.map (category_theory.forget₂ TopCommRing Top) φ)
    sorry sorry sorry sorry

end continuous_functions


/-- An upgraded version of the Yoneda embedding, observing that the continuous maps
from `X : Top` to `R : TopCommRing` form a commutative ring, functorial in both `X` and `R`. -/
def CommRing_yoneda : TopCommRing ⥤ Topᵒᵖ ⥤ CommRing :=
  category_theory.functor.mk
    (fun (R : TopCommRing) =>
      category_theory.functor.mk (fun (X : Topᵒᵖ) => continuous_functions X R)
        fun (X Y : Topᵒᵖ) (f : X ⟶ Y) => continuous_functions.pullback f R)
    fun (R S : TopCommRing) (φ : R ⟶ S) => category_theory.nat_trans.mk fun (X : Topᵒᵖ) => continuous_functions.map X φ

/--
The presheaf (of commutative rings), consisting of functions on an open set `U ⊆ X` with
values in some topological commutative ring `T`.

For example, we could construct the presheaf of continuous complex valued functions of `X` as
```
presheaf_to_TopCommRing X (TopCommRing.of ℂ)
```
(this requires `import topology.instances.complex`).
-/
def presheaf_to_TopCommRing (X : Top) (T : TopCommRing) : presheaf CommRing X :=
  category_theory.functor.op (topological_space.opens.to_Top X) ⋙ category_theory.functor.obj CommRing_yoneda T

