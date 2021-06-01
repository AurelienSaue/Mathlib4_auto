/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monad.limits
import Mathlib.topology.uniform_space.completion
import Mathlib.topology.category.Top.basic
import Mathlib.PostPort

universes u u_1 l 

namespace Mathlib

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

/-- A (bundled) uniform space. -/
def UniformSpace := category_theory.bundled uniform_space

namespace UniformSpace


/-- The information required to build morphisms for `UniformSpace`. -/
protected instance uniform_continuous.category_theory.unbundled_hom :
    category_theory.unbundled_hom uniform_continuous :=
  category_theory.unbundled_hom.mk uniform_continuous_id uniform_continuous.comp

protected instance has_coe_to_sort : has_coe_to_sort UniformSpace :=
  category_theory.bundled.has_coe_to_sort

protected instance uniform_space (x : UniformSpace) : uniform_space ↥x :=
  category_theory.bundled.str x

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [uniform_space α] : UniformSpace := category_theory.bundled.mk α

protected instance inhabited : Inhabited UniformSpace := { default := of empty }

@[simp] theorem coe_of (X : Type u) [uniform_space X] : ↥(of X) = X := rfl

protected instance category_theory.has_hom.hom.has_coe_to_fun (X : UniformSpace)
    (Y : UniformSpace) : has_coe_to_fun (X ⟶ Y) :=
  has_coe_to_fun.mk (fun (_x : X ⟶ Y) => ↥X → ↥Y)
    (category_theory.functor.map (category_theory.forget UniformSpace))

@[simp] theorem coe_comp {X : UniformSpace} {Y : UniformSpace} {Z : UniformSpace} (f : X ⟶ Y)
    (g : Y ⟶ Z) : ⇑(f ≫ g) = ⇑g ∘ ⇑f :=
  rfl

@[simp] theorem coe_id (X : UniformSpace) : ⇑𝟙 = id := rfl

@[simp] theorem coe_mk {X : UniformSpace} {Y : UniformSpace} (f : ↥X → ↥Y)
    (hf : uniform_continuous f) : ⇑{ val := f, property := hf } = f :=
  rfl

theorem hom_ext {X : UniformSpace} {Y : UniformSpace} {f : X ⟶ Y} {g : X ⟶ Y} : ⇑f = ⇑g → f = g :=
  subtype.eq

/-- The forgetful functor from uniform spaces to topological spaces. -/
protected instance has_forget_to_Top : category_theory.has_forget₂ UniformSpace Top :=
  category_theory.has_forget₂.mk
    (category_theory.functor.mk (fun (X : UniformSpace) => Top.of ↥X)
      fun (X Y : UniformSpace) (f : X ⟶ Y) => continuous_map.mk ⇑f)

end UniformSpace


/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace where
  α : Type u
  is_uniform_space : uniform_space α
  is_complete_space : complete_space α
  is_separated : separated_space α

namespace CpltSepUniformSpace


protected instance has_coe_to_sort : has_coe_to_sort CpltSepUniformSpace :=
  has_coe_to_sort.mk (Type u) α

def to_UniformSpace (X : CpltSepUniformSpace) : UniformSpace := UniformSpace.of ↥X

protected instance complete_space (X : CpltSepUniformSpace) :
    complete_space (category_theory.bundled.α (to_UniformSpace X)) :=
  is_complete_space X

protected instance separated_space (X : CpltSepUniformSpace) :
    separated_space (category_theory.bundled.α (to_UniformSpace X)) :=
  is_separated X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [uniform_space X] [complete_space X] [separated_space X] :
    CpltSepUniformSpace :=
  mk X

@[simp] theorem coe_of (X : Type u) [uniform_space X] [complete_space X] [separated_space X] :
    ↥(of X) = X :=
  rfl

protected instance inhabited : Inhabited CpltSepUniformSpace := { default := of empty }

/-- The category instance on `CpltSepUniformSpace`. -/
protected instance category : category_theory.large_category CpltSepUniformSpace :=
  category_theory.induced_category.category to_UniformSpace

/-- The concrete category instance on `CpltSepUniformSpace`. -/
protected instance concrete_category : category_theory.concrete_category CpltSepUniformSpace :=
  category_theory.induced_category.concrete_category to_UniformSpace

protected instance has_forget_to_UniformSpace :
    category_theory.has_forget₂ CpltSepUniformSpace UniformSpace :=
  category_theory.induced_category.has_forget₂ to_UniformSpace

end CpltSepUniformSpace


namespace UniformSpace


/-- The functor turning uniform spaces into complete separated uniform spaces. -/
def completion_functor : UniformSpace ⥤ CpltSepUniformSpace :=
  category_theory.functor.mk
    (fun (X : UniformSpace) => CpltSepUniformSpace.of (uniform_space.completion ↥X))
    fun (X Y : UniformSpace) (f : X ⟶ Y) =>
      { val := uniform_space.completion.map (subtype.val f), property := sorry }

/-- The inclusion of a uniform space into its completion. -/
def completion_hom (X : UniformSpace) :
    X ⟶
        category_theory.functor.obj (category_theory.forget₂ CpltSepUniformSpace UniformSpace)
          (category_theory.functor.obj completion_functor X) :=
  { val := coe, property := sorry }

@[simp] theorem completion_hom_val (X : UniformSpace) (x : ↥X) : coe_fn (completion_hom X) x = ↑x :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
def extension_hom {X : UniformSpace} {Y : CpltSepUniformSpace}
    (f :
      X ⟶
        category_theory.functor.obj (category_theory.forget₂ CpltSepUniformSpace UniformSpace) Y) :
    category_theory.functor.obj completion_functor X ⟶ Y :=
  { val := uniform_space.completion.extension ⇑f, property := sorry }

@[simp] theorem extension_hom_val {X : UniformSpace} {Y : CpltSepUniformSpace}
    (f :
      X ⟶ category_theory.functor.obj (category_theory.forget₂ CpltSepUniformSpace UniformSpace) Y)
    (x :
      ↥(CpltSepUniformSpace.to_UniformSpace (category_theory.functor.obj completion_functor X))) :
    coe_fn (extension_hom f) x = uniform_space.completion.extension (⇑f) x :=
  rfl

@[simp] theorem extension_comp_coe {X : UniformSpace} {Y : CpltSepUniformSpace}
    (f :
      CpltSepUniformSpace.to_UniformSpace (CpltSepUniformSpace.of (uniform_space.completion ↥X)) ⟶
        CpltSepUniformSpace.to_UniformSpace Y) :
    extension_hom (completion_hom X ≫ f) = f :=
  sorry

/-- The completion functor is left adjoint to the forgetful functor. -/
def adj : completion_functor ⊣ category_theory.forget₂ CpltSepUniformSpace UniformSpace :=
  category_theory.adjunction.mk_of_hom_equiv
    (category_theory.adjunction.core_hom_equiv.mk
      fun (X : UniformSpace) (Y : CpltSepUniformSpace) =>
        equiv.mk
          (fun (f : category_theory.functor.obj completion_functor X ⟶ Y) => completion_hom X ≫ f)
          (fun
            (f :
            X ⟶
              category_theory.functor.obj (category_theory.forget₂ CpltSepUniformSpace UniformSpace)
                Y) =>
            extension_hom f)
          sorry sorry)

protected instance category_theory.forget₂.category_theory.is_right_adjoint :
    category_theory.is_right_adjoint (category_theory.forget₂ CpltSepUniformSpace UniformSpace) :=
  category_theory.is_right_adjoint.mk completion_functor adj

protected instance category_theory.forget₂.category_theory.reflective :
    category_theory.reflective (category_theory.forget₂ CpltSepUniformSpace UniformSpace) :=
  category_theory.reflective.mk

end Mathlib