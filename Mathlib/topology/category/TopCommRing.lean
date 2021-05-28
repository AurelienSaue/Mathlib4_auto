/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.CommRing.basic
import Mathlib.topology.category.Top.basic
import Mathlib.topology.algebra.ring
import Mathlib.PostPort

universes u l u_1 u_2 

namespace Mathlib

/-- A bundled topological commutative ring. -/
structure TopCommRing 
where
  α : Type u
  is_comm_ring : comm_ring α
  is_topological_space : topological_space α
  is_topological_ring : topological_ring α

namespace TopCommRing


protected instance has_coe_to_sort : has_coe_to_sort TopCommRing :=
  has_coe_to_sort.mk (Type u) α

protected instance category_theory.category : category_theory.category TopCommRing :=
  category_theory.category.mk

protected instance category_theory.concrete_category : category_theory.concrete_category TopCommRing :=
  category_theory.concrete_category.mk
    (category_theory.functor.mk (fun (R : TopCommRing) => ↥R) fun (R S : TopCommRing) (f : R ⟶ S) => ⇑(subtype.val f))

/-- Construct a bundled `TopCommRing` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [comm_ring X] [topological_space X] [topological_ring X] : TopCommRing :=
  mk X

@[simp] theorem coe_of (X : Type u) [comm_ring X] [topological_space X] [topological_ring X] : ↥(of X) = X :=
  rfl

protected instance forget_topological_space (R : TopCommRing) : topological_space (category_theory.functor.obj (category_theory.forget TopCommRing) R) :=
  is_topological_space R

protected instance forget_comm_ring (R : TopCommRing) : comm_ring (category_theory.functor.obj (category_theory.forget TopCommRing) R) :=
  is_comm_ring R

protected instance forget_topological_ring (R : TopCommRing) : topological_ring (category_theory.functor.obj (category_theory.forget TopCommRing) R) :=
  is_topological_ring R

protected instance has_forget_to_CommRing : category_theory.has_forget₂ TopCommRing CommRing :=
  category_theory.has_forget₂.mk' (fun (R : TopCommRing) => CommRing.of ↥R) sorry
    (fun (R S : TopCommRing) (f : R ⟶ S) => subtype.val f) sorry

protected instance forget_to_CommRing_topological_space (R : TopCommRing) : topological_space ↥(category_theory.functor.obj (category_theory.forget₂ TopCommRing CommRing) R) :=
  is_topological_space R

/-- The forgetful functor to Top. -/
protected instance has_forget_to_Top : category_theory.has_forget₂ TopCommRing Top :=
  category_theory.has_forget₂.mk' (fun (R : TopCommRing) => Top.of ↥R) sorry
    (fun (R S : TopCommRing) (f : R ⟶ S) => continuous_map.mk ⇑(subtype.val f)) sorry

protected instance forget_to_Top_comm_ring (R : TopCommRing) : comm_ring ↥(category_theory.functor.obj (category_theory.forget₂ TopCommRing Top) R) :=
  is_comm_ring R

protected instance forget_to_Top_topological_ring (R : TopCommRing) : topological_ring ↥(category_theory.functor.obj (category_theory.forget₂ TopCommRing Top) R) :=
  is_topological_ring R

/--
The forgetful functors to `Type` do not reflect isomorphisms,
but the forgetful functor from `TopCommRing` to `Top` does.
-/
protected instance category_theory.forget₂.category_theory.reflects_isomorphisms : category_theory.reflects_isomorphisms (category_theory.forget₂ TopCommRing Top) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : TopCommRing) (f : X ⟶ Y)
      (_x : category_theory.is_iso (category_theory.functor.map (category_theory.forget₂ TopCommRing Top) f)) =>
      let i_Top :
        category_theory.functor.obj (category_theory.forget₂ TopCommRing Top) X ≅
          category_theory.functor.obj (category_theory.forget₂ TopCommRing Top) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget₂ TopCommRing Top) f);
      let e_Ring : ↥X ≃+* ↥Y :=
        ring_equiv.mk (ring_hom.to_fun (subtype.val f))
          (equiv.inv_fun
            (category_theory.iso.to_equiv (category_theory.functor.map_iso (category_theory.forget Top) i_Top)))
          sorry sorry sorry sorry;
      category_theory.is_iso.mk { val := ↑(ring_equiv.symm e_Ring), property := sorry }

