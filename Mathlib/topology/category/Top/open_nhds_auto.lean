/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.category.Top.opens
import Mathlib.category_theory.filtered
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace topological_space


def open_nhds {X : Top} (x : ↥X) := Subtype fun (U : opens ↥X) => x ∈ U

namespace open_nhds


protected instance partial_order {X : Top} (x : ↥X) : partial_order (open_nhds x) :=
  partial_order.mk (fun (U V : open_nhds x) => subtype.val U ≤ subtype.val V)
    (preorder.lt._default fun (U V : open_nhds x) => subtype.val U ≤ subtype.val V) sorry sorry
    sorry

protected instance lattice {X : Top} (x : ↥X) : lattice (open_nhds x) :=
  lattice.mk
    (fun (U V : open_nhds x) => { val := subtype.val U ⊔ subtype.val V, property := sorry })
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry
    (fun (U V : open_nhds x) => { val := subtype.val U ⊓ subtype.val V, property := sorry }) sorry
    sorry sorry

protected instance order_top {X : Top} (x : ↥X) : order_top (open_nhds x) :=
  order_top.mk { val := ⊤, property := trivial } partial_order.le partial_order.lt sorry sorry sorry
    sorry

protected instance open_nhds_category {X : Top} (x : ↥X) : category_theory.category (open_nhds x) :=
  eq.mpr sorry (category_theory.full_subcategory fun (U : opens ↥X) => x ∈ U)

protected instance opens_nhds_hom_has_coe_to_fun {X : Top} {x : ↥X} {U : open_nhds x}
    {V : open_nhds x} : has_coe_to_fun (U ⟶ V) :=
  has_coe_to_fun.mk (fun (f : U ⟶ V) => ↥(subtype.val U) → ↥(subtype.val V))
    fun (f : U ⟶ V) (x_1 : ↥(subtype.val U)) => { val := ↑x_1, property := sorry }

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left {X : Top} {x : ↥X} (U : open_nhds x) (V : open_nhds x) : U ⊓ V ⟶ U :=
  category_theory.hom_of_le sorry

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right {X : Top} {x : ↥X} (U : open_nhds x) (V : open_nhds x) : U ⊓ V ⟶ V :=
  category_theory.hom_of_le sorry

def inclusion {X : Top} (x : ↥X) : open_nhds x ⥤ opens ↥X :=
  category_theory.full_subcategory_inclusion fun (U : opens ↥X) => x ∈ U

@[simp] theorem inclusion_obj {X : Top} (x : ↥X) (U : opens ↥X) (p : x ∈ U) :
    category_theory.functor.obj (inclusion x) { val := U, property := p } = U :=
  rfl

protected instance open_nhds_is_filtered {X : Top} (x : ↥X) :
    category_theory.is_filtered (open_nhds xᵒᵖ) :=
  category_theory.is_filtered.mk

def map {X : Top} {Y : Top} (f : X ⟶ Y) (x : ↥X) : open_nhds (coe_fn f x) ⥤ open_nhds x :=
  category_theory.functor.mk
    (fun (U : open_nhds (coe_fn f x)) =>
      { val := category_theory.functor.obj (opens.map f) (subtype.val U), property := sorry })
    fun (U V : open_nhds (coe_fn f x)) (i : U ⟶ V) => category_theory.functor.map (opens.map f) i

@[simp] theorem map_obj {X : Top} {Y : Top} (f : X ⟶ Y) (x : ↥X) (U : opens ↥Y)
    (q : coe_fn f x ∈ U) :
    category_theory.functor.obj (map f x) { val := U, property := q } =
        { val := category_theory.functor.obj (opens.map f) U, property := q } :=
  rfl

@[simp] theorem map_id_obj {X : Top} (x : ↥X) (U : open_nhds (coe_fn 𝟙 x)) :
    category_theory.functor.obj (map 𝟙 x) U = U :=
  sorry

@[simp] theorem map_id_obj' {X : Top} (x : ↥X) (U : set ↥X) (p : is_open U)
    (q : coe_fn 𝟙 x ∈ { val := U, property := p }) :
    category_theory.functor.obj (map 𝟙 x) { val := { val := U, property := p }, property := q } =
        { val := { val := U, property := p }, property := q } :=
  rfl

@[simp] theorem map_id_obj_unop {X : Top} (x : ↥X) (U : open_nhds xᵒᵖ) :
    category_theory.functor.obj (map 𝟙 x) (opposite.unop U) = opposite.unop U :=
  sorry

@[simp] theorem op_map_id_obj {X : Top} (x : ↥X) (U : open_nhds xᵒᵖ) :
    category_theory.functor.obj (category_theory.functor.op (map 𝟙 x)) U = U :=
  sorry

def inclusion_map_iso {X : Top} {Y : Top} (f : X ⟶ Y) (x : ↥X) :
    inclusion (coe_fn f x) ⋙ opens.map f ≅ map f x ⋙ inclusion x :=
  category_theory.nat_iso.of_components
    (fun (U : open_nhds (coe_fn f x)) => category_theory.iso.mk 𝟙 𝟙) sorry

@[simp] theorem inclusion_map_iso_hom {X : Top} {Y : Top} (f : X ⟶ Y) (x : ↥X) :
    category_theory.iso.hom (inclusion_map_iso f x) = 𝟙 :=
  rfl

@[simp] theorem inclusion_map_iso_inv {X : Top} {Y : Top} (f : X ⟶ Y) (x : ↥X) :
    category_theory.iso.inv (inclusion_map_iso f x) = 𝟙 :=
  rfl

end Mathlib