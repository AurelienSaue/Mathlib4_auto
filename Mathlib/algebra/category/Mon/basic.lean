/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.concrete_category.bundled_hom
import Mathlib.category_theory.concrete_category.reflects_isomorphisms
import Mathlib.algebra.punit_instances
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Category instances for monoid, add_monoid, comm_monoid, and add_comm_monoid.

We introduce the bundled categories:
* `Mon`
* `AddMon`
* `CommMon`
* `AddCommMon`
along with the relevant forgetful functors between them.
-/

/-- The category of monoids and monoid morphisms. -/
def Mon :=
  category_theory.bundled monoid

/-- The category of additive monoids and monoid morphisms. -/
namespace Mon


protected instance Mathlib.AddMon.bundled_hom : category_theory.bundled_hom add_monoid_hom :=
  category_theory.bundled_hom.mk add_monoid_hom.to_fun add_monoid_hom.id add_monoid_hom.comp

protected instance Mathlib.AddMon.concrete_category : category_theory.concrete_category AddMon :=
  category_theory.bundled_hom.category_theory.bundled.category_theory.concrete_category add_monoid_hom

/-- Construct a bundled `Mon` from the underlying type and typeclass. -/
def Mathlib.AddMon.of (M : Type u) [add_monoid M] : AddMon :=
  category_theory.bundled.of M

/-- Construct a bundled `Mon` from the underlying type and typeclass. -/
-- The default instance for `monoid punit` is derived via `punit.comm_ring`,

protected instance Mathlib.AddMon.inhabited : Inhabited AddMon :=
  { default := AddMon.of PUnit }

-- which breaks to_additive.

protected instance Mathlib.AddMon.add_monoid (M : AddMon) : add_monoid ↥M :=
  category_theory.bundled.str M

@[simp] theorem Mathlib.AddMon.coe_of (R : Type u) [add_monoid R] : ↥(AddMon.of R) = R :=
  rfl

end Mon


/-- The category of commutative monoids and monoid morphisms. -/
def CommMon :=
  category_theory.bundled comm_monoid

/-- The category of additive commutative monoids and monoid morphisms. -/
namespace CommMon


protected instance comm_monoid.to_monoid.category_theory.bundled_hom.parent_projection : category_theory.bundled_hom.parent_projection comm_monoid.to_monoid :=
  category_theory.bundled_hom.parent_projection.mk

protected instance has_coe_to_sort : has_coe_to_sort CommMon :=
  category_theory.bundled.has_coe_to_sort

/-- Construct a bundled `CommMon` from the underlying type and typeclass. -/
def of (M : Type u) [comm_monoid M] : CommMon :=
  category_theory.bundled.of M

/-- Construct a bundled `AddCommMon` from the underlying type and typeclass. -/
-- The default instance for `comm_monoid punit` is derived via `punit.comm_ring`,

protected instance Mathlib.AddCommMon.inhabited : Inhabited AddCommMon :=
  { default := AddCommMon.of PUnit }

-- which breaks to_additive.

protected instance Mathlib.AddCommMon.add_comm_monoid (M : AddCommMon) : add_comm_monoid ↥M :=
  category_theory.bundled.str M

@[simp] theorem coe_of (R : Type u) [comm_monoid R] : ↥(of R) = R :=
  rfl

protected instance Mathlib.AddCommMon.has_forget_to_AddMon : category_theory.has_forget₂ AddCommMon AddMon :=
  category_theory.bundled_hom.forget₂ add_monoid_hom add_comm_monoid.to_add_monoid

end CommMon


-- We verify that the coercions of morphisms to functions work correctly:

-- We verify that when constructing a morphism in `CommMon`,

-- when we construct the `to_fun` field, the types are presented as `↥R`,

-- rather than `R.α` or (as we used to have) `↥(bundled.map comm_monoid.to_monoid R)`.

/-- Build an isomorphism in the category `Mon` from a `mul_equiv` between `monoid`s. -/
def mul_equiv.to_Mon_iso {X : Type u} {Y : Type u} [monoid X] [monoid Y] (e : X ≃* Y) : Mon.of X ≅ Mon.of Y :=
  category_theory.iso.mk (mul_equiv.to_monoid_hom e) (mul_equiv.to_monoid_hom (mul_equiv.symm e))

@[simp] theorem mul_equiv.to_Mon_iso_hom {X : Type u} {Y : Type u} [monoid X] [monoid Y] {e : X ≃* Y} : category_theory.iso.hom (mul_equiv.to_Mon_iso e) = mul_equiv.to_monoid_hom e :=
  rfl

@[simp] theorem add_equiv.to_AddMon_iso_inv {X : Type u} {Y : Type u} [add_monoid X] [add_monoid Y] {e : X ≃+ Y} : category_theory.iso.inv (add_equiv.to_AddMon_iso e) = add_equiv.to_add_monoid_hom (add_equiv.symm e) :=
  rfl

/-- Build an isomorphism in the category `CommMon` from a `mul_equiv` between `comm_monoid`s. -/
def add_equiv.to_AddCommMon_iso {X : Type u} {Y : Type u} [add_comm_monoid X] [add_comm_monoid Y] (e : X ≃+ Y) : AddCommMon.of X ≅ AddCommMon.of Y :=
  category_theory.iso.mk (add_equiv.to_add_monoid_hom e) (add_equiv.to_add_monoid_hom (add_equiv.symm e))

@[simp] theorem add_equiv.to_AddCommMon_iso_hom {X : Type u} {Y : Type u} [add_comm_monoid X] [add_comm_monoid Y] {e : X ≃+ Y} : category_theory.iso.hom (add_equiv.to_AddCommMon_iso e) = add_equiv.to_add_monoid_hom e :=
  rfl

@[simp] theorem add_equiv.to_AddCommMon_iso_inv {X : Type u} {Y : Type u} [add_comm_monoid X] [add_comm_monoid Y] {e : X ≃+ Y} : category_theory.iso.inv (add_equiv.to_AddCommMon_iso e) = add_equiv.to_add_monoid_hom (add_equiv.symm e) :=
  rfl

namespace category_theory.iso


/-- Build a `mul_equiv` from an isomorphism in the category `Mon`. -/
def AddMon_iso_to_add_equiv {X : AddMon} {Y : AddMon} (i : X ≅ Y) : ↥X ≃+ ↥Y :=
  add_monoid_hom.to_add_equiv (hom i) (inv i) (hom_inv_id i) (inv_hom_id i)

/-- Build a `mul_equiv` from an isomorphism in the category `CommMon`. -/
def CommMon_iso_to_add_equiv {X : AddCommMon} {Y : AddCommMon} (i : X ≅ Y) : ↥X ≃+ ↥Y :=
  add_monoid_hom.to_add_equiv (hom i) (inv i) (hom_inv_id i) (inv_hom_id i)

end category_theory.iso


/-- multiplicative equivalences between `monoid`s are the same as (isomorphic to) isomorphisms
in `Mon` -/
def mul_equiv_iso_Mon_iso {X : Type u} {Y : Type u} [monoid X] [monoid Y] : X ≃* Y ≅ Mon.of X ≅ Mon.of Y :=
  category_theory.iso.mk (fun (e : X ≃* Y) => mul_equiv.to_Mon_iso e)
    fun (i : Mon.of X ≅ Mon.of Y) => category_theory.iso.Mon_iso_to_mul_equiv i

/-- multiplicative equivalences between `comm_monoid`s are the same as (isomorphic to) isomorphisms
in `CommMon` -/
def add_equiv_iso_AddCommMon_iso {X : Type u} {Y : Type u} [add_comm_monoid X] [add_comm_monoid Y] : X ≃+ Y ≅ AddCommMon.of X ≅ AddCommMon.of Y :=
  category_theory.iso.mk (fun (e : X ≃+ Y) => add_equiv.to_AddCommMon_iso e)
    fun (i : AddCommMon.of X ≅ AddCommMon.of Y) => category_theory.iso.CommMon_iso_to_add_equiv i

protected instance AddMon.forget_reflects_isos : category_theory.reflects_isomorphisms (category_theory.forget AddMon) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : AddMon) (f : X ⟶ Y)
      (_x : category_theory.is_iso (category_theory.functor.map (category_theory.forget AddMon) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget AddMon) X ≅
          category_theory.functor.obj (category_theory.forget AddMon) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget AddMon) f);
      let e : ↥X ≃+ ↥Y :=
        add_equiv.mk (add_monoid_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (add_equiv.to_AddMon_iso e))

protected instance CommMon.forget_reflects_isos : category_theory.reflects_isomorphisms (category_theory.forget CommMon) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : CommMon) (f : X ⟶ Y)
      (_x : category_theory.is_iso (category_theory.functor.map (category_theory.forget CommMon) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget CommMon) X ≅
          category_theory.functor.obj (category_theory.forget CommMon) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget CommMon) f);
      let e : ↥X ≃* ↥Y :=
        mul_equiv.mk (monoid_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (mul_equiv.to_CommMon_iso e))

