/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Group.basic
import Mathlib.data.equiv.ring
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Category instances for semiring, ring, comm_semiring, and comm_ring.

We introduce the bundled categories:
* `SemiRing`
* `Ring`
* `CommSemiRing`
* `CommRing`
along with the relevant forgetful functors between them.
-/

/-- The category of semirings. -/
def SemiRing := category_theory.bundled semiring

namespace SemiRing


protected instance bundled_hom : category_theory.bundled_hom ring_hom :=
  category_theory.bundled_hom.mk ring_hom.to_fun ring_hom.id ring_hom.comp

protected instance large_category : category_theory.large_category SemiRing :=
  category_theory.bundled_hom.category ring_hom

/-- Construct a bundled SemiRing from the underlying type and typeclass. -/
def of (R : Type u) [semiring R] : SemiRing := category_theory.bundled.of R

protected instance inhabited : Inhabited SemiRing := { default := of PUnit }

protected instance semiring (R : SemiRing) : semiring ↥R := category_theory.bundled.str R

@[simp] theorem coe_of (R : Type u) [semiring R] : ↥(of R) = R := rfl

protected instance has_forget_to_Mon : category_theory.has_forget₂ SemiRing Mon :=
  category_theory.bundled_hom.mk_has_forget₂
    (fun (R : Type u_1) (hR : semiring R) => monoid_with_zero.to_monoid R)
    (fun (R₁ R₂ : category_theory.bundled semiring) => ring_hom.to_monoid_hom) sorry

-- can't use bundled_hom.mk_has_forget₂, since AddCommMon is an induced category

protected instance has_forget_to_AddCommMon : category_theory.has_forget₂ SemiRing AddCommMon :=
  category_theory.has_forget₂.mk
    (category_theory.functor.mk (fun (R : SemiRing) => AddCommMon.of ↥R)
      fun (R₁ R₂ : SemiRing) (f : R₁ ⟶ R₂) => ring_hom.to_add_monoid_hom f)

end SemiRing


/-- The category of rings. -/
def Ring := category_theory.bundled ring

namespace Ring


protected instance ring.to_semiring.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection ring.to_semiring :=
  category_theory.bundled_hom.parent_projection.mk

protected instance concrete_category : category_theory.concrete_category Ring :=
  category_theory.bundled_hom.category_theory.bundled.category_theory.concrete_category
    (category_theory.bundled_hom.map_hom ring_hom ring.to_semiring)

/-- Construct a bundled Ring from the underlying type and typeclass. -/
def of (R : Type u) [ring R] : Ring := category_theory.bundled.of R

protected instance inhabited : Inhabited Ring := { default := of PUnit }

protected instance ring (R : Ring) : ring ↥R := category_theory.bundled.str R

@[simp] theorem coe_of (R : Type u) [ring R] : ↥(of R) = R := rfl

protected instance has_forget_to_SemiRing : category_theory.has_forget₂ Ring SemiRing :=
  category_theory.bundled_hom.forget₂ ring_hom ring.to_semiring

-- can't use bundled_hom.mk_has_forget₂, since AddCommGroup is an induced category

protected instance has_forget_to_AddCommGroup : category_theory.has_forget₂ Ring AddCommGroup :=
  category_theory.has_forget₂.mk
    (category_theory.functor.mk (fun (R : Ring) => AddCommGroup.of ↥R)
      fun (R₁ R₂ : Ring) (f : R₁ ⟶ R₂) => ring_hom.to_add_monoid_hom f)

end Ring


/-- The category of commutative semirings. -/
def CommSemiRing := category_theory.bundled comm_semiring

namespace CommSemiRing


protected instance comm_semiring.to_semiring.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection comm_semiring.to_semiring :=
  category_theory.bundled_hom.parent_projection.mk

protected instance large_category : category_theory.large_category CommSemiRing :=
  category_theory.bundled_hom.category
    (category_theory.bundled_hom.map_hom ring_hom comm_semiring.to_semiring)

/-- Construct a bundled CommSemiRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_semiring R] : CommSemiRing := category_theory.bundled.of R

protected instance inhabited : Inhabited CommSemiRing := { default := of PUnit }

protected instance comm_semiring (R : CommSemiRing) : comm_semiring ↥R :=
  category_theory.bundled.str R

@[simp] theorem coe_of (R : Type u) [comm_semiring R] : ↥(of R) = R := rfl

protected instance has_forget_to_SemiRing : category_theory.has_forget₂ CommSemiRing SemiRing :=
  category_theory.bundled_hom.forget₂ ring_hom comm_semiring.to_semiring

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
protected instance has_forget_to_CommMon : category_theory.has_forget₂ CommSemiRing CommMon :=
  category_theory.has_forget₂.mk' (fun (R : CommSemiRing) => CommMon.of ↥R) sorry
    (fun (R₁ R₂ : CommSemiRing) (f : R₁ ⟶ R₂) => ring_hom.to_monoid_hom f) sorry

end CommSemiRing


/-- The category of commutative rings. -/
def CommRing := category_theory.bundled comm_ring

namespace CommRing


protected instance comm_ring.to_ring.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection comm_ring.to_ring :=
  category_theory.bundled_hom.parent_projection.mk

protected instance concrete_category : category_theory.concrete_category CommRing :=
  category_theory.bundled_hom.category_theory.bundled.category_theory.concrete_category
    (category_theory.bundled_hom.map_hom
      (category_theory.bundled_hom.map_hom ring_hom ring.to_semiring) comm_ring.to_ring)

/-- Construct a bundled CommRing from the underlying type and typeclass. -/
def of (R : Type u) [comm_ring R] : CommRing := category_theory.bundled.of R

protected instance inhabited : Inhabited CommRing := { default := of PUnit }

protected instance comm_ring (R : CommRing) : comm_ring ↥R := category_theory.bundled.str R

@[simp] theorem coe_of (R : Type u) [comm_ring R] : ↥(of R) = R := rfl

protected instance has_forget_to_Ring : category_theory.has_forget₂ CommRing Ring :=
  category_theory.bundled_hom.forget₂
    (category_theory.bundled_hom.map_hom ring_hom ring.to_semiring) comm_ring.to_ring

/-- The forgetful functor from commutative rings to (multiplicative) commutative monoids. -/
protected instance has_forget_to_CommSemiRing : category_theory.has_forget₂ CommRing CommSemiRing :=
  category_theory.has_forget₂.mk' (fun (R : CommRing) => CommSemiRing.of ↥R) sorry
    (fun (R₁ R₂ : CommRing) (f : R₁ ⟶ R₂) => f) sorry

protected instance category_theory.forget₂.category_theory.full :
    category_theory.full (category_theory.forget₂ CommRing CommSemiRing) :=
  category_theory.full.mk
    fun (X Y : CommRing)
      (f :
      category_theory.functor.obj (category_theory.forget₂ CommRing CommSemiRing) X ⟶
        category_theory.functor.obj (category_theory.forget₂ CommRing CommSemiRing) Y) =>
      f

end CommRing


-- This example verifies an improvement possible in Lean 3.8.

-- Before that, to have `add_ring_hom.map_zero` usable by `simp` here,

-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.

-- Now, it just works.

namespace ring_equiv


/-- Build an isomorphism in the category `Ring` from a `ring_equiv` between `ring`s. -/
@[simp] theorem to_Ring_iso_inv {X : Type u} {Y : Type u} [ring X] [ring Y] (e : X ≃+* Y) :
    category_theory.iso.inv (to_Ring_iso e) = to_ring_hom (ring_equiv.symm e) :=
  Eq.refl (category_theory.iso.inv (to_Ring_iso e))

/-- Build an isomorphism in the category `CommRing` from a `ring_equiv` between `comm_ring`s. -/
def to_CommRing_iso {X : Type u} {Y : Type u} [comm_ring X] [comm_ring Y] (e : X ≃+* Y) :
    CommRing.of X ≅ CommRing.of Y :=
  category_theory.iso.mk (to_ring_hom e) (to_ring_hom (ring_equiv.symm e))

end ring_equiv


namespace category_theory.iso


/-- Build a `ring_equiv` from an isomorphism in the category `Ring`. -/
def Ring_iso_to_ring_equiv {X : Ring} {Y : Ring} (i : X ≅ Y) : ↥X ≃+* ↥Y :=
  ring_equiv.mk ⇑(hom i) ⇑(inv i) sorry sorry sorry sorry

/-- Build a `ring_equiv` from an isomorphism in the category `CommRing`. -/
def CommRing_iso_to_ring_equiv {X : CommRing} {Y : CommRing} (i : X ≅ Y) : ↥X ≃+* ↥Y :=
  ring_equiv.mk ⇑(hom i) ⇑(inv i) sorry sorry sorry sorry

end category_theory.iso


/-- Ring equivalences between `ring`s are the same as (isomorphic to) isomorphisms in `Ring`. -/
def ring_equiv_iso_Ring_iso {X : Type u} {Y : Type u} [ring X] [ring Y] :
    X ≃+* Y ≅ Ring.of X ≅ Ring.of Y :=
  category_theory.iso.mk (fun (e : X ≃+* Y) => ring_equiv.to_Ring_iso e)
    fun (i : Ring.of X ≅ Ring.of Y) => category_theory.iso.Ring_iso_to_ring_equiv i

/-- Ring equivalences between `comm_ring`s are the same as (isomorphic to) isomorphisms
in `CommRing`. -/
def ring_equiv_iso_CommRing_iso {X : Type u} {Y : Type u} [comm_ring X] [comm_ring Y] :
    X ≃+* Y ≅ CommRing.of X ≅ CommRing.of Y :=
  category_theory.iso.mk (fun (e : X ≃+* Y) => ring_equiv.to_CommRing_iso e)
    fun (i : CommRing.of X ≅ CommRing.of Y) => category_theory.iso.CommRing_iso_to_ring_equiv i

protected instance Ring.forget_reflects_isos :
    category_theory.reflects_isomorphisms (category_theory.forget Ring) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : Ring) (f : X ⟶ Y)
      (_x : category_theory.is_iso (category_theory.functor.map (category_theory.forget Ring) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget Ring) X ≅
          category_theory.functor.obj (category_theory.forget Ring) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget Ring) f);
      let e : ↥X ≃+* ↥Y :=
        ring_equiv.mk (ring_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry
          sorry sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (ring_equiv.to_Ring_iso e))

protected instance CommRing.forget_reflects_isos :
    category_theory.reflects_isomorphisms (category_theory.forget CommRing) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : CommRing) (f : X ⟶ Y)
      (_x :
      category_theory.is_iso (category_theory.functor.map (category_theory.forget CommRing) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget CommRing) X ≅
          category_theory.functor.obj (category_theory.forget CommRing) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget CommRing) f);
      let e : ↥X ≃+* ↥Y :=
        ring_equiv.mk (ring_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry
          sorry sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (ring_equiv.to_CommRing_iso e))

end Mathlib