/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Mon.basic
import Mathlib.category_theory.endomorphism
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Category instances for group, add_group, comm_group, and add_comm_group.

We introduce the bundled categories:
* `Group`
* `AddGroup`
* `CommGroup`
* `AddCommGroup`
along with the relevant forgetful functors between them, and to the bundled monoid categories.
-/

/-- The category of groups and group morphisms. -/
def AddGroup := category_theory.bundled add_group

/-- The category of additive groups and group morphisms -/
namespace Group


protected instance Mathlib.AddGroup.group.to_monoid.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection add_group.to_add_monoid :=
  category_theory.bundled_hom.parent_projection.mk

protected instance has_coe_to_sort : has_coe_to_sort Group :=
  category_theory.bundled.has_coe_to_sort

/-- Construct a bundled `Group` from the underlying type and typeclass. -/
def of (X : Type u) [group X] : Group := category_theory.bundled.of X

/-- Construct a bundled `AddGroup` from the underlying type and typeclass. -/
protected instance group (G : Group) : group ↥G := category_theory.bundled.str G

@[simp] theorem coe_of (R : Type u) [group R] : ↥(of R) = R := rfl

protected instance Mathlib.AddGroup.has_zero : HasZero AddGroup := { zero := AddGroup.of PUnit }

protected instance inhabited : Inhabited Group := { default := 1 }

protected instance one.unique : unique ↥1 := unique.mk { default := 1 } sorry

@[simp] theorem one_apply (G : Group) (H : Group) (g : ↥G) : coe_fn 1 g = 1 := rfl

theorem ext (G : Group) (H : Group) (f₁ : G ⟶ H) (f₂ : G ⟶ H)
    (w : ∀ (x : ↥G), coe_fn f₁ x = coe_fn f₂ x) : f₁ = f₂ :=
  monoid_hom.ext fun (x : ↥G) => w x

-- should to_additive do this automatically?

protected instance Mathlib.AddGroup.has_forget_to_AddMon :
    category_theory.has_forget₂ AddGroup AddMon :=
  category_theory.bundled_hom.forget₂ add_monoid_hom add_group.to_add_monoid

end Group


/-- The category of commutative groups and group morphisms. -/
def AddCommGroup := category_theory.bundled add_comm_group

/-- The category of additive commutative groups and group morphisms. -/
/-- `Ab` is an abbreviation for `AddCommGroup`, for the sake of mathematicians' sanity. -/
def Ab := AddCommGroup

namespace CommGroup


protected instance comm_group.to_group.category_theory.bundled_hom.parent_projection :
    category_theory.bundled_hom.parent_projection comm_group.to_group :=
  category_theory.bundled_hom.parent_projection.mk

protected instance large_category : category_theory.large_category CommGroup :=
  category_theory.bundled_hom.category
    (category_theory.bundled_hom.map_hom
      (category_theory.bundled_hom.map_hom monoid_hom group.to_monoid) comm_group.to_group)

/-- Construct a bundled `CommGroup` from the underlying type and typeclass. -/
def of (G : Type u) [comm_group G] : CommGroup := category_theory.bundled.of G

/-- Construct a bundled `AddCommGroup` from the underlying type and typeclass. -/
protected instance Mathlib.AddCommGroup.add_comm_group_instance (G : AddCommGroup) :
    add_comm_group ↥G :=
  category_theory.bundled.str G

@[simp] theorem coe_of (R : Type u) [comm_group R] : ↥(of R) = R := rfl

protected instance Mathlib.AddCommGroup.has_zero : HasZero AddCommGroup :=
  { zero := AddCommGroup.of PUnit }

protected instance inhabited : Inhabited CommGroup := { default := 1 }

protected instance one.unique : unique ↥1 := unique.mk { default := 1 } sorry

@[simp] theorem one_apply (G : CommGroup) (H : CommGroup) (g : ↥G) : coe_fn 1 g = 1 := rfl

theorem ext (G : CommGroup) (H : CommGroup) (f₁ : G ⟶ H) (f₂ : G ⟶ H)
    (w : ∀ (x : ↥G), coe_fn f₁ x = coe_fn f₂ x) : f₁ = f₂ :=
  monoid_hom.ext fun (x : ↥G) => w x

protected instance Mathlib.AddCommGroup.has_forget_to_AddGroup :
    category_theory.has_forget₂ AddCommGroup AddGroup :=
  category_theory.bundled_hom.forget₂
    (category_theory.bundled_hom.map_hom add_monoid_hom add_group.to_add_monoid)
    add_comm_group.to_add_group

protected instance Mathlib.AddCommGroup.has_forget_to_AddCommMon :
    category_theory.has_forget₂ AddCommGroup AddCommMon :=
  category_theory.induced_category.has_forget₂ fun (G : AddCommGroup) => AddCommMon.of ↥G

end CommGroup


-- This example verifies an improvement possible in Lean 3.8.

-- Before that, to have `monoid_hom.map_map` usable by `simp` here,

-- we had to mark all the concrete category `has_coe_to_sort` instances reducible.

-- Now, it just works.

namespace AddCommGroup


/-- Any element of an abelian group gives a unique morphism from `ℤ` sending
`1` to that element. -/
-- Note that because `ℤ : Type 0`, this forces `G : AddCommGroup.{0}`,

-- so we write this explicitly to be clear.

-- TODO generalize this, requiring a `ulift_instances.lean` file

def as_hom {G : AddCommGroup} (g : ↥G) : of ℤ ⟶ G := coe_fn (gmultiples_hom ↥G) g

@[simp] theorem as_hom_apply {G : AddCommGroup} (g : ↥G) (i : ℤ) : coe_fn (as_hom g) i = i • g :=
  rfl

theorem as_hom_injective {G : AddCommGroup} : function.injective as_hom := sorry

theorem int_hom_ext {G : AddCommGroup} (f : of ℤ ⟶ G) (g : of ℤ ⟶ G) (w : coe_fn f 1 = coe_fn g 1) :
    f = g :=
  add_monoid_hom.ext_int w

-- TODO: this argument should be generalised to the situation where

-- the forgetful functor is representable.

theorem injective_of_mono {G : AddCommGroup} {H : AddCommGroup} (f : G ⟶ H)
    [category_theory.mono f] : function.injective ⇑f :=
  sorry

end AddCommGroup


/-- Build an isomorphism in the category `Group` from a `mul_equiv` between `group`s. -/
def mul_equiv.to_Group_iso {X : Type u} {Y : Type u} [group X] [group Y] (e : X ≃* Y) :
    Group.of X ≅ Group.of Y :=
  category_theory.iso.mk (mul_equiv.to_monoid_hom e) (mul_equiv.to_monoid_hom (mul_equiv.symm e))

/-- Build an isomorphism in the category `AddGroup` from an `add_equiv` between `add_group`s. -/
/-- Build an isomorphism in the category `CommGroup` from a `mul_equiv` between `comm_group`s. -/
def add_equiv.to_AddCommGroup_iso {X : Type u} {Y : Type u} [add_comm_group X] [add_comm_group Y]
    (e : X ≃+ Y) : AddCommGroup.of X ≅ AddCommGroup.of Y :=
  category_theory.iso.mk (add_equiv.to_add_monoid_hom e)
    (add_equiv.to_add_monoid_hom (add_equiv.symm e))

/-- Build an isomorphism in the category `AddCommGroup` from a `add_equiv` between
`add_comm_group`s. -/
namespace category_theory.iso


/-- Build a `mul_equiv` from an isomorphism in the category `Group`. -/
@[simp] theorem Group_iso_to_add_equiv_apply {X : AddGroup} {Y : AddGroup} (i : X ≅ Y) :
    ∀ (ᾰ : ↥X), coe_fn (AddGroup_iso_to_add_equiv i) ᾰ = coe_fn (hom i) ᾰ :=
  fun (ᾰ : ↥X) => Eq.refl (coe_fn (hom i) ᾰ)

/-- Build a `mul_equiv` from an isomorphism in the category `CommGroup`. -/
@[simp] theorem CommGroup_iso_to_add_equiv_apply {X : AddCommGroup} {Y : AddCommGroup} (i : X ≅ Y) :
    ∀ (ᾰ : ↥X), coe_fn (AddCommGroup_iso_to_add_equiv i) ᾰ = coe_fn (hom i) ᾰ :=
  fun (ᾰ : ↥X) => Eq.refl (coe_fn (hom i) ᾰ)

end category_theory.iso


/-- multiplicative equivalences between `group`s are the same as (isomorphic to) isomorphisms
in `Group` -/
def add_equiv_iso_AddGroup_iso {X : Type u} {Y : Type u} [add_group X] [add_group Y] :
    X ≃+ Y ≅ AddGroup.of X ≅ AddGroup.of Y :=
  category_theory.iso.mk (fun (e : X ≃+ Y) => add_equiv.to_AddGroup_iso e)
    fun (i : AddGroup.of X ≅ AddGroup.of Y) => category_theory.iso.AddGroup_iso_to_add_equiv i

/-- multiplicative equivalences between `comm_group`s are the same as (isomorphic to) isomorphisms
in `CommGroup` -/
def mul_equiv_iso_CommGroup_iso {X : Type u} {Y : Type u} [comm_group X] [comm_group Y] :
    X ≃* Y ≅ CommGroup.of X ≅ CommGroup.of Y :=
  category_theory.iso.mk (fun (e : X ≃* Y) => mul_equiv.to_CommGroup_iso e)
    fun (i : CommGroup.of X ≅ CommGroup.of Y) => category_theory.iso.CommGroup_iso_to_mul_equiv i

namespace category_theory.Aut


/-- The (bundled) group of automorphisms of a type is isomorphic to the (bundled) group
of permutations. -/
def iso_perm {α : Type u} : Group.of (Aut α) ≅ Group.of (equiv.perm α) :=
  iso.mk (monoid_hom.mk (fun (g : ↥(Group.of (Aut α))) => iso.to_equiv g) sorry sorry)
    (monoid_hom.mk (fun (g : ↥(Group.of (equiv.perm α))) => equiv.to_iso g) sorry sorry)

/-- The (unbundled) group of automorphisms of a type is `mul_equiv` to the (unbundled) group
of permutations. -/
def mul_equiv_perm {α : Type u} : Aut α ≃* equiv.perm α := iso.Group_iso_to_mul_equiv iso_perm

end category_theory.Aut


protected instance Group.forget_reflects_isos :
    category_theory.reflects_isomorphisms (category_theory.forget Group) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : Group) (f : X ⟶ Y)
      (_x :
      category_theory.is_iso (category_theory.functor.map (category_theory.forget Group) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget Group) X ≅
          category_theory.functor.obj (category_theory.forget Group) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget Group) f);
      let e : ↥X ≃* ↥Y :=
        mul_equiv.mk (monoid_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry
          sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (mul_equiv.to_Group_iso e))

protected instance CommGroup.forget_reflects_isos :
    category_theory.reflects_isomorphisms (category_theory.forget CommGroup) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : CommGroup) (f : X ⟶ Y)
      (_x :
      category_theory.is_iso (category_theory.functor.map (category_theory.forget CommGroup) f)) =>
      let i :
        category_theory.functor.obj (category_theory.forget CommGroup) X ≅
          category_theory.functor.obj (category_theory.forget CommGroup) Y :=
        category_theory.as_iso (category_theory.functor.map (category_theory.forget CommGroup) f);
      let e : ↥X ≃* ↥Y :=
        mul_equiv.mk (monoid_hom.to_fun f) (equiv.inv_fun (category_theory.iso.to_equiv i)) sorry
          sorry sorry;
      category_theory.is_iso.mk (category_theory.iso.inv (mul_equiv.to_CommGroup_iso e))

end Mathlib