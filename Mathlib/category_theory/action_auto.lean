/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.elements
import Mathlib.category_theory.single_obj
import Mathlib.group_theory.group_action.basic
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Actions as functors and as categories

From a multiplicative action M ↻ X, we can construct a functor from M to the category of
types, mapping the single object of M to X and an element `m : M` to map `X → X` given by
multiplication by `m`.
  This functor induces a category structure on X -- a special case of the category of elements.
A morphism `x ⟶ y` in this category is simply a scalar `m : M` such that `m • x = y`. In the case
where M is a group, this category is a groupoid -- the `action groupoid'.
-/

namespace category_theory


/-- A multiplicative action M ↻ X viewed as a functor mapping the single object of M to X
  and an element `m : M` to the map `X → X` given by multiplication by `m`. -/
@[simp] theorem action_as_functor_obj (M : Type u_1) [monoid M] (X : Type u) [mul_action M X]
    (_x : single_obj M) : functor.obj (action_as_functor M X) _x = X :=
  Eq.refl (functor.obj (action_as_functor M X) _x)

/-- A multiplicative action M ↻ X induces a category strucure on X, where a morphism
 from x to y is a scalar taking x to y. Due to implementation details, the object type
 of this category is not equal to X, but is in bijection with X. -/
def action_category (M : Type u_1) [monoid M] (X : Type u) [mul_action M X] :=
  functor.elements (action_as_functor M X)

namespace action_category


protected instance category_theory.groupoid (X : Type u) (G : Type u_1) [group G] [mul_action G X] :
    groupoid (action_category G X) :=
  category_theory.groupoid_of_elements (action_as_functor G X)

/-- The projection from the action category to the monoid, mapping a morphism to its
  label. -/
def π (M : Type u_1) [monoid M] (X : Type u) [mul_action M X] :
    action_category M X ⥤ single_obj M :=
  category_of_elements.π (action_as_functor M X)

@[simp] theorem π_map (M : Type u_1) [monoid M] (X : Type u) [mul_action M X]
    (p : action_category M X) (q : action_category M X) (f : p ⟶ q) :
    functor.map (π M X) f = subtype.val f :=
  rfl

@[simp] theorem π_obj (M : Type u_1) [monoid M] (X : Type u) [mul_action M X]
    (p : action_category M X) : functor.obj (π M X) p = single_obj.star M :=
  subsingleton.elim (functor.obj (π M X) p) (single_obj.star M)

/-- An object of the action category given by M ↻ X corresponds to an element of X. -/
def obj_equiv (M : Type u_1) [monoid M] (X : Type u) [mul_action M X] : X ≃ action_category M X :=
  equiv.mk (fun (x : X) => sigma.mk (single_obj.star M) x)
    (fun (p : action_category M X) => sigma.snd p) sorry sorry

theorem hom_as_subtype (M : Type u_1) [monoid M] (X : Type u) [mul_action M X]
    (p : action_category M X) (q : action_category M X) :
    (p ⟶ q) =
        Subtype
          fun (m : M) =>
            m • coe_fn (equiv.symm (obj_equiv M X)) p = coe_fn (equiv.symm (obj_equiv M X)) q :=
  rfl

protected instance inhabited (M : Type u_1) [monoid M] (X : Type u) [mul_action M X] [Inhabited X] :
    Inhabited (action_category M X) :=
  { default := coe_fn (obj_equiv M X) Inhabited.default }

/-- The stabilizer of a point is isomorphic to the endomorphism monoid at the
  corresponding point. In fact they are definitionally equivalent. -/
def stabilizer_iso_End (M : Type u_1) [monoid M] {X : Type u} [mul_action M X] (x : X) :
    ↥(mul_action.stabilizer.submonoid M x) ≃* End (coe_fn (obj_equiv M X) x) :=
  mul_equiv.refl ↥(mul_action.stabilizer.submonoid M x)

@[simp] theorem stabilizer_iso_End_apply (M : Type u_1) [monoid M] {X : Type u} [mul_action M X]
    (x : X) (f : ↥(mul_action.stabilizer.submonoid M x)) :
    mul_equiv.to_fun (stabilizer_iso_End M x) f = f :=
  rfl

@[simp] theorem stabilizer_iso_End_symm_apply (M : Type u_1) [monoid M] {X : Type u}
    [mul_action M X] (x : X) (f : End (coe_fn (obj_equiv M X) x)) :
    mul_equiv.inv_fun (stabilizer_iso_End M x) f = f :=
  rfl

end Mathlib