/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.ring
import Mathlib.algebra.opposites
import PostPort

universes u_1 l 

namespace Mathlib

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notations

We provide a coercion to a function `R → Rᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

/-- A ring involution -/
structure ring_invo (R : Type u_1) [semiring R] 
extends R ≃+* (Rᵒᵖ)
where
  involution' : ∀ (x : R), opposite.unop (ring_equiv.to_fun _to_ring_equiv (opposite.unop (ring_equiv.to_fun _to_ring_equiv x))) = x

namespace ring_invo


/-- Construct a ring involution from a ring homomorphism. -/
def mk' {R : Type u_1} [semiring R] (f : R →+* (Rᵒᵖ)) (involution : ∀ (r : R), opposite.unop (coe_fn f (opposite.unop (coe_fn f r))) = r) : ring_invo R :=
  mk
    (ring_equiv.mk (ring_hom.to_fun f) (fun (r : Rᵒᵖ) => opposite.unop (coe_fn f (opposite.unop r))) sorry sorry sorry
      sorry)
    involution

protected instance has_coe_to_fun {R : Type u_1} [semiring R] : has_coe_to_fun (ring_invo R) :=
  has_coe_to_fun.mk (fun (f : ring_invo R) => R → (Rᵒᵖ)) fun (f : ring_invo R) => ring_equiv.to_fun (to_ring_equiv f)

@[simp] theorem to_fun_eq_coe {R : Type u_1} [semiring R] (f : ring_invo R) : ring_equiv.to_fun (to_ring_equiv f) = ⇑f :=
  rfl

@[simp] theorem involution {R : Type u_1} [semiring R] (f : ring_invo R) (x : R) : opposite.unop (coe_fn f (opposite.unop (coe_fn f x))) = x :=
  involution' f x

protected instance has_coe_to_ring_equiv {R : Type u_1} [semiring R] : has_coe (ring_invo R) (R ≃+* (Rᵒᵖ)) :=
  has_coe.mk to_ring_equiv

theorem coe_ring_equiv {R : Type u_1} [semiring R] (f : ring_invo R) (a : R) : coe_fn (↑f) a = coe_fn f a :=
  rfl

@[simp] theorem map_eq_zero_iff {R : Type u_1} [semiring R] (f : ring_invo R) {x : R} : coe_fn f x = 0 ↔ x = 0 :=
  ring_equiv.map_eq_zero_iff (to_ring_equiv f)

end ring_invo


/-- The identity function of a `comm_ring` is a ring involution. -/
protected def ring_invo.id (R : Type u_1) [comm_ring R] : ring_invo R :=
  ring_invo.mk
    (ring_equiv.mk (ring_equiv.to_fun (ring_equiv.to_opposite R)) (ring_equiv.inv_fun (ring_equiv.to_opposite R)) sorry
      sorry sorry sorry)
    sorry

protected instance ring_invo.inhabited (R : Type u_1) [comm_ring R] : Inhabited (ring_invo R) :=
  { default := ring_invo.id R }

