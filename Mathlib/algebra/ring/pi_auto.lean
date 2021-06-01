/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.pi_instances
import Mathlib.algebra.group.pi
import Mathlib.algebra.ring.basic
import Mathlib.PostPort

universes u v w u_1 u_2 

namespace Mathlib

/-!
# Pi instances for ring

This file defines instances for ring, semiring and related structures on Pi Types
-/

namespace pi


protected instance distrib {I : Type u} {f : I → Type v} [(i : I) → distrib (f i)] :
    distrib ((i : I) → f i) :=
  distrib.mk Mul.mul Add.add sorry sorry

protected instance semiring {I : Type u} {f : I → Type v} [(i : I) → semiring (f i)] :
    semiring ((i : I) → f i) :=
  semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry sorry

protected instance comm_semiring {I : Type u} {f : I → Type v} [(i : I) → comm_semiring (f i)] :
    comm_semiring ((i : I) → f i) :=
  comm_semiring.mk Add.add sorry 0 sorry sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry
    sorry sorry

protected instance ring {I : Type u} {f : I → Type v} [(i : I) → ring (f i)] :
    ring ((i : I) → f i) :=
  ring.mk Add.add sorry 0 sorry sorry Neg.neg
    (fun (ᾰ ᾰ_1 : (i : I) → f i) (i : I) => ring.sub (ᾰ i) (ᾰ_1 i)) sorry sorry Mul.mul sorry 1
    sorry sorry sorry sorry

protected instance comm_ring {I : Type u} {f : I → Type v} [(i : I) → comm_ring (f i)] :
    comm_ring ((i : I) → f i) :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg
    (fun (ᾰ ᾰ_1 : (i : I) → f i) (i : I) => comm_ring.sub (ᾰ i) (ᾰ_1 i)) sorry sorry Mul.mul sorry 1
    sorry sorry sorry sorry sorry

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
protected def ring_hom {α : Type u} {β : α → Type v} [R : (a : α) → semiring (β a)] {γ : Type w}
    [semiring γ] (f : (a : α) → γ →+* β a) : γ →+* (a : α) → β a :=
  ring_hom.mk (fun (x : γ) (b : α) => coe_fn (f b) x) sorry sorry sorry sorry

@[simp] theorem ring_hom_apply {α : Type u} {β : α → Type v} [R : (a : α) → semiring (β a)]
    {γ : Type w} [semiring γ] (f : (a : α) → γ →+* β a) (g : γ) (a : α) :
    coe_fn (pi.ring_hom f) g a = coe_fn (f a) g :=
  rfl

end pi


/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism. -/
def ring_hom.apply {I : Type u_1} (f : I → Type u_2) [(i : I) → semiring (f i)] (i : I) :
    ((i : I) → f i) →+* f i :=
  ring_hom.mk (monoid_hom.to_fun (monoid_hom.apply f i)) sorry sorry sorry sorry

@[simp] theorem ring_hom.apply_apply {I : Type u_1} (f : I → Type u_2) [(i : I) → semiring (f i)]
    (i : I) (g : (i : I) → f i) : coe_fn (ring_hom.apply f i) g = g i :=
  rfl

end Mathlib