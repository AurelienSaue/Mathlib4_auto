/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.apply_fun
import Mathlib.algebra.ordered_ring
import Mathlib.algebra.big_operators.basic
import Mathlib.data.equiv.ring
import Mathlib.PostPort

universes u l u_1 

namespace Mathlib

/-!
# Star monoids and star rings

We introduce the basic algebraic notions of star monoids, and star rings.
Star algebras are introduced in `algebra.algebra.star`.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) 
where
  star : R → R

/--
A star operation (e.g. complex conjugate).
-/
def star {R : Type u} [has_star R] (r : R) : R :=
  has_star.star r

/--
Typeclass for a star operation with is involutive.
-/
class has_involutive_star (R : Type u) 
extends has_star R
where
  star_involutive : function.involutive has_star.star

@[simp] theorem star_star {R : Type u} [has_involutive_star R] (r : R) : star (star r) = r :=
  has_involutive_star.star_involutive r

theorem star_injective {R : Type u} [has_involutive_star R] : function.injective star :=
  function.involutive.injective has_involutive_star.star_involutive

/--
A *-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] 
extends has_involutive_star R
where
  star_mul : ∀ (r s : R), has_star.star (r * s) = has_star.star s * has_star.star r

@[simp] theorem star_mul {R : Type u} [monoid R] [star_monoid R] (r : R) (s : R) : star (r * s) = star s * star r :=
  star_monoid.star_mul r s

/-- `star` as an `mul_equiv` from `R` to `Rᵒᵖ` -/
@[simp] theorem star_mul_equiv_apply {R : Type u} [monoid R] [star_monoid R] (x : R) : coe_fn star_mul_equiv x = opposite.op (star x) :=
  Eq.refl (coe_fn star_mul_equiv x)

@[simp] theorem star_one (R : Type u) [monoid R] [star_monoid R] : star 1 = 1 := sorry

/--
A *-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a *-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] 
extends star_monoid R
where
  star_add : ∀ (r s : R), has_star.star (r + s) = has_star.star r + has_star.star s

@[simp] theorem star_add {R : Type u} [semiring R] [star_ring R] (r : R) (s : R) : star (r + s) = star r + star s :=
  star_ring.star_add r s

/-- `star` as an `add_equiv` -/
def star_add_equiv {R : Type u} [semiring R] [star_ring R] : R ≃+ R :=
  add_equiv.mk star (equiv.inv_fun (function.involutive.to_equiv star sorry)) sorry sorry star_add

@[simp] theorem star_zero (R : Type u) [semiring R] [star_ring R] : star 0 = 0 :=
  add_equiv.map_zero star_add_equiv

/-- `star` as an `ring_equiv` from `R` to `Rᵒᵖ` -/
@[simp] theorem star_ring_equiv_apply {R : Type u} [semiring R] [star_ring R] (x : R) : coe_fn star_ring_equiv x = opposite.op (star x) :=
  Eq.refl (coe_fn star_ring_equiv x)

@[simp] theorem star_sum {R : Type u} [semiring R] [star_ring R] {α : Type u_1} (s : finset α) (f : α → R) : star (finset.sum s fun (x : α) => f x) = finset.sum s fun (x : α) => star (f x) :=
  add_equiv.map_sum star_add_equiv (fun (x : α) => f x) s

@[simp] theorem star_neg {R : Type u} [ring R] [star_ring R] (r : R) : star (-r) = -star r :=
  add_equiv.map_neg star_add_equiv r

@[simp] theorem star_sub {R : Type u} [ring R] [star_ring R] (r : R) (s : R) : star (r - s) = star r - star s :=
  add_equiv.map_sub star_add_equiv r s

@[simp] theorem star_bit0 {R : Type u} [ring R] [star_ring R] (r : R) : star (bit0 r) = bit0 (star r) := sorry

@[simp] theorem star_bit1 {R : Type u} [ring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) := sorry

/--
Any commutative semiring admits the trivial *-structure.
-/
def star_ring_of_comm {R : Type u_1} [comm_semiring R] : star_ring R :=
  star_ring.mk sorry

@[simp] theorem star_id_of_comm {R : Type u_1} [comm_semiring R] {x : R} : star x = x :=
  rfl

