/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.group_action.group
import Mathlib.data.equiv.ring
import Mathlib.deprecated.subring
import Mathlib.PostPort

universes u v l u_1 

namespace Mathlib

/-!
# Group action on rings

This file defines the typeclass of monoid acting on semirings `mul_semiring_action M R`,
and the corresponding typeclass of invariant subrings.

Note that `algebra` does not satisfy the axioms of `mul_semiring_action`.

## Implementation notes

There is no separate typeclass for group acting on rings, group acting on fields, etc.
They are all grouped under `mul_semiring_action`.

## Tags

group action, invariant subring

-/

/-- Typeclass for multiplicative actions by monoids on semirings. -/
class mul_semiring_action (M : Type u) [monoid M] (R : Type v) [semiring R] 
extends distrib_mul_action M R
where
  smul_one : ∀ (g : M), g • 1 = 1
  smul_mul : ∀ (g : M) (x y : R), g • (x * y) = g • x * g • y

/-- Typeclass for faithful multiplicative actions by monoids on semirings. -/
class faithful_mul_semiring_action (M : Type u) [monoid M] (R : Type v) [semiring R] 
extends mul_semiring_action M R
where
  eq_of_smul_eq_smul' : ∀ {m₁ m₂ : M}, (∀ (r : R), m₁ • r = m₂ • r) → m₁ = m₂

@[simp] theorem smul_mul' {M : Type u} [monoid M] {R : Type v} [semiring R] [mul_semiring_action M R] (g : M) (x : R) (y : R) : g • (x * y) = g • x * g • y :=
  mul_semiring_action.smul_mul g x y

theorem eq_of_smul_eq_smul {M : Type u} [monoid M] (R : Type v) [semiring R] [faithful_mul_semiring_action M R] {m₁ : M} {m₂ : M} : (∀ (r : R), m₁ • r = m₂ • r) → m₁ = m₂ :=
  faithful_mul_semiring_action.eq_of_smul_eq_smul'

/-- Each element of the monoid defines a additive monoid homomorphism. -/
def distrib_mul_action.to_add_monoid_hom (M : Type u) [monoid M] (A : Type v) [add_monoid A] [distrib_mul_action M A] (x : M) : A →+ A :=
  add_monoid_hom.mk (has_scalar.smul x) (smul_zero x) (smul_add x)

/-- Each element of the group defines an additive monoid isomorphism. -/
def distrib_mul_action.to_add_equiv (G : Type u) [group G] (A : Type v) [add_monoid A] [distrib_mul_action G A] (x : G) : A ≃+ A :=
  add_equiv.mk (add_monoid_hom.to_fun (distrib_mul_action.to_add_monoid_hom G A x))
    (equiv.inv_fun (coe_fn (mul_action.to_perm G A) x)) sorry sorry sorry

/-- Each element of the group defines an additive monoid homomorphism. -/
def distrib_mul_action.hom_add_monoid_hom (M : Type u) [monoid M] (A : Type v) [add_monoid A] [distrib_mul_action M A] : M →* add_monoid.End A :=
  monoid_hom.mk (distrib_mul_action.to_add_monoid_hom M A) sorry sorry

/-- Each element of the monoid defines a semiring homomorphism. -/
def mul_semiring_action.to_semiring_hom (M : Type u) [monoid M] (R : Type v) [semiring R] [mul_semiring_action M R] (x : M) : R →+* R :=
  ring_hom.mk (add_monoid_hom.to_fun (distrib_mul_action.to_add_monoid_hom M R x)) (smul_one x) (smul_mul' x) sorry sorry

theorem injective_to_semiring_hom (M : Type u) [monoid M] (R : Type v) [semiring R] [faithful_mul_semiring_action M R] : function.injective (mul_semiring_action.to_semiring_hom M R) :=
  fun (m₁ m₂ : M) (h : mul_semiring_action.to_semiring_hom M R m₁ = mul_semiring_action.to_semiring_hom M R m₂) =>
    eq_of_smul_eq_smul R fun (r : R) => iff.mp ring_hom.ext_iff h r

/-- Each element of the group defines a semiring isomorphism. -/
def mul_semiring_action.to_semiring_equiv (G : Type u) [group G] (R : Type v) [semiring R] [mul_semiring_action G R] (x : G) : R ≃+* R :=
  ring_equiv.mk (add_equiv.to_fun (distrib_mul_action.to_add_equiv G R x))
    (add_equiv.inv_fun (distrib_mul_action.to_add_equiv G R x)) sorry sorry sorry sorry

theorem list.smul_prod (M : Type u) [monoid M] (R : Type v) [semiring R] [mul_semiring_action M R] (g : M) (L : List R) : g • list.prod L = list.prod (list.map (has_scalar.smul g) L) :=
  monoid_hom.map_list_prod (↑(mul_semiring_action.to_semiring_hom M R g)) L

theorem multiset.smul_prod (M : Type u) [monoid M] (S : Type v) [comm_semiring S] [mul_semiring_action M S] (g : M) (m : multiset S) : g • multiset.prod m = multiset.prod (multiset.map (has_scalar.smul g) m) :=
  monoid_hom.map_multiset_prod (↑(mul_semiring_action.to_semiring_hom M S g)) m

theorem smul_prod (M : Type u) [monoid M] (S : Type v) [comm_semiring S] [mul_semiring_action M S] (g : M) {ι : Type u_1} (f : ι → S) (s : finset ι) : (g • finset.prod s fun (i : ι) => f i) = finset.prod s fun (i : ι) => g • f i :=
  monoid_hom.map_prod (↑(mul_semiring_action.to_semiring_hom M S g)) f s

@[simp] theorem smul_inv {M : Type u} [monoid M] (F : Type v) [field F] [mul_semiring_action M F] (x : M) (m : F) : x • (m⁻¹) = (x • m⁻¹) :=
  ring_hom.map_inv (mul_semiring_action.to_semiring_hom M F x) m

@[simp] theorem smul_pow {M : Type u} [monoid M] {R : Type v} [semiring R] [mul_semiring_action M R] (x : M) (m : R) (n : ℕ) : x • m ^ n = (x • m) ^ n :=
  nat.rec_on n (smul_one x)
    fun (n : ℕ) (ih : x • m ^ n = (x • m) ^ n) => Eq.trans (smul_mul' x m (m ^ n)) (congr_arg (Mul.mul (x • m)) ih)

/-- A subring invariant under the action. -/
class is_invariant_subring (M : Type u) [monoid M] {R : Type v} [ring R] [mul_semiring_action M R] (S : set R) [is_subring S] 
where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S

protected instance is_invariant_subring.to_mul_semiring_action (M : Type u) [monoid M] {R : Type v} [ring R] [mul_semiring_action M R] (S : set R) [is_subring S] [is_invariant_subring M S] : mul_semiring_action M ↥S :=
  mul_semiring_action.mk sorry sorry

