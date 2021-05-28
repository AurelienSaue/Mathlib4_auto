/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.lie.basic
import Mathlib.ring_theory.algebra_tower
import PostPort

universes u_1 u_2 u_3 l u_4 

namespace Mathlib

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Notation

The notation `⁅D1, D2⁆` is used for the commutator of two derivations.

TODO: this file is just a stub to go on with some PRs in the geometry section. It only
implements the definition of derivations in commutative algebra. This will soon change: as soon
as bimodules will be there in mathlib I will change this file to take into account the
non-commutative case. Any development on the theory of derivations is discouraged until the
definitive definition of derivation will be implemented.
-/

/-- `D : derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`
equality.
TODO: update this when bimodules are defined. -/
structure derivation (R : Type u_1) (A : Type u_2) [comm_semiring R] [comm_semiring A] [algebra R A] (M : Type u_3) [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] 
extends linear_map R A M
where
  leibniz' : ∀ (a b : A),
  linear_map.to_fun _to_linear_map (a * b) =
    a • linear_map.to_fun _to_linear_map b + b • linear_map.to_fun _to_linear_map a

namespace derivation


protected instance has_coe_to_fun {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : has_coe_to_fun (derivation R A M) :=
  has_coe_to_fun.mk (fun (D : derivation R A M) => A → M)
    fun (D : derivation R A M) => linear_map.to_fun (derivation.to_linear_map D)

protected instance has_coe_to_linear_map {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : has_coe (derivation R A M) (linear_map R A M) :=
  has_coe.mk fun (D : derivation R A M) => derivation.to_linear_map D

@[simp] theorem to_fun_eq_coe {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) : linear_map.to_fun (derivation.to_linear_map D) = ⇑D :=
  rfl

@[simp] theorem coe_fn_coe {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (f : derivation R A M) : ⇑↑f = ⇑f :=
  rfl

theorem coe_injective {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] {D1 : derivation R A M} {D2 : derivation R A M} (H : ⇑D1 = ⇑D2) : D1 = D2 := sorry

theorem ext {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] {D1 : derivation R A M} {D2 : derivation R A M} (H : ∀ (a : A), coe_fn D1 a = coe_fn D2 a) : D1 = D2 :=
  coe_injective (funext H)

@[simp] theorem map_add {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (a : A) (b : A) : coe_fn D (a + b) = coe_fn D a + coe_fn D b :=
  is_add_hom.map_add (⇑D) a b

@[simp] theorem map_zero {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) : coe_fn D 0 = 0 :=
  is_add_monoid_hom.map_zero ⇑D

@[simp] theorem map_smul {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (r : R) (a : A) : coe_fn D (r • a) = r • coe_fn D a :=
  linear_map.map_smul (↑D) r a

@[simp] theorem leibniz {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (a : A) (b : A) : coe_fn D (a * b) = a • coe_fn D b + b • coe_fn D a :=
  derivation.leibniz' D a b

@[simp] theorem map_one_eq_zero {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) : coe_fn D 1 = 0 := sorry

@[simp] theorem map_algebra_map {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (r : R) : coe_fn D (coe_fn (algebra_map R A) r) = 0 := sorry

protected instance has_zero {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : HasZero (derivation R A M) :=
  { zero := mk 0 sorry }

protected instance inhabited {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : Inhabited (derivation R A M) :=
  { default := 0 }

protected instance add_comm_monoid {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : add_comm_monoid (derivation R A M) :=
  add_comm_monoid.mk (fun (D1 D2 : derivation R A M) => mk (↑D1 + ↑D2) sorry) sorry 0 sorry sorry sorry

@[simp] theorem add_apply {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] {D1 : derivation R A M} {D2 : derivation R A M} (a : A) : coe_fn (D1 + D2) a = coe_fn D1 a + coe_fn D2 a :=
  rfl

protected instance derivation.Rsemimodule {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : semimodule R (derivation R A M) :=
  semimodule.mk sorry sorry

@[simp] theorem smul_to_linear_map_coe {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (r : R) : ↑(r • D) = r • ↑D :=
  rfl

@[simp] theorem Rsmul_apply {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (r : R) (a : A) : coe_fn (r • D) a = r • coe_fn D a :=
  rfl

protected instance semimodule {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : semimodule A (derivation R A M) :=
  semimodule.mk sorry sorry

@[simp] theorem smul_apply {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (D : derivation R A M) (a : A) (b : A) : coe_fn (a • D) b = a • coe_fn D b :=
  rfl

protected instance is_scalar_tower {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : is_scalar_tower R A (derivation R A M) :=
  is_scalar_tower.mk fun (x : R) (y : A) (z : derivation R A M) => ext fun (a : A) => smul_assoc x y (coe_fn (↑z) a)

@[simp] theorem map_neg {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] {M : Type u_3} [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M] (D : derivation R A M) (a : A) : coe_fn D (-a) = -coe_fn D a :=
  linear_map.map_neg (↑D) a

@[simp] theorem map_sub {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] {M : Type u_3} [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M] (D : derivation R A M) (a : A) (b : A) : coe_fn D (a - b) = coe_fn D a - coe_fn D b :=
  linear_map.map_sub (↑D) a b

protected instance add_comm_group {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] {M : Type u_3} [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M] : add_comm_group (derivation R A M) :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry
    (fun (D : derivation R A M) => mk (-↑D) sorry) (fun (D1 D2 : derivation R A M) => mk (↑D1 - ↑D2) sorry) sorry sorry

@[simp] theorem sub_apply {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] {M : Type u_3} [add_comm_group M] [module A M] [module R M] [is_scalar_tower R A M] {D1 : derivation R A M} {D2 : derivation R A M} (a : A) : coe_fn (D1 - D2) a = coe_fn D1 a - coe_fn D2 a :=
  rfl

/-! # Lie structures -/

/-- The commutator of derivations is again a derivation. -/
def commutator {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] (D1 : derivation R A A) (D2 : derivation R A A) : derivation R A A :=
  mk (linear_map.mk (linear_map.to_fun (has_bracket.bracket ↑D1 ↑D2)) sorry sorry) sorry

protected instance has_bracket {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] : has_bracket (derivation R A A) (derivation R A A) :=
  has_bracket.mk commutator

@[simp] theorem commutator_coe_linear_map {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] {D1 : derivation R A A} {D2 : derivation R A A} : ↑(has_bracket.bracket D1 D2) = has_bracket.bracket ↑D1 ↑D2 :=
  rfl

theorem commutator_apply {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] {D1 : derivation R A A} {D2 : derivation R A A} (a : A) : coe_fn (has_bracket.bracket D1 D2) a = coe_fn D1 (coe_fn D2 a) - coe_fn D2 (coe_fn D1 a) :=
  rfl

protected instance lie_ring {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] : lie_ring (derivation R A A) :=
  lie_ring.mk sorry sorry sorry sorry

protected instance lie_algebra {R : Type u_1} [comm_ring R] {A : Type u_2} [comm_ring A] [algebra R A] : lie_algebra R (derivation R A A) :=
  lie_algebra.mk sorry

end derivation


namespace linear_map


/-- The composition of a linear map and a derivation is a derivation. -/
def comp_der {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] {N : Type u_4} [add_cancel_comm_monoid N] [semimodule A N] [semimodule R N] [is_scalar_tower R A M] [is_scalar_tower R A N] (f : linear_map A M N) (D : derivation R A M) : derivation R A N :=
  derivation.mk (mk (fun (a : A) => coe_fn f (coe_fn D a)) sorry sorry) sorry

@[simp] theorem comp_der_apply {R : Type u_1} [comm_semiring R] {A : Type u_2} [comm_semiring A] [algebra R A] {M : Type u_3} [add_cancel_comm_monoid M] [semimodule A M] [semimodule R M] {N : Type u_4} [add_cancel_comm_monoid N] [semimodule A N] [semimodule R N] [is_scalar_tower R A M] [is_scalar_tower R A N] (f : linear_map A M N) (D : derivation R A M) (a : A) : coe_fn (comp_der f D) a = coe_fn f (coe_fn D a) :=
  rfl

