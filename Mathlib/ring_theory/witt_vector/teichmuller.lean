/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Teichmüller lifts

This file defines `witt_vector.teichmuller`, a monoid hom `R →* 𝕎 R`, which embeds `r : R` as the
`0`-th component of a Witt vector whose other coefficients are `0`.

## Main declarations

- `witt_vector.teichmuller`: the Teichmuller map.
- `witt_vector.map_teichmuller`: `witt_vector.teichmuller` is a natural transformation.
- `witt_vector.ghost_component_teichmuller`:
  the `n`-th ghost component of `witt_vector.teichmuller p r` is `r ^ p ^ n`.

-/

namespace witt_vector


/--
The underlying function of the monoid hom `witt_vector.teichmuller`.
The `0`-th coefficient of `teichmuller_fun p r` is `r`, and all others are `0`.
-/
def teichmuller_fun (p : ℕ) {R : Type u_1} [comm_ring R] (r : R) : witt_vector p R :=
  sorry

/-!
## `teichmuller` is a monoid homomorphism

On ghost components, it is clear that `teichmuller_fun` is a monoid homomorphism.
But in general the ghost map is not injective.
We follow the same strategy as for proving that the the ring operations on `𝕎 R`
satisfy the ring axioms.

1. We first prove it for rings `R` where `p` is invertible,
   because then the ghost map is in fact an isomorphism.
2. After that, we derive the result for `mv_polynomial R ℤ`,
3. and from that we can prove the result for arbitrary `R`.
-/

/-- The Teichmüller lift of an element of `R` to `𝕎 R`.
The `0`-th coefficient of `teichmuller p r` is `r`, and all others are `0`.
This is a monoid homomorphism. -/
def teichmuller (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] : R →* witt_vector p R :=
  monoid_hom.mk (teichmuller_fun p) sorry sorry

@[simp] theorem teichmuller_coeff_zero (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (r : R) : coeff (coe_fn (teichmuller p) r) 0 = r :=
  rfl

@[simp] theorem teichmuller_coeff_pos (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (r : R) (n : ℕ) (hn : 0 < n) : coeff (coe_fn (teichmuller p) r) n = 0 := sorry

@[simp] theorem teichmuller_zero (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] : coe_fn (teichmuller p) 0 = 0 := sorry

/-- `teichmuller` is a natural transformation. -/
@[simp] theorem map_teichmuller (p : ℕ) {R : Type u_1} {S : Type u_2} [hp : fact (nat.prime p)] [comm_ring R] [comm_ring S] (f : R →+* S) (r : R) : coe_fn (map f) (coe_fn (teichmuller p) r) = coe_fn (teichmuller p) (coe_fn f r) :=
  map_teichmuller_fun p f r

/-- The `n`-th ghost component of `teichmuller p r` is `r ^ p ^ n`. -/
@[simp] theorem ghost_component_teichmuller (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (r : R) (n : ℕ) : coe_fn (ghost_component n) (coe_fn (teichmuller p) r) = r ^ p ^ n :=
  ghost_component_teichmuller_fun p r n

