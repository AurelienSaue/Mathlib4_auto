/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.dual
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

/-- The natural left-handed pairing between a module and its dual. -/
def contract_left (R : Type u) (M : Type v) [comm_ring R] [add_comm_group M] [module R M] :
    linear_map R (tensor_product R (module.dual R M) M) R :=
  linear_map.to_fun (tensor_product.uncurry R (module.dual R M) M R) linear_map.id

/-- The natural right-handed pairing between a module and its dual. -/
def contract_right (R : Type u) (M : Type v) [comm_ring R] [add_comm_group M] [module R M] :
    linear_map R (tensor_product R M (module.dual R M)) R :=
  linear_map.to_fun (tensor_product.uncurry R M (module.dual R M) R) (linear_map.flip linear_map.id)

/-- The natural map associating a linear map to the tensor product of two modules. -/
def dual_tensor_hom (R : Type u) (M : Type v) (N : Type v) [comm_ring R] [add_comm_group M]
    [add_comm_group N] [module R M] [module R N] :
    linear_map R (tensor_product R (module.dual R M) N) (linear_map R M N) :=
  let M' : Type (max v u) := module.dual R M;
  coe_fn (tensor_product.uncurry R M' N (linear_map R M N)) linear_map.smul_rightₗ

@[simp] theorem contract_left_apply {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
    [module R M] (f : module.dual R M) (m : M) :
    coe_fn (contract_left R M) (tensor_product.tmul R f m) = coe_fn f m :=
  tensor_product.uncurry_apply linear_map.id f m

@[simp] theorem contract_right_apply {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M]
    [module R M] (f : module.dual R M) (m : M) :
    coe_fn (contract_right R M) (tensor_product.tmul R m f) = coe_fn f m :=
  tensor_product.uncurry_apply (linear_map.flip linear_map.id) m f

@[simp] theorem dual_tensor_hom_apply {R : Type u} {M : Type v} {N : Type v} [comm_ring R]
    [add_comm_group M] [add_comm_group N] [module R M] [module R N] (f : module.dual R M) (m : M)
    (n : N) :
    coe_fn (coe_fn (dual_tensor_hom R M N) (tensor_product.tmul R f n)) m = coe_fn f m • n :=
  sorry

end Mathlib