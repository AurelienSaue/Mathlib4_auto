/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finsupp
import Mathlib.linear_algebra.direct_sum.tensor_product
import Mathlib.PostPort

universes u u_1 v u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Results on direct sums and finitely supported functions.

1. The linear equivalence between finitely supported functions `ι →₀ M` and
the direct sum of copies of `M` indexed by `ι`.

2. The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N).
-/

/-- The finitely supported functions ι →₀ M are in linear equivalence with the direct sum of
copies of M indexed by ι. -/
def finsupp_lequiv_direct_sum (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] (ι : Type u_1) [DecidableEq ι] : linear_equiv R (ι →₀ M) (direct_sum ι fun (i : ι) => M) :=
  linear_equiv.of_linear
    (coe_fn finsupp.lsum
      ((fun (this : ι → linear_map R M (direct_sum ι fun (i : ι) => M)) => this) (direct_sum.lof R ι fun (i : ι) => M)))
    (direct_sum.to_module R ι (ι →₀ M) finsupp.lsingle) sorry sorry

@[simp] theorem finsupp_lequiv_direct_sum_single (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] (ι : Type u_1) [DecidableEq ι] (i : ι) (m : M) : coe_fn (finsupp_lequiv_direct_sum R M ι) (finsupp.single i m) = coe_fn (direct_sum.lof R ι (fun (i : ι) => M) i) m :=
  finsupp.sum_single_index
    (linear_map.map_zero
      ((fun (this : ι → linear_map R M (direct_sum ι fun (i : ι) => M)) => this) (direct_sum.lof R ι fun (i : ι) => M) i))

@[simp] theorem finsupp_lequiv_direct_sum_symm_lof (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] (ι : Type u_1) [DecidableEq ι] (i : ι) (m : M) : coe_fn (linear_equiv.symm (finsupp_lequiv_direct_sum R M ι)) (coe_fn (direct_sum.lof R ι (fun (i : ι) => M) i) m) =
  finsupp.single i m :=
  direct_sum.to_module_lof R i m

/-- The tensor product of ι →₀ M and κ →₀ N is linearly equivalent to (ι × κ) →₀ (M ⊗ N). -/
def finsupp_tensor_finsupp (R : Type u_1) (M : Type u_2) (N : Type u_3) (ι : Type u_4) (κ : Type u_5) [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] : linear_equiv R (tensor_product R (ι →₀ M) (κ →₀ N)) (ι × κ →₀ tensor_product R M N) :=
  linear_equiv.trans (tensor_product.congr (finsupp_lequiv_direct_sum R M ι) (finsupp_lequiv_direct_sum R N κ))
    (linear_equiv.trans (tensor_product.direct_sum R ι κ (fun (i : ι) => M) fun (i : κ) => N)
      (linear_equiv.symm (finsupp_lequiv_direct_sum R (tensor_product R M N) (ι × κ))))

@[simp] theorem finsupp_tensor_finsupp_single (R : Type u_1) (M : Type u_2) (N : Type u_3) (ι : Type u_4) (κ : Type u_5) [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] (i : ι) (m : M) (k : κ) (n : N) : coe_fn (finsupp_tensor_finsupp R M N ι κ) (tensor_product.tmul R (finsupp.single i m) (finsupp.single k n)) =
  finsupp.single (i, k) (tensor_product.tmul R m n) := sorry

@[simp] theorem finsupp_tensor_finsupp_symm_single (R : Type u_1) (M : Type u_2) (N : Type u_3) (ι : Type u_4) (κ : Type u_5) [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] (i : ι × κ) (m : M) (n : N) : coe_fn (linear_equiv.symm (finsupp_tensor_finsupp R M N ι κ)) (finsupp.single i (tensor_product.tmul R m n)) =
  tensor_product.tmul R (finsupp.single (prod.fst i) m) (finsupp.single (prod.snd i) n) := sorry

