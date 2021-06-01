/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.algebra_tower
import Mathlib.linear_algebra.matrix
import Mathlib.PostPort

universes u v w 

namespace Mathlib

/-!
# Tower of field extensions

In this file we prove the tower law for arbitrary extensions and finite extensions.
Suppose `L` is a field extension of `K` and `K` is a field extension of `F`.
Then `[L:F] = [L:K] [K:F]` where `[E₁:E₂]` means the `E₂`-dimension of `E₁`.

In fact we generalize it to vector spaces, where `L` is not necessarily a field,
but just a vector space over `K`.

## Implementation notes

We prove two versions, since there are two notions of dimensions: `vector_space.dim` which gives
the dimension of an arbitrary vector space as a cardinal, and `finite_dimensional.findim` which
gives the dimension of a finitely-dimensional vector space as a natural number.

## Tags

tower law

-/

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim' (F : Type u) (K : Type v) (A : Type w) [field F] [field K] [add_comm_group A]
    [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A] :
    cardinal.lift (vector_space.dim F K) * cardinal.lift (vector_space.dim K A) =
        cardinal.lift (vector_space.dim F A) :=
  sorry

/-- Tower law: if `A` is a `K`-vector space and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem dim_mul_dim (F : Type u) (K : Type v) (A : Type v) [field F] [field K] [add_comm_group A]
    [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A] :
    vector_space.dim F K * vector_space.dim K A = vector_space.dim F A :=
  sorry

namespace finite_dimensional


theorem trans (F : Type u) (K : Type v) (A : Type w) [field F] [field K] [add_comm_group A]
    [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A]
    [finite_dimensional F K] [finite_dimensional K A] : finite_dimensional F A :=
  sorry

theorem right (F : Type u) (K : Type v) (A : Type w) [field F] [field K] [add_comm_group A]
    [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A]
    [hf : finite_dimensional F A] : finite_dimensional K A :=
  sorry

/-- Tower law: if `A` is a `K`-algebra and `K` is a field extension of `F` then
`dim_F(A) = dim_F(K) * dim_K(A)`. -/
theorem findim_mul_findim (F : Type u) (K : Type v) (A : Type w) [field F] [field K]
    [add_comm_group A] [algebra F K] [vector_space K A] [vector_space F A] [is_scalar_tower F K A]
    [finite_dimensional F K] : findim F K * findim K A = findim F A :=
  sorry

protected instance linear_map (F : Type u) (V : Type v) (W : Type w) [field F] [add_comm_group V]
    [vector_space F V] [add_comm_group W] [vector_space F W] [finite_dimensional F V]
    [finite_dimensional F W] : finite_dimensional F (linear_map F V W) :=
  sorry

theorem findim_linear_map (F : Type u) (V : Type v) (W : Type w) [field F] [add_comm_group V]
    [vector_space F V] [add_comm_group W] [vector_space F W] [finite_dimensional F V]
    [finite_dimensional F W] : findim F (linear_map F V W) = findim F V * findim F W :=
  sorry

-- TODO: generalize by removing [finite_dimensional F K]

-- V = ⊕F,

-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = ⊕K

protected instance linear_map' (F : Type u) (K : Type v) (V : Type w) [field F] [field K]
    [algebra F K] [finite_dimensional F K] [add_comm_group V] [vector_space F V]
    [finite_dimensional F V] : finite_dimensional K (linear_map F V K) :=
  right F K (linear_map F V K)

theorem findim_linear_map' (F : Type u) (K : Type v) (V : Type w) [field F] [field K] [algebra F K]
    [finite_dimensional F K] [add_comm_group V] [vector_space F V] [finite_dimensional F V] :
    findim K (linear_map F V K) = findim F V :=
  iff.mp (nat.mul_right_inj ((fun (this : 0 < findim F K) => this) findim_pos))
    (Eq.trans (Eq.trans (findim_mul_findim F K (linear_map F V K)) (findim_linear_map F V K))
      (mul_comm (findim F V) (findim F K)))

end Mathlib