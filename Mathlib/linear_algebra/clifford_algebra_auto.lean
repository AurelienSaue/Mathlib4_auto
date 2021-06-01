/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ring_quot
import Mathlib.linear_algebra.tensor_algebra
import Mathlib.linear_algebra.exterior_algebra
import Mathlib.linear_algebra.quadratic_form
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic_form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic_form `Q` is denoted as
`clifford_algebra Q`.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebra_map _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism, which is denoted `clifford_algebra.lift Q f cond`.

The canonical linear map `M → clifford_algebra Q` is denoted `clifford_algebra.ι Q`.

## Theorems

The main theorems proved ensure that `clifford_algebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

Additionally, when `Q = 0` an `alg_equiv` to the `exterior_algebra` is provided as `as_exterior`.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `clifford_algebra.rel Q` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `linear_algebra/exterior_algebra.lean`.
-/

namespace clifford_algebra


/-- `rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The Clifford algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M]
    (Q : quadratic_form R M) : tensor_algebra R M → tensor_algebra R M → Prop
    where
| of :
    ∀ (m : M),
      rel Q (coe_fn (tensor_algebra.ι R) m * coe_fn (tensor_algebra.ι R) m)
        (coe_fn (algebra_map R (tensor_algebra R M)) (coe_fn Q m))

end clifford_algebra


/--
The Clifford algebra of an `R`-module `M` equipped with a quadratic_form `Q`.
-/
def clifford_algebra {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M]
    (Q : quadratic_form R M) :=
  ring_quot sorry

namespace clifford_algebra


/--
The canonical linear map `M →ₗ[R] clifford_algebra Q`.
-/
def ι {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M]
    (Q : quadratic_form R M) : linear_map R M (clifford_algebra Q) :=
  linear_map.comp (alg_hom.to_linear_map (ring_quot.mk_alg_hom R (rel Q))) (tensor_algebra.ι R)

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp] theorem ι_square_scalar {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] (Q : quadratic_form R M) (m : M) :
    coe_fn (ι Q) m * coe_fn (ι Q) m = coe_fn (algebra_map R (clifford_algebra Q)) (coe_fn Q m) :=
  sorry

@[simp] theorem comp_ι_square_scalar {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] {Q : quadratic_form R M} {A : Type u_3} [semiring A] [algebra R A]
    (g : alg_hom R (clifford_algebra Q) A) (m : M) :
    coe_fn g (coe_fn (ι Q) m) * coe_fn g (coe_fn (ι Q) m) = coe_fn (algebra_map R A) (coe_fn Q m) :=
  sorry

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `clifford_algebra Q` to `A`.
-/
@[simp] theorem lift_symm_apply {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] (Q : quadratic_form R M) {A : Type u_3} [semiring A] [algebra R A]
    (F : alg_hom R (clifford_algebra Q) A) :
    coe_fn (equiv.symm (lift Q)) F =
        { val := linear_map.comp (alg_hom.to_linear_map F) (ι Q), property := lift._proof_2 Q F } :=
  Eq.refl (coe_fn (equiv.symm (lift Q)) F)

@[simp] theorem ι_comp_lift {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] {Q : quadratic_form R M} {A : Type u_3} [semiring A] [algebra R A]
    (f : linear_map R M A)
    (cond : ∀ (m : M), coe_fn f m * coe_fn f m = coe_fn (algebra_map R A) (coe_fn Q m)) :
    linear_map.comp (alg_hom.to_linear_map (coe_fn (lift Q) { val := f, property := cond })) (ι Q) =
        f :=
  iff.mp subtype.mk_eq_mk (equiv.symm_apply_apply (lift Q) { val := f, property := cond })

@[simp] theorem lift_ι_apply {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] {Q : quadratic_form R M} {A : Type u_3} [semiring A] [algebra R A]
    (f : linear_map R M A)
    (cond : ∀ (m : M), coe_fn f m * coe_fn f m = coe_fn (algebra_map R A) (coe_fn Q m)) (x : M) :
    coe_fn (coe_fn (lift Q) { val := f, property := cond }) (coe_fn (ι Q) x) = coe_fn f x :=
  iff.mp linear_map.ext_iff (ι_comp_lift f cond) x

@[simp] theorem lift_unique {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] {Q : quadratic_form R M} {A : Type u_3} [semiring A] [algebra R A]
    (f : linear_map R M A)
    (cond : ∀ (m : M), coe_fn f m * coe_fn f m = coe_fn (algebra_map R A) (coe_fn Q m))
    (g : alg_hom R (clifford_algebra Q) A) :
    linear_map.comp (alg_hom.to_linear_map g) (ι Q) = f ↔
        g = coe_fn (lift Q) { val := f, property := cond } :=
  sorry

@[simp] theorem lift_comp_ι {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] {Q : quadratic_form R M} {A : Type u_3} [semiring A] [algebra R A]
    (g : alg_hom R (clifford_algebra Q) A) :
    coe_fn (lift Q)
          { val := linear_map.comp (alg_hom.to_linear_map g) (ι Q),
            property := comp_ι_square_scalar g } =
        g :=
  sorry

/-- See note [partially-applied ext lemmas]. -/
theorem hom_ext {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M]
    {Q : quadratic_form R M} {A : Type u_3} [semiring A] [algebra R A]
    {f : alg_hom R (clifford_algebra Q) A} {g : alg_hom R (clifford_algebra Q) A} :
    linear_map.comp (alg_hom.to_linear_map f) (ι Q) =
          linear_map.comp (alg_hom.to_linear_map g) (ι Q) →
        f = g :=
  sorry

/-- A Clifford algebra with a zero quadratic form is isomorphic to an `exterior_algebra` -/
def as_exterior {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] :
    alg_equiv R (clifford_algebra 0) (exterior_algebra R M) :=
  alg_equiv.of_alg_hom (coe_fn (lift 0) { val := exterior_algebra.ι R, property := sorry })
    (coe_fn (exterior_algebra.lift R) { val := ι 0, property := sorry }) sorry sorry

end clifford_algebra


namespace tensor_algebra


/-- The canonical image of the `tensor_algebra` in the `clifford_algebra`, which maps
`tensor_algebra.ι R x` to `clifford_algebra.ι Q x`. -/
def to_clifford {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M]
    {Q : quadratic_form R M} : alg_hom R (tensor_algebra R M) (clifford_algebra Q) :=
  coe_fn (lift R) (clifford_algebra.ι Q)

@[simp] theorem to_clifford_ι {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M]
    [module R M] {Q : quadratic_form R M} (m : M) :
    coe_fn to_clifford (coe_fn (ι R) m) = coe_fn (clifford_algebra.ι Q) m :=
  sorry

end Mathlib