/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ring_quot
import Mathlib.linear_algebra.tensor_algebra
import Mathlib.linear_algebra.alternating
import Mathlib.group_theory.perm.sign
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Exterior Algebras

We construct the exterior algebra of a semimodule `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-semimodule `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ι_multi` is the `alternating_map` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `0`.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

namespace exterior_algebra


/-- `rel` relates each `ι m * ι m`, for `m : M`, with `0`.

The exterior algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel (R : Type u_1) [comm_semiring R] (M : Type u_2) [add_comm_monoid M] [semimodule R M] :
    tensor_algebra R M → tensor_algebra R M → Prop
    where
| of : ∀ (m : M), rel R M (coe_fn (tensor_algebra.ι R) m * coe_fn (tensor_algebra.ι R) m) 0

end exterior_algebra


/--
The exterior algebra of an `R`-semimodule `M`.
-/
def exterior_algebra (R : Type u_1) [comm_semiring R] (M : Type u_2) [add_comm_monoid M]
    [semimodule R M] :=
  ring_quot sorry

namespace exterior_algebra


-- typeclass resolution times out here, so we give it a hand

protected instance ring {M : Type u_2} [add_comm_monoid M] {S : Type u_1} [comm_ring S]
    [semimodule S M] : ring (exterior_algebra S M) :=
  let i : ring (tensor_algebra S M) := infer_instance;
  ring_quot.ring (rel S M)

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M] :
    linear_map R M (exterior_algebra R M) :=
  linear_map.comp (alg_hom.to_linear_map (ring_quot.mk_alg_hom R (rel R M))) (tensor_algebra.ι R)

/-- As well as being linear, `ι m` squares to zero -/
@[simp] theorem ι_square_zero {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] (m : M) : coe_fn (ι R) m * coe_fn (ι R) m = 0 :=
  sorry

@[simp] theorem comp_ι_square_zero {R : Type u_1} [comm_semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] {A : Type u_3} [semiring A] [algebra R A]
    (g : alg_hom R (exterior_algebra R M) A) (m : M) :
    coe_fn g (coe_fn (ι R) m) * coe_fn g (coe_fn (ι R) m) = 0 :=
  sorry

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
def lift (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {A : Type u_3} [semiring A] [algebra R A] :
    (Subtype fun (f : linear_map R M A) => ∀ (m : M), coe_fn f m * coe_fn f m = 0) ≃
        alg_hom R (exterior_algebra R M) A :=
  equiv.mk
    (fun (f : Subtype fun (f : linear_map R M A) => ∀ (m : M), coe_fn f m * coe_fn f m = 0) =>
      coe_fn (ring_quot.lift_alg_hom R)
        { val := coe_fn (tensor_algebra.lift R) ↑f, property := sorry })
    (fun (F : alg_hom R (exterior_algebra R M) A) =>
      { val := linear_map.comp (alg_hom.to_linear_map F) (ι R), property := sorry })
    sorry sorry

@[simp] theorem ι_comp_lift (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A] (f : linear_map R M A)
    (cond : ∀ (m : M), coe_fn f m * coe_fn f m = 0) :
    linear_map.comp (alg_hom.to_linear_map (coe_fn (lift R) { val := f, property := cond })) (ι R) =
        f :=
  iff.mp subtype.mk_eq_mk (equiv.symm_apply_apply (lift R) { val := f, property := cond })

@[simp] theorem lift_ι_apply (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A] (f : linear_map R M A)
    (cond : ∀ (m : M), coe_fn f m * coe_fn f m = 0) (x : M) :
    coe_fn (coe_fn (lift R) { val := f, property := cond }) (coe_fn (ι R) x) = coe_fn f x :=
  iff.mp linear_map.ext_iff (ι_comp_lift R f cond) x

@[simp] theorem lift_unique (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A] (f : linear_map R M A)
    (cond : ∀ (m : M), coe_fn f m * coe_fn f m = 0) (g : alg_hom R (exterior_algebra R M) A) :
    linear_map.comp (alg_hom.to_linear_map g) (ι R) = f ↔
        g = coe_fn (lift R) { val := f, property := cond } :=
  sorry

-- Marking `exterior_algebra` irreducible makes our `ring` instances inaccessible.

-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241

-- For now, we avoid this by not marking it irreducible.

@[simp] theorem lift_comp_ι {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A]
    (g : alg_hom R (exterior_algebra R M) A) :
    coe_fn (lift R)
          { val := linear_map.comp (alg_hom.to_linear_map g) (ι R),
            property := comp_ι_square_zero g } =
        g :=
  sorry

/-- See note [partially-applied ext lemmas]. -/
theorem hom_ext {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {A : Type u_3} [semiring A] [algebra R A] {f : alg_hom R (exterior_algebra R M) A}
    {g : alg_hom R (exterior_algebra R M) A}
    (h :
      linear_map.comp (alg_hom.to_linear_map f) (ι R) =
        linear_map.comp (alg_hom.to_linear_map g) (ι R)) :
    f = g :=
  sorry

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] : alg_hom R (exterior_algebra R M) R :=
  coe_fn (lift R) { val := 0, property := sorry }

theorem algebra_map_left_inverse {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] :
    function.left_inverse ⇑algebra_map_inv ⇑(algebra_map R (exterior_algebra R M)) :=
  sorry

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ι_inv {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M] :
    linear_map R (exterior_algebra R M) M :=
  linear_map.comp (triv_sq_zero_ext.snd_hom R M)
    (alg_hom.to_linear_map
      (coe_fn (lift R) { val := triv_sq_zero_ext.inr_hom R M, property := sorry }))

theorem ι_left_inverse {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] : function.left_inverse ⇑ι_inv ⇑(ι R) :=
  sorry

@[simp] theorem ι_add_mul_swap {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] (x : M) (y : M) :
    coe_fn (ι R) x * coe_fn (ι R) y + coe_fn (ι R) y * coe_fn (ι R) x = 0 :=
  sorry

theorem ι_mul_prod_list {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {n : ℕ} (f : fin n → M) (i : fin n) :
    coe_fn (ι R) (f i) * list.prod (list.of_fn fun (i : fin n) => coe_fn (ι R) (f i)) = 0 :=
  sorry

/-- The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `multilinear_map.mk_pi_algebra_fin` -/
def ι_multi (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    (n : ℕ) : alternating_map R M (exterior_algebra R M) (fin n) :=
  let F : multilinear_map R (fun (i : fin n) => M) (exterior_algebra R M) :=
    multilinear_map.comp_linear_map (multilinear_map.mk_pi_algebra_fin R n (exterior_algebra R M))
      fun (i : fin n) => ι R;
  alternating_map.mk ⇑F sorry sorry sorry

theorem ι_multi_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {n : ℕ} (v : fin n → M) :
    coe_fn (ι_multi R n) v = list.prod (list.of_fn fun (i : fin n) => coe_fn (ι R) (v i)) :=
  rfl

end exterior_algebra


namespace tensor_algebra


/-- The canonical image of the `tensor_algebra` in the `exterior_algebra`, which maps
`tensor_algebra.ι R x` to `exterior_algebra.ι R x`. -/
def to_exterior {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] : alg_hom R (tensor_algebra R M) (exterior_algebra R M) :=
  coe_fn (lift R) (exterior_algebra.ι R)

@[simp] theorem to_exterior_ι {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] (m : M) :
    coe_fn to_exterior (coe_fn (ι R) m) = coe_fn (exterior_algebra.ι R) m :=
  sorry

end Mathlib