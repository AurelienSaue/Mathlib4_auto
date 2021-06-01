/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Topaz.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.free_algebra
import Mathlib.algebra.ring_quot
import Mathlib.algebra.triv_sq_zero_ext
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Tensor Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the tensor algebra of `M`.
This is the free `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

1. `tensor_algebra R M` is the tensor algebra itself. It is endowed with an R-algebra structure.
2. `tensor_algebra.ι R` is the canonical R-linear map `M → tensor_algebra R M`.
3. Given a linear map `f : M → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `tensor_algebra R M → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : tensor_algebra R M → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.

## Implementation details

As noted above, the tensor algebra of `M` is constructed as the free `R`-algebra generated by `M`,
modulo the additional relations making the inclusion of `M` into an `R`-linear map.
-/

namespace tensor_algebra


/--
An inductively defined relation on `pre R M` used to force the initial algebra structure on
the associated quotient.
-/
-- force `ι` to be linear

inductive rel (R : Type u_1) [comm_semiring R] (M : Type u_2) [add_comm_monoid M] [semimodule R M] :
    free_algebra R M → free_algebra R M → Prop
    where
| add : ∀ {a b : M}, rel R M (free_algebra.ι R (a + b)) (free_algebra.ι R a + free_algebra.ι R b)
| smul :
    ∀ {r : R} {a : M},
      rel R M (free_algebra.ι R (r • a))
        (coe_fn (algebra_map R (free_algebra R M)) r * free_algebra.ι R a)

end tensor_algebra


/--
The tensor algebra of the module `M` over the commutative semiring `R`.
-/
def tensor_algebra (R : Type u_1) [comm_semiring R] (M : Type u_2) [add_comm_monoid M]
    [semimodule R M] :=
  ring_quot sorry

namespace tensor_algebra


protected instance ring (M : Type u_2) [add_comm_monoid M] {S : Type u_1} [comm_ring S]
    [semimodule S M] : ring (tensor_algebra S M) :=
  ring_quot.ring (rel S M)

/--
The canonical linear map `M →ₗ[R] tensor_algebra R M`.
-/
def ι (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M] :
    linear_map R M (tensor_algebra R M) :=
  linear_map.mk (fun (m : M) => coe_fn (ring_quot.mk_alg_hom R (rel R M)) (free_algebra.ι R m))
    sorry sorry

theorem ring_quot_mk_alg_hom_free_algebra_ι_eq_ι (R : Type u_1) [comm_semiring R] {M : Type u_2}
    [add_comm_monoid M] [semimodule R M] (m : M) :
    coe_fn (ring_quot.mk_alg_hom R (rel R M)) (free_algebra.ι R m) = coe_fn (ι R) m :=
  rfl

/--
Given a linear map `f : M → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `tensor_algebra R M → A`.
-/
def lift (R : Type u_1) [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {A : Type u_3} [semiring A] [algebra R A] :
    linear_map R M A ≃ alg_hom R (tensor_algebra R M) A :=
  equiv.mk
    (⇑(ring_quot.lift_alg_hom R) ∘
      fun (f : linear_map R M A) => { val := coe_fn (free_algebra.lift R) ⇑f, property := sorry })
    (fun (F : alg_hom R (tensor_algebra R M) A) => linear_map.comp (alg_hom.to_linear_map F) (ι R))
    sorry sorry

@[simp] theorem ι_comp_lift {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A] (f : linear_map R M A) :
    linear_map.comp (alg_hom.to_linear_map (coe_fn (lift R) f)) (ι R) = f :=
  equiv.symm_apply_apply (lift R) f

@[simp] theorem lift_ι_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A] (f : linear_map R M A) (x : M) :
    coe_fn (coe_fn (lift R) f) (coe_fn (ι R) x) = coe_fn f x :=
  id (Eq.refl (coe_fn f x))

@[simp] theorem lift_unique {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A] (f : linear_map R M A)
    (g : alg_hom R (tensor_algebra R M) A) :
    linear_map.comp (alg_hom.to_linear_map g) (ι R) = f ↔ g = coe_fn (lift R) f :=
  equiv.symm_apply_eq (lift R)

-- Marking `tensor_algebra` irreducible makes `ring` instances inaccessible on quotients.

-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241

-- For now, we avoid this by not marking it irreducible.

@[simp] theorem lift_comp_ι {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] {A : Type u_3} [semiring A] [algebra R A]
    (g : alg_hom R (tensor_algebra R M) A) :
    coe_fn (lift R) (linear_map.comp (alg_hom.to_linear_map g) (ι R)) = g :=
  sorry

/-- See note [partially-applied ext lemmas]. -/
theorem hom_ext {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M]
    {A : Type u_3} [semiring A] [algebra R A] {f : alg_hom R (tensor_algebra R M) A}
    {g : alg_hom R (tensor_algebra R M) A}
    (w :
      linear_map.comp (alg_hom.to_linear_map f) (ι R) =
        linear_map.comp (alg_hom.to_linear_map g) (ι R)) :
    f = g :=
  sorry

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] : alg_hom R (tensor_algebra R M) R :=
  coe_fn (lift R) 0

theorem algebra_map_left_inverse {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] :
    function.left_inverse ⇑algebra_map_inv ⇑(algebra_map R (tensor_algebra R M)) :=
  sorry

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ι_inv {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M] :
    linear_map R (tensor_algebra R M) M :=
  linear_map.comp (triv_sq_zero_ext.snd_hom R M)
    (alg_hom.to_linear_map (coe_fn (lift R) (triv_sq_zero_ext.inr_hom R M)))

theorem ι_left_inverse {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] : function.left_inverse ⇑ι_inv ⇑(ι R) :=
  sorry

end tensor_algebra


namespace free_algebra


/-- The canonical image of the `free_algebra` in the `tensor_algebra`, which maps
`free_algebra.ι R x` to `tensor_algebra.ι R x`. -/
def to_tensor {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M] :
    alg_hom R (free_algebra R M) (tensor_algebra R M) :=
  coe_fn (lift R) ⇑(tensor_algebra.ι R)

@[simp] theorem to_tensor_ι {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M]
    [semimodule R M] (m : M) : coe_fn to_tensor (ι R m) = coe_fn (tensor_algebra.ι R) m :=
  sorry

end Mathlib