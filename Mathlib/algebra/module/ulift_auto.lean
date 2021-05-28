/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.basic
import Mathlib.algebra.ring.ulift
import PostPort

universes u v u_1 w 

namespace Mathlib

/-!
# `ulift` instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ulift.semimodule_equiv : ulift M ≃ₗ[R] M`.

-/

namespace ulift


protected instance has_scalar {R : Type u} {M : Type v} [has_scalar R M] : has_scalar (ulift R) M :=
  has_scalar.mk fun (s : ulift R) (x : M) => down s • x

@[simp] theorem smul_down {R : Type u} {M : Type v} [has_scalar R M] (s : ulift R) (x : M) : s • x = down s • x :=
  rfl

protected instance has_scalar' {R : Type u} {M : Type v} [has_scalar R M] : has_scalar R (ulift M) :=
  has_scalar.mk fun (s : R) (x : ulift M) => up (s • down x)

@[simp] theorem smul_down' {R : Type u} {M : Type v} [has_scalar R M] (s : R) (x : ulift M) : down (s • x) = s • down x :=
  rfl

protected instance is_scalar_tower {R : Type u} {M : Type v} {N : Type w} [has_scalar R M] [has_scalar M N] [has_scalar R N] [is_scalar_tower R M N] : is_scalar_tower (ulift R) M N :=
  is_scalar_tower.mk
    fun (x : ulift R) (y : M) (z : N) =>
      (fun (this : (down x • y) • z = down x • y • z) => this) (smul_assoc (down x) y z)

protected instance is_scalar_tower' {R : Type u} {M : Type v} {N : Type w} [has_scalar R M] [has_scalar M N] [has_scalar R N] [is_scalar_tower R M N] : is_scalar_tower R (ulift M) N :=
  is_scalar_tower.mk
    fun (x : R) (y : ulift M) (z : N) =>
      (fun (this : (x • down y) • z = x • down y • z) => this) (smul_assoc x (down y) z)

protected instance is_scalar_tower'' {R : Type u} {M : Type v} {N : Type w} [has_scalar R M] [has_scalar M N] [has_scalar R N] [is_scalar_tower R M N] : is_scalar_tower R M (ulift N) :=
  is_scalar_tower.mk
    fun (x : R) (y : M) (z : ulift N) =>
      (fun (this : up ((x • y) • down z) = up (x • y • down z)) => this)
        (eq.mpr (id (Eq._oldrec (Eq.refl (up ((x • y) • down z) = up (x • y • down z))) (smul_assoc x y (down z))))
          (Eq.refl (up (x • y • down z))))

protected instance mul_action {R : Type u} {M : Type v} [monoid R] [mul_action R M] : mul_action (ulift R) M :=
  mul_action.mk sorry sorry

protected instance mul_action' {R : Type u} {M : Type v} [monoid R] [mul_action R M] : mul_action R (ulift M) :=
  mul_action.mk sorry sorry

protected instance distrib_mul_action {R : Type u} {M : Type v} [monoid R] [add_monoid M] [distrib_mul_action R M] : distrib_mul_action (ulift R) M :=
  distrib_mul_action.mk sorry sorry

protected instance distrib_mul_action' {R : Type u} {M : Type v} [monoid R] [add_monoid M] [distrib_mul_action R M] : distrib_mul_action R (ulift M) :=
  distrib_mul_action.mk sorry sorry

protected instance semimodule {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule (ulift R) M :=
  semimodule.mk sorry sorry

protected instance semimodule' {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule R (ulift M) :=
  semimodule.mk sorry sorry

/--
The `R`-linear equivalence between `ulift M` and `M`.
-/
def semimodule_equiv {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : linear_equiv R (ulift M) M :=
  linear_equiv.mk down sorry sorry up sorry sorry

