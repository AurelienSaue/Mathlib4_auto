/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Trivial Square-Zero Extension

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/

/--
"Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
def triv_sq_zero_ext (R : Type u) (M : Type v)  :=
  R × M

namespace triv_sq_zero_ext


/-- The canonical inclusion `R → triv_sq_zero_ext R M`. -/
def inl {R : Type u} {M : Type v} [HasZero M] (r : R) : triv_sq_zero_ext R M :=
  (r, 0)

/-- The canonical inclusion `M → triv_sq_zero_ext R M`. -/
def inr {R : Type u} {M : Type v} [HasZero R] (m : M) : triv_sq_zero_ext R M :=
  (0, m)

/-- The canonical projection `triv_sq_zero_ext R M → R`. -/
def fst {R : Type u} {M : Type v} (x : triv_sq_zero_ext R M) : R :=
  prod.fst x

/-- The canonical projection `triv_sq_zero_ext R M → M`. -/
def snd {R : Type u} {M : Type v} (x : triv_sq_zero_ext R M) : M :=
  prod.snd x

theorem ext {R : Type u} {M : Type v} {x : triv_sq_zero_ext R M} {y : triv_sq_zero_ext R M} (h1 : fst x = fst y) (h2 : snd x = snd y) : x = y :=
  prod.ext h1 h2

@[simp] theorem fst_inl {R : Type u} {M : Type v} [HasZero M] (r : R) : fst (inl r) = r :=
  rfl

@[simp] theorem snd_inl {R : Type u} {M : Type v} [HasZero M] (r : R) : snd (inl r) = 0 :=
  rfl

@[simp] theorem fst_inr {R : Type u} {M : Type v} [HasZero R] (m : M) : fst (inr m) = 0 :=
  rfl

@[simp] theorem snd_inr {R : Type u} {M : Type v} [HasZero R] (m : M) : snd (inr m) = m :=
  rfl

theorem inl_injective {R : Type u} {M : Type v} [HasZero M] : function.injective inl :=
  function.left_inverse.injective fst_inl

theorem inr_injective {R : Type u} {M : Type v} [HasZero R] : function.injective inr :=
  function.left_inverse.injective snd_inr

protected instance has_zero (R : Type u) (M : Type v) [HasZero R] [HasZero M] : HasZero (triv_sq_zero_ext R M) :=
  prod.has_zero

@[simp] theorem fst_zero (R : Type u) (M : Type v) [HasZero R] [HasZero M] : fst 0 = 0 :=
  rfl

@[simp] theorem snd_zero (R : Type u) (M : Type v) [HasZero R] [HasZero M] : snd 0 = 0 :=
  rfl

@[simp] theorem inl_zero (R : Type u) (M : Type v) [HasZero R] [HasZero M] : inl 0 = 0 :=
  rfl

@[simp] theorem inr_zero (R : Type u) (M : Type v) [HasZero R] [HasZero M] : inr 0 = 0 :=
  rfl

protected instance has_add (R : Type u) (M : Type v) [Add R] [Add M] : Add (triv_sq_zero_ext R M) :=
  prod.has_add

@[simp] theorem fst_add (R : Type u) (M : Type v) [Add R] [Add M] (x₁ : triv_sq_zero_ext R M) (x₂ : triv_sq_zero_ext R M) : fst (x₁ + x₂) = fst x₁ + fst x₂ :=
  rfl

@[simp] theorem snd_add (R : Type u) (M : Type v) [Add R] [Add M] (x₁ : triv_sq_zero_ext R M) (x₂ : triv_sq_zero_ext R M) : snd (x₁ + x₂) = snd x₁ + snd x₂ :=
  rfl

protected instance has_neg (R : Type u) (M : Type v) [Neg R] [Neg M] : Neg (triv_sq_zero_ext R M) :=
  prod.has_neg

@[simp] theorem fst_neg (R : Type u) (M : Type v) [Neg R] [Neg M] (x : triv_sq_zero_ext R M) : fst (-x) = -fst x :=
  rfl

@[simp] theorem snd_neg (R : Type u) (M : Type v) [Neg R] [Neg M] (x : triv_sq_zero_ext R M) : snd (-x) = -snd x :=
  rfl

protected instance add_semigroup (R : Type u) (M : Type v) [add_semigroup R] [add_semigroup M] : add_semigroup (triv_sq_zero_ext R M) :=
  prod.add_semigroup

protected instance add_monoid (R : Type u) (M : Type v) [add_monoid R] [add_monoid M] : add_monoid (triv_sq_zero_ext R M) :=
  prod.add_monoid

@[simp] theorem inl_add (R : Type u) (M : Type v) [Add R] [add_monoid M] (r₁ : R) (r₂ : R) : inl (r₁ + r₂) = inl r₁ + inl r₂ :=
  ext rfl (Eq.symm (add_zero 0))

@[simp] theorem inr_add (R : Type u) (M : Type v) [add_monoid R] [Add M] (m₁ : M) (m₂ : M) : inr (m₁ + m₂) = inr m₁ + inr m₂ :=
  ext (Eq.symm (add_zero 0)) rfl

theorem inl_fst_add_inr_snd_eq (R : Type u) (M : Type v) [add_monoid R] [add_monoid M] (x : triv_sq_zero_ext R M) : inl (fst x) + inr (snd x) = x :=
  ext (add_zero (prod.fst x)) (zero_add (prod.snd x))

protected instance add_group (R : Type u) (M : Type v) [add_group R] [add_group M] : add_group (triv_sq_zero_ext R M) :=
  prod.add_group

@[simp] theorem inl_neg (R : Type u) (M : Type v) [Neg R] [add_group M] (r : R) : inl (-r) = -inl r :=
  ext rfl (Eq.symm neg_zero)

@[simp] theorem inr_neg (R : Type u) (M : Type v) [add_group R] [Neg M] (m : M) : inr (-m) = -inr m :=
  ext (Eq.symm neg_zero) rfl

protected instance add_comm_semigroup (R : Type u) (M : Type v) [add_comm_semigroup R] [add_comm_semigroup M] : add_comm_semigroup (triv_sq_zero_ext R M) :=
  prod.add_comm_semigroup

protected instance add_comm_monoid (R : Type u) (M : Type v) [add_comm_monoid R] [add_comm_monoid M] : add_comm_monoid (triv_sq_zero_ext R M) :=
  prod.add_comm_monoid

protected instance add_comm_group (R : Type u) (M : Type v) [add_comm_group R] [add_comm_group M] : add_comm_group (triv_sq_zero_ext R M) :=
  prod.add_comm_group

protected instance has_scalar (R : Type u) (M : Type v) [Mul R] [has_scalar R M] : has_scalar R (triv_sq_zero_ext R M) :=
  has_scalar.mk fun (r : R) (x : triv_sq_zero_ext R M) => (r * prod.fst x, r • prod.snd x)

@[simp] theorem fst_smul (R : Type u) (M : Type v) [Mul R] [has_scalar R M] (r : R) (x : triv_sq_zero_ext R M) : fst (r • x) = r * fst x :=
  rfl

@[simp] theorem snd_smul (R : Type u) (M : Type v) [Mul R] [has_scalar R M] (r : R) (x : triv_sq_zero_ext R M) : snd (r • x) = r • snd x :=
  rfl

@[simp] theorem inr_smul (R : Type u) (M : Type v) [mul_zero_class R] [has_scalar R M] (r : R) (m : M) : inr (r • m) = r • inr m :=
  ext (Eq.symm (mul_zero r)) rfl

protected instance mul_action (R : Type u) (M : Type v) [monoid R] [mul_action R M] : mul_action R (triv_sq_zero_ext R M) :=
  mul_action.mk sorry sorry

protected instance distrib_mul_action (R : Type u) (M : Type v) [semiring R] [add_monoid M] [distrib_mul_action R M] : distrib_mul_action R (triv_sq_zero_ext R M) :=
  distrib_mul_action.mk sorry sorry

protected instance semimodule (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] : semimodule R (triv_sq_zero_ext R M) :=
  semimodule.mk sorry sorry

protected instance module (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] : module R (triv_sq_zero_ext R M) :=
  semimodule.mk sorry sorry

/-- The canonical `R`-linear inclusion `M → triv_sq_zero_ext R M`. -/
@[simp] theorem inr_hom_apply (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (m : M) : coe_fn (inr_hom R M) m = inr m :=
  Eq.refl (coe_fn (inr_hom R M) m)

protected instance has_one (R : Type u) (M : Type v) [HasOne R] [HasZero M] : HasOne (triv_sq_zero_ext R M) :=
  { one := (1, 0) }

@[simp] theorem fst_one (R : Type u) (M : Type v) [HasOne R] [HasZero M] : fst 1 = 1 :=
  rfl

@[simp] theorem snd_one (R : Type u) (M : Type v) [HasOne R] [HasZero M] : snd 1 = 0 :=
  rfl

@[simp] theorem inl_one (R : Type u) (M : Type v) [HasOne R] [HasZero M] : inl 1 = 1 :=
  rfl

protected instance has_mul (R : Type u) (M : Type v) [Mul R] [Add M] [has_scalar R M] : Mul (triv_sq_zero_ext R M) :=
  { mul :=
      fun (x y : triv_sq_zero_ext R M) => (prod.fst x * prod.fst y, prod.fst x • prod.snd y + prod.fst y • prod.snd x) }

@[simp] theorem fst_mul (R : Type u) (M : Type v) [Mul R] [Add M] [has_scalar R M] (x₁ : triv_sq_zero_ext R M) (x₂ : triv_sq_zero_ext R M) : fst (x₁ * x₂) = fst x₁ * fst x₂ :=
  rfl

@[simp] theorem snd_mul (R : Type u) (M : Type v) [Mul R] [Add M] [has_scalar R M] (x₁ : triv_sq_zero_ext R M) (x₂ : triv_sq_zero_ext R M) : snd (x₁ * x₂) = fst x₁ • snd x₂ + fst x₂ • snd x₁ :=
  rfl

@[simp] theorem inl_mul (R : Type u) (M : Type v) [monoid R] [add_monoid M] [distrib_mul_action R M] (r₁ : R) (r₂ : R) : inl (r₁ * r₂) = inl r₁ * inl r₂ := sorry

theorem inl_mul_inl (R : Type u) (M : Type v) [monoid R] [add_monoid M] [distrib_mul_action R M] (r₁ : R) (r₂ : R) : inl r₁ * inl r₂ = inl (r₁ * r₂) :=
  Eq.symm (inl_mul R M r₁ r₂)

theorem inl_mul_inr (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (r : R) (m : M) : inl r * inr m = inr (r • m) := sorry

theorem inr_mul_inl (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (r : R) (m : M) : inr m * inl r = inr (r • m) := sorry

@[simp] theorem inr_mul_inr (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (m₁ : M) (m₂ : M) : inr m₁ * inr m₂ = 0 := sorry

protected instance monoid (R : Type u) (M : Type v) [comm_monoid R] [add_monoid M] [distrib_mul_action R M] : monoid (triv_sq_zero_ext R M) :=
  monoid.mk Mul.mul sorry 1 sorry sorry

protected instance comm_semiring (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] : comm_semiring (triv_sq_zero_ext R M) :=
  comm_semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry monoid.one sorry
    sorry sorry sorry sorry sorry sorry

/-- The canonical inclusion of rings `R → triv_sq_zero_ext R M`. -/
def inl_hom (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] : R →+* triv_sq_zero_ext R M :=
  ring_hom.mk inl sorry sorry sorry sorry

protected instance algebra (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] : algebra R (triv_sq_zero_ext R M) :=
  algebra.mk (ring_hom.mk (ring_hom.to_fun (inl_hom R M)) sorry sorry sorry sorry) sorry sorry

/-- The canonical `R`-algebra projection `triv_sq_zero_ext R M → R`. -/
def fst_hom (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] : alg_hom R (triv_sq_zero_ext R M) R :=
  alg_hom.mk fst sorry sorry sorry sorry sorry

/-- The canonical `R`-module projection `triv_sq_zero_ext R M → M`. -/
@[simp] theorem snd_hom_apply (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] (x : triv_sq_zero_ext R M) : coe_fn (snd_hom R M) x = snd x :=
  Eq.refl (coe_fn (snd_hom R M) x)

