/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.rename
import Mathlib.PostPort

universes u_1 u_2 u_4 u_3 

namespace Mathlib

/-!
# `comap` operation on `mv_polynomial`

This file defines the `comap` function on `mv_polynomial`.

`mv_polynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

-/

namespace mv_polynomial


/--
Given an algebra hom `f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
def comap {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R]
    (f : alg_hom R (mv_polynomial σ R) (mv_polynomial τ R)) : (τ → R) → σ → R :=
  fun (x : τ → R) (i : σ) => coe_fn (aeval x) (coe_fn f (X i))

@[simp] theorem comap_apply {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R]
    (f : alg_hom R (mv_polynomial σ R) (mv_polynomial τ R)) (x : τ → R) (i : σ) :
    comap f x i = coe_fn (aeval x) (coe_fn f (X i)) :=
  rfl

@[simp] theorem comap_id_apply {σ : Type u_1} {R : Type u_4} [comm_semiring R] (x : σ → R) :
    comap (alg_hom.id R (mv_polynomial σ R)) x = x :=
  sorry

theorem comap_id (σ : Type u_1) (R : Type u_4) [comm_semiring R] :
    comap (alg_hom.id R (mv_polynomial σ R)) = id :=
  funext fun (x : σ → R) => comap_id_apply x

theorem comap_comp_apply {σ : Type u_1} {τ : Type u_2} {υ : Type u_3} {R : Type u_4}
    [comm_semiring R] (f : alg_hom R (mv_polynomial σ R) (mv_polynomial τ R))
    (g : alg_hom R (mv_polynomial τ R) (mv_polynomial υ R)) (x : υ → R) :
    comap (alg_hom.comp g f) x = comap f (comap g x) :=
  sorry

theorem comap_comp {σ : Type u_1} {τ : Type u_2} {υ : Type u_3} {R : Type u_4} [comm_semiring R]
    (f : alg_hom R (mv_polynomial σ R) (mv_polynomial τ R))
    (g : alg_hom R (mv_polynomial τ R) (mv_polynomial υ R)) :
    comap (alg_hom.comp g f) = comap f ∘ comap g :=
  funext fun (x : υ → R) => comap_comp_apply f g x

theorem comap_eq_id_of_eq_id {σ : Type u_1} {R : Type u_4} [comm_semiring R]
    (f : alg_hom R (mv_polynomial σ R) (mv_polynomial σ R))
    (hf : ∀ (φ : mv_polynomial σ R), coe_fn f φ = φ) (x : σ → R) : comap f x = x :=
  sorry

theorem comap_rename {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R] (f : σ → τ)
    (x : τ → R) : comap (rename f) x = x ∘ f :=
  sorry

/--
If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to `R`.
-/
def comap_equiv {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R]
    (f : alg_equiv R (mv_polynomial σ R) (mv_polynomial τ R)) : (τ → R) ≃ (σ → R) :=
  equiv.mk (comap ↑f) (comap ↑(alg_equiv.symm f)) sorry sorry

@[simp] theorem comap_equiv_coe {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R]
    (f : alg_equiv R (mv_polynomial σ R) (mv_polynomial τ R)) : ⇑(comap_equiv f) = comap ↑f :=
  rfl

@[simp] theorem comap_equiv_symm_coe {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [comm_semiring R]
    (f : alg_equiv R (mv_polynomial σ R) (mv_polynomial τ R)) :
    ⇑(equiv.symm (comap_equiv f)) = comap ↑(alg_equiv.symm f) :=
  rfl

end Mathlib