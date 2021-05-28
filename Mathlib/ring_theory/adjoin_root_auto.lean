/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes

Adjoining roots of polynomials
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.polynomial.field_division
import Mathlib.ring_theory.adjoin
import Mathlib.ring_theory.principal_ideal_domain
import Mathlib.linear_algebra.finite_dimensional
import PostPort

universes u v u_1 u_2 w 

namespace Mathlib

/-!
# Adjoining roots of polynomials

This file defines the commutative ring `adjoin_root f`, the ring R[X]/(f) obtained from a
commutative ring `R` and a polynomial `f : R[X]`. If furthermore `R` is a field and `f` is
irreducible, the field structure on `adjoin_root f` is constructed.

## Main definitions and results

The main definitions are in the `adjoin_root` namespace.

*  `mk f : polynomial R →+* adjoin_root f`, the natural ring homomorphism.

*  `of f : R →+* adjoin_root f`, the natural ring homomorphism.

* `root f : adjoin_root f`, the image of X in R[X]/(f).

* `lift (i : R →+* S) (x : S) (h : f.eval₂ i x = 0) : (adjoin_root f) →+* S`, the ring
  homomorphism from R[X]/(f) to S extending `i : R →+* S` and sending `X` to `x`.

* `lift_hom (x : S) (hfx : aeval x f = 0) : adjoin_root f →ₐ[R] S`, the algebra
  homomorphism from R[X]/(f) to S extending `algebra_map R S` and sending `X` to `x`

* `equiv : (adjoin_root f →ₐ[F] E) ≃ {x // x ∈ (f.map (algebra_map F E)).roots}` a
  bijection between algebra homomorphisms from `adjoin_root` and roots of `f` in `S`

-/

/-- Adjoin a root of a polynomial `f` to a commutative ring `R`. We define the new ring
as the quotient of `R` by the principal ideal of `f`. -/
def adjoin_root {R : Type u} [comm_ring R] (f : polynomial R)  :=
  ideal.quotient (ideal.span (singleton f))

namespace adjoin_root


protected instance comm_ring {R : Type u} [comm_ring R] (f : polynomial R) : comm_ring (adjoin_root f) :=
  ideal.quotient.comm_ring (ideal.span (singleton f))

protected instance inhabited {R : Type u} [comm_ring R] (f : polynomial R) : Inhabited (adjoin_root f) :=
  { default := 0 }

protected instance decidable_eq {R : Type u} [comm_ring R] (f : polynomial R) : DecidableEq (adjoin_root f) :=
  classical.dec_eq (adjoin_root f)

/-- Ring homomorphism from `R[x]` to `adjoin_root f` sending `X` to the `root`. -/
def mk {R : Type u} [comm_ring R] (f : polynomial R) : polynomial R →+* adjoin_root f :=
  ideal.quotient.mk (ideal.span (singleton f))

theorem induction_on {R : Type u} [comm_ring R] (f : polynomial R) {C : adjoin_root f → Prop} (x : adjoin_root f) (ih : ∀ (p : polynomial R), C (coe_fn (mk f) p)) : C x :=
  quotient.induction_on' x ih

/-- Embedding of the original ring `R` into `adjoin_root f`. -/
def of {R : Type u} [comm_ring R] (f : polynomial R) : R →+* adjoin_root f :=
  ring_hom.comp (mk f) (ring_hom.of ⇑polynomial.C)

protected instance algebra {R : Type u} [comm_ring R] (f : polynomial R) : algebra R (adjoin_root f) :=
  ring_hom.to_algebra (of f)

@[simp] theorem algebra_map_eq {R : Type u} [comm_ring R] (f : polynomial R) : algebra_map R (adjoin_root f) = of f :=
  rfl

/-- The adjoined root. -/
def root {R : Type u} [comm_ring R] (f : polynomial R) : adjoin_root f :=
  coe_fn (mk f) polynomial.X

protected instance adjoin_root.has_coe_t {R : Type u} [comm_ring R] {f : polynomial R} : has_coe_t R (adjoin_root f) :=
  has_coe_t.mk ⇑(of f)

@[simp] theorem mk_self {R : Type u} [comm_ring R] {f : polynomial R} : coe_fn (mk f) f = 0 := sorry

@[simp] theorem mk_C {R : Type u} [comm_ring R] {f : polynomial R} (x : R) : coe_fn (mk f) (coe_fn polynomial.C x) = ↑x :=
  rfl

@[simp] theorem mk_X {R : Type u} [comm_ring R] {f : polynomial R} : coe_fn (mk f) polynomial.X = root f :=
  rfl

@[simp] theorem aeval_eq {R : Type u} [comm_ring R] {f : polynomial R} (p : polynomial R) : coe_fn (polynomial.aeval (root f)) p = coe_fn (mk f) p := sorry

theorem adjoin_root_eq_top {R : Type u} [comm_ring R] {f : polynomial R} : algebra.adjoin R (singleton (root f)) = ⊤ := sorry

@[simp] theorem eval₂_root {R : Type u} [comm_ring R] (f : polynomial R) : polynomial.eval₂ (of f) (root f) f = 0 := sorry

theorem is_root_root {R : Type u} [comm_ring R] (f : polynomial R) : polynomial.is_root (polynomial.map (of f) f) (root f) := sorry

/-- Lift a ring homomorphism `i : R →+* S` to `adjoin_root f →+* S`. -/
def lift {R : Type u} {S : Type v} [comm_ring R] {f : polynomial R} [comm_ring S] (i : R →+* S) (x : S) (h : polynomial.eval₂ i x f = 0) : adjoin_root f →+* S :=
  ideal.quotient.lift (ideal.span (singleton f)) (polynomial.eval₂_ring_hom i x) sorry

@[simp] theorem lift_mk {R : Type u} {S : Type v} [comm_ring R] {f : polynomial R} [comm_ring S] {i : R →+* S} {a : S} {h : polynomial.eval₂ i a f = 0} {g : polynomial R} : coe_fn (lift i a h) (coe_fn (mk f) g) = polynomial.eval₂ i a g :=
  ideal.quotient.lift_mk (ideal.span (singleton f)) (polynomial.eval₂_ring_hom i a) (lift._proof_1 i a h)

@[simp] theorem lift_root {R : Type u} {S : Type v} [comm_ring R] {f : polynomial R} [comm_ring S] {i : R →+* S} {a : S} {h : polynomial.eval₂ i a f = 0} : coe_fn (lift i a h) (root f) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (lift i a h) (root f) = a)) (root.equations._eqn_1 f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (lift i a h) (coe_fn (mk f) polynomial.X) = a)) lift_mk))
      (eq.mpr (id (Eq._oldrec (Eq.refl (polynomial.eval₂ i a polynomial.X = a)) (polynomial.eval₂_X i a))) (Eq.refl a)))

@[simp] theorem lift_of {R : Type u} {S : Type v} [comm_ring R] {f : polynomial R} [comm_ring S] {i : R →+* S} {a : S} {h : polynomial.eval₂ i a f = 0} {x : R} : coe_fn (lift i a h) ↑x = coe_fn i x := sorry

@[simp] theorem lift_comp_of {R : Type u} {S : Type v} [comm_ring R] {f : polynomial R} [comm_ring S] {i : R →+* S} {a : S} {h : polynomial.eval₂ i a f = 0} : ring_hom.comp (lift i a h) (of f) = i :=
  ring_hom.ext fun (_x : R) => lift_of

/-- Produce an algebra homomorphism `adjoin_root f →ₐ[R] S` sending `root f` to
a root of `f` in `S`. -/
def lift_hom {R : Type u} {S : Type v} [comm_ring R] (f : polynomial R) [comm_ring S] [algebra R S] (x : S) (hfx : coe_fn (polynomial.aeval x) f = 0) : alg_hom R (adjoin_root f) S :=
  alg_hom.mk (ring_hom.to_fun (lift (algebra_map R S) x hfx)) sorry sorry sorry sorry sorry

@[simp] theorem coe_lift_hom {R : Type u} {S : Type v} [comm_ring R] (f : polynomial R) [comm_ring S] [algebra R S] (x : S) (hfx : coe_fn (polynomial.aeval x) f = 0) : ↑(lift_hom f x hfx) = lift (algebra_map R S) x hfx :=
  rfl

@[simp] theorem aeval_alg_hom_eq_zero {R : Type u} {S : Type v} [comm_ring R] (f : polynomial R) [comm_ring S] [algebra R S] (ϕ : alg_hom R (adjoin_root f) S) : coe_fn (polynomial.aeval (coe_fn ϕ (root f))) f = 0 := sorry

@[simp] theorem lift_hom_eq_alg_hom {R : Type u} {S : Type v} [comm_ring R] [comm_ring S] [algebra R S] (f : polynomial R) (ϕ : alg_hom R (adjoin_root f) S) : lift_hom f (coe_fn ϕ (root f)) (aeval_alg_hom_eq_zero f ϕ) = ϕ := sorry

/-- If `E` is a field extension of `F` and `f` is a polynomial over `F` then the set
of maps from `F[x]/(f)` into `E` is in bijection with the set of roots of `f` in `E`. -/
def equiv (F : Type u_1) (E : Type u_2) [field F] [field E] [algebra F E] (f : polynomial F) (hf : f ≠ 0) : alg_hom F (adjoin_root f) E ≃ Subtype fun (x : E) => x ∈ polynomial.roots (polynomial.map (algebra_map F E) f) :=
  equiv.mk (fun (ϕ : alg_hom F (adjoin_root f) E) => { val := coe_fn ϕ (root f), property := sorry })
    (fun (x : Subtype fun (x : E) => x ∈ polynomial.roots (polynomial.map (algebra_map F E) f)) => lift_hom f ↑x sorry)
    sorry sorry

protected instance is_maximal_span {K : Type w} [field K] {f : polynomial K} [irreducible f] : ideal.is_maximal (ideal.span (singleton f)) :=
  principal_ideal_ring.is_maximal_of_irreducible _inst_2

protected instance field {K : Type w} [field K] {f : polynomial K} [irreducible f] : field (adjoin_root f) :=
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul sorry
    comm_ring.one sorry sorry sorry sorry sorry field.inv sorry sorry sorry

theorem coe_injective {K : Type w} [field K] {f : polynomial K} [irreducible f] : function.injective coe :=
  ring_hom.injective (of f)

theorem mul_div_root_cancel {K : Type w} [field K] (f : polynomial K) [irreducible f] : (polynomial.X - coe_fn polynomial.C (root f)) *
    (polynomial.map (of f) f / (polynomial.X - coe_fn polynomial.C (root f))) =
  polynomial.map (of f) f :=
  iff.mpr polynomial.mul_div_eq_iff_is_root (is_root_root f)

