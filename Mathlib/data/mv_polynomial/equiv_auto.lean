/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.mv_polynomial.rename
import Mathlib.data.equiv.fin
import PostPort

universes u u_1 v w x 

namespace Mathlib

/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/

namespace mv_polynomial


/-- The ring isomorphism between multivariable polynomials in no variables and the ground ring. -/
def pempty_ring_equiv (R : Type u) [comm_semiring R] : mv_polynomial pempty R ≃+* R :=
  ring_equiv.mk (eval₂ (ring_hom.id R) pempty.elim) ⇑C sorry sorry sorry sorry

/-- The algebra isomorphism between multivariable polynomials in no variables and the ground ring. -/
@[simp] theorem pempty_alg_equiv_symm_apply (R : Type u) [comm_semiring R] : ∀ (ᾰ : R), coe_fn (alg_equiv.symm (pempty_alg_equiv R)) ᾰ = coe_fn C ᾰ :=
  fun (ᾰ : R) => Eq.refl (coe_fn (alg_equiv.symm (pempty_alg_equiv R)) ᾰ)

/--
The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simp] theorem punit_ring_equiv_symm_apply (R : Type u) [comm_semiring R] (p : polynomial R) : coe_fn (ring_equiv.symm (punit_ring_equiv R)) p = polynomial.eval₂ C (X PUnit.unit) p :=
  Eq.refl (coe_fn (ring_equiv.symm (punit_ring_equiv R)) p)

/-- The ring isomorphism between multivariable polynomials induced by an equivalence of the variables.  -/
@[simp] theorem ring_equiv_of_equiv_symm_apply (R : Type u) {S₁ : Type v} {S₂ : Type w} [comm_semiring R] (e : S₁ ≃ S₂) : ∀ (ᾰ : mv_polynomial S₂ R), coe_fn (ring_equiv.symm (ring_equiv_of_equiv R e)) ᾰ = coe_fn (rename ⇑(equiv.symm e)) ᾰ :=
  fun (ᾰ : mv_polynomial S₂ R) => Eq.refl (coe_fn (ring_equiv.symm (ring_equiv_of_equiv R e)) ᾰ)

/-- The algebra isomorphism between multivariable polynomials induced by an equivalence of the variables.  -/
@[simp] theorem alg_equiv_of_equiv_symm_apply (R : Type u) {S₁ : Type v} {S₂ : Type w} [comm_semiring R] (e : S₁ ≃ S₂) : ∀ (ᾰ : mv_polynomial S₂ R), coe_fn (alg_equiv.symm (alg_equiv_of_equiv R e)) ᾰ = coe_fn (rename ⇑(equiv.symm e)) ᾰ :=
  fun (ᾰ : mv_polynomial S₂ R) => Eq.refl (coe_fn (alg_equiv.symm (alg_equiv_of_equiv R e)) ᾰ)

/-- The ring isomorphism between multivariable polynomials induced by a ring isomorphism of the ground ring. -/
def ring_equiv_congr (R : Type u) {S₁ : Type v} {S₂ : Type w} [comm_semiring R] [comm_semiring S₂] (e : R ≃+* S₂) : mv_polynomial S₁ R ≃+* mv_polynomial S₁ S₂ :=
  ring_equiv.mk ⇑(map ↑e) ⇑(map ↑(ring_equiv.symm e)) sorry sorry sorry sorry

/--
The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.

See `sum_ring_equiv` for the ring isomorphism.
-/
def sum_to_iter (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] : mv_polynomial (S₁ ⊕ S₂) R →+* mv_polynomial S₁ (mv_polynomial S₂ R) :=
  eval₂_hom (ring_hom.comp C C) fun (bc : S₁ ⊕ S₂) => sum.rec_on bc X (⇑C ∘ X)

protected instance is_semiring_hom_sum_to_iter (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] : is_semiring_hom ⇑(sum_to_iter R S₁ S₂) :=
  eval₂.is_semiring_hom (ring_hom.comp C C) fun (n : S₁ ⊕ S₂) => (fun (bc : S₁ ⊕ S₂) => sum.rec_on bc X (⇑C ∘ X)) n

@[simp] theorem sum_to_iter_C (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] (a : R) : coe_fn (sum_to_iter R S₁ S₂) (coe_fn C a) = coe_fn C (coe_fn C a) :=
  eval₂_C (ring_hom.comp C C) (fun (n : S₁ ⊕ S₂) => (fun (bc : S₁ ⊕ S₂) => sum.rec_on bc X (⇑C ∘ X)) n) a

@[simp] theorem sum_to_iter_Xl (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] (b : S₁) : coe_fn (sum_to_iter R S₁ S₂) (X (sum.inl b)) = X b :=
  eval₂_X (ring_hom.comp C C) (fun (n : S₁ ⊕ S₂) => (fun (bc : S₁ ⊕ S₂) => sum.rec_on bc X (⇑C ∘ X)) n) (sum.inl b)

@[simp] theorem sum_to_iter_Xr (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] (c : S₂) : coe_fn (sum_to_iter R S₁ S₂) (X (sum.inr c)) = coe_fn C (X c) :=
  eval₂_X (ring_hom.comp C C) (fun (n : S₁ ⊕ S₂) => (fun (bc : S₁ ⊕ S₂) => sum.rec_on bc X (⇑C ∘ X)) n) (sum.inr c)

/--
The function from multivariable polynomials in one type,
with coefficents in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sum_ring_equiv` for the ring isomorphism.
-/
def iter_to_sum (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] : mv_polynomial S₁ (mv_polynomial S₂ R) →+* mv_polynomial (S₁ ⊕ S₂) R :=
  eval₂_hom (ring_hom.of (eval₂ C (X ∘ sum.inr))) (X ∘ sum.inl)

theorem iter_to_sum_C_C (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] (a : R) : coe_fn (iter_to_sum R S₁ S₂) (coe_fn C (coe_fn C a)) = coe_fn C a :=
  Eq.trans (eval₂_C (ring_hom.of (eval₂ C (X ∘ sum.inr))) (fun (n : S₁) => function.comp X sum.inl n) (coe_fn C a))
    (eval₂_C C (fun (n : S₂) => function.comp X sum.inr n) a)

theorem iter_to_sum_X (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] (b : S₁) : coe_fn (iter_to_sum R S₁ S₂) (X b) = X (sum.inl b) :=
  eval₂_X (ring_hom.of (eval₂ C (X ∘ sum.inr))) (fun (n : S₁) => function.comp X sum.inl n) b

theorem iter_to_sum_C_X (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] (c : S₂) : coe_fn (iter_to_sum R S₁ S₂) (coe_fn C (X c)) = X (sum.inr c) :=
  Eq.trans (eval₂_C (ring_hom.of (eval₂ C (X ∘ sum.inr))) (fun (n : S₁) => function.comp X sum.inl n) (X c))
    (eval₂_X C (fun (n : S₂) => function.comp X sum.inr n) c)

/-- A helper function for `sum_ring_equiv`. -/
@[simp] theorem mv_polynomial_equiv_mv_polynomial_apply (R : Type u) (S₁ : Type v) (S₂ : Type w) (S₃ : Type x) [comm_semiring R] [comm_semiring S₃] (f : mv_polynomial S₁ R →+* mv_polynomial S₂ S₃) (g : mv_polynomial S₂ S₃ →+* mv_polynomial S₁ R) (hfgC : ∀ (a : S₃), coe_fn f (coe_fn g (coe_fn C a)) = coe_fn C a) (hfgX : ∀ (n : S₂), coe_fn f (coe_fn g (X n)) = X n) (hgfC : ∀ (a : R), coe_fn g (coe_fn f (coe_fn C a)) = coe_fn C a) (hgfX : ∀ (n : S₁), coe_fn g (coe_fn f (X n)) = X n) : ∀ (ᾰ : mv_polynomial S₁ R), coe_fn (mv_polynomial_equiv_mv_polynomial R S₁ S₂ S₃ f g hfgC hfgX hgfC hgfX) ᾰ = coe_fn f ᾰ :=
  fun (ᾰ : mv_polynomial S₁ R) =>
    Eq.refl (coe_fn (mv_polynomial_equiv_mv_polynomial R S₁ S₂ S₃ f g hfgC hfgX hgfC hgfX) ᾰ)

/--
The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficents in multivariable polynomials in the other type.
-/
def sum_ring_equiv (R : Type u) (S₁ : Type v) (S₂ : Type w) [comm_semiring R] : mv_polynomial (S₁ ⊕ S₂) R ≃+* mv_polynomial S₁ (mv_polynomial S₂ R) :=
  mv_polynomial_equiv_mv_polynomial R (S₁ ⊕ S₂) S₁ (mv_polynomial S₂ R) (sum_to_iter R S₁ S₂) (iter_to_sum R S₁ S₂) sorry
    sorry sorry sorry

/--
The ring isomorphism between multivariable polynomials in `option S₁` and
polynomials with coefficients in `mv_polynomial S₁ R`.
-/
def option_equiv_left (R : Type u) (S₁ : Type v) [comm_semiring R] : mv_polynomial (Option S₁) R ≃+* polynomial (mv_polynomial S₁ R) :=
  ring_equiv.trans (ring_equiv_of_equiv R (equiv.trans (equiv.option_equiv_sum_punit S₁) (equiv.sum_comm S₁ PUnit)))
    (ring_equiv.trans (sum_ring_equiv R PUnit S₁) (punit_ring_equiv (mv_polynomial S₁ R)))

/--
The ring isomorphism between multivariable polynomials in `option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
def option_equiv_right (R : Type u) (S₁ : Type v) [comm_semiring R] : mv_polynomial (Option S₁) R ≃+* mv_polynomial S₁ (polynomial R) :=
  ring_equiv.trans (ring_equiv_of_equiv R (equiv.option_equiv_sum_punit S₁))
    (ring_equiv.trans (sum_ring_equiv R S₁ Unit) (ring_equiv_congr (mv_polynomial Unit R) (punit_ring_equiv R)))

/--
The ring isomorphism between multivariable polynomials in `fin (n + 1)` and
polynomials over multivariable polynomials in `fin n`.
-/
def fin_succ_equiv (R : Type u) [comm_semiring R] (n : ℕ) : mv_polynomial (fin (n + 1)) R ≃+* polynomial (mv_polynomial (fin n) R) :=
  ring_equiv.trans (ring_equiv_of_equiv R (fin_succ_equiv n)) (option_equiv_left R (fin n))

theorem fin_succ_equiv_eq (R : Type u) [comm_semiring R] (n : ℕ) : ↑(fin_succ_equiv R n) =
  eval₂_hom (ring_hom.comp polynomial.C C)
    fun (i : fin (n + 1)) => fin.cases polynomial.X (fun (k : fin n) => coe_fn polynomial.C (X k)) i := sorry

@[simp] theorem fin_succ_equiv_apply (R : Type u) [comm_semiring R] (n : ℕ) (p : mv_polynomial (fin (n + 1)) R) : coe_fn (fin_succ_equiv R n) p =
  coe_fn
    (eval₂_hom (ring_hom.comp polynomial.C C)
      fun (i : fin (n + 1)) => fin.cases polynomial.X (fun (k : fin n) => coe_fn polynomial.C (X k)) i)
    p := sorry

theorem fin_succ_equiv_comp_C_eq_C {R : Type u} [comm_semiring R] (n : ℕ) : ring_hom.comp (ring_equiv.to_ring_hom (ring_equiv.symm (fin_succ_equiv R n))) (ring_hom.comp polynomial.C C) = C := sorry

