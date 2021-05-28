/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.direct_limit
import Mathlib.field_theory.splitting_field
import Mathlib.analysis.complex.polynomial
import Mathlib.PostPort

universes u l u_1 u_2 v 

namespace Mathlib

/-!
# Algebraic Closure

In this file we define the typeclass for algebraically closed fields and algebraic closures.
We also construct an algebraic closure for any field.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure k K` is the typeclass saying `K` is an algebraic closure of `k`.

- `algebraic_closure k` is an algebraic closure of `k` (in the same universe).
  It is constructed by taking the polynomial ring generated by indeterminates `x_f`
  corresponding to monic irreducible polynomials `f` with coefficients in `k`, and quotienting
  out by a maximal ideal containing every `f(x_f)`, and then repeating this step countably
  many times. See Exercise 1.13 in Atiyah--Macdonald.

## TODO

Show that any algebraic extension embeds into any algebraically closed extension (via Zorn's lemma).

## Tags

algebraic closure, algebraically closed

-/

/-- Typeclass for algebraically closed fields. -/
class is_alg_closed (k : Type u) [field k] 
where
  splits : ∀ (p : polynomial k), polynomial.splits (ring_hom.id k) p

theorem polynomial.splits' {k : Type u_1} {K : Type u_2} [field k] [is_alg_closed k] [field K] {f : k →+* K} (p : polynomial k) : polynomial.splits f p :=
  polynomial.splits_of_splits_id f (is_alg_closed.splits p)

namespace is_alg_closed


theorem of_exists_root (k : Type u) [field k] (H : ∀ (p : polynomial k), polynomial.monic p → irreducible p → ∃ (x : k), polynomial.eval x p = 0) : is_alg_closed k := sorry

theorem degree_eq_one_of_irreducible (k : Type u) [field k] [is_alg_closed k] {p : polynomial k} (h_nz : p ≠ 0) (hp : irreducible p) : polynomial.degree p = 1 :=
  polynomial.degree_eq_one_of_irreducible_of_splits h_nz hp (polynomial.splits' p)

theorem algebra_map_surjective_of_is_integral {k : Type u_1} {K : Type u_2} [field k] [domain K] [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_integral k K) : function.surjective ⇑(algebra_map k K) := sorry

theorem algebra_map_surjective_of_is_integral' {k : Type u_1} {K : Type u_2} [field k] [integral_domain K] [hk : is_alg_closed k] (f : k →+* K) (hf : ring_hom.is_integral f) : function.surjective ⇑f :=
  algebra_map_surjective_of_is_integral hf

theorem algebra_map_surjective_of_is_algebraic {k : Type u_1} {K : Type u_2} [field k] [domain K] [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_algebraic k K) : function.surjective ⇑(algebra_map k K) :=
  algebra_map_surjective_of_is_integral (iff.mp (is_algebraic_iff_is_integral' k) hf)

end is_alg_closed


protected instance complex.is_alg_closed : is_alg_closed ℂ :=
  is_alg_closed.of_exists_root ℂ
    fun (p : polynomial ℂ) (_x : polynomial.monic p) (hp : irreducible p) =>
      complex.exists_root (polynomial.degree_pos_of_irreducible hp)

/-- Typeclass for an extension being an algebraic closure. -/
def is_alg_closure (k : Type u) [field k] (K : Type v) [field K] [algebra k K]  :=
  is_alg_closed K ∧ algebra.is_algebraic k K

namespace algebraic_closure


/-- The subtype of monic irreducible polynomials -/
def monic_irreducible (k : Type u) [field k]  :=
  Subtype fun (f : polynomial k) => polynomial.monic f ∧ irreducible f

/-- Sends a monic irreducible polynomial `f` to `f(x_f)` where `x_f` is a formal indeterminate. -/
def eval_X_self (k : Type u) [field k] (f : monic_irreducible k) : mv_polynomial (monic_irreducible k) k :=
  polynomial.eval₂ mv_polynomial.C (mv_polynomial.X f) ↑f

/-- The span of `f(x_f)` across monic irreducible polynomials `f` where `x_f` is an indeterminate. -/
def span_eval (k : Type u) [field k] : ideal (mv_polynomial (monic_irreducible k) k) :=
  ideal.span (set.range (eval_X_self k))

/-- Given a finset of monic irreducible polynomials, construct an algebra homomorphism to the
splitting field of the product of the polynomials sending each indeterminate `x_f` represented by
the polynomial `f` in the finset to a root of `f`. -/
def to_splitting_field (k : Type u) [field k] (s : finset (monic_irreducible k)) : alg_hom k (mv_polynomial (monic_irreducible k) k)
  (polynomial.splitting_field (finset.prod s fun (x : monic_irreducible k) => ↑x)) :=
  mv_polynomial.aeval
    fun (f : monic_irreducible k) =>
      dite (f ∈ s)
        (fun (hf : f ∈ s) =>
          polynomial.root_of_splits
            (algebra_map k (polynomial.splitting_field (finset.prod s fun (x : monic_irreducible k) => ↑x))) sorry sorry)
        fun (hf : ¬f ∈ s) => bit1 (bit0 (bit1 (bit0 (bit0 1))))

theorem to_splitting_field_eval_X_self (k : Type u) [field k] {s : finset (monic_irreducible k)} {f : monic_irreducible k} (hf : f ∈ s) : coe_fn (to_splitting_field k s) (eval_X_self k f) = 0 := sorry

theorem span_eval_ne_top (k : Type u) [field k] : span_eval k ≠ ⊤ := sorry

/-- A random maximal ideal that contains `span_eval k` -/
def max_ideal (k : Type u) [field k] : ideal (mv_polynomial (monic_irreducible k) k) :=
  classical.some sorry

protected instance max_ideal.is_maximal (k : Type u) [field k] : ideal.is_maximal (max_ideal k) :=
  and.left (classical.some_spec (ideal.exists_le_maximal (span_eval k) (span_eval_ne_top k)))

theorem le_max_ideal (k : Type u) [field k] : span_eval k ≤ max_ideal k :=
  and.right (classical.some_spec (ideal.exists_le_maximal (span_eval k) (span_eval_ne_top k)))

/-- The first step of constructing `algebraic_closure`: adjoin a root of all monic polynomials -/
def adjoin_monic (k : Type u) [field k]  :=
  ideal.quotient (max_ideal k)

protected instance adjoin_monic.field (k : Type u) [field k] : field (adjoin_monic k) :=
  ideal.quotient.field (max_ideal k)

protected instance adjoin_monic.inhabited (k : Type u) [field k] : Inhabited (adjoin_monic k) :=
  { default := bit1 (bit0 (bit1 (bit0 (bit0 1)))) }

/-- The canonical ring homomorphism to `adjoin_monic k`. -/
def to_adjoin_monic (k : Type u) [field k] : k →+* adjoin_monic k :=
  ring_hom.comp (ideal.quotient.mk (max_ideal k)) mv_polynomial.C

protected instance adjoin_monic.algebra (k : Type u) [field k] : algebra k (adjoin_monic k) :=
  ring_hom.to_algebra (to_adjoin_monic k)

theorem adjoin_monic.algebra_map (k : Type u) [field k] : algebra_map k (adjoin_monic k) = ring_hom.comp (ideal.quotient.mk (max_ideal k)) mv_polynomial.C :=
  rfl

theorem adjoin_monic.is_integral (k : Type u) [field k] (z : adjoin_monic k) : is_integral k z := sorry

theorem adjoin_monic.exists_root (k : Type u) [field k] {f : polynomial k} (hfm : polynomial.monic f) (hfi : irreducible f) : ∃ (x : adjoin_monic k), polynomial.eval₂ (to_adjoin_monic k) x f = 0 := sorry

/-- The `n`th step of constructing `algebraic_closure`, together with its `field` instance. -/
def step_aux (k : Type u) [field k] (n : ℕ) : sigma fun (α : Type u) => field α :=
  nat.rec_on n (sigma.mk k infer_instance)
    fun (n : ℕ) (ih : sigma fun (α : Type u) => field α) =>
      sigma.mk (adjoin_monic (sigma.fst ih)) (adjoin_monic.field (sigma.fst ih))

/-- The `n`th step of constructing `algebraic_closure`. -/
def step (k : Type u) [field k] (n : ℕ)  :=
  sigma.fst (step_aux k n)

protected instance step.field (k : Type u) [field k] (n : ℕ) : field (step k n) :=
  sigma.snd (step_aux k n)

protected instance step.inhabited (k : Type u) [field k] (n : ℕ) : Inhabited (step k n) :=
  { default := bit1 (bit0 (bit1 (bit0 (bit0 1)))) }

/-- The canonical inclusion to the `0`th step. -/
def to_step_zero (k : Type u) [field k] : k →+* step k 0 :=
  ring_hom.id k

/-- The canonical ring homomorphism to the next step. -/
def to_step_succ (k : Type u) [field k] (n : ℕ) : step k n →+* step k (n + 1) :=
  to_adjoin_monic (step k n)

protected instance step.algebra_succ (k : Type u) [field k] (n : ℕ) : algebra (step k n) (step k (n + 1)) :=
  ring_hom.to_algebra (to_step_succ k n)

theorem to_step_succ.exists_root (k : Type u) [field k] {n : ℕ} {f : polynomial (step k n)} (hfm : polynomial.monic f) (hfi : irreducible f) : ∃ (x : step k (n + 1)), polynomial.eval₂ (to_step_succ k n) x f = 0 :=
  adjoin_monic.exists_root (step k n) hfm hfi

/-- The canonical ring homomorphism to a step with a greater index. -/
def to_step_of_le (k : Type u) [field k] (m : ℕ) (n : ℕ) (h : m ≤ n) : step k m →+* step k n :=
  ring_hom.mk (nat.le_rec_on h fun (n : ℕ) => ⇑(to_step_succ k n)) sorry sorry sorry sorry

@[simp] theorem coe_to_step_of_le (k : Type u) [field k] (m : ℕ) (n : ℕ) (h : m ≤ n) : ⇑(to_step_of_le k m n h) = nat.le_rec_on h fun (n : ℕ) => ⇑(to_step_succ k n) :=
  rfl

protected instance step.algebra (k : Type u) [field k] (n : ℕ) : algebra k (step k n) :=
  ring_hom.to_algebra (to_step_of_le k 0 n (nat.zero_le n))

protected instance step.scalar_tower (k : Type u) [field k] (n : ℕ) : is_scalar_tower k (step k n) (step k (n + 1)) :=
  is_scalar_tower.of_algebra_map_eq fun (z : k) => nat.le_rec_on_succ (nat.zero_le n) z

theorem step.is_integral (k : Type u) [field k] (n : ℕ) (z : step k n) : is_integral k z :=
  nat.rec_on n (fun (z : step k 0) => is_integral_algebra_map)
    fun (n : ℕ) (ih : ∀ (z : step k n), is_integral k z) (z : step k (Nat.succ n)) =>
      is_integral_trans ih z (adjoin_monic.is_integral (step k n) z)

protected instance to_step_of_le.directed_system (k : Type u) [field k] : directed_system (step k) fun (i j : ℕ) (h : i ≤ j) => ⇑(to_step_of_le k i j h) :=
  directed_system.mk (fun (i : ℕ) (x : step k i) (h : i ≤ i) => nat.le_rec_on_self x)
    fun (i₁ i₂ i₃ : ℕ) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) (x : step k i₁) => Eq.symm (nat.le_rec_on_trans h₁₂ h₂₃ x)

end algebraic_closure


/-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for each polynomial over the field. -/
def algebraic_closure (k : Type u) [field k]  :=
  ring.direct_limit sorry fun (i j : ℕ) (h : i ≤ j) => ⇑sorry

namespace algebraic_closure


protected instance field (k : Type u) [field k] : field (algebraic_closure k) :=
  field.direct_limit.field (step k) fun (i j : ℕ) (h : i ≤ j) => to_step_of_le k i j h

protected instance inhabited (k : Type u) [field k] : Inhabited (algebraic_closure k) :=
  { default := bit1 (bit0 (bit1 (bit0 (bit0 1)))) }

/-- The canonical ring embedding from the `n`th step to the algebraic closure. -/
def of_step (k : Type u) [field k] (n : ℕ) : step k n →+* algebraic_closure k :=
  ring_hom.of ⇑(ring.direct_limit.of (step k) (fun (i j : ℕ) (h : i ≤ j) => ⇑(to_step_of_le k i j h)) n)

protected instance algebra_of_step (k : Type u) [field k] (n : ℕ) : algebra (step k n) (algebraic_closure k) :=
  ring_hom.to_algebra (of_step k n)

theorem of_step_succ (k : Type u) [field k] (n : ℕ) : ring_hom.comp (of_step k (n + 1)) (to_step_succ k n) = of_step k n := sorry

theorem exists_of_step (k : Type u) [field k] (z : algebraic_closure k) : ∃ (n : ℕ), ∃ (x : step k n), coe_fn (of_step k n) x = z :=
  ring.direct_limit.exists_of z

-- slow

theorem exists_root (k : Type u) [field k] {f : polynomial (algebraic_closure k)} (hfm : polynomial.monic f) (hfi : irreducible f) : ∃ (x : algebraic_closure k), polynomial.eval x f = 0 := sorry

protected instance is_alg_closed (k : Type u) [field k] : is_alg_closed (algebraic_closure k) :=
  is_alg_closed.of_exists_root (algebraic_closure k) fun (f : polynomial (algebraic_closure k)) => exists_root k

protected instance algebra (k : Type u) [field k] : algebra k (algebraic_closure k) :=
  ring_hom.to_algebra (of_step k 0)

/-- Canonical algebra embedding from the `n`th step to the algebraic closure. -/
def of_step_hom (k : Type u) [field k] (n : ℕ) : alg_hom k (step k n) (algebraic_closure k) :=
  alg_hom.mk (ring_hom.to_fun (of_step k n)) sorry sorry sorry sorry sorry

theorem is_algebraic (k : Type u) [field k] : algebra.is_algebraic k (algebraic_closure k) := sorry

protected instance is_alg_closure (k : Type u) [field k] : is_alg_closure k (algebraic_closure k) :=
  { left := algebraic_closure.is_alg_closed k, right := is_algebraic k }

