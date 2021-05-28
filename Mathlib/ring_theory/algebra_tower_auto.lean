/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.algebra.tower
import Mathlib.algebra.invertible
import Mathlib.linear_algebra.basis
import Mathlib.ring_theory.adjoin
import PostPort

universes u v w u₁ u_1 u_2 u_3 u_4 v₁ w₁ 

namespace Mathlib

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `field_theory/tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is a `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/

namespace is_scalar_tower


protected instance polynomial (R : Type u) {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : is_scalar_tower R S (polynomial A) :=
  of_algebra_map_eq fun (x : R) => congr_arg (⇑polynomial.C) (algebra_map_apply R S A x)

theorem aeval_apply (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (x : A) (p : polynomial R) : coe_fn (polynomial.aeval x) p = coe_fn (polynomial.aeval x) (polynomial.map (algebra_map R S) p) := sorry

/-- Suppose that `R -> S -> A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
def invertible.algebra_tower (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (r : R) [invertible (coe_fn (algebra_map R S) r)] : invertible (coe_fn (algebra_map R A) r) :=
  invertible.copy (invertible.map (↑(algebra_map S A)) (coe_fn (algebra_map R S) r)) (coe_fn (algebra_map R A) r) sorry

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertible_algebra_coe_nat (R : Type u) (A : Type w) [comm_semiring R] [semiring A] [algebra R A] (n : ℕ) [inv : invertible ↑n] : invertible ↑n :=
  invertible.algebra_tower ℕ R A n

theorem algebra_map_aeval (R : Type u) (A : Type w) (B : Type u₁) [comm_semiring R] [comm_semiring A] [comm_semiring B] [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B] (x : A) (p : polynomial R) : coe_fn (algebra_map A B) (coe_fn (polynomial.aeval x) p) = coe_fn (polynomial.aeval (coe_fn (algebra_map A B) x)) p := sorry

theorem aeval_eq_zero_of_aeval_algebra_map_eq_zero (R : Type u) (A : Type w) (B : Type u₁) [comm_semiring R] [comm_semiring A] [comm_semiring B] [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B] {x : A} {p : polynomial R} (h : function.injective ⇑(algebra_map A B)) (hp : coe_fn (polynomial.aeval (coe_fn (algebra_map A B) x)) p = 0) : coe_fn (polynomial.aeval x) p = 0 := sorry

theorem aeval_eq_zero_of_aeval_algebra_map_eq_zero_field {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_semiring R] [field A] [comm_semiring B] [nontrivial B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B] {x : A} {p : polynomial R} (h : coe_fn (polynomial.aeval (coe_fn (algebra_map A B) x)) p = 0) : coe_fn (polynomial.aeval x) p = 0 :=
  aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B (ring_hom.injective (algebra_map A B)) h

end is_scalar_tower


namespace algebra


theorem adjoin_algebra_map' {R : Type u} {S : Type v} {A : Type w} [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] (s : set S) : adjoin R (⇑(algebra_map S (comap R S A)) '' s) = subalgebra.map (adjoin R s) (to_comap R S A) := sorry

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w) [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (s : set S) : adjoin R (⇑(algebra_map S A) '' s) = subalgebra.map (adjoin R s) (is_scalar_tower.to_alg_hom R S A) := sorry

theorem adjoin_res (C : Type u_1) (D : Type u_2) (E : Type u_3) [comm_semiring C] [comm_semiring D] [comm_semiring E] [algebra C D] [algebra C E] [algebra D E] [is_scalar_tower C D E] (S : set E) : subalgebra.res C (adjoin D S) =
  subalgebra.under (subalgebra.map ⊤ (is_scalar_tower.to_alg_hom C D E))
    (adjoin (↥(subalgebra.map ⊤ (is_scalar_tower.to_alg_hom C D E))) S) := sorry

theorem adjoin_res_eq_adjoin_res (C : Type u_1) (D : Type u_2) (E : Type u_3) (F : Type u_4) [comm_semiring C] [comm_semiring D] [comm_semiring E] [comm_semiring F] [algebra C D] [algebra C E] [algebra C F] [algebra D F] [algebra E F] [is_scalar_tower C D F] [is_scalar_tower C E F] {S : set D} {T : set E} (hS : adjoin C S = ⊤) (hT : adjoin C T = ⊤) : subalgebra.res C (adjoin E (⇑(algebra_map D F) '' S)) = subalgebra.res C (adjoin D (⇑(algebra_map E F) '' T)) := sorry

end algebra


namespace subalgebra


@[simp] theorem aeval_coe (R : Type u) {A : Type w} [comm_semiring R] [comm_semiring A] [algebra R A] {S : subalgebra R A} {x : ↥S} {p : polynomial R} : coe_fn (polynomial.aeval ↑x) p = ↑(coe_fn (polynomial.aeval x) p) :=
  Eq.symm (is_scalar_tower.algebra_map_aeval R (↥S) A x p)

end subalgebra


theorem algebra.fg_trans' {R : Type u_1} {S : Type u_2} {A : Type u_3} [comm_ring R] [comm_ring S] [comm_ring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (hRS : subalgebra.fg ⊤) (hSA : subalgebra.fg ⊤) : subalgebra.fg ⊤ := sorry

theorem linear_independent_smul {R : Type u} {S : Type v} {A : Type w} [comm_ring R] [ring S] [add_comm_group A] [algebra R S] [module S A] [module R A] [is_scalar_tower R S A] {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A} (hb : linear_independent R b) (hc : linear_independent S c) : linear_independent R fun (p : ι × ι') => b (prod.fst p) • c (prod.snd p) := sorry

theorem is_basis.smul {R : Type u} {S : Type v} {A : Type w} [comm_ring R] [ring S] [add_comm_group A] [algebra R S] [module S A] [module R A] [is_scalar_tower R S A] {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A} (hb : is_basis R b) (hc : is_basis S c) : is_basis R fun (p : ι × ι') => b (prod.fst p) • c (prod.snd p) := sorry

theorem is_basis.smul_repr {R : Type u} {S : Type v} {A : Type w} [comm_ring R] [ring S] [add_comm_group A] [algebra R S] [module S A] [module R A] [is_scalar_tower R S A] {ι : Type u_1} {ι' : Type u_2} {b : ι → S} {c : ι' → A} (hb : is_basis R b) (hc : is_basis S c) (x : A) (ij : ι × ι') : coe_fn (coe_fn (is_basis.repr (is_basis.smul hb hc)) x) ij =
  coe_fn (coe_fn (is_basis.repr hb) (coe_fn (coe_fn (is_basis.repr hc) x) (prod.snd ij))) (prod.fst ij) := sorry

theorem is_basis.smul_repr_mk {R : Type u} {S : Type v} {A : Type w} [comm_ring R] [ring S] [add_comm_group A] [algebra R S] [module S A] [module R A] [is_scalar_tower R S A] {ι : Type u_1} {ι' : Type u_2} {b : ι → S} {c : ι' → A} (hb : is_basis R b) (hc : is_basis S c) (x : A) (i : ι) (j : ι') : coe_fn (coe_fn (is_basis.repr (is_basis.smul hb hc)) x) (i, j) =
  coe_fn (coe_fn (is_basis.repr hb) (coe_fn (coe_fn (is_basis.repr hc) x) j)) i := sorry

theorem exists_subalgebra_of_fg (A : Type w) (B : Type u₁) (C : Type u_1) [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C] (hAC : subalgebra.fg ⊤) (hBC : submodule.fg ⊤) : ∃ (B₀ : subalgebra A B), subalgebra.fg B₀ ∧ submodule.fg ⊤ := sorry

/-- Artin--Tate lemma: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg (A : Type w) (B : Type u₁) (C : Type u_1) [comm_ring A] [comm_ring B] [comm_ring C] [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C] [is_noetherian_ring A] (hAC : subalgebra.fg ⊤) (hBC : submodule.fg ⊤) (hBCi : function.injective ⇑(algebra_map B C)) : subalgebra.fg ⊤ := sorry

/-- Restrict the domain of an `alg_hom`. -/
def alg_hom.restrict_domain {A : Type w} (B : Type u₁) {C : Type u_1} {D : Type u_2} [comm_semiring A] [comm_semiring C] [comm_semiring D] [algebra A C] [algebra A D] (f : alg_hom A C D) [comm_semiring B] [algebra A B] [algebra B C] [is_scalar_tower A B C] : alg_hom A B D :=
  alg_hom.comp f (is_scalar_tower.to_alg_hom A B C)

/-- Extend the scalars of an `alg_hom`. -/
def alg_hom.extend_scalars {A : Type w} (B : Type u₁) {C : Type u_1} {D : Type u_2} [comm_semiring A] [comm_semiring C] [comm_semiring D] [algebra A C] [algebra A D] (f : alg_hom A C D) [comm_semiring B] [algebra A B] [algebra B C] [is_scalar_tower A B C] : alg_hom B C D :=
  alg_hom.mk (alg_hom.to_fun f) sorry sorry sorry sorry sorry

/-- `alg_hom`s from the top of a tower are equivalent to a pair of `alg_hom`s. -/
def alg_hom_equiv_sigma {A : Type w} {B : Type u₁} {C : Type u_1} {D : Type u_2} [comm_semiring A] [comm_semiring C] [comm_semiring D] [algebra A C] [algebra A D] [comm_semiring B] [algebra A B] [algebra B C] [is_scalar_tower A B C] : alg_hom A C D ≃ sigma fun (f : alg_hom A B D) => alg_hom B C D :=
  equiv.mk (fun (f : alg_hom A C D) => sigma.mk (alg_hom.restrict_domain B f) (alg_hom.extend_scalars B f))
    (fun (fg : sigma fun (f : alg_hom A B D) => alg_hom B C D) => is_scalar_tower.restrict_base A (sigma.snd fg)) sorry
    sorry

