/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.nat.multiplicity
import Mathlib.ring_theory.witt_vector.basic
import Mathlib.ring_theory.witt_vector.is_poly
import PostPort

universes u_1 

namespace Mathlib

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `witt_vector.frobenius_fun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials can not be obtained using the machinery
of `witt_structure_int` that was developed in `structure_polynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_fun_eq_map_frobenius`
that `witt_vector.frobenius_fun` is equal to `witt_vector.map (frobenius R p)`.

### Main definitions and results

* `frobenius_poly`: the polynomials that describe the coefficients of `frobenius_fun`;
* `frobenius_fun`: the Frobenius endomorphism on Witt vectors;
* `frobenius_fun_is_poly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_fun_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `witt_vector.map (frobenius R p)`.

TODO: Show that `witt_vector.frobenius_fun` is a ring homomorphism,
and bundle it into `witt_vector.frobenius`.

-/

namespace witt_vector


/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobenius_poly_rat (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : mv_polynomial ℕ ℚ :=
  coe_fn (mv_polynomial.bind₁ (witt_polynomial p ℚ ∘ fun (n : ℕ) => n + 1)) (X_in_terms_of_W p ℚ n)

theorem bind₁_frobenius_poly_rat_witt_polynomial (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : coe_fn (mv_polynomial.bind₁ (frobenius_poly_rat p)) (witt_polynomial p ℚ n) = witt_polynomial p ℚ (n + 1) := sorry

/-- An auxilliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
/-- An auxilliary polynomial over the integers, that satisfies
`(frobenius_poly_aux p n - X n ^ p) / p = frobenius_poly p n`.
This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
modulo `p`. -/
def frobenius_poly_aux (p : ℕ) [hp : fact (nat.prime p)] : ℕ → mv_polynomial ℕ ℤ :=
  sorry

theorem frobenius_poly_aux_eq (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : frobenius_poly_aux p n =
  mv_polynomial.X (n + 1) -
    finset.sum (finset.range n)
      fun (i : ℕ) =>
        finset.sum (finset.range (p ^ (n - i)))
          fun (j : ℕ) =>
            (mv_polynomial.X i ^ p) ^ (p ^ (n - i) - (j + 1)) * frobenius_poly_aux p i ^ (j + 1) *
              coe_fn mv_polynomial.C
                ↑(nat.choose (p ^ (n - i)) (j + 1) /
                      p ^ (n - i - pnat_multiplicity p { val := j + 1, property := nat.succ_pos j }) *
                    ↑p ^ (j - pnat_multiplicity p { val := j + 1, property := nat.succ_pos j })) := sorry

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobenius_poly (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : mv_polynomial ℕ ℤ :=
  mv_polynomial.X n ^ p + coe_fn mv_polynomial.C ↑p * frobenius_poly_aux p n

/-
Our next goal is to prove
```
lemma map_frobenius_poly (n : ℕ) :
  mv_polynomial.map (int.cast_ring_hom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n
```
This lemma has a rather long proof, but it mostly boils down to applying induction,
and then using the following two key facts at the right point.
-/

/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₁ (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (j : ℕ) (hj : j < p ^ n) : p ^ (n - pnat_multiplicity p { val := j + 1, property := nat.succ_pos j }) ∣ nat.choose (p ^ n) (j + 1) := sorry

/-- A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₂ (p : ℕ) [hp : fact (nat.prime p)] {n : ℕ} {i : ℕ} {j : ℕ} (hi : i < n) (hj : j < p ^ (n - i)) : j - pnat_multiplicity p { val := j + 1, property := nat.succ_pos j } + n =
  i + j + (n - i - pnat_multiplicity p { val := j + 1, property := nat.succ_pos j }) := sorry

theorem map_frobenius_poly (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : coe_fn (mv_polynomial.map (int.cast_ring_hom ℚ)) (frobenius_poly p n) = frobenius_poly_rat p n := sorry

theorem frobenius_poly_zmod (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : coe_fn (mv_polynomial.map (int.cast_ring_hom (zmod p))) (frobenius_poly p n) = mv_polynomial.X n ^ p := sorry

@[simp] theorem bind₁_frobenius_poly_witt_polynomial (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) : coe_fn (mv_polynomial.bind₁ (frobenius_poly p)) (witt_polynomial p ℤ n) = witt_polynomial p ℤ (n + 1) := sorry

/-- `frobenius_fun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
def frobenius_fun {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) : witt_vector p R :=
  mk p fun (n : ℕ) => coe_fn (mv_polynomial.aeval (coeff x)) (frobenius_poly p n)

theorem coeff_frobenius_fun {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coeff (frobenius_fun x) n = coe_fn (mv_polynomial.aeval (coeff x)) (frobenius_poly p n) := sorry

/-- `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
theorem frobenius_fun_is_poly (p : ℕ) [hp : fact (nat.prime p)] : is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) => frobenius_fun :=
  Exists.intro (frobenius_poly p)
    fun (R : Type u_1) (_inst_4 : comm_ring R) (x : witt_vector p R) => funext fun (n : ℕ) => coeff_frobenius_fun x n

theorem ghost_component_frobenius_fun {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (n : ℕ) (x : witt_vector p R) : coe_fn (ghost_component n) (frobenius_fun x) = coe_fn (ghost_component (n + 1)) x := sorry

/--
If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `witt_vector.frobenius_fun`.
-/
def frobenius {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] : witt_vector p R →+* witt_vector p R :=
  ring_hom.mk frobenius_fun sorry sorry sorry sorry

theorem coeff_frobenius {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (x : witt_vector p R) (n : ℕ) : coeff (coe_fn frobenius x) n = coe_fn (mv_polynomial.aeval (coeff x)) (frobenius_poly p n) :=
  coeff_frobenius_fun x n

theorem ghost_component_frobenius {p : ℕ} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] (n : ℕ) (x : witt_vector p R) : coe_fn (ghost_component n) (coe_fn frobenius x) = coe_fn (ghost_component (n + 1)) x :=
  ghost_component_frobenius_fun n x

/-- `frobenius` is tautologically a polynomial function. -/
theorem frobenius_is_poly (p : ℕ) [hp : fact (nat.prime p)] : is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) => ⇑frobenius :=
  frobenius_fun_is_poly p

@[simp] theorem coeff_frobenius_char_p (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] [char_p R p] (x : witt_vector p R) (n : ℕ) : coeff (coe_fn frobenius x) n = coeff x n ^ p := sorry

theorem frobenius_eq_map_frobenius (p : ℕ) {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R] [char_p R p] : frobenius = map (frobenius R p) := sorry

@[simp] theorem frobenius_zmodp (p : ℕ) [hp : fact (nat.prime p)] (x : witt_vector p (zmod p)) : coe_fn frobenius x = x := sorry

