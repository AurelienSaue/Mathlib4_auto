/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.padics.padic_integers
import Mathlib.topology.metric_space.cau_seq_filter
import Mathlib.analysis.specific_limits
import Mathlib.data.polynomial.identities
import Mathlib.topology.algebra.polynomial
import Mathlib.PostPort

namespace Mathlib

/-!
# Hensel's lemma on ℤ_p

This file proves Hensel's lemma on ℤ_p, roughly following Keith Conrad's writeup:
<http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>

Hensel's lemma gives a simple condition for the existence of a root of a polynomial.

The proof and motivation are described in the paper
[R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019].

## References

* <http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/Hensel%27s_lemma>

## Tags

p-adic, p adic, padic, p-adic integer
-/

-- We begin with some general lemmas that are used below in the computation.

theorem padic_polynomial_dist {p : ℕ} [fact (nat.prime p)] (F : polynomial (padic_int p))
    (x : padic_int p) (y : padic_int p) :
    norm (polynomial.eval x F - polynomial.eval y F) ≤ norm (x - y) :=
  sorry

theorem limit_zero_of_norm_tendsto_zero {p : ℕ} [fact (nat.prime p)]
    {ncs : cau_seq (padic_int p) norm} {F : polynomial (padic_int p)}
    (hnorm :
      filter.tendsto (fun (i : ℕ) => norm (polynomial.eval (coe_fn ncs i) F)) filter.at_top
        (nhds 0)) :
    polynomial.eval (cau_seq.lim ncs) F = 0 :=
  tendsto_nhds_unique (comp_tendsto_lim ncs) (tendsto_zero_of_norm_tendsto_zero hnorm)

/-- `T` is an auxiliary value that is used to control the behavior of the polynomial `F`. -/
/-- We will construct a sequence of elements of ℤ_p satisfying successive values of `ih`. -/
/-- Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer. -/
-- why doesn't "noncomputable theory" stick here?

theorem hensels_lemma {p : ℕ} [fact (nat.prime p)] {F : polynomial (padic_int p)} {a : padic_int p}
    (hnorm :
      norm (polynomial.eval a F) <
        norm (polynomial.eval a (coe_fn polynomial.derivative F)) ^ bit0 1) :
    ∃ (z : padic_int p),
        polynomial.eval z F = 0 ∧
          norm (z - a) < norm (polynomial.eval a (coe_fn polynomial.derivative F)) ∧
            norm (polynomial.eval z (coe_fn polynomial.derivative F)) =
                norm (polynomial.eval a (coe_fn polynomial.derivative F)) ∧
              ∀ (z' : padic_int p),
                polynomial.eval z' F = 0 →
                  norm (z' - a) < norm (polynomial.eval a (coe_fn polynomial.derivative F)) →
                    z' = z :=
  sorry

end Mathlib