/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.rat.default
import Mathlib.data.fintype.card
import Mathlib.PostPort

namespace Mathlib

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ is even then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

Note however that this result is not yet formalised in Lean.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

Note that $B_1=+1/2$, meaning that we are using the $B_n^+$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).
To get the "minus" convention, just use `(-1)^n * bernoulli n`.

There is no particular reason that the `+` convention was used.
In some sense it's like choosing whether you want to sum over `fin n`
(so `j < n`) or sum over `j ≤ n` (or `nat.antidiagonal n`). Indeed
$$(t+1)\sum_{j\lt n}j^t=\sum_{k\leq t}\binom{t+1}{k}B_k^{-}n^{t+1-k}$$
and
$$(t+1)\sum_{j\leq n}j^t=\sum_{k\leq t}\binom{t+1}{k}B_k^{+}n^{t+1-k}.$$

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$.

## Main theorems

`sum_bernoulli : ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n`

## Todo

* `∑ k : fin n, n.binomial k * (-1)^k * bernoulli k = if n = 1 then 1 else 0`

* Bernoulli polynomials

* `∑ k : fin n, k ^ t =` the Bernoulli polynomial B_t evaluated at n

* `∑ k : fin n.succ, n.succ.choose k bernoulli_poly k X = n.succ * X ^ n` as polynomials
-/

/-!

### Definitions

-/

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli : ℕ → ℚ :=
  well_founded.fix nat.lt_wf
    fun (n : ℕ) (bernoulli : (y : ℕ) → nat.lt y n → ℚ) =>
      1 -
        finset.sum finset.univ
          fun (k : fin n) => ↑(nat.choose n ↑k) / (↑n - ↑k + 1) * bernoulli ↑k sorry

theorem bernoulli_def' (n : ℕ) :
    bernoulli n =
        1 -
          finset.sum finset.univ
            fun (k : fin n) => ↑(nat.choose n ↑k) / (↑n - ↑k + 1) * bernoulli ↑k :=
  sorry

theorem bernoulli_def (n : ℕ) :
    bernoulli n =
        1 -
          finset.sum (finset.range n)
            fun (k : ℕ) => ↑(nat.choose n k) / (↑n - ↑k + 1) * bernoulli k :=
  sorry

/-!

### Examples

-/

@[simp] theorem bernoulli_zero : bernoulli 0 = 1 := rfl

@[simp] theorem bernoulli_one : bernoulli 1 = 1 / bit0 1 := sorry

@[simp] theorem bernoulli_two : bernoulli (bit0 1) = 1 / bit0 (bit1 1) := sorry

@[simp] theorem bernoulli_three : bernoulli (bit1 1) = 0 := sorry

@[simp] theorem bernoulli_four : bernoulli (bit0 (bit0 1)) = -1 / bit0 (bit1 (bit1 (bit1 1))) :=
  sorry

@[simp] theorem sum_bernoulli (n : ℕ) :
    (finset.sum (finset.range n) fun (k : ℕ) => ↑(nat.choose n k) * bernoulli k) = ↑n :=
  sorry

end Mathlib