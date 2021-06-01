/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.analysis.calculus.mean_value
import Mathlib.data.nat.parity
import Mathlib.analysis.special_functions.pow
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `convex_on_exp` : the exponential function is convex on $(-∞, +∞)$;
* `convex_on_pow_of_even` : given an even natural number $n$, the function $f(x)=x^n$
  is convex on $(-∞, +∞)$;
* `convex_on_pow` : for a natural $n$, the function $f(x)=x^n$ is convex on $[0, +∞)$;
* `convex_on_fpow` : for an integer $m$, the function $f(x)=x^m$ is convex on $(0, +∞)$.
* `convex_on_rpow : ∀ p : ℝ, 1 ≤ p → convex_on (Ici 0) (λ x, x ^ p)`
* `concave_on_log_Ioi` and `concave_on_log_Iio`: log is concave on `Ioi 0` and `Iio 0` respectively.
-/

/-- `exp` is convex on the whole real line -/
theorem convex_on_exp : convex_on set.univ real.exp := sorry

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
theorem convex_on_pow_of_even {n : ℕ} (hn : even n) : convex_on set.univ fun (x : ℝ) => x ^ n :=
  sorry

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
theorem convex_on_pow (n : ℕ) : convex_on (set.Ici 0) fun (x : ℝ) => x ^ n := sorry

theorem finset.prod_nonneg_of_card_nonpos_even {α : Type u_1} {β : Type u_2}
    [linear_ordered_comm_ring β] {f : α → β} [decidable_pred fun (x : α) => f x ≤ 0] {s : finset α}
    (h0 : even (finset.card (finset.filter (fun (x : α) => f x ≤ 0) s))) :
    0 ≤ finset.prod s fun (x : α) => f x :=
  sorry

theorem int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : even n) :
    0 ≤ finset.prod (finset.range n) fun (k : ℕ) => m - ↑k :=
  sorry

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
theorem convex_on_fpow (m : ℤ) : convex_on (set.Ioi 0) fun (x : ℝ) => x ^ m := sorry

theorem convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on (set.Ici 0) fun (x : ℝ) => x ^ p := sorry

theorem concave_on_log_Ioi : concave_on (set.Ioi 0) real.log := sorry

theorem concave_on_log_Iio : concave_on (set.Iio 0) real.log := sorry

end Mathlib