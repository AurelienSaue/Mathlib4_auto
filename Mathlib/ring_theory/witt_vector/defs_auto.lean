/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.structure_polynomial
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Witt vectors

In this file we define the type of `p`-typical Witt vectors and ring operations on it.
The ring axioms are verified in `ring_theory/witt_vector/basic.lean`.

For a fixed commutative ring `R` and prime `p`,
a Witt vector `x : π R` is an infinite sequence `β β R` of elements of `R`.
However, the ring operations `+` and `*` are not defined in the obvious component-wise way.
Instead, these operations are defined via certain polynomials
using the machinery in `structure_polynomial.lean`.
The `n`th value of the sum of two Witt vectors can depend on the `0`-th through `n`th values
of the summands. This effectively simulates a βcarryingβ operation.

## Main definitions

* `witt_vector p R`: the type of `p`-typical Witt vectors with coefficients in `R`.
* `witt_vector.coeff x n`: projects the `n`th value of the Witt vector `x`.

## Notation

We use notation `π R`, entered `\bbW`, for the Witt vectors over `R`.

-/

/-- `witt_vector p R` is the ring of `p`-typical Witt vectors over the commutative ring `R`,
where `p` is a prime number.

If `p` is invertible in `R`, this ring is isomorphic to `β β R` (the product of `β` copies of `R`).
If `R` is a ring of characteristic `p`, then `witt_vector p R` is a ring of characteristic `0`.
The canonical example is `witt_vector p (zmod p)`,
which is isomorphic to the `p`-adic integers `β€_[p]`. -/
def witt_vector (p : β) (R : Type u_1) := β β R

/- We cannot make this `localized` notation, because the `p` on the RHS doesn't occur on the left
Hiding the `p` in the notation is very convenient, so we opt for repeating the `local notation`
in other files that use Witt vectors. -/

namespace witt_vector


/-- Construct a Witt vector `mk p x : π R` from a sequence `x` of elements of `R`. -/
def mk (p : β) {R : Type u_1} (x : β β R) : witt_vector p R := x

protected instance inhabited {p : β} {R : Type u_1} [Inhabited R] : Inhabited (witt_vector p R) :=
  { default := mk p fun (_x : β) => Inhabited.default }

/--
`x.coeff n` is the `n`th coefficient of the Witt vector `x`.

This concept does not have a standard name in the literature.
-/
def coeff {p : β} {R : Type u_1} (x : witt_vector p R) (n : β) : R := x n

theorem ext {p : β} {R : Type u_1} {x : witt_vector p R} {y : witt_vector p R}
    (h : β (n : β), coeff x n = coeff y n) : x = y :=
  funext fun (n : β) => h n

theorem ext_iff {p : β} {R : Type u_1} {x : witt_vector p R} {y : witt_vector p R} :
    x = y β β (n : β), coeff x n = coeff y n :=
  { mp :=
      fun (h : x = y) (n : β) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (coeff x n = coeff y n)) h)) (Eq.refl (coeff y n)),
    mpr := ext }

@[simp] theorem coeff_mk (p : β) {R : Type u_1} (x : β β R) : coeff (mk p x) = x := rfl

/- These instances are not needed for the rest of the development,
but it is interesting to establish early on that `witt_vector p` is a lawful functor. -/

protected instance functor (p : β) : Functor (witt_vector p) :=
  { map := fun (Ξ± Ξ² : Type u_1) (f : Ξ± β Ξ²) (v : witt_vector p Ξ±) => f β v,
    mapConst := fun (Ξ± Ξ² : Type u_1) (a : Ξ±) (v : witt_vector p Ξ²) (_x : β) => a }

protected instance is_lawful_functor (p : β) : is_lawful_functor (witt_vector p) :=
  is_lawful_functor.mk (fun (Ξ± : Type u_1) (v : witt_vector p Ξ±) => rfl)
    fun (Ξ± Ξ² Ξ³ : Type u_1) (f : Ξ± β Ξ²) (g : Ξ² β Ξ³) (v : witt_vector p Ξ±) => rfl

/-- The polynomials used for defining the element `0` of the ring of Witt vectors. -/
def witt_zero (p : β) [hp : fact (nat.prime p)] : β β mv_polynomial (fin 0 Γ β) β€ :=
  witt_structure_int p 0

/-- The polynomials used for defining the element `1` of the ring of Witt vectors. -/
def witt_one (p : β) [hp : fact (nat.prime p)] : β β mv_polynomial (fin 0 Γ β) β€ :=
  witt_structure_int p 1

/-- The polynomials used for defining the addition of the ring of Witt vectors. -/
def witt_add (p : β) [hp : fact (nat.prime p)] : β β mv_polynomial (fin (bit0 1) Γ β) β€ :=
  witt_structure_int p (mv_polynomial.X 0 + mv_polynomial.X 1)

/-- The polynomials used for describing the subtraction of the ring of Witt vectors. -/
def witt_sub (p : β) [hp : fact (nat.prime p)] : β β mv_polynomial (fin (bit0 1) Γ β) β€ :=
  witt_structure_int p (mv_polynomial.X 0 - mv_polynomial.X 1)

/-- The polynomials used for defining the multiplication of the ring of Witt vectors. -/
def witt_mul (p : β) [hp : fact (nat.prime p)] : β β mv_polynomial (fin (bit0 1) Γ β) β€ :=
  witt_structure_int p (mv_polynomial.X 0 * mv_polynomial.X 1)

/-- The polynomials used for defining the negation of the ring of Witt vectors. -/
def witt_neg (p : β) [hp : fact (nat.prime p)] : β β mv_polynomial (fin 1 Γ β) β€ :=
  witt_structure_int p (-mv_polynomial.X 0)

/-- An auxiliary definition used in `witt_vector.eval`.
Evaluates a polynomial whose variables come from the disjoint union of `k` copies of `β`,
with a curried evaluation `x`.
This can be defined more generally but we use only a specific instance here. -/
def peval {R : Type u_1} [comm_ring R] {k : β} (Ο : mv_polynomial (fin k Γ β) β€)
    (x : fin k β β β R) : R :=
  coe_fn (mv_polynomial.aeval (function.uncurry x)) Ο

/--
Let `Ο` be a family of polynomials, indexed by natural numbers, whose variables come from the
disjoint union of `k` copies of `β`, and let `xα΅’` be a Witt vector for `0 β€ i < k`.

`eval Ο x` evaluates `Ο` mapping the variable `X_(i, n)` to the `n`th coefficient of `xα΅’`.

Instantiating `Ο` with certain polynomials defined in `structure_polynomial.lean` establishes the
ring operations on `π R`. For example, `witt_vector.witt_add` is such a `Ο` with `k = 2`;
evaluating this at `(xβ, xβ)` gives us the sum of two Witt vectors `xβ + xβ`.
-/
def eval {p : β} {R : Type u_1} [comm_ring R] {k : β} (Ο : β β mv_polynomial (fin k Γ β) β€)
    (x : fin k β witt_vector p R) : witt_vector p R :=
  mk p fun (n : β) => peval (Ο n) fun (i : fin k) => coeff (x i)

protected instance has_zero {p : β} (R : Type u_1) [comm_ring R] [fact (nat.prime p)] :
    HasZero (witt_vector p R) :=
  { zero := eval (witt_zero p) matrix.vec_empty }

protected instance has_one {p : β} (R : Type u_1) [comm_ring R] [fact (nat.prime p)] :
    HasOne (witt_vector p R) :=
  { one := eval (witt_one p) matrix.vec_empty }

protected instance has_add {p : β} (R : Type u_1) [comm_ring R] [fact (nat.prime p)] :
    Add (witt_vector p R) :=
  { add :=
      fun (x y : witt_vector p R) =>
        eval (witt_add p) (matrix.vec_cons x (matrix.vec_cons y matrix.vec_empty)) }

protected instance has_sub {p : β} (R : Type u_1) [comm_ring R] [fact (nat.prime p)] :
    Sub (witt_vector p R) :=
  { sub :=
      fun (x y : witt_vector p R) =>
        eval (witt_sub p) (matrix.vec_cons x (matrix.vec_cons y matrix.vec_empty)) }

protected instance has_mul {p : β} (R : Type u_1) [comm_ring R] [fact (nat.prime p)] :
    Mul (witt_vector p R) :=
  { mul :=
      fun (x y : witt_vector p R) =>
        eval (witt_mul p) (matrix.vec_cons x (matrix.vec_cons y matrix.vec_empty)) }

protected instance has_neg {p : β} (R : Type u_1) [comm_ring R] [fact (nat.prime p)] :
    Neg (witt_vector p R) :=
  { neg := fun (x : witt_vector p R) => eval (witt_neg p) (matrix.vec_cons x matrix.vec_empty) }

@[simp] theorem witt_zero_eq_zero (p : β) [hp : fact (nat.prime p)] (n : β) : witt_zero p n = 0 :=
  sorry

@[simp] theorem witt_one_zero_eq_one (p : β) [hp : fact (nat.prime p)] : witt_one p 0 = 1 := sorry

@[simp] theorem witt_one_pos_eq_zero (p : β) [hp : fact (nat.prime p)] (n : β) (hn : 0 < n) :
    witt_one p n = 0 :=
  sorry

@[simp] theorem witt_add_zero (p : β) [hp : fact (nat.prime p)] :
    witt_add p 0 = mv_polynomial.X (0, 0) + mv_polynomial.X (1, 0) :=
  sorry

@[simp] theorem witt_sub_zero (p : β) [hp : fact (nat.prime p)] :
    witt_sub p 0 = mv_polynomial.X (0, 0) - mv_polynomial.X (1, 0) :=
  sorry

@[simp] theorem witt_mul_zero (p : β) [hp : fact (nat.prime p)] :
    witt_mul p 0 = mv_polynomial.X (0, 0) * mv_polynomial.X (1, 0) :=
  sorry

@[simp] theorem witt_neg_zero (p : β) [hp : fact (nat.prime p)] :
    witt_neg p 0 = -mv_polynomial.X (0, 0) :=
  sorry

@[simp] theorem constant_coeff_witt_add (p : β) [hp : fact (nat.prime p)] (n : β) :
    coe_fn mv_polynomial.constant_coeff (witt_add p n) = 0 :=
  sorry

@[simp] theorem constant_coeff_witt_sub (p : β) [hp : fact (nat.prime p)] (n : β) :
    coe_fn mv_polynomial.constant_coeff (witt_sub p n) = 0 :=
  sorry

@[simp] theorem constant_coeff_witt_mul (p : β) [hp : fact (nat.prime p)] (n : β) :
    coe_fn mv_polynomial.constant_coeff (witt_mul p n) = 0 :=
  sorry

@[simp] theorem constant_coeff_witt_neg (p : β) [hp : fact (nat.prime p)] (n : β) :
    coe_fn mv_polynomial.constant_coeff (witt_neg p n) = 0 :=
  sorry

@[simp] theorem zero_coeff (p : β) (R : Type u_1) [hp : fact (nat.prime p)] [comm_ring R] (n : β) :
    coeff 0 n = 0 :=
  sorry

@[simp] theorem one_coeff_zero (p : β) (R : Type u_1) [hp : fact (nat.prime p)] [comm_ring R] :
    coeff 1 0 = 1 :=
  sorry

@[simp] theorem one_coeff_eq_of_pos (p : β) (R : Type u_1) [hp : fact (nat.prime p)] [comm_ring R]
    (n : β) (hn : 0 < n) : coeff 1 n = 0 :=
  sorry

theorem add_coeff {p : β} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R]
    (x : witt_vector p R) (y : witt_vector p R) (n : β) :
    coeff (x + y) n =
        peval (witt_add p n)
          (matrix.vec_cons (coeff x) (matrix.vec_cons (coeff y) matrix.vec_empty)) :=
  rfl

theorem sub_coeff {p : β} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R]
    (x : witt_vector p R) (y : witt_vector p R) (n : β) :
    coeff (x - y) n =
        peval (witt_sub p n)
          (matrix.vec_cons (coeff x) (matrix.vec_cons (coeff y) matrix.vec_empty)) :=
  rfl

theorem mul_coeff {p : β} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R]
    (x : witt_vector p R) (y : witt_vector p R) (n : β) :
    coeff (x * y) n =
        peval (witt_mul p n)
          (matrix.vec_cons (coeff x) (matrix.vec_cons (coeff y) matrix.vec_empty)) :=
  rfl

theorem neg_coeff {p : β} {R : Type u_1} [hp : fact (nat.prime p)] [comm_ring R]
    (x : witt_vector p R) (n : β) :
    coeff (-x) n = peval (witt_neg p n) (matrix.vec_cons (coeff x) matrix.vec_empty) :=
  rfl

theorem witt_add_vars (p : β) [hp : fact (nat.prime p)] (n : β) :
    mv_polynomial.vars (witt_add p n) β finset.product finset.univ (finset.range (n + 1)) :=
  witt_structure_int_vars p (mv_polynomial.X 0 + mv_polynomial.X 1) n

theorem witt_sub_vars (p : β) [hp : fact (nat.prime p)] (n : β) :
    mv_polynomial.vars (witt_sub p n) β finset.product finset.univ (finset.range (n + 1)) :=
  witt_structure_int_vars p (mv_polynomial.X 0 - mv_polynomial.X 1) n

theorem witt_mul_vars (p : β) [hp : fact (nat.prime p)] (n : β) :
    mv_polynomial.vars (witt_mul p n) β finset.product finset.univ (finset.range (n + 1)) :=
  witt_structure_int_vars p (mv_polynomial.X 0 * mv_polynomial.X 1) n

theorem witt_neg_vars (p : β) [hp : fact (nat.prime p)] (n : β) :
    mv_polynomial.vars (witt_neg p n) β finset.product finset.univ (finset.range (n + 1)) :=
  witt_structure_int_vars p (-mv_polynomial.X 0) n

end Mathlib