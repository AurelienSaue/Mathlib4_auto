/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.ring.ulift
import Mathlib.ring_theory.witt_vector.basic
import Mathlib.data.mv_polynomial.funext
import Mathlib.PostPort

universes u_2 u_1 u 

namespace Mathlib

/-!
# The `is_poly` predicate

`witt_vector.is_poly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → mv_polynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `is_poly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (witt_polynomial p _ n) = bind₁ ψ (witt_polynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `witt_vector.frobenius`
and `witt_vector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `witt_vector.is_poly`, `witt_vector.is_poly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `witt_vector.is_poly.ext`, `witt_vector.is_poly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynmials on them.
* `witt_vector.is_poly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `witt_vector.id_is_poly`, `witt_vector.neg_is_poly`,
  `witt_vector.add_is_poly₂`, `witt_vector.mul_is_poly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `is_polyₙ` for functions of higher arity,
together with `is_polyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attributes `@[is_poly]` and `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

Any atomic proof of `is_poly` or `is_poly₂` (i.e. not taking additional `is_poly` arguments)
should be tagged as `@[is_poly]`.

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (witt_polynomial p ℤ n) = (witt_polynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
begin
  ghost_calc _,
  <minor preprocessing>,
  ghost_simp
end
```
-/

/-
### Simplification tactics

`ghost_simp` is used later in the development for certain simplifications.
We define it here so it is a shared import.
-/

namespace tactic


namespace interactive


/-- A macro for a common simplification when rewriting with ghost component equations. -/
/--
`ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
end interactive


end tactic


namespace witt_vector


/-!
### The `is_poly` predicate
-/

theorem poly_eq_of_witt_polynomial_bind_eq' (p : ℕ) {idx : Type u_2} [hp : fact (nat.prime p)]
    (f : ℕ → mv_polynomial (idx × ℕ) ℤ) (g : ℕ → mv_polynomial (idx × ℕ) ℤ)
    (h :
      ∀ (n : ℕ),
        coe_fn (mv_polynomial.bind₁ f) (witt_polynomial p ℤ n) =
          coe_fn (mv_polynomial.bind₁ g) (witt_polynomial p ℤ n)) :
    f = g :=
  sorry

theorem poly_eq_of_witt_polynomial_bind_eq (p : ℕ) [hp : fact (nat.prime p)]
    (f : ℕ → mv_polynomial ℕ ℤ) (g : ℕ → mv_polynomial ℕ ℤ)
    (h :
      ∀ (n : ℕ),
        coe_fn (mv_polynomial.bind₁ f) (witt_polynomial p ℤ n) =
          coe_fn (mv_polynomial.bind₁ g) (witt_polynomial p ℤ n)) :
    f = g :=
  sorry

-- Ideally, we would generalise this to n-ary functions

-- But we don't have a good theory of n-ary compositions in mathlib

/--
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `witt_vector.is_poly₂` for the binary variant.

The `ghost_calc` tactic treats `is_poly` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `is_poly f`.
For the most part, users are not expected to treat `is_poly` as a class.
-/
def is_poly (p : ℕ)
    (f : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R) :=
  ∃ (φ : ℕ → mv_polynomial ℕ ℤ),
    ∀ {R : Type u_1} [_inst_4 : comm_ring R] (x : witt_vector p R),
      coeff (f x) = fun (n : ℕ) => coe_fn (mv_polynomial.aeval (coeff x)) (φ n)

/-- The identity function on Witt vectors is a polynomial function. -/
protected instance id_is_poly (p : ℕ) : is_poly p fun (_x : Type u_1) (_x_1 : comm_ring _x) => id :=
  Exists.intro mv_polynomial.X
    fun (R : Type u_1) (_inst_4 : comm_ring R) (x : witt_vector p R) =>
      eq.mpr
        (id
          ((fun (a a_1 : ℕ → R) (e_1 : a = a_1) (ᾰ ᾰ_1 : ℕ → R) (e_2 : ᾰ = ᾰ_1) =>
              congr (congr_arg Eq e_1) e_2)
            (coeff ((fun (_x : Type u_1) (_x_1 : comm_ring _x) => id) R _inst_4 x)) (coeff x)
            ((fun (x x_1 : witt_vector p R) (e_1 : x = x_1) => congr_arg coeff e_1)
              ((fun (_x : Type u_1) (_x_1 : comm_ring _x) => id) R _inst_4 x) x
              (id.equations._eqn_1 x))
            (fun (n : ℕ) => coe_fn (mv_polynomial.aeval (coeff x)) (mv_polynomial.X n)) (coeff x)
            (funext fun (n : ℕ) => mv_polynomial.aeval_X (coeff x) n)))
        (Eq.refl (coeff x))

protected instance id_is_poly_i' (p : ℕ) :
    is_poly p fun (_x : Type u_1) (_x_1 : comm_ring _x) (a : witt_vector p _x) => a :=
  witt_vector.id_is_poly p

namespace is_poly


protected instance inhabited (p : ℕ) :
    Inhabited (is_poly p fun (_x : Type u_1) (_x_1 : comm_ring _x) => id) :=
  { default := witt_vector.id_is_poly p }

theorem ext {p : ℕ} [hp : fact (nat.prime p)]
    {f : {R : Type u} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    {g : {R : Type u} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    (hf : is_poly p f) (hg : is_poly p g)
    (h :
      ∀ (R : Type u) [_Rcr : comm_ring R] (x : witt_vector p R) (n : ℕ),
        coe_fn (ghost_component n) (f x) = coe_fn (ghost_component n) (g x))
    (R : Type u) [comm_ring R] (x : witt_vector p R) : f x = g x :=
  sorry

/-- The composition of polynomial functions is polynomial. -/
theorem comp {p : ℕ}
    {g : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    {f : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    (hg : is_poly p g) (hf : is_poly p f) :
    is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) => g ∘ f :=
  sorry

end is_poly


/--
A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `witt_vector.is_poly` for the unary variant.

The `ghost_calc` tactic treats `is_poly₂` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `is_poly₂ f`.
For the most part, users are not expected to treat `is_poly₂` as a class.
-/
def is_poly₂ (p : ℕ)
    (f :
      {R : Type u_1} →
        [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R) :=
  ∃ (φ : ℕ → mv_polynomial (fin (bit0 1) × ℕ) ℤ),
    ∀ {R : Type u_1} [_inst_4 : comm_ring R] (x y : witt_vector p R),
      coeff (f x y) =
        fun (n : ℕ) =>
          peval (φ n) (matrix.vec_cons (coeff x) (matrix.vec_cons (coeff y) matrix.vec_empty))

/-- The composition of polynomial functions is polynomial. -/
theorem is_poly₂.comp {p : ℕ}
    {h :
      {R : Type u_1} →
        [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    {f : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    {g : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    (hh : is_poly₂ p h) (hf : is_poly p f) (hg : is_poly p g) :
    is_poly₂ p fun (R : Type u_1) (_Rcr : comm_ring R) (x y : witt_vector p R) => h (f x) (g y) :=
  sorry

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
theorem is_poly.comp₂ {p : ℕ}
    {g : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    {f :
      {R : Type u_1} →
        [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    (hg : is_poly p g) (hf : is_poly₂ p f) :
    is_poly₂ p fun (R : Type u_1) (_Rcr : comm_ring R) (x y : witt_vector p R) => g (f x y) :=
  sorry

/-- The diagonal `λ x, f x x` of a polynomial function `f` is polynomial. -/
theorem is_poly₂.diag {p : ℕ}
    {f :
      {R : Type u_1} →
        [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    (hf : is_poly₂ p f) :
    is_poly p fun (R : Type u_1) (_Rcr : comm_ring R) (x : witt_vector p R) => f x x :=
  sorry

namespace tactic


/-!
### The `@[is_poly]` attribute

This attribute is used to derive specialized composition instances
for `is_poly` and `is_poly₂` declarations.
-/

/--
If `n` is the name of a lemma with opened type `∀ vars, is_poly p _`,
`mk_poly_comp_lemmas n vars p` adds composition instances to the environment
`n.comp_i` and `n.comp₂_i`.
-/
/--
If `n` is the name of a lemma with opened type `∀ vars, is_poly₂ p _`,
`mk_poly₂_comp_lemmas n vars p` adds composition instances to the environment
`n.comp₂_i` and `n.comp_diag`.
-/
/--
The `after_set` function for `@[is_poly]`. Calls `mk_poly(₂)_comp_lemmas`.
-/
/--
`@[is_poly]` is applied to lemmas of the form `is_poly f φ` or `is_poly₂ f φ`.
These lemmas should *not* be tagged as instances, and only atomic `is_poly` defs should be tagged:
composition lemmas should not. Roughly speaking, lemmas that take `is_poly` proofs as arguments
should not be tagged.

Type class inference struggles with function composition, and the higher order unification problems
involved in inferring `is_poly` proofs are complex. The standard style writing these proofs by hand
doesn't work very well. Instead, we construct the type class hierarchy "under the hood", with
limited forms of composition.

Applying `@[is_poly]` to a lemma creates a number of instances. Roughly, if the tagged lemma is a
proof of `is_poly f φ`, the instances added have the form
```lean
∀ g ψ, [is_poly g ψ] → is_poly (f ∘ g) _
```
Since `f` is fixed in this instance, it restricts the HO unification needed when the instance is
applied. Composition lemmas relating `is_poly` with `is_poly₂` are also added.
`id_is_poly` is an atomic instance.

The user-written lemmas are not instances. Users should be able to assemble `is_poly` proofs by hand
"as normal" if the tactic fails.
-/
end tactic


/-!
### `is_poly` instances

These are not declared as instances at the top level,
but the `@[is_poly]` attribute adds instances based on each one.
Users are expected to use the non-instance versions manually.
-/

/-- The additive negation is a polynomial function on Witt vectors. -/
theorem neg_is_poly {p : ℕ} [hp : fact (nat.prime p)] :
    is_poly p fun (R : Type u_1) (_x : comm_ring R) => Neg.neg :=
  sorry

/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/

/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
protected instance zero_is_poly {p : ℕ} [hp : fact (nat.prime p)] :
    is_poly p fun (_x : Type u_1) (_x_1 : comm_ring _x) (_x_2 : witt_vector p _x) => 0 :=
  Exists.intro 0
    fun (R : Type u_1) (_inst_4 : comm_ring R) (x : witt_vector p R) =>
      funext
        fun (n : ℕ) =>
          eq.mpr
            (id
              ((fun (a a_1 : R) (e_1 : a = a_1) (ᾰ ᾰ_1 : R) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg Eq e_1) e_2)
                (coeff
                  ((fun (_x : Type u_1) (_x_1 : comm_ring _x) (_x_2 : witt_vector p _x) => 0) R
                    _inst_4 x)
                  n)
                0 (zero_coeff p R n) (coe_fn (mv_polynomial.aeval (coeff x)) (HasZero.zero n)) 0
                (Eq.trans
                  ((fun (x x_1 : alg_hom ℤ (mv_polynomial ℕ ℤ) R) (e_1 : x = x_1)
                      (ᾰ ᾰ_1 : mv_polynomial ℕ ℤ) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg coe_fn e_1) e_2)
                    (mv_polynomial.aeval (coeff x)) (mv_polynomial.aeval (coeff x))
                    (Eq.refl (mv_polynomial.aeval (coeff x))) (HasZero.zero n) 0 (pi.zero_apply n))
                  (alg_hom.map_zero (mv_polynomial.aeval (coeff x))))))
            (Eq.refl 0)

@[simp] theorem bind₁_zero_witt_polynomial {p : ℕ} {R : Type u} [hp : fact (nat.prime p)]
    [comm_ring R] (n : ℕ) : coe_fn (mv_polynomial.bind₁ 0) (witt_polynomial p R n) = 0 :=
  sorry

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def one_poly (n : ℕ) : mv_polynomial ℕ ℤ := ite (n = 0) 1 0

@[simp] theorem bind₁_one_poly_witt_polynomial {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) :
    coe_fn (mv_polynomial.bind₁ one_poly) (witt_polynomial p ℤ n) = 1 :=
  sorry

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
protected instance one_is_poly {p : ℕ} [hp : fact (nat.prime p)] :
    is_poly p fun (_x : Type u_1) (_x_1 : comm_ring _x) (_x_2 : witt_vector p _x) => 1 :=
  sorry

/-- Addition of Witt vectors is a polynomial function. -/
theorem add_is_poly₂ {p : ℕ} [fact (nat.prime p)] :
    is_poly₂ p fun (_x : Type u_1) (_x_1 : comm_ring _x) => Add.add :=
  Exists.intro (witt_add p)
    fun (R : Type u_1) (_inst_4 : comm_ring R) (x y : witt_vector p R) =>
      Eq.refl (coeff ((fun (_x : Type u_1) (_x_1 : comm_ring _x) => Add.add) R _inst_4 x y))

/-- Multiplication of Witt vectors is a polynomial function. -/
theorem mul_is_poly₂ {p : ℕ} [fact (nat.prime p)] :
    is_poly₂ p fun (_x : Type u_1) (_x_1 : comm_ring _x) => Mul.mul :=
  Exists.intro (witt_mul p)
    fun (R : Type u_1) (_inst_4 : comm_ring R) (x y : witt_vector p R) =>
      Eq.refl (coeff ((fun (_x : Type u_1) (_x_1 : comm_ring _x) => Mul.mul) R _inst_4 x y))

-- unfortunately this is not universe polymorphic, merely because `f` isn't

theorem is_poly.map {p : ℕ} {R : Type u} {S : Type u} [hp : fact (nat.prime p)] [comm_ring R]
    [comm_ring S] {f : {R : Type u} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    (hf : is_poly p f) (g : R →+* S) (x : witt_vector p R) :
    coe_fn (map g) (f x) = f (coe_fn (map g) x) :=
  sorry

namespace is_poly₂


protected instance inhabited {p : ℕ} [fact (nat.prime p)] :
    Inhabited (is_poly₂ p fun (_x : Type u_1) (_x_1 : comm_ring _x) => Add.add) :=
  { default := add_is_poly₂ }

/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
theorem comp_left {p : ℕ}
    {g :
      {R : Type u_1} →
        [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    {f : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    (hg : is_poly₂ p g) (hf : is_poly p f) :
    is_poly₂ p fun (R : Type u_1) (_Rcr : comm_ring R) (x y : witt_vector p R) => g (f x) y :=
  comp hg hf (witt_vector.id_is_poly p)

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
theorem comp_right {p : ℕ}
    {g :
      {R : Type u_1} →
        [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    {f : {R : Type u_1} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R}
    (hg : is_poly₂ p g) (hf : is_poly p f) :
    is_poly₂ p fun (R : Type u_1) (_Rcr : comm_ring R) (x y : witt_vector p R) => g x (f y) :=
  comp hg (witt_vector.id_is_poly p) hf

theorem ext {p : ℕ} [hp : fact (nat.prime p)]
    {f :
      {R : Type u} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    {g :
      {R : Type u} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    (hf : is_poly₂ p f) (hg : is_poly₂ p g)
    (h :
      ∀ (R : Type u) [_Rcr : comm_ring R] (x y : witt_vector p R) (n : ℕ),
        coe_fn (ghost_component n) (f x y) = coe_fn (ghost_component n) (g x y))
    (R : Type u) [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) : f x y = g x y :=
  sorry

-- unfortunately this is not universe polymorphic, merely because `f` isn't

theorem map {p : ℕ} {R : Type u} {S : Type u} [hp : fact (nat.prime p)] [comm_ring R] [comm_ring S]
    {f :
      {R : Type u} → [_inst_3 : comm_ring R] → witt_vector p R → witt_vector p R → witt_vector p R}
    (hf : is_poly₂ p f) (g : R →+* S) (x : witt_vector p R) (y : witt_vector p R) :
    coe_fn (map g) (f x y) = f (coe_fn (map g) x) (coe_fn (map g) y) :=
  sorry

end Mathlib