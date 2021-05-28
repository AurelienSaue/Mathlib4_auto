/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Tim Baanen.

Solve equations in commutative (semi)rings with exponents.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.norm_num
import Mathlib.control.traversable.basic
import PostPort

universes l u u_1 

namespace Mathlib

/-!
# `ring_exp` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The motivating example is proving `2 * 2^n * b = b * 2^(n+1)`,
something that the `ring` tactic cannot do, but `ring_exp` can.

## Implementation notes

The basic approach to prove equalities is to normalise both sides and check for equality.
The normalisation is guided by building a value in the type `ex` at the meta level,
together with a proof (at the base level) that the original value is equal to
the normalised version.
The normalised version and normalisation proofs are also stored in the `ex` type.

The outline of the file:
- Define an inductive family of types `ex`, parametrised over `ex_type`,
  which can represent expressions with `+`, `*`, `^` and rational numerals.
  The parametrisation over `ex_type` ensures that associativity and distributivity are applied,
  by restricting which kinds of subexpressions appear as arguments to the various operators.
- Represent addition, multiplication and exponentiation in the `ex` type,
  thus allowing us to map expressions to `ex` (the `eval` function drives this).
  We apply associativity and distributivity of the operators here (helped by `ex_type`)
  and commutativity as well (by sorting the subterms; unfortunately not helped by anything).
  Any expression not of the above formats is treated as an atom (the same as a variable).

There are some details we glossed over which make the plan more complicated:
- The order on atoms is not initially obvious.
  We construct a list containing them in order of initial appearance in the expression,
  then use the index into the list as a key to order on.
- In the tactic, a normalized expression `ps : ex` lives in the meta-world,
  but the normalization proofs live in the real world.
  Thus, we cannot directly say `ps.orig = ps.pretty` anywhere,
  but we have to carefully construct the proof when we compute `ps`.
  This was a major source of bugs in development!
- For `pow`, the exponent must be a natural number, while the base can be any semiring `α`.
  We swap out operations for the base ring `α` with those for the exponent ring `ℕ`
  as soon as we deal with exponents.
  This is accomplished by the `in_exponent` function and is relatively painless since
  we work in a `reader` monad.
- The normalized form of an expression is the one that is useful for the tactic,
  but not as nice to read. To remedy this, the user-facing normalization calls `ex.simp`.

## Caveats and future work

Subtraction cancels out identical terms, but division does not.
That is: `a - a = 0 := by ring_exp` solves the goal,
but `a / a := 1 by ring_exp` doesn't.
Note that `0 / 0` is generally defined to be `0`,
so division cancelling out is not true in general.

Multiplication of powers can be simplified a little bit further:
`2 ^ n * 2 ^ n = 4 ^ n := by ring_exp` could be implemented
in a similar way that `2 * a + 2 * a = 4 * a := by ring_exp` already works.
This feature wasn't needed yet, so it's not implemented yet.

## Tags

ring, semiring, exponent, power
-/

-- The base ring `α` will have a universe level `u`.

-- We do not introduce `α` as a variable yet,

-- in order to make it explicit or implicit as required.

namespace tactic.ring_exp


/--
The `atom` structure is used to represent atomic expressions:
those which `ring_exp` cannot parse any further.

For instance, `a + (a % b)` has `a` and `(a % b)` as atoms.
The `ring_exp_eq` tactic does not normalize the subexpressions in atoms,
but `ring_exp` does if `ring_exp_eq` was not sufficient.

Atoms in fact represent equivalence classes of expressions,
modulo definitional equality.
The field `index : ℕ` should be a unique number for each class,
while `value : expr` contains a representative of this class.
The function `resolve_atom` determines the appropriate atom
for a given expression.
-/
namespace atom


/--
The `eq` operation on `atom`s works modulo definitional equality,
ignoring their `value`s.
The invariants on `atom` ensure indices are unique per value.
Thus, `eq` indicates equality as long as the `atom`s come from the same context.
-/
/--
We order `atom`s on the order of appearance in the main expression.
-/
end atom


/-!
### `expression` section

In this section, we define the `ex` type and its basic operations.

First, we introduce the supporting types `coeff`, `ex_type` and `ex_info`.
For understanding the code, it's easier to check out `ex` itself first,
then refer back to the supporting types.

The arithmetic operations on `ex` need additional definitions,
so they are defined in a later section.
-/

/--
Coefficients in the expression are stored in a wrapper structure,
allowing for easier modification of the data structures.
The modifications might be caching of the result of `expr.of_rat`,
or using a different meta representation of numerals.
-/
structure coeff 
where
  value : ℚ

/-- The values in `ex_type` are used as parameters to `ex` to control the expression's structure. -/
inductive ex_type 
where
| base : ex_type
| sum : ex_type
| prod : ex_type
| exp : ex_type

/--
Each `ex` stores information for its normalization proof.

The `orig` expression is the expression that was passed to `eval`.

The `pretty` expression is the normalised form that the `ex` represents.
(I didn't call this something like `norm`, because there are already
too many things called `norm` in mathematics!)

The field `proof` contains an optional proof term of type `%%orig = %%pretty`.
The value `none` for the proof indicates that everything reduces to reflexivity.
(Which saves space in quite a lot of cases.)
-/
/--
The `ex` type is an abstract representation of an expression with `+`, `*` and `^`.
Those operators are mapped to the `sum`, `prod` and `exp` constructors respectively.

The `zero` constructor is the base case for `ex sum`, e.g. `1 + 2` is represented
by (something along the lines of) `sum 1 (sum 2 zero)`.

The `coeff` constructor is the base case for `ex prod`, and is used for numerals.
The code maintains the invariant that the coefficient is never `0`.

The `var` constructor is the base case for `ex exp`, and is used for atoms.

The `sum_b` constructor allows for addition in the base of an exponentiation;
it serves a similar purpose as the parentheses in `(a + b)^c`.
The code maintains the invariant that the argument to `sum_b` is not `zero`
or `sum _ zero`.

All of the constructors contain an `ex_info` field,
used to carry around (arguments to) proof terms.

While the `ex_type` parameter enforces some simplification invariants,
the following ones must be manually maintained at the risk of insufficient power:
- the argument to `coeff` must be nonzero (to ensure `0 = 0 * 1`)
- the argument to `sum_b` must be of the form `sum a (sum b bs)` (to ensure `(a + 0)^n = a^n`)
- normalisation proofs of subexpressions must be `refl ps.pretty`
- if we replace `sum` with `cons` and `zero` with `nil`, the resulting list is sorted
  according to the `lt` relation defined further down; similarly for `prod` and `coeff`
  (to ensure `a + b = b + a`).

The first two invariants could be encoded in a subtype of `ex`,
but aren't (yet) to spare some implementation burden.
The other invariants cannot be encoded because we need the `tactic` monad to check them.
(For example, the correct equality check of `expr` is `is_def_eq : expr → expr → tactic unit`.)
-/
/--
Return the proof information associated to the `ex`.
-/
/--
Return the original, non-normalized version of this `ex`.

Note that arguments to another `ex` are always "pre-normalized":
their `orig` and `pretty` are equal, and their `proof` is reflexivity.
-/
/--
Return the normalized version of this `ex`.
-/
/--
Return the normalisation proof of the given expression.
If the proof is `refl`, we give `none` instead,
which helps to control the size of proof terms.
To get an actual term, use `ex.proof_term`,
or use `mk_proof` with the correct set of arguments.
-/
/--
Update the `orig` and `proof` fields of the `ex_info`.
Intended for use in `ex.set_info`.
-/
/--
Update the `ex_info` of the given expression.

We use this to combine intermediate normalisation proofs.
Since `pretty` only depends on the subexpressions,
which do not change, we do not set `pretty`.
-/
protected instance coeff_has_repr : has_repr coeff :=
  has_repr.mk fun (x : coeff) => repr (coeff.value x)

/-- Convert an `ex` to a `string`. -/
/--
Equality test for expressions.

Since equivalence of `atom`s is not the same as equality,
we cannot make a true `(=)` operator for `ex` either.
-/
/--
The ordering on expressions.

As for `ex.eq`, this is a linear order only in one context.
-/
/-!
### `operations` section

This section defines the operations (on `ex`) that use tactics.
They live in the `ring_exp_m` monad,
which adds a cache and a list of encountered atoms to the `tactic` monad.

Throughout this section, we will be constructing proof terms.
The lemmas used in the construction are all defined over a commutative semiring α.
-/

/--
Stores the information needed in the `eval` function and its dependencies,
so they can (re)construct expressions.

The `eval_info` structure stores this information for one type,
and the `context` combines the two types, one for bases and one for exponents.
-/
-- Cache the instances for optimization and consistency

-- Optional instances (only required for (-) and (/) respectively)

-- Cache common constants.

/--
The `context` contains the full set of information needed for the `eval` function.

This structure has two copies of `eval_info`:
one is for the base (typically some semiring `α`) and another for the exponent (always `ℕ`).
When evaluating an exponent, we put `info_e` in `info_b`.
-/
/--
The `ring_exp_m` monad is used instead of `tactic` to store the context.
-/
/--
Access the instance cache.
-/
/--
Lift an operation in the `tactic` monad to the `ring_exp_m` monad.

This operation will not access the cache.
-/
/--
Change the context of the given computation,
so that expressions are evaluated in the exponent ring,
instead of the base ring.
-/
/--
Specialized version of `mk_app` where the first two arguments are `{α}` `[some_class α]`.
Should be faster because it can use the cached instances.
-/
/--
Specialized version of `mk_app` where the first two arguments are `{α}` `[comm_semiring α]`.
Should be faster because it can use the cached instances.
 -/
/--
Specialized version of `mk_app ``has_add.add`.
Should be faster because it can use the cached instances.
-/
/--
Specialized version of `mk_app ``has_mul.mul`.
Should be faster because it can use the cached instances.
-/
/--
Specialized version of `mk_app ``has_pow.pow`.
Should be faster because it can use the cached instances.
-/
/-- Construct a normalization proof term or return the cached one. -/
/-- Construct a normalization proof term or return the cached one. -/
/--
If all `ex_info` have trivial proofs, return a trivial proof.
Otherwise, construct all proof terms.

Useful in applications where trivial proofs combine to another trivial proof,
most importantly to pass to `mk_proof_or_refl`.
-/
/--
Use the proof terms as arguments to the given lemma.
If the lemma could reduce to reflexivity, consider using `mk_proof_or_refl.`
-/
/--
Use the proof terms as arguments to the given lemma.
Often, we construct a proof term using congruence where reflexivity suffices.
To solve this, the following function tries to get away with reflexivity.
-/
/-- A shortcut for adding the original terms of two expressions. -/
/-- A shortcut for multiplying the original terms of two expressions. -/
/-- A shortcut for exponentiating the original terms of two expressions. -/
/-- Congruence lemma for constructing `ex.sum`. -/
theorem sum_congr {α : Type u} [comm_semiring α] {p : α} {p' : α} {ps : α} {ps' : α} : p = p' → ps = ps' → p + ps = p' + ps' := sorry

/-- Congruence lemma for constructing `ex.prod`. -/
theorem prod_congr {α : Type u} [comm_semiring α] {p : α} {p' : α} {ps : α} {ps' : α} : p = p' → ps = ps' → p * ps = p' * ps' := sorry

/-- Congruence lemma for constructing `ex.exp`. -/
theorem exp_congr {α : Type u} [comm_semiring α] {p : α} {p' : α} {ps : ℕ} {ps' : ℕ} : p = p' → ps = ps' → p ^ ps = p' ^ ps' := sorry

/-- Constructs `ex.zero` with the correct arguments. -/
/-- Constructs `ex.sum` with the correct arguments. -/
/--
Constructs `ex.coeff` with the correct arguments.

There are more efficient constructors for specific numerals:
if `x = 0`, you should use `ex_zero`; if `x = 1`, use `ex_one`.
-/
/--
Constructs `ex.coeff 1` with the correct arguments.
This is a special case for optimization purposes.
-/
/-- Constructs `ex.prod` with the correct arguments. -/
/-- Constructs `ex.var` with the correct arguments. -/
/-- Constructs `ex.sum_b` with the correct arguments. -/
/-- Constructs `ex.exp` with the correct arguments. -/
theorem base_to_exp_pf {α : Type u} [comm_semiring α] {p : α} {p' : α} : p = p' → p = p' ^ 1 := sorry

/-- Conversion from `ex base` to `ex exp`. -/
theorem exp_to_prod_pf {α : Type u} [comm_semiring α] {p : α} {p' : α} : p = p' → p = p' * 1 := sorry

/-- Conversion from `ex exp` to `ex prod`. -/
theorem prod_to_sum_pf {α : Type u} [comm_semiring α] {p : α} {p' : α} : p = p' → p = p' + 0 := sorry

/-- Conversion from `ex prod` to `ex sum`. -/
/--
theorem atom_to_sum_pf {α : Type u} [comm_semiring α] (p : α) : p = p ^ 1 * 1 + 0 := sorry

A more efficient conversion from `atom` to `ex sum`.

The result should be the same as `ex_var p >>= base_to_exp >>= exp_to_prod >>= prod_to_sum`,
except we need to calculate less intermediate steps.
-/
/--
Compute the sum of two coefficients.
Note that the result might not be a valid expression:
if `p = -q`, then the result should be `ex.zero : ex sum` instead.
The caller must detect when this happens!

The returned value is of the form `ex.coeff _ (p + q)`,
with the proof of `expr.of_rat p + expr.of_rat q = expr.of_rat (p + q)`.
-/
theorem mul_coeff_pf_one_mul {α : Type u} [comm_semiring α] (q : α) : 1 * q = q :=
  one_mul q

theorem mul_coeff_pf_mul_one {α : Type u} [comm_semiring α] (p : α) : p * 1 = p :=
  mul_one p

/--
Compute the product of two coefficients.

The returned value is of the form `ex.coeff _ (p * q)`,
with the proof of `expr.of_rat p * expr.of_rat q = expr.of_rat (p * q)`.
-/
/-! ### `rewrite` section

In this section we deal with rewriting terms to fit in the basic grammar of `eval`.
For example, `nat.succ n` is rewritten to `n + 1` before it is evaluated further.
-/

/-- Given a proof that the expressions `ps_o` and `ps'.orig` are equal,
show that `ps_o` and `ps'.pretty` are equal.

Useful to deal with aliases in `eval`. For instance, `nat.succ p` can be handled
as an alias of `p + 1` as follows:
```
| ps_o@`(nat.succ %%p_o) := do
  ps' ← eval `(%%p_o + 1),
  pf ← lift $ mk_app ``nat.succ_eq_add_one [p_o],
  rewrite ps_o ps' pf
```
-/
/--
Represents the way in which two products are equal except coefficient.

This type is used in the function `add_overlap`.
In order to deal with equations of the form `a * 2 + a = 3 * a`,
the `add` function will add up overlapping products,
turning `a * 2 + a` into `a * 3`.
We need to distinguish `a * 2 + a` from `a * 2 + b` in order to do this,
and the `overlap` type carries the information on how it overlaps.

The case `none` corresponds to non-overlapping products, e.g. `a * 2 + b`;
the case `nonzero` to overlapping products adding to non-zero, e.g. `a * 2 + a`
(the `ex prod` field will then look like `a * 3` with a proof that `a * 2 + a = a * 3`);
the case `zero` to overlapping products adding to zero, e.g. `a * 2 + a * -2`.
We distinguish those two cases because in the second, the whole product reduces to `0`.

A potential extension to the tactic would also do this for the base of exponents,
e.g. to show `2^n * 2^n = 4^n`.
-/
theorem add_overlap_pf {α : Type u} [comm_semiring α] {ps : α} {qs : α} {pq : α} (p : α) : ps + qs = pq → p * ps + p * qs = p * pq :=
  fun (pq_pf : ps + qs = pq) =>
    Eq.trans (symm (mul_add p ps qs))
      (eq.mpr (id (Eq._oldrec (Eq.refl (p * (ps + qs) = p * pq)) pq_pf)) (Eq.refl (p * pq)))

theorem add_overlap_pf_zero {α : Type u} [comm_semiring α] {ps : α} {qs : α} (p : α) : ps + qs = 0 → p * ps + p * qs = 0 := sorry

/--
Given arguments `ps`, `qs` of the form `ps' * x` and `ps' * y` respectively
return `ps + qs = ps' * (x + y)` (with `x` and `y` arbitrary coefficients).
For other arguments, return `overlap.none`.
-/
theorem add_pf_z_sum {α : Type u} [comm_semiring α] {ps : α} {qs : α} {qs' : α} : ps = 0 → qs = qs' → ps + qs = qs' := sorry

theorem add_pf_sum_z {α : Type u} [comm_semiring α] {ps : α} {ps' : α} {qs : α} : ps = ps' → qs = 0 → ps + qs = ps' := sorry

theorem add_pf_sum_overlap {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {qqs : α} {q : α} {qs : α} {pq : α} {pqs : α} : pps = p + ps → qqs = q + qs → p + q = pq → ps + qs = pqs → pps + qqs = pq + pqs := sorry

theorem add_pf_sum_overlap_zero {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {qqs : α} {q : α} {qs : α} {pqs : α} : pps = p + ps → qqs = q + qs → p + q = 0 → ps + qs = pqs → pps + qqs = pqs := sorry

theorem add_pf_sum_lt {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {qqs : α} {pqs : α} : pps = p + ps → ps + qqs = pqs → pps + qqs = p + pqs := sorry

theorem add_pf_sum_gt {α : Type u} [comm_semiring α] {pps : α} {qqs : α} {q : α} {qs : α} {pqs : α} : qqs = q + qs → pps + qs = pqs → pps + qqs = q + pqs := sorry

/--
Add two expressions.

* `0 + qs = 0`
* `ps + 0 = 0`
* `ps * x + ps * y = ps * (x + y)` (for `x`, `y` coefficients; uses `add_overlap`)
* `(p + ps) + (q + qs) = p + (ps + (q + qs))` (if `p.lt q`)
* `(p + ps) + (q + qs) = q + ((p + ps) + qs)` (if not `p.lt q`)
-/
theorem mul_pf_c_c {α : Type u} [comm_semiring α] {ps : α} {ps' : α} {qs : α} {qs' : α} {pq : α} : ps = ps' → qs = qs' → ps' * qs' = pq → ps * qs = pq := sorry

theorem mul_pf_c_prod {α : Type u} [comm_semiring α] {ps : α} {qqs : α} {q : α} {qs : α} {pqs : α} : qqs = q * qs → ps * qs = pqs → ps * qqs = q * pqs := sorry

theorem mul_pf_prod_c {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {qs : α} {pqs : α} : pps = p * ps → ps * qs = pqs → pps * qs = p * pqs := sorry

theorem mul_pp_pf_overlap {α : Type u} [comm_semiring α] {pps : α} {p_b : α} {ps : α} {qqs : α} {qs : α} {psqs : α} {p_e : ℕ} {q_e : ℕ} : pps = p_b ^ p_e * ps → qqs = p_b ^ q_e * qs → p_b ^ (p_e + q_e) * (ps * qs) = psqs → pps * qqs = psqs := sorry

theorem mul_pp_pf_prod_lt {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {qqs : α} {pqs : α} : pps = p * ps → ps * qqs = pqs → pps * qqs = p * pqs := sorry

theorem mul_pp_pf_prod_gt {α : Type u} [comm_semiring α] {pps : α} {qqs : α} {q : α} {qs : α} {pqs : α} : qqs = q * qs → pps * qs = pqs → pps * qqs = q * pqs := sorry

/--
Multiply two expressions.

* `x * y = (x * y)` (for `x`, `y` coefficients)
* `x * (q * qs) = q * (qs * x)` (for `x` coefficient)
* `(p * ps) * y = p * (ps * y)` (for `y` coefficient)
* `(p_b^p_e * ps) * (p_b^q_e * qs) = p_b^(p_e + q_e) * (ps * qs)`
    (if `p_e` and `q_e` are identical except coefficient)
* `(p * ps) * (q * qs) = p * (ps * (q * qs))` (if `p.lt q`)
* `(p * ps) * (q * qs) = q * ((p * ps) * qs)` (if not `p.lt q`)
-/
theorem mul_p_pf_zero {α : Type u} [comm_semiring α] {ps : α} {qs : α} : ps = 0 → ps * qs = 0 :=
  fun (ps_pf : ps = 0) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (ps * qs = 0)) ps_pf))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 * qs = 0)) (zero_mul qs))) (Eq.refl 0))

theorem mul_p_pf_sum {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {qs : α} {ppsqs : α} : pps = p + ps → p * qs + ps * qs = ppsqs → pps * qs = ppsqs := sorry

/--
Multiply two expressions.

* `0 * qs = 0`
* `(p + ps) * qs = (p * qs) + (ps * qs)`
-/
theorem mul_pf_zero {α : Type u} [comm_semiring α] {ps : α} {qs : α} : qs = 0 → ps * qs = 0 :=
  fun (qs_pf : qs = 0) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (ps * qs = 0)) qs_pf))
      (eq.mpr (id (Eq._oldrec (Eq.refl (ps * 0 = 0)) (mul_zero ps))) (Eq.refl 0))

theorem mul_pf_sum {α : Type u} [comm_semiring α] {ps : α} {qqs : α} {q : α} {qs : α} {psqqs : α} : qqs = q + qs → ps * q + ps * qs = psqqs → ps * qqs = psqqs := sorry

/--
Multiply two expressions.

* `ps * 0 = 0`
* `ps * (q + qs) = (ps * q) + (ps * qs)`
-/
theorem pow_e_pf_exp {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : ℕ} {qs : ℕ} {psqs : ℕ} : pps = p ^ ps → ps * qs = psqs → pps ^ qs = p ^ psqs := sorry

/--
Compute the exponentiation of two coefficients.

The returned value is of the form `ex.coeff _ (p ^ q)`,
with the proof of `expr.of_rat p ^ expr.of_rat q = expr.of_rat (p ^ q)`.
-/
/--
Exponentiate two expressions.

* `(p ^ ps) ^ qs = p ^ (ps * qs)`
-/
theorem pow_pp_pf_one {α : Type u} [comm_semiring α] {ps : α} {qs : ℕ} : ps = 1 → ps ^ qs = 1 :=
  fun (ps_pf : ps = 1) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (ps ^ qs = 1)) ps_pf))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 ^ qs = 1)) (one_pow qs))) (Eq.refl 1))

theorem pow_pf_c_c {α : Type u} [comm_semiring α] {ps : α} {ps' : α} {pq : α} {qs : ℕ} {qs' : ℕ} : ps = ps' → qs = qs' → ps' ^ qs' = pq → ps ^ qs = pq := sorry

theorem pow_pp_pf_c {α : Type u} [comm_semiring α] {ps : α} {ps' : α} {pqs : α} {qs : ℕ} {qs' : ℕ} : ps = ps' → qs = qs' → ps' ^ qs' = pqs → ps ^ qs = pqs * 1 := sorry

theorem pow_pp_pf_prod {α : Type u} [comm_semiring α] {pps : α} {p : α} {ps : α} {pqs : α} {psqs : α} {qs : ℕ} : pps = p * ps → p ^ qs = pqs → ps ^ qs = psqs → pps ^ qs = pqs * psqs := sorry

/--
Exponentiate two expressions.

* `1 ^ qs = 1`
* `x ^ qs = x ^ qs` (for `x` coefficient)
* `(p * ps) ^ qs = p ^ qs + ps ^ qs`
-/
theorem pow_p_pf_one {α : Type u} [comm_semiring α] {ps : α} {ps' : α} {qs : ℕ} : ps = ps' → qs = 1 → ps ^ qs = ps' := sorry

theorem pow_p_pf_zero {α : Type u} [comm_semiring α] {ps : α} {qs : ℕ} {qs' : ℕ} : ps = 0 → qs = Nat.succ qs' → ps ^ qs = 0 := sorry

theorem pow_p_pf_succ {α : Type u} [comm_semiring α] {ps : α} {pqqs : α} {qs : ℕ} {qs' : ℕ} : qs = Nat.succ qs' → ps * ps ^ qs' = pqqs → ps ^ qs = pqqs := sorry

theorem pow_p_pf_singleton {α : Type u} [comm_semiring α] {pps : α} {p : α} {pqs : α} {qs : ℕ} : pps = p + 0 → p ^ qs = pqs → pps ^ qs = pqs := sorry

theorem pow_p_pf_cons {α : Type u} [comm_semiring α] {ps : α} {ps' : α} {qs : ℕ} {qs' : ℕ} : ps = ps' → qs = qs' → ps ^ qs = ps' ^ qs' := sorry

/--
Exponentiate two expressions.

* `ps ^ 1 = ps`
* `0 ^ qs = 0` (note that this is handled *after* `ps ^ 0 = 1`)
* `(p + 0) ^ qs = p ^ qs`
* `ps ^ (qs + 1) = ps * ps ^ qs` (note that this is handled *after* `p + 0 ^ qs = p ^ qs`)
* `ps ^ qs = ps ^ qs` (otherwise)
-/
theorem pow_pf_zero {α : Type u} [comm_semiring α] {ps : α} {qs : ℕ} : qs = 0 → ps ^ qs = 1 :=
  fun (qs_pf : qs = 0) =>
    Eq.trans (eq.mpr (id (Eq._oldrec (Eq.refl (ps ^ qs = ps ^ 0)) qs_pf)) (Eq.refl (ps ^ 0))) (pow_zero ps)

theorem pow_pf_sum {α : Type u} [comm_semiring α] {ps : α} {psqqs : α} {qqs : ℕ} {q : ℕ} {qs : ℕ} : qqs = q + qs → ps ^ q * ps ^ qs = psqqs → ps ^ qqs = psqqs := sorry

/--
Exponentiate two expressions.

* `ps ^ 0 = 1`
* `ps ^ (q + qs) = ps ^ q * ps ^ qs`
-/
theorem simple_pf_sum_zero {α : Type u} [comm_semiring α] {p : α} {p' : α} : p = p' → p + 0 = p' := sorry

theorem simple_pf_prod_one {α : Type u} [comm_semiring α] {p : α} {p' : α} : p = p' → p * 1 = p' := sorry

theorem simple_pf_prod_neg_one {α : Type u_1} [ring α] {p : α} {p' : α} : p = p' → p * -1 = -p' := sorry

theorem simple_pf_var_one {α : Type u} [comm_semiring α] (p : α) : p ^ 1 = p := sorry

theorem simple_pf_exp_one {α : Type u} [comm_semiring α] {p : α} {p' : α} : p = p' → p ^ 1 = p' := sorry

/--
Give a simpler, more human-readable representation of the normalized expression.

Normalized expressions might have the form `a^1 * 1 + 0`,
since the dummy operations reduce special cases in pattern-matching.
Humans prefer to read `a` instead.
This tactic gets rid of the dummy additions, multiplications and exponentiations.
-/
/--
Performs a lookup of the atom `a` in the list of known atoms,
or allocates a new one.

If `a` is not definitionally equal to any of the list's entries,
a new atom is appended to the list and returned.
The index of this atom is kept track of in the second inductive argument.

This function is mostly useful in `resolve_atom`,
which updates the state with the new list of atoms.
-/
/--
Convert the expression to an atom:
either look up a definitionally equal atom,
or allocate it as a new atom.

You probably want to use `eval_base` if `eval` doesn't work
instead of directly calling `resolve_atom`,
since `eval_base` can also handle numerals.
-/
/--
Treat the expression atomically: as a coefficient or atom.

Handles cases where `eval` cannot treat the expression as a known operation
because it is just a number or single variable.
-/
theorem negate_pf {α : Type u_1} [ring α] {ps : α} {ps' : α} : -1 * ps = ps' → -ps = ps' := sorry

/--
Negate an expression by multiplying with `-1`.

Only works if there is a `ring` instance; otherwise it will `fail`.
-/
theorem inverse_pf {α : Type u_1} [division_ring α] {ps : α} {ps_u : α} {ps_p : α} {e' : α} {e'' : α} : ps = ps_u → ps_u = ps_p → ps_p⁻¹ = e' → e' = e'' → ps⁻¹ = e'' := sorry

/--
Invert an expression by simplifying, applying `has_inv.inv` and treating the result as an atom.

Only works if there is a `division_ring` instance; otherwise it will `fail`.
-/
theorem sub_pf {α : Type u_1} [ring α] {ps : α} {qs : α} {psqs : α} (h : ps + -qs = psqs) : ps - qs = psqs :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ps - qs = psqs)) (sub_eq_add_neg ps qs))) h

theorem div_pf {α : Type u_1} [division_ring α] {ps : α} {qs : α} {psqs : α} (h : ps * (qs⁻¹) = psqs) : ps / qs = psqs :=
  eq.mpr (id (Eq._oldrec (Eq.refl (ps / qs = psqs)) (div_eq_mul_inv ps qs))) h

/-!
### `wiring` section

This section deals with going from `expr` to `ex` and back.

The main attraction is `eval`, which uses `add`, `mul`, etc.
to calculate an `ex` from a given `expr`.
Other functions use `ex`es to produce `expr`s together with a proof,
or produce the context to run `ring_exp_m` from an `expr`.
-/

/--
Compute a normalized form (of type `ex`) from an expression (of type `expr`).

This is the main driver of the `ring_exp` tactic,
calling out to `add`, `mul`, `pow`, etc. to parse the `expr`.
-/
/--
Run `eval` on the expression and return the result together with normalization proof.

See also `eval_simple` if you want something that behaves like `norm_num`.
-/
/--
Run `eval` on the expression and simplify the result.

Returns a simplified normalized expression, together with an equality proof.

See also `eval_with_proof` if you just want to check the equality of two expressions.
-/
/-- Compute the `eval_info` for a given type `α`. -/
/-- Use `e` to build the context for running `mx`. -/
/-- Repeatedly apply `eval_simple` on (sub)expressions. -/
end tactic.ring_exp


namespace tactic.interactive


/--
Tactic for solving equations of *commutative* (semi)rings,
allowing variables in the exponent.
This version of `ring_exp` fails if the target is not an equality.

The variant `ring_exp_eq!` will use a more aggressive reducibility setting
to determine equality of atoms.
-/
/--
Tactic for evaluating expressions in *commutative* (semi)rings, allowing for variables in the
exponent.

This tactic extends `ring`: it should solve every goal that `ring` can solve.
Additionally, it knows how to evaluate expressions with complicated exponents
(where `ring` only understands constant exponents).
The variants `ring_exp!` and `ring_exp_eq!` use a more aggessive reducibility setting to determine
equality of atoms.

For example:
```lean
example (n : ℕ) (m : ℤ) : 2^(n+1) * m = 2 * 2^n * m := by ring_exp
example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + b^2 + a * b + b * a) * (a + b)^n := by ring_exp
example (x y : ℕ) : x + id y = y + id x := by ring_exp!
```
-/
