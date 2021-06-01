/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.norm_num
import Mathlib.data.int.range
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# `ring`

Evaluate expressions in the language of commutative (semi)rings.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .
-/

namespace tactic


namespace ring


/-- The normal form that `ring` uses is mediated by the function `horner a x n b := a * x ^ n + b`.
The reason we use a definition rather than the (more readable) expression on the right is because
this expression contains a number of typeclass arguments in different positions, while `horner`
contains only one `comm_semiring` instance at the top level. See also `horner_expr` for a
description of normal form. -/
def horner {α : Type u_1} [comm_semiring α] (a : α) (x : α) (n : ℕ) (b : α) : α := a * x ^ n + b

/-- This cache contains data required by the `ring` tactic during execution. -/
/-- The monad that `ring` works in. This is a reader monad containing a mutable cache (using `ref`
for mutability), as well as the list of atoms-up-to-defeq encountered thus far, used for atom
sorting. -/
/-- Get the `ring` data from the monad. -/
/-- Get an already encountered atom by its index. -/
/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
/-- Lift a tactic into the `ring_m` monad. -/
/-- Run a `ring_m` tactic in the tactic monad. This version of `ring_m.run` uses an external
atoms ref, so that subexpressions can be named across multiple `ring_m` calls. -/
/-- Run a `ring_m` tactic in the tactic monad. -/
/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This version
is abstract over the instance cache in question (either the ring `α`, or `ℕ` for exponents). -/
/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This uses
the instance cache corresponding to the ring `α`. -/
/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This uses
the instance cache corresponding to `ℕ`, which is used for computations in the exponent. -/
/-- Apply a theorem that expects a `comm_semiring` instance. This is a special case of
`ic_lift mk_app`, but it comes up often because `horner` and all its theorems have this assumption;
it also does not require the tactic monad which improves access speed a bit. -/
/-- Every expression in the language of commutative semirings can be viewed as a sum of monomials,
where each monomial is a product of powers of atoms. We fix a global order on atoms (up to
definitional equality), and then separate the terms according to their smallest atom. So the top
level expression is `a * x^n + b` where `x` is the smallest atom and `n > 0` is a numeral, and
`n` is maximal (so `a` contains at least one monomial not containing an `x`), and `b` contains no
monomials with an `x` (hence all atoms in `b` are larger than `x`).

If there is no `x` satisfying these constraints, then the expression must be a numeral. Even though
we are working over rings, we allow rational constants when these can be interpreted in the ring,
so we can solve problems like `x / 3 = 1 / 3 * x` even though these are not technically in the
language of rings.

These constraints ensure that there is a unique normal form for each ring expression, and so the
algorithm is simply to calculate the normal form of each side and compare for equality.

To allow us to efficiently pattern match on normal forms, we maintain this inductive type that
holds a normalized expression together with its structure. All the `expr`s in this type could be
removed without loss of information, and conversely the `horner_expr` structure and the `ℕ` and
`ℚ` values can be recovered from the top level `expr`, but we keep both in order to keep proof
 producing normalization functions efficient. -/
/-- Get the expression corresponding to a `horner_expr`. This can be calculated recursively from
the structure, but we cache the exprs in all subterms so that this function can be computed in
constant time. -/
/-- Is this expr the constant `0`? -/
/-- Construct a `xadd` node, generating the cached expr using the input cache. -/
/-- Pretty printer for `horner_expr`. -/
/-- Pretty printer for `horner_expr`. -/
/-- Reflexivity conversion for a `horner_expr`. -/
theorem zero_horner {α : Type u_1} [comm_semiring α] (x : α) (n : ℕ) (b : α) : horner 0 x n b = b :=
  sorry

theorem horner_horner {α : Type u_1} [comm_semiring α] (a₁ : α) (x : α) (n₁ : ℕ) (n₂ : ℕ) (b : α)
    (n' : ℕ) (h : n₁ + n₂ = n') : horner (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
  sorry

/-- Evaluate `horner a n x b` where `a` and `b` are already in normal form. -/
theorem const_add_horner {α : Type u_1} [comm_semiring α] (k : α) (a : α) (x : α) (n : ℕ) (b : α)
    (b' : α) (h : k + b = b') : k + horner a x n b = horner a x n b' :=
  sorry

theorem horner_add_const {α : Type u_1} [comm_semiring α] (a : α) (x : α) (n : ℕ) (b : α) (k : α)
    (b' : α) (h : b + k = b') : horner a x n b + k = horner a x n b' :=
  sorry

theorem horner_add_horner_lt {α : Type u_1} [comm_semiring α] (a₁ : α) (x : α) (n₁ : ℕ) (b₁ : α)
    (a₂ : α) (n₂ : ℕ) (b₂ : α) (k : ℕ) (a' : α) (b' : α) (h₁ : n₁ + k = n₂)
    (h₂ : a₁ + horner a₂ x k 0 = a') (h₃ : b₁ + b₂ = b') :
    horner a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₁ b' :=
  sorry

theorem horner_add_horner_gt {α : Type u_1} [comm_semiring α] (a₁ : α) (x : α) (n₁ : ℕ) (b₁ : α)
    (a₂ : α) (n₂ : ℕ) (b₂ : α) (k : ℕ) (a' : α) (b' : α) (h₁ : n₂ + k = n₁)
    (h₂ : horner a₁ x k 0 + a₂ = a') (h₃ : b₁ + b₂ = b') :
    horner a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₂ b' :=
  sorry

theorem horner_add_horner_eq {α : Type u_1} [comm_semiring α] (a₁ : α) (x : α) (n : ℕ) (b₁ : α)
    (a₂ : α) (b₂ : α) (a' : α) (b' : α) (t : α) (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b')
    (h₃ : horner a' x n b' = t) : horner a₁ x n b₁ + horner a₂ x n b₂ = t :=
  sorry

/-- Evaluate `a + b` where `a` and `b` are already in normal form. -/
theorem horner_neg {α : Type u_1} [comm_ring α] (a : α) (x : α) (n : ℕ) (b : α) (a' : α) (b' : α)
    (h₁ : -a = a') (h₂ : -b = b') : -horner a x n b = horner a' x n b' :=
  sorry

/-- Evaluate `-a` where `a` is already in normal form. -/
theorem horner_const_mul {α : Type u_1} [comm_semiring α] (c : α) (a : α) (x : α) (n : ℕ) (b : α)
    (a' : α) (b' : α) (h₁ : c * a = a') (h₂ : c * b = b') : c * horner a x n b = horner a' x n b' :=
  sorry

theorem horner_mul_const {α : Type u_1} [comm_semiring α] (a : α) (x : α) (n : ℕ) (b : α) (c : α)
    (a' : α) (b' : α) (h₁ : a * c = a') (h₂ : b * c = b') : horner a x n b * c = horner a' x n b' :=
  sorry

/-- Evaluate `k * a` where `k` is a rational numeral and `a` is in normal form. -/
theorem horner_mul_horner_zero {α : Type u_1} [comm_semiring α] (a₁ : α) (x : α) (n₁ : ℕ) (b₁ : α)
    (a₂ : α) (n₂ : ℕ) (aa : α) (t : α) (h₁ : horner a₁ x n₁ b₁ * a₂ = aa)
    (h₂ : horner aa x n₂ 0 = t) : horner a₁ x n₁ b₁ * horner a₂ x n₂ 0 = t :=
  sorry

theorem horner_mul_horner {α : Type u_1} [comm_semiring α] (a₁ : α) (x : α) (n₁ : ℕ) (b₁ : α)
    (a₂ : α) (n₂ : ℕ) (b₂ : α) (aa : α) (haa : α) (ab : α) (bb : α) (t : α)
    (h₁ : horner a₁ x n₁ b₁ * a₂ = aa) (h₂ : horner aa x n₂ 0 = haa) (h₃ : a₁ * b₂ = ab)
    (h₄ : b₁ * b₂ = bb) (H : haa + horner ab x n₁ bb = t) :
    horner a₁ x n₁ b₁ * horner a₂ x n₂ b₂ = t :=
  sorry

/-- Evaluate `a * b` where `a` and `b` are in normal form. -/
theorem horner_pow {α : Type u_1} [comm_semiring α] (a : α) (x : α) (n : ℕ) (m : ℕ) (n' : ℕ)
    (a' : α) (h₁ : n * m = n') (h₂ : a ^ m = a') : horner a x n 0 ^ m = horner a' x n' 0 :=
  sorry

theorem pow_succ {α : Type u_1} [comm_semiring α] (a : α) (n : ℕ) (b : α) (c : α) (h₁ : a ^ n = b)
    (h₂ : b * a = c) : a ^ (n + 1) = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n + 1) = c)) (Eq.symm h₂)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n + 1) = b * a)) (Eq.symm h₁)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ (n + 1) = a ^ n * a)) (pow_succ' a n)))
        (Eq.refl (a ^ n * a))))

/-- Evaluate `a ^ n` where `a` is in normal form and `n` is a natural numeral. -/
theorem horner_atom {α : Type u_1} [comm_semiring α] (x : α) : x = horner 1 x 1 0 := sorry

/-- Evaluate `a` where `a` is an atom. -/
theorem subst_into_pow {α : Type u_1} [monoid α] (l : α) (r : ℕ) (tl : α) (tr : ℕ) (t : α)
    (prl : l = tl) (prr : r = tr) (prt : tl ^ tr = t) : l ^ r = t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (l ^ r = t)) prl))
    (eq.mpr (id (Eq._oldrec (Eq.refl (tl ^ r = t)) prr))
      (eq.mpr (id (Eq._oldrec (Eq.refl (tl ^ tr = t)) prt)) (Eq.refl t)))

theorem unfold_sub {α : Type u_1} [add_group α] (a : α) (b : α) (c : α) (h : a + -b = c) :
    a - b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b = c)) (sub_eq_add_neg a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + -b = c)) h)) (Eq.refl c))

theorem unfold_div {α : Type u_1} [division_ring α] (a : α) (b : α) (c : α) (h : a * (b⁻¹) = c) :
    a / b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b = c)) (div_eq_mul_inv a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (b⁻¹) = c)) h)) (Eq.refl c))

/-- Evaluate a ring expression `e` recursively to normal form, together with a proof of
equality. -/
/-- Evaluate a ring expression `e` recursively to normal form, together with a proof of
equality. -/
theorem horner_def' {α : Type u_1} [comm_semiring α] (a : α) (x : α) (n : ℕ) (b : α) :
    horner a x n b = x ^ n * a + b :=
  sorry

theorem mul_assoc_rev {α : Type u_1} [semigroup α] (a : α) (b : α) (c : α) :
    a * (b * c) = a * b * c :=
  sorry

theorem pow_add_rev {α : Type u_1} [monoid α] (a : α) (m : ℕ) (n : ℕ) :
    a ^ m * a ^ n = a ^ (m + n) :=
  sorry

theorem pow_add_rev_right {α : Type u_1} [monoid α] (a : α) (b : α) (m : ℕ) (n : ℕ) :
    b * a ^ m * a ^ n = b * a ^ (m + n) :=
  sorry

theorem add_neg_eq_sub {α : Type u_1} [add_group α] (a : α) (b : α) : a + -b = a - b :=
  Eq.symm (sub_eq_add_neg a b)

/-- If `ring` fails to close the goal, it falls back on normalizing the expression to a "pretty"
form so that you can see why it failed. This setting adjusts the resulting form:

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
inductive normalize_mode where
| raw : normalize_mode
| SOP : normalize_mode
| horner : normalize_mode

protected instance normalize_mode.inhabited : Inhabited normalize_mode :=
  { default := normalize_mode.horner }

/-- A `ring`-based normalization simplifier that rewrites ring expressions into the specified mode.

  * `raw` is the form that `ring` actually uses internally, with iterated applications of `horner`.
    Not very readable but useful if you don't want any postprocessing.
    This results in terms like `horner (horner (horner 3 y 1 0) x 2 1) x 1 (horner 1 y 1 0)`.
  * `horner` maintains the Horner form structure, but it unfolds the `horner` definition itself,
    and tries to otherwise minimize parentheses.
    This results in terms like `(3 * x ^ 2 * y + 1) * x + y`.
  * `SOP` means sum of products form, expanding everything to monomials.
    This results in terms like `3 * x ^ 3 * y + x + y`. -/
end ring


namespace interactive


/-- Tactic for solving equations in the language of *commutative* (semi)rings.
  This version of `ring` fails if the target is not an equality
  that is provable by the axioms of commutative (semi)rings. -/
/-- Parser for `ring`'s `mode` argument, which can only be the "keywords" `raw`, `horner` or `SOP`.
(Because these are not actually keywords we use a name parser and postprocess the result.) -/
/-- Tactic for solving equations in the language of *commutative* (semi)rings.
Attempts to prove the goal outright if there is no `at`
specifier and the target is an equality, but if this
fails it falls back to rewriting all ring expressions
into a normal form. When writing a normal form,
`ring SOP` will use sum-of-products form instead of horner form.
`ring!` will use a more aggressive reducibility setting to identify atoms.

Based on [Proving Equalities in a Commutative Ring Done Right
in Coq](http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf) by Benjamin Grégoire
and Assia Mahboubi.
-/
end Mathlib