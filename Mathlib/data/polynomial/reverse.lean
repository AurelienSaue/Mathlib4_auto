/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.erase_lead
import Mathlib.data.polynomial.degree.default
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : polynomial R` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.nat_degree * f(1/X)`.

The main result is that `reverse (f * g) = reverse (f) * reverse (g)`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

namespace polynomial


/-- If `i ≤ N`, then `rev_at_fun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `rev_at`.
-/
def rev_at_fun (N : ℕ) (i : ℕ) : ℕ :=
  ite (i ≤ N) (N - i) i

theorem rev_at_fun_invol {N : ℕ} {i : ℕ} : rev_at_fun N (rev_at_fun N i) = i := sorry

theorem rev_at_fun_inj {N : ℕ} : function.injective (rev_at_fun N) := sorry

/-- If `i ≤ N`, then `rev_at N i` returns `N - i`, otherwise it returns `i`.
Essentially, this embedding is only used for `i ≤ N`.
The advantage of `rev_at N i` over `N - i` is that `rev_at` is an involution.
-/
def rev_at (N : ℕ) : ℕ ↪ ℕ :=
  function.embedding.mk (fun (i : ℕ) => ite (i ≤ N) (N - i) i) rev_at_fun_inj

/-- We prefer to use the bundled `rev_at` over unbundled `rev_at_fun`. -/
@[simp] theorem rev_at_fun_eq (N : ℕ) (i : ℕ) : rev_at_fun N i = coe_fn (rev_at N) i :=
  rfl

@[simp] theorem rev_at_invol {N : ℕ} {i : ℕ} : coe_fn (rev_at N) (coe_fn (rev_at N) i) = i :=
  rev_at_fun_invol

@[simp] theorem rev_at_le {N : ℕ} {i : ℕ} (H : i ≤ N) : coe_fn (rev_at N) i = N - i :=
  if_pos H

theorem rev_at_add {N : ℕ} {O : ℕ} {n : ℕ} {o : ℕ} (hn : n ≤ N) (ho : o ≤ O) : coe_fn (rev_at (N + O)) (n + o) = coe_fn (rev_at N) n + coe_fn (rev_at O) o := sorry

/-- `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (rev_at N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`.  -/
def reflect {R : Type u_1} [semiring R] (N : ℕ) (f : polynomial R) : polynomial R :=
  finsupp.emb_domain (rev_at N) f

theorem reflect_support {R : Type u_1} [semiring R] (N : ℕ) (f : polynomial R) : finsupp.support (reflect N f) = finset.image (⇑(rev_at N)) (finsupp.support f) := sorry

@[simp] theorem coeff_reflect {R : Type u_1} [semiring R] (N : ℕ) (f : polynomial R) (i : ℕ) : coeff (reflect N f) i = coeff f (coe_fn (rev_at N) i) := sorry

@[simp] theorem reflect_zero {R : Type u_1} [semiring R] {N : ℕ} : reflect N 0 = 0 :=
  rfl

@[simp] theorem reflect_eq_zero_iff {R : Type u_1} [semiring R] {N : ℕ} {f : polynomial R} : reflect N f = 0 ↔ f = 0 := sorry

@[simp] theorem reflect_add {R : Type u_1} [semiring R] (f : polynomial R) (g : polynomial R) (N : ℕ) : reflect N (f + g) = reflect N f + reflect N g := sorry

@[simp] theorem reflect_C_mul {R : Type u_1} [semiring R] (f : polynomial R) (r : R) (N : ℕ) : reflect N (coe_fn C r * f) = coe_fn C r * reflect N f := sorry

@[simp] theorem reflect_C_mul_X_pow {R : Type u_1} [semiring R] (N : ℕ) (n : ℕ) {c : R} : reflect N (coe_fn C c * X ^ n) = coe_fn C c * X ^ coe_fn (rev_at N) n := sorry

@[simp] theorem reflect_monomial {R : Type u_1} [semiring R] (N : ℕ) (n : ℕ) : reflect N (X ^ n) = X ^ coe_fn (rev_at N) n := sorry

theorem reflect_mul_induction {R : Type u_1} [semiring R] (cf : ℕ) (cg : ℕ) (N : ℕ) (O : ℕ) (f : polynomial R) (g : polynomial R) : finset.card (finsupp.support f) ≤ Nat.succ cf →
  finset.card (finsupp.support g) ≤ Nat.succ cg →
    nat_degree f ≤ N → nat_degree g ≤ O → reflect (N + O) (f * g) = reflect N f * reflect O g := sorry

@[simp] theorem reflect_mul {R : Type u_1} [semiring R] (f : polynomial R) (g : polynomial R) {F : ℕ} {G : ℕ} (Ff : nat_degree f ≤ F) (Gg : nat_degree g ≤ G) : reflect (F + G) (f * g) = reflect F f * reflect G g :=
  reflect_mul_induction (finset.card (finsupp.support f)) (finset.card (finsupp.support g)) F G f g
    (nat.le_succ (finset.card (finsupp.support f))) (nat.le_succ (finset.card (finsupp.support g))) Ff Gg

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, reverse f = f (1/X) * X ^ f.nat_degree. -/
def reverse {R : Type u_1} [semiring R] (f : polynomial R) : polynomial R :=
  reflect (nat_degree f) f

@[simp] theorem reverse_zero {R : Type u_1} [semiring R] : reverse 0 = 0 :=
  rfl

theorem reverse_mul {R : Type u_1} [semiring R] {f : polynomial R} {g : polynomial R} (fg : leading_coeff f * leading_coeff g ≠ 0) : reverse (f * g) = reverse f * reverse g := sorry

@[simp] theorem reverse_mul_of_domain {R : Type u_1} [domain R] (f : polynomial R) (g : polynomial R) : reverse (f * g) = reverse f * reverse g := sorry

@[simp] theorem coeff_zero_reverse {R : Type u_1} [semiring R] (f : polynomial R) : coeff (reverse f) 0 = leading_coeff f := sorry

@[simp] theorem coeff_one_reverse {R : Type u_1} [semiring R] (f : polynomial R) : coeff (reverse f) 1 = next_coeff f := sorry

