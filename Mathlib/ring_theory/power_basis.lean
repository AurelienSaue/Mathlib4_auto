/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.field_theory.adjoin
import Mathlib.field_theory.minpoly
import Mathlib.ring_theory.adjoin
import Mathlib.ring_theory.adjoin_root
import Mathlib.ring_theory.algebraic
import Mathlib.PostPort

universes u_8 u_9 l u_2 u_6 u_1 u_4 u_7 

namespace Mathlib

/-!
# Power basis

This file defines a structure `power_basis R S`, giving a basis of the
`R`-algebra `S` as a finite list of powers `1, x, ..., x^n`.
There are also constructors for `power_basis` when adjoining an algebraic
element to a ring/field.

## Definitions

* `power_basis R A`: a structure containing an `x` and an `n` such that
`1, x, ..., x^n` is a basis for the `R`-algebra `A` (viewed as an `R`-module).

* `findim (hf : f ≠ 0) : finite_dimensional.findim K (adjoin_root f) = f.nat_degree`,
  the dimension of `adjoin_root f` equals the degree of `f`

* `power_basis.lift (pb : power_basis R S)`: if `y : S'` satisfies the same
  equations as `pb.gen`, this is the map `S →ₐ[R] S'` sending `pb.gen` to `y`

* `power_basis.equiv`: if two power bases satisfy the same equations, they are
  equivalent as algebras

## Implementation notes

Throughout this file, `R`, `S`, ... are `comm_ring`s, `A`, `B`, ... are
`integral_domain`s and `K`, `L`, ... are `field`s.
`S` is an `R`-algebra, `B` is an `A`-algebra, `L` is a `K`-algebra.

## Tags

power basis, powerbasis

-/

/-- `pb : power_basis R S` states that `1, pb.gen, ..., pb.gen ^ (pb.dim - 1)`
is a basis for the `R`-algebra `S` (viewed as `R`-module).

This is a structure, not a class, since the same algebra can have many power bases.
For the common case where `S` is defined by adjoining an integral element to `R`,
the canonical power basis is given by `{algebra,intermediate_field}.adjoin.power_basis`.
-/
structure power_basis (R : Type u_8) (S : Type u_9) [comm_ring R] [ring S] [algebra R S] 
where
  gen : S
  dim : ℕ
  is_basis : is_basis R fun (i : fin dim) => gen ^ ↑i

namespace power_basis


/-- Cannot be an instance because `power_basis` cannot be a class. -/
theorem finite_dimensional {S : Type u_2} [comm_ring S] {K : Type u_6} [field K] [algebra K S] (pb : power_basis K S) : finite_dimensional K S :=
  finite_dimensional.of_fintype_basis (is_basis pb)

theorem findim {S : Type u_2} [comm_ring S] {K : Type u_6} [field K] [algebra K S] (pb : power_basis K S) : finite_dimensional.findim K S = dim pb := sorry

/-- TODO: this mixes `polynomial` and `finsupp`, we should hide this behind a
new function `polynomial.of_finsupp`. -/
theorem polynomial.mem_supported_range {R : Type u_1} [comm_ring R] {f : polynomial R} {d : ℕ} : f ∈ finsupp.supported R R ↑(finset.range d) ↔ polynomial.degree f < ↑d := sorry

theorem mem_span_pow' {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [algebra R S] {x : S} {y : S} {d : ℕ} : y ∈ submodule.span R (set.range fun (i : fin d) => x ^ ↑i) ↔
  ∃ (f : polynomial R), polynomial.degree f < ↑d ∧ y = coe_fn (polynomial.aeval x) f := sorry

theorem mem_span_pow {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [algebra R S] {x : S} {y : S} {d : ℕ} (hd : d ≠ 0) : y ∈ submodule.span R (set.range fun (i : fin d) => x ^ ↑i) ↔
  ∃ (f : polynomial R), polynomial.nat_degree f < d ∧ y = coe_fn (polynomial.aeval x) f := sorry

theorem dim_ne_zero {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [algebra R S] [nontrivial S] (pb : power_basis R S) : dim pb ≠ 0 := sorry

theorem exists_eq_aeval {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [algebra R S] [nontrivial S] (pb : power_basis R S) (y : S) : ∃ (f : polynomial R), polynomial.nat_degree f < dim pb ∧ y = coe_fn (polynomial.aeval (gen pb)) f :=
  iff.mp (mem_span_pow (dim_ne_zero pb)) (is_basis.mem_span (is_basis pb) y)

/-- `pb.minpoly_gen` is a minimal polynomial for `pb.gen`.

If `A` is not a field, it might not necessarily be *the* minimal polynomial,
however `nat_degree_minpoly` shows its degree is indeed minimal.
-/
def minpoly_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (pb : power_basis A S) : polynomial A :=
  polynomial.X ^ dim pb -
    finset.sum finset.univ
      fun (i : fin (dim pb)) =>
        coe_fn polynomial.C (coe_fn (coe_fn (is_basis.repr sorry) (gen pb ^ dim pb)) i) * polynomial.X ^ ↑i

@[simp] theorem nat_degree_minpoly_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (pb : power_basis A S) : polynomial.nat_degree (minpoly_gen pb) = dim pb := sorry

theorem minpoly_gen_monic {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (pb : power_basis A S) : polynomial.monic (minpoly_gen pb) := sorry

@[simp] theorem aeval_minpoly_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (pb : power_basis A S) : coe_fn (polynomial.aeval (gen pb)) (minpoly_gen pb) = 0 := sorry

theorem is_integral_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (pb : power_basis A S) : is_integral A (gen pb) :=
  Exists.intro (minpoly_gen pb) { left := minpoly_gen_monic pb, right := aeval_minpoly_gen pb }

theorem dim_le_nat_degree_of_root {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (h : power_basis A S) {p : polynomial A} (ne_zero : p ≠ 0) (root : coe_fn (polynomial.aeval (gen h)) p = 0) : dim h ≤ polynomial.nat_degree p := sorry

@[simp] theorem nat_degree_minpoly {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] (pb : power_basis A S) : polynomial.nat_degree (minpoly A (gen pb)) = dim pb := sorry

theorem nat_degree_lt_nat_degree {R : Type u_1} [comm_ring R] {p : polynomial R} {q : polynomial R} (hp : p ≠ 0) (hpq : polynomial.degree p < polynomial.degree q) : polynomial.nat_degree p < polynomial.nat_degree q := sorry

theorem constr_pow_aeval {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] (pb : power_basis A S) {y : S'} (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) (f : polynomial A) : coe_fn (is_basis.constr (is_basis pb) fun (i : fin (dim pb)) => y ^ ↑i) (coe_fn (polynomial.aeval (gen pb)) f) =
  coe_fn (polynomial.aeval y) f := sorry

theorem constr_pow_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] (pb : power_basis A S) {y : S'} (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) : coe_fn (is_basis.constr (is_basis pb) fun (i : fin (dim pb)) => y ^ ↑i) (gen pb) = y := sorry

theorem constr_pow_algebra_map {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] (pb : power_basis A S) {y : S'} (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) (x : A) : coe_fn (is_basis.constr (is_basis pb) fun (i : fin (dim pb)) => y ^ ↑i) (coe_fn (algebra_map A S) x) =
  coe_fn (algebra_map A S') x := sorry

theorem constr_pow_mul {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] (pb : power_basis A S) {y : S'} (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) (x : S) (x' : S) : coe_fn (is_basis.constr (is_basis pb) fun (i : fin (dim pb)) => y ^ ↑i) (x * x') =
  coe_fn (is_basis.constr (is_basis pb) fun (i : fin (dim pb)) => y ^ ↑i) x *
    coe_fn (is_basis.constr (is_basis pb) fun (i : fin (dim pb)) => y ^ ↑i) x' := sorry

/-- `pb.lift y hy` is the algebra map sending `pb.gen` to `y`,
where `hy` states the higher powers of `y` are the same as the higher powers of `pb.gen`. -/
def lift {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] (pb : power_basis A S) (y : S') (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) : alg_hom A S S' :=
  alg_hom.mk (linear_map.to_fun (is_basis.constr sorry fun (i : fin (dim pb)) => y ^ ↑i)) sorry (constr_pow_mul pb hy)
    sorry sorry (constr_pow_algebra_map pb hy)

@[simp] theorem lift_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] (pb : power_basis A S) (y : S') (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) : coe_fn (lift pb y hy) (gen pb) = y :=
  constr_pow_gen pb hy

@[simp] theorem lift_aeval {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] (pb : power_basis A S) (y : S') (hy : coe_fn (polynomial.aeval y) (minpoly A (gen pb)) = 0) (f : polynomial A) : coe_fn (lift pb y hy) (coe_fn (polynomial.aeval (gen pb)) f) = coe_fn (polynomial.aeval y) f :=
  constr_pow_aeval pb hy f

/-- `pb.equiv pb' h` is an equivalence of algebras with the same power basis. -/
def equiv {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] [nontrivial S'] (pb : power_basis A S) (pb' : power_basis A S') (h : minpoly A (gen pb) = minpoly A (gen pb')) : alg_equiv A S S' :=
  alg_equiv.of_alg_hom (lift pb (gen pb') sorry) (lift pb' (gen pb) sorry) sorry sorry

@[simp] theorem equiv_aeval {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] [nontrivial S'] (pb : power_basis A S) (pb' : power_basis A S') (h : minpoly A (gen pb) = minpoly A (gen pb')) (f : polynomial A) : coe_fn (equiv pb pb' h) (coe_fn (polynomial.aeval (gen pb)) f) = coe_fn (polynomial.aeval (gen pb')) f :=
  lift_aeval pb (gen pb') (Eq.symm h ▸ minpoly.aeval A (gen pb')) f

@[simp] theorem equiv_gen {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] [nontrivial S'] (pb : power_basis A S) (pb' : power_basis A S') (h : minpoly A (gen pb) = minpoly A (gen pb')) : coe_fn (equiv pb pb' h) (gen pb) = gen pb' :=
  lift_gen pb (gen pb') (Eq.symm h ▸ minpoly.aeval A (gen pb'))

@[simp] theorem equiv_symm {S : Type u_2} [comm_ring S] {A : Type u_4} [integral_domain A] [algebra A S] {S' : Type u_8} [comm_ring S'] [algebra A S'] [nontrivial S] [nontrivial S'] (pb : power_basis A S) (pb' : power_basis A S') (h : minpoly A (gen pb) = minpoly A (gen pb')) : alg_equiv.symm (equiv pb pb' h) = equiv pb' pb (Eq.symm h) :=
  rfl

end power_basis


namespace algebra


theorem mem_span_power_basis {R : Type u_1} {S : Type u_2} [comm_ring R] [comm_ring S] [algebra R S] [nontrivial R] {x : S} {y : S} (hx : is_integral R x) (hy : ∃ (f : polynomial R), y = coe_fn (polynomial.aeval x) f) : y ∈ submodule.span R (set.range fun (i : fin (polynomial.nat_degree (minpoly R x))) => x ^ ↑i) := sorry

theorem linear_independent_power_basis {S : Type u_2} [comm_ring S] {K : Type u_6} [field K] [algebra K S] {x : S} (hx : is_integral K x) : linear_independent K fun (i : fin (polynomial.nat_degree (minpoly K x))) => x ^ ↑i := sorry

theorem power_basis_is_basis {S : Type u_2} [comm_ring S] {K : Type u_6} [field K] [algebra K S] {x : S} (hx : is_integral K x) : is_basis K
  fun (i : fin (polynomial.nat_degree (minpoly K x))) =>
    { val := x, property := subset_adjoin (set.mem_singleton x) } ^ ↑i := sorry

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K[x]`,
where `d` is the degree of the minimal polynomial of `x`. -/
def adjoin.power_basis {S : Type u_2} [comm_ring S] {K : Type u_6} [field K] [algebra K S] {x : S} (hx : is_integral K x) : power_basis K ↥(adjoin K (singleton x)) :=
  power_basis.mk { val := x, property := sorry } (polynomial.nat_degree (minpoly K x)) (power_basis_is_basis hx)

end algebra


namespace adjoin_root


theorem power_basis_is_basis {K : Type u_6} [field K] {f : polynomial K} (hf : f ≠ 0) : is_basis K fun (i : fin (polynomial.nat_degree f)) => root f ^ subtype.val i := sorry

/-- The power basis `1, root f, ..., root f ^ (d - 1)` for `adjoin_root f`,
where `f` is an irreducible polynomial over a field of degree `d`. -/
def power_basis {K : Type u_6} [field K] {f : polynomial K} (hf : f ≠ 0) : power_basis K (adjoin_root f) :=
  power_basis.mk (root f) (polynomial.nat_degree f) (power_basis_is_basis hf)

end adjoin_root


namespace intermediate_field


theorem power_basis_is_basis {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] {x : L} (hx : is_integral K x) : is_basis K fun (i : fin (polynomial.nat_degree (minpoly K x))) => adjoin_simple.gen K x ^ ↑i := sorry

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
def adjoin.power_basis {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] {x : L} (hx : is_integral K x) : power_basis K ↥(adjoin K (insert.insert ∅ x)) :=
  power_basis.mk (adjoin_simple.gen K x) (polynomial.nat_degree (minpoly K x)) (power_basis_is_basis hx)

@[simp] theorem adjoin.power_basis.gen_eq {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] {x : L} (hx : is_integral K x) : power_basis.gen (adjoin.power_basis hx) = adjoin_simple.gen K x :=
  rfl

theorem adjoin.finite_dimensional {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] {x : L} (hx : is_integral K x) : finite_dimensional K ↥(adjoin K (insert.insert ∅ x)) :=
  power_basis.finite_dimensional (adjoin.power_basis hx)

theorem adjoin.findim {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] {x : L} (hx : is_integral K x) : finite_dimensional.findim K ↥(adjoin K (insert.insert ∅ x)) = polynomial.nat_degree (minpoly K x) := sorry

end intermediate_field


namespace power_basis


/-- `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
def equiv_adjoin_simple {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] (pb : power_basis K L) : alg_equiv K (↥(intermediate_field.adjoin K (intermediate_field.insert.insert ∅ (gen pb)))) L :=
  equiv (intermediate_field.adjoin.power_basis sorry) pb sorry

@[simp] theorem equiv_adjoin_simple_aeval {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] (pb : power_basis K L) (f : polynomial K) : coe_fn (equiv_adjoin_simple pb) (coe_fn (polynomial.aeval (intermediate_field.adjoin_simple.gen K (gen pb))) f) =
  coe_fn (polynomial.aeval (gen pb)) f :=
  equiv_aeval (intermediate_field.adjoin.power_basis (equiv_adjoin_simple._proof_3 pb)) pb
    (equiv_adjoin_simple._proof_4 pb) f

@[simp] theorem equiv_adjoin_simple_gen {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] (pb : power_basis K L) : coe_fn (equiv_adjoin_simple pb) (intermediate_field.adjoin_simple.gen K (gen pb)) = gen pb :=
  equiv_gen (intermediate_field.adjoin.power_basis (equiv_adjoin_simple._proof_3 pb)) pb (equiv_adjoin_simple._proof_4 pb)

@[simp] theorem equiv_adjoin_simple_symm_aeval {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] (pb : power_basis K L) (f : polynomial K) : coe_fn (alg_equiv.symm (equiv_adjoin_simple pb)) (coe_fn (polynomial.aeval (gen pb)) f) =
  coe_fn (polynomial.aeval (intermediate_field.adjoin_simple.gen K (gen pb))) f := sorry

@[simp] theorem equiv_adjoin_simple_symm_gen {K : Type u_6} {L : Type u_7} [field K] [field L] [algebra K L] (pb : power_basis K L) : coe_fn (alg_equiv.symm (equiv_adjoin_simple pb)) (gen pb) = intermediate_field.adjoin_simple.gen K (gen pb) := sorry

