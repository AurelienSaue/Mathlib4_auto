/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u l v w 

namespace Mathlib

/-!
# Invariant basis number property

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

## Main definitions

`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial commutative ring has the invariant basis number property.

## Future work

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or prividing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number

## Tags

free module, rank, invariant basis number, IBN

-/

/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class invariant_basis_number (R : Type u) [ring R] 
where
  eq_of_fin_equiv : ∀ {n m : ℕ}, linear_equiv R (fin n → R) (fin m → R) → n = m

theorem eq_of_fin_equiv (R : Type u) [ring R] [invariant_basis_number R] {n : ℕ} {m : ℕ} : linear_equiv R (fin n → R) (fin m → R) → n = m :=
  invariant_basis_number.eq_of_fin_equiv

theorem nontrivial_of_invariant_basis_number (R : Type u) [ring R] [invariant_basis_number R] : nontrivial R := sorry

/-- A field has invariant basis number. This will be superseded below by the fact that any nonzero
    commutative ring has invariant basis number. -/
theorem invariant_basis_number_field {K : Type u} [field K] : invariant_basis_number K := sorry

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `ideal.pi_quot_equiv` and is located in the file `ring_theory/ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
/-- Nontrivial commutative rings have the invariant basis number property. -/
protected instance invariant_basis_number_of_nontrivial_of_comm_ring {R : Type u} [comm_ring R] [nontrivial R] : invariant_basis_number R :=
  invariant_basis_number.mk fun (n m : ℕ) (e : linear_equiv R (fin n → R) (fin m → R)) => sorry

