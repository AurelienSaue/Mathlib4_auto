/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Devon Tuma
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.ideal.operations
import Mathlib.ring_theory.polynomial.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical to ideals of `R`,
by letting the radical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a commutative ring, and `I` be an ideal of `R`

* `jacobson I` is the jacobson radical, i.e. the infimum of all maximal ideals containing I.

* `is_local I` is the proposition that the jacobson radical of `I` is itself a maximal ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the jacobson of I

* `is_local_of_is_maximal_radical`: if the radical of I is maximal then so is the jacobson radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/

namespace ideal


/-- The Jacobson radical of `I` is the infimum of all maximal ideals containing `I`. -/
def jacobson {R : Type u} [comm_ring R] (I : ideal R) : ideal R :=
  Inf (set_of fun (J : ideal R) => I ≤ J ∧ is_maximal J)

theorem le_jacobson {R : Type u} [comm_ring R] {I : ideal R} : I ≤ jacobson I :=
  fun (x : R) (hx : x ∈ I) =>
    iff.mpr mem_Inf fun (J : ideal R) (hJ : J ∈ set_of fun (J : ideal R) => I ≤ J ∧ is_maximal J) => and.left hJ x hx

@[simp] theorem jacobson_idem {R : Type u} [comm_ring R] {I : ideal R} : jacobson (jacobson I) = jacobson I := sorry

theorem radical_le_jacobson {R : Type u} [comm_ring R] {I : ideal R} : radical I ≤ jacobson I :=
  le_Inf
    fun (J : ideal R) (hJ : J ∈ set_of fun (J : ideal R) => I ≤ J ∧ is_maximal J) =>
      Eq.symm (radical_eq_Inf I) ▸ Inf_le { left := and.left hJ, right := is_maximal.is_prime (and.right hJ) }

theorem eq_radical_of_eq_jacobson {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = I → radical I = I :=
  fun (h : jacobson I = I) => le_antisymm (le_trans radical_le_jacobson (le_of_eq h)) le_radical

@[simp] theorem jacobson_top {R : Type u} [comm_ring R] : jacobson ⊤ = ⊤ :=
  iff.mpr eq_top_iff le_jacobson

@[simp] theorem jacobson_eq_top_iff {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = ⊤ ↔ I = ⊤ := sorry

theorem jacobson_eq_bot {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = ⊥ → I = ⊥ :=
  fun (h : jacobson I = ⊥) => iff.mpr eq_bot_iff (h ▸ le_jacobson)

theorem jacobson_eq_self_of_is_maximal {R : Type u} [comm_ring R] {I : ideal R} [H : is_maximal I] : jacobson I = I :=
  le_antisymm (Inf_le { left := le_of_eq rfl, right := H }) le_jacobson

protected instance jacobson.is_maximal {R : Type u} [comm_ring R] {I : ideal R} [H : is_maximal I] : is_maximal (jacobson I) :=
  { left := fun (htop : jacobson I = ⊤) => and.left H (iff.mp jacobson_eq_top_iff htop),
    right := fun (J : ideal R) (hJ : jacobson I < J) => and.right H J (lt_of_le_of_lt le_jacobson hJ) }

theorem mem_jacobson_iff {R : Type u} [comm_ring R] {I : ideal R} {x : R} : x ∈ jacobson I ↔ ∀ (y : R), ∃ (z : R), x * y * z + z - 1 ∈ I := sorry

/-- An ideal equals its Jacobson radical iff it is the intersection of a set of maximal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
theorem eq_jacobson_iff_Inf_maximal {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = I ↔ ∃ (M : set (ideal R)), (∀ (J : ideal R), J ∈ M → is_maximal J ∨ J = ⊤) ∧ I = Inf M := sorry

theorem eq_jacobson_iff_Inf_maximal' {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = I ↔ ∃ (M : set (ideal R)), (∀ (J : ideal R), J ∈ M → ∀ (K : ideal R), J < K → K = ⊤) ∧ I = Inf M := sorry

/-- An ideal `I` equals its Jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
theorem eq_jacobson_iff_not_mem {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = I ↔ ∀ (x : R), ¬x ∈ I → ∃ (M : ideal R), (I ≤ M ∧ is_maximal M) ∧ ¬x ∈ M := sorry

theorem map_jacobson_of_surjective {R : Type u} [comm_ring R] {I : ideal R} {S : Type v} [comm_ring S] {f : R →+* S} (hf : function.surjective ⇑f) : ring_hom.ker f ≤ I → map f (jacobson I) = jacobson (map f I) := sorry

theorem map_jacobson_of_bijective {R : Type u} [comm_ring R] {I : ideal R} {S : Type v} [comm_ring S] {f : R →+* S} (hf : function.bijective ⇑f) : map f (jacobson I) = jacobson (map f I) :=
  map_jacobson_of_surjective (and.right hf)
    (le_trans (le_of_eq (iff.mp (ring_hom.injective_iff_ker_eq_bot f) (and.left hf))) bot_le)

theorem comap_jacobson {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] {f : R →+* S} {K : ideal S} : comap f (jacobson K) = Inf (comap f '' set_of fun (J : ideal S) => K ≤ J ∧ is_maximal J) :=
  trans (comap_Inf' f (set_of fun (J : ideal S) => K ≤ J ∧ is_maximal J)) (Eq.symm Inf_eq_infi)

theorem comap_jacobson_of_surjective {R : Type u} [comm_ring R] {S : Type v} [comm_ring S] {f : R →+* S} (hf : function.surjective ⇑f) {K : ideal S} : comap f (jacobson K) = jacobson (comap f K) := sorry

theorem mem_jacobson_bot {R : Type u} [comm_ring R] {x : R} : x ∈ jacobson ⊥ ↔ ∀ (y : R), is_unit (x * y + 1) := sorry

/-- An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal -/
theorem jacobson_eq_iff_jacobson_quotient_eq_bot {R : Type u} [comm_ring R] {I : ideal R} : jacobson I = I ↔ jacobson ⊥ = ⊥ := sorry

/-- The standard radical and Jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide -/
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot {R : Type u} [comm_ring R] {I : ideal R} : radical I = jacobson I ↔ radical ⊥ = jacobson ⊥ := sorry

theorem jacobson_mono {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} : I ≤ J → jacobson I ≤ jacobson J := sorry

theorem jacobson_radical_eq_jacobson {R : Type u} [comm_ring R] {I : ideal R} : jacobson (radical I) = jacobson I := sorry

theorem jacobson_bot_polynomial_le_Inf_map_maximal {R : Type u} [comm_ring R] : jacobson ⊥ ≤ Inf (map polynomial.C '' set_of fun (J : ideal R) => is_maximal J) := sorry

theorem jacobson_bot_polynomial_of_jacobson_bot {R : Type u} [comm_ring R] (h : jacobson ⊥ = ⊥) : jacobson ⊥ = ⊥ := sorry

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
def is_local {R : Type u} [comm_ring R] (I : ideal R) :=
  is_maximal (jacobson I)

theorem is_local_of_is_maximal_radical {R : Type u} [comm_ring R] {I : ideal R} (hi : is_maximal (radical I)) : is_local I := sorry

theorem is_local.le_jacobson {R : Type u} [comm_ring R] {I : ideal R} {J : ideal R} (hi : is_local I) (hij : I ≤ J) (hj : J ≠ ⊤) : J ≤ jacobson I := sorry

theorem is_local.mem_jacobson_or_exists_inv {R : Type u} [comm_ring R] {I : ideal R} (hi : is_local I) (x : R) : x ∈ jacobson I ∨ ∃ (y : R), y * x - 1 ∈ I := sorry

theorem is_primary_of_is_maximal_radical {R : Type u} [comm_ring R] {I : ideal R} (hi : is_maximal (radical I)) : is_primary I := sorry

