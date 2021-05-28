/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.algebra.basic
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and aet `A` be an `R`-algebra.

* `1 : submodule R A`       : the R-submodule R of the R-algebra A
* `has_mul (submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `has_div (submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `submodule R A` is a semiring, and also an algebra over `set A`.

## Tags

multiplication of submodules, division of subodules, submodule semiring
-/

namespace submodule


/-- `1 : submodule R A` is the submodule R of A. -/
protected instance has_one {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] : HasOne (submodule R A) :=
  { one := map (alg_hom.to_linear_map (algebra.of_id R A)) ⊤ }

theorem one_eq_map_top {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] : 1 = map (alg_hom.to_linear_map (algebra.of_id R A)) ⊤ :=
  rfl

theorem one_eq_span {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] : 1 = span R (singleton 1) := sorry

theorem one_le {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {P : submodule R A} : 1 ≤ P ↔ 1 ∈ P := sorry

/-- Multiplication of sub-R-modules of an R-algebra A. The submodule `M * N` is the
smallest R-submodule of `A` containing the elements `m * n` for `m ∈ M` and `n ∈ N`. -/
protected instance has_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] : Mul (submodule R A) :=
  { mul := fun (M N : submodule R A) => supr fun (s : ↥M) => map (coe_fn (algebra.lmul R A) (subtype.val s)) N }

theorem mul_mem_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {m : A} {n : A} (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  le_supr (fun (s : ↥M) => map (coe_fn (algebra.lmul R A) (subtype.val s)) N) { val := m, property := hm } (m * n)
    (Exists.intro n { left := hn, right := rfl })

theorem mul_le {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {P : submodule R A} : M * N ≤ P ↔ ∀ (m : A), m ∈ M → ∀ (n : A), n ∈ N → m * n ∈ P := sorry

protected theorem mul_induction_on {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {C : A → Prop} {r : A} (hr : r ∈ M * N) (hm : ∀ (m : A), m ∈ M → ∀ (n : A), n ∈ N → C (m * n)) (h0 : C 0) (ha : ∀ (x y : A), C x → C y → C (x + y)) (hs : ∀ (r : R) (x : A), C x → C (r • x)) : C r :=
  iff.mpr mul_le hm r hr

theorem span_mul_span (R : Type u) [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (S : set A) (T : set A) : span R S * span R T = span R (S * T) := sorry

protected theorem mul_assoc {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) (N : submodule R A) (P : submodule R A) : M * N * P = M * (N * P) := sorry

@[simp] theorem mul_bot {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) : M * ⊥ = ⊥ := sorry

@[simp] theorem bot_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) : ⊥ * M = ⊥ := sorry

@[simp] protected theorem one_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) : 1 * M = M := sorry

@[simp] protected theorem mul_one {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) : M * 1 = M := sorry

theorem mul_le_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {P : submodule R A} {Q : submodule R A} (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q :=
  iff.mpr mul_le fun (m : A) (hm : m ∈ M) (n : A) (hn : n ∈ N) => mul_mem_mul (hmp hm) (hnq hn)

theorem mul_le_mul_left {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {P : submodule R A} (h : M ≤ N) : M * P ≤ N * P :=
  mul_le_mul h (le_refl P)

theorem mul_le_mul_right {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {P : submodule R A} (h : N ≤ P) : M * N ≤ M * P :=
  mul_le_mul (le_refl M) h

theorem mul_sup {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) (N : submodule R A) (P : submodule R A) : M * (N ⊔ P) = M * N ⊔ M * P := sorry

theorem sup_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) (N : submodule R A) (P : submodule R A) : (M ⊔ N) * P = M * P ⊔ N * P := sorry

theorem mul_subset_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) (N : submodule R A) : ↑M * ↑N ⊆ ↑(M * N) := sorry

theorem map_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) (N : submodule R A) {A' : Type u_1} [semiring A'] [algebra R A'] (f : alg_hom R A A') : map (alg_hom.to_linear_map f) (M * N) = map (alg_hom.to_linear_map f) M * map (alg_hom.to_linear_map f) N := sorry

theorem mem_span_mul_finite_of_mem_span_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {S : set A} {S' : set A} {x : A} (hx : x ∈ span R (S * S')) : ∃ (T : finset A), ∃ (T' : finset A), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span R (↑T * ↑T') := sorry

theorem mem_span_mul_finite_of_mem_mul {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] {P : submodule R A} {Q : submodule R A} {x : A} (hx : x ∈ P * Q) : ∃ (T : finset A), ∃ (T' : finset A), ↑T ⊆ ↑P ∧ ↑T' ⊆ ↑Q ∧ x ∈ span R (↑T * ↑T') := sorry

/-- Sub-R-modules of an R-algebra form a semiring. -/
protected instance semiring {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] : semiring (submodule R A) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry Mul.mul submodule.mul_assoc 1
    submodule.one_mul submodule.mul_one bot_mul mul_bot mul_sup sup_mul

theorem pow_subset_pow {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] (M : submodule R A) {n : ℕ} : ↑M ^ n ⊆ ↑(M ^ n) := sorry

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
def span.ring_hom {R : Type u} [comm_semiring R] {A : Type v} [semiring A] [algebra R A] : set.set_semiring A →+* submodule R A :=
  ring_hom.mk (span R) sorry sorry sorry sorry

theorem mul_mem_mul_rev {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {M : submodule R A} {N : submodule R A} {m : A} {n : A} (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N :=
  mul_comm m n ▸ mul_mem_mul hm hn

protected theorem mul_comm {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] (M : submodule R A) (N : submodule R A) : M * N = N * M :=
  le_antisymm (iff.mpr mul_le fun (r : A) (hrm : r ∈ M) (s : A) (hsn : s ∈ N) => mul_mem_mul_rev hsn hrm)
    (iff.mpr mul_le fun (r : A) (hrn : r ∈ N) (s : A) (hsm : s ∈ M) => mul_mem_mul_rev hsm hrn)

/-- Sub-R-modules of an R-algebra A form a semiring. -/
protected instance comm_semiring {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] : comm_semiring (submodule R A) :=
  comm_semiring.mk semiring.add sorry semiring.zero sorry sorry sorry semiring.mul sorry semiring.one sorry sorry sorry
    sorry sorry sorry submodule.mul_comm

/-- R-submodules of the R-algebra A are a module over `set A`. -/
protected instance semimodule_set (R : Type u) [comm_semiring R] (A : Type v) [comm_semiring A] [algebra R A] : semimodule (set.set_semiring A) (submodule R A) :=
  semimodule.mk sorry sorry

theorem smul_def {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {s : set.set_semiring A} {P : submodule R A} : s • P = span R s * P :=
  rfl

theorem smul_le_smul {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {s : set.set_semiring A} {t : set.set_semiring A} {M : submodule R A} {N : submodule R A} (h₁ : set.set_semiring.down s ≤ set.set_semiring.down t) (h₂ : M ≤ N) : s • M ≤ t • N :=
  mul_le_mul (span_mono h₁) h₂

theorem smul_singleton {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] (a : A) (M : submodule R A) : set.up (singleton a) • M = map (algebra.lmul_left R a) M := sorry

/-- The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_forall_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
protected instance has_div {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] : Div (submodule R A) :=
  { div := fun (I J : submodule R A) => mk (set_of fun (x : A) => ∀ (y : A), y ∈ J → x * y ∈ I) sorry sorry sorry }

theorem mem_div_iff_forall_mul_mem {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {x : A} {I : submodule R A} {J : submodule R A} : x ∈ I / J ↔ ∀ (y : A), y ∈ J → x * y ∈ I :=
  iff.refl (x ∈ I / J)

theorem mem_div_iff_smul_subset {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {x : A} {I : submodule R A} {J : submodule R A} : x ∈ I / J ↔ x • ↑J ⊆ ↑I := sorry

theorem le_div_iff {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {I : submodule R A} {J : submodule R A} {K : submodule R A} : I ≤ J / K ↔ ∀ (x : A), x ∈ I → ∀ (z : A), z ∈ K → x * z ∈ J :=
  iff.refl (I ≤ J / K)

theorem le_div_iff_mul_le {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {I : submodule R A} {J : submodule R A} {K : submodule R A} : I ≤ J / K ↔ I * K ≤ J :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ≤ J / K ↔ I * K ≤ J)) (propext le_div_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((∀ (x : A), x ∈ I → ∀ (z : A), z ∈ K → x * z ∈ J) ↔ I * K ≤ J)) (propext mul_le)))
      (iff.refl (∀ (x : A), x ∈ I → ∀ (z : A), z ∈ K → x * z ∈ J)))

@[simp] theorem one_le_one_div {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {I : submodule R A} : 1 ≤ 1 / I ↔ I ≤ 1 := sorry

theorem le_self_mul_one_div {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {I : submodule R A} (hI : I ≤ 1) : I ≤ I * (1 / I) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ≤ I * (1 / I))) (Eq.symm (mul_one I))))
    (mul_le_mul_right (iff.mpr one_le_one_div hI))

theorem mul_one_div_le_one {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {I : submodule R A} : I * (1 / I) ≤ 1 := sorry

@[simp] theorem map_div {R : Type u} [comm_semiring R] {A : Type v} [comm_semiring A] [algebra R A] {B : Type u_1} [comm_ring B] [algebra R B] (I : submodule R A) (J : submodule R A) (h : alg_equiv R A B) : map (alg_equiv.to_linear_map h) (I / J) = map (alg_equiv.to_linear_map h) I / map (alg_equiv.to_linear_map h) J := sorry

