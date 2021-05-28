/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.witt_vector.init_tail
import Mathlib.tactic.equiv_rw
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!

# Truncated Witt vectors

The ring of truncated Witt vectors (of length `n`) is a quotient of the ring of Witt vectors.
It retains the first `n` coefficients of each Witt vector.
In this file, we set up the basic quotient API for this ring.

The ring of Witt vectors is the projective limit of all the rings of truncated Witt vectors.

## Main declarations

- `truncated_witt_vector`: the underlying type of the ring of truncated Witt vectors
- `truncated_witt_vector.comm_ring`: the ring structure on truncated Witt vectors
- `witt_vector.truncate`: the quotient homomorphism that truncates a Witt vector,
  to obtain a truncated Witt vector
- `truncated_witt_vector.truncate`: the homomorphism that truncates
  a truncated Witt vector of length `n` to one of length `m` (for some `m ≤ n`)
- `witt_vector.lift`: the unique ring homomorphism into the ring of Witt vectors
  that is compatible with a family of ring homomorphisms to the truncated Witt vectors:
  this realizes the ring of Witt vectors as projective limit of the rings of truncated Witt vectors

-/

/--
A truncated Witt vector over `R` is a vector of elements of `R`,
i.e., the first `n` coefficients of a Witt vector.
We will define operations on this type that are compatible with the (untruncated) Witt
vector operations.

`truncated_witt_vector p n R` takes a parameter `p : ℕ` that is not used in the definition.
In practice, this number `p` is assumed to be a prime number,
and under this assumption we construct a ring structure on `truncated_witt_vector p n R`.
(`truncated_witt_vector p₁ n R` and `truncated_witt_vector p₂ n R` are definitionally
equal as types but will have different ring operations.)
-/
def truncated_witt_vector (p : ℕ) (n : ℕ) (R : Type u_1)  :=
  fin n → R

protected instance truncated_witt_vector.inhabited (p : ℕ) (n : ℕ) (R : Type u_1) [Inhabited R] : Inhabited (truncated_witt_vector p n R) :=
  { default := fun (_x : fin n) => Inhabited.default }

namespace truncated_witt_vector


/-- Create a `truncated_witt_vector` from a vector `x`. -/
def mk (p : ℕ) {n : ℕ} {R : Type u_1} (x : fin n → R) : truncated_witt_vector p n R :=
  x

/-- `x.coeff i` is the `i`th entry of `x`. -/
def coeff {p : ℕ} {n : ℕ} {R : Type u_1} (i : fin n) (x : truncated_witt_vector p n R) : R :=
  x i

theorem ext {p : ℕ} {n : ℕ} {R : Type u_1} {x : truncated_witt_vector p n R} {y : truncated_witt_vector p n R} (h : ∀ (i : fin n), coeff i x = coeff i y) : x = y :=
  funext h

theorem ext_iff {p : ℕ} {n : ℕ} {R : Type u_1} {x : truncated_witt_vector p n R} {y : truncated_witt_vector p n R} : x = y ↔ ∀ (i : fin n), coeff i x = coeff i y :=
  { mp :=
      fun (h : x = y) (i : fin n) => eq.mpr (id (Eq._oldrec (Eq.refl (coeff i x = coeff i y)) h)) (Eq.refl (coeff i y)),
    mpr := ext }

@[simp] theorem coeff_mk {p : ℕ} {n : ℕ} {R : Type u_1} (x : fin n → R) (i : fin n) : coeff i (mk p x) = x i :=
  rfl

@[simp] theorem mk_coeff {p : ℕ} {n : ℕ} {R : Type u_1} (x : truncated_witt_vector p n R) : (mk p fun (i : fin n) => coeff i x) = x := sorry

/--
We can turn a truncated Witt vector `x` into a Witt vector
by setting all coefficients after `x` to be 0.
-/
def out {p : ℕ} {n : ℕ} {R : Type u_1} [comm_ring R] (x : truncated_witt_vector p n R) : witt_vector p R :=
  witt_vector.mk p
    fun (i : ℕ) => dite (i < n) (fun (h : i < n) => coeff { val := i, property := h } x) fun (h : ¬i < n) => 0

@[simp] theorem coeff_out {p : ℕ} {n : ℕ} {R : Type u_1} [comm_ring R] (x : truncated_witt_vector p n R) (i : fin n) : witt_vector.coeff (out x) ↑i = coeff i x := sorry

theorem out_injective {p : ℕ} {n : ℕ} {R : Type u_1} [comm_ring R] : function.injective out := sorry

end truncated_witt_vector


namespace witt_vector


/-- `truncate_fun n x` uses the first `n` entries of `x` to construct a `truncated_witt_vector`,
which has the same base `p` as `x`.
This function is bundled into a ring homomorphism in `witt_vector.truncate` -/
def truncate_fun {p : ℕ} (n : ℕ) {R : Type u_1} (x : witt_vector p R) : truncated_witt_vector p n R :=
  truncated_witt_vector.mk p fun (i : fin n) => coeff x ↑i

@[simp] theorem coeff_truncate_fun {p : ℕ} {n : ℕ} {R : Type u_1} (x : witt_vector p R) (i : fin n) : truncated_witt_vector.coeff i (truncate_fun n x) = coeff x ↑i := sorry

@[simp] theorem out_truncate_fun {p : ℕ} {n : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) : truncated_witt_vector.out (truncate_fun n x) = init n x := sorry

end witt_vector


namespace truncated_witt_vector


@[simp] theorem truncate_fun_out {p : ℕ} {n : ℕ} {R : Type u_1} [comm_ring R] (x : truncated_witt_vector p n R) : witt_vector.truncate_fun n (out x) = x := sorry

protected instance has_zero (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : HasZero (truncated_witt_vector p n R) :=
  { zero := witt_vector.truncate_fun n 0 }

protected instance has_one (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : HasOne (truncated_witt_vector p n R) :=
  { one := witt_vector.truncate_fun n 1 }

protected instance has_add (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : Add (truncated_witt_vector p n R) :=
  { add := fun (x y : truncated_witt_vector p n R) => witt_vector.truncate_fun n (out x + out y) }

protected instance has_mul (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : Mul (truncated_witt_vector p n R) :=
  { mul := fun (x y : truncated_witt_vector p n R) => witt_vector.truncate_fun n (out x * out y) }

protected instance has_neg (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : Neg (truncated_witt_vector p n R) :=
  { neg := fun (x : truncated_witt_vector p n R) => witt_vector.truncate_fun n (-out x) }

@[simp] theorem coeff_zero (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] (i : fin n) : coeff i 0 = 0 :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (coeff i (witt_vector.truncate_fun n 0) = 0)) (witt_vector.coeff_truncate_fun 0 i)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (witt_vector.coeff 0 ↑i = 0)) (witt_vector.zero_coeff p R ↑i))) (Eq.refl 0)))

end truncated_witt_vector


/-- A macro tactic used to prove that `truncate_fun` respects ring operations. -/
namespace witt_vector


theorem truncate_fun_surjective (p : ℕ) (n : ℕ) (R : Type u_1) [comm_ring R] : function.surjective (truncate_fun n) :=
  fun (x : truncated_witt_vector p n R) =>
    Exists.intro (truncated_witt_vector.out x) (truncated_witt_vector.truncate_fun_out x)

@[simp] theorem truncate_fun_zero (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : truncate_fun n 0 = 0 :=
  rfl

@[simp] theorem truncate_fun_one (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : truncate_fun n 1 = 1 :=
  rfl

@[simp] theorem truncate_fun_add {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) : truncate_fun n (x + y) = truncate_fun n x + truncate_fun n y := sorry

@[simp] theorem truncate_fun_mul {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] (x : witt_vector p R) (y : witt_vector p R) : truncate_fun n (x * y) = truncate_fun n x * truncate_fun n y := sorry

theorem truncate_fun_neg {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] (x : witt_vector p R) : truncate_fun n (-x) = -truncate_fun n x := sorry

end witt_vector


namespace truncated_witt_vector


protected instance comm_ring (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : comm_ring (truncated_witt_vector p n R) :=
  function.surjective.comm_ring (witt_vector.truncate_fun n) (witt_vector.truncate_fun_surjective p n R)
    (witt_vector.truncate_fun_zero p n R) (witt_vector.truncate_fun_one p n R) (witt_vector.truncate_fun_add n)
    (witt_vector.truncate_fun_mul n) (witt_vector.truncate_fun_neg n)

end truncated_witt_vector


namespace witt_vector


/-- `truncate n` is a ring homomorphism that truncates `x` to its first `n` entries
to obtain a `truncated_witt_vector`, which has the same base `p` as `x`. -/
def truncate {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] : witt_vector p R →+* truncated_witt_vector p n R :=
  ring_hom.mk (truncate_fun n) (truncate_fun_one p n R) (truncate_fun_mul n) (truncate_fun_zero p n R)
    (truncate_fun_add n)

theorem truncate_surjective (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (R : Type u_1) [comm_ring R] : function.surjective ⇑(truncate n) :=
  truncate_fun_surjective p n R

@[simp] theorem coeff_truncate {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {R : Type u_1} [comm_ring R] (x : witt_vector p R) (i : fin n) : truncated_witt_vector.coeff i (coe_fn (truncate n) x) = coeff x ↑i :=
  coeff_truncate_fun x i

theorem mem_ker_truncate {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] (x : witt_vector p R) : x ∈ ring_hom.ker (truncate n) ↔ ∀ (i : ℕ), i < n → coeff x i = 0 := sorry

@[simp] theorem truncate_mk (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] (f : ℕ → R) : coe_fn (truncate n) (mk p f) = truncated_witt_vector.mk p fun (k : fin n) => f ↑k := sorry

end witt_vector


namespace truncated_witt_vector


/--
A ring homomorphism that truncates a truncated Witt vector of length `m` to
a truncated Witt vector of length `n`, for `n ≤ m`.
-/
def truncate {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {R : Type u_1} [comm_ring R] {m : ℕ} (hm : n ≤ m) : truncated_witt_vector p m R →+* truncated_witt_vector p n R :=
  ring_hom.lift_of_surjective (witt_vector.truncate m) (witt_vector.truncate_surjective p m R) (witt_vector.truncate n)
    sorry

@[simp] theorem truncate_comp_witt_vector_truncate {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {R : Type u_1} [comm_ring R] {m : ℕ} (hm : n ≤ m) : ring_hom.comp (truncate hm) (witt_vector.truncate m) = witt_vector.truncate n :=
  ring_hom.lift_of_surjective_comp (witt_vector.truncate m) (witt_vector.truncate_surjective p m R)
    (witt_vector.truncate n) (truncate._proof_1 hm)

@[simp] theorem truncate_witt_vector_truncate {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {R : Type u_1} [comm_ring R] {m : ℕ} (hm : n ≤ m) (x : witt_vector p R) : coe_fn (truncate hm) (coe_fn (witt_vector.truncate m) x) = coe_fn (witt_vector.truncate n) x :=
  ring_hom.lift_of_surjective_comp_apply (witt_vector.truncate m) (witt_vector.truncate_surjective p m R)
    (witt_vector.truncate n) (truncate._proof_1 hm) x

@[simp] theorem truncate_truncate {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {n₁ : ℕ} {n₂ : ℕ} {n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) (x : truncated_witt_vector p n₃ R) : coe_fn (truncate h1) (coe_fn (truncate h2) x) = coe_fn (truncate (has_le.le.trans h1 h2)) x := sorry

@[simp] theorem truncate_comp {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {n₁ : ℕ} {n₂ : ℕ} {n₃ : ℕ} (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) : ring_hom.comp (truncate h1) (truncate h2) = truncate (has_le.le.trans h1 h2) := sorry

theorem truncate_surjective {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {R : Type u_1} [comm_ring R] {m : ℕ} (hm : n ≤ m) : function.surjective ⇑(truncate hm) := sorry

@[simp] theorem coeff_truncate {p : ℕ} [hp : fact (nat.prime p)] {n : ℕ} {R : Type u_1} [comm_ring R] {m : ℕ} (hm : n ≤ m) (i : fin n) (x : truncated_witt_vector p m R) : coeff i (coe_fn (truncate hm) x) = coeff (coe_fn (fin.cast_le hm) i) x := sorry

protected instance fintype {p : ℕ} {n : ℕ} {R : Type u_1} [fintype R] : fintype (truncated_witt_vector p n R) :=
  pi.fintype

theorem card (p : ℕ) (n : ℕ) {R : Type u_1} [fintype R] : fintype.card (truncated_witt_vector p n R) = fintype.card R ^ n := sorry

theorem infi_ker_truncate {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] : (infi fun (i : ℕ) => ring_hom.ker (witt_vector.truncate i)) = ⊥ := sorry

end truncated_witt_vector


namespace witt_vector


/--
Given a family `fₖ : S → truncated_witt_vector p k R` and `s : S`, we produce a Witt vector by
defining the `k`th entry to be the final entry of `fₖ s`.
-/
def lift_fun {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] (f : (k : ℕ) → S →+* truncated_witt_vector p k R) (s : S) : witt_vector p R :=
  mk p fun (k : ℕ) => truncated_witt_vector.coeff (fin.last k) (coe_fn (f (k + 1)) s)

@[simp] theorem truncate_lift_fun {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] {f : (k : ℕ) → S →+* truncated_witt_vector p k R} (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), ring_hom.comp (truncated_witt_vector.truncate hk) (f k₂) = f k₁) (s : S) : coe_fn (truncate n) (lift_fun f s) = coe_fn (f n) s := sorry

/--
Given compatible ring homs from `S` into `truncated_witt_vector n` for each `n`, we can lift these
to a ring hom `S → 𝕎 R`.

`lift` defines the universal property of `𝕎 R` as the inverse limit of `truncated_witt_vector n`.
-/
def lift {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] (f : (k : ℕ) → S →+* truncated_witt_vector p k R) (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), ring_hom.comp (truncated_witt_vector.truncate hk) (f k₂) = f k₁) : S →+* witt_vector p R :=
  ring_hom.mk (lift_fun f) sorry sorry sorry sorry

@[simp] theorem truncate_lift {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] {f : (k : ℕ) → S →+* truncated_witt_vector p k R} (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), ring_hom.comp (truncated_witt_vector.truncate hk) (f k₂) = f k₁) (s : S) : coe_fn (truncate n) (coe_fn (lift (fun (k₂ : ℕ) => f k₂) f_compat) s) = coe_fn (f n) s :=
  truncate_lift_fun n f_compat s

@[simp] theorem truncate_comp_lift {p : ℕ} [hp : fact (nat.prime p)] (n : ℕ) {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] {f : (k : ℕ) → S →+* truncated_witt_vector p k R} (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), ring_hom.comp (truncated_witt_vector.truncate hk) (f k₂) = f k₁) : ring_hom.comp (truncate n) (lift (fun (k₂ : ℕ) => f k₂) f_compat) = f n := sorry

/-- The uniqueness part of the universal property of `𝕎 R`. -/
theorem lift_unique {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] {f : (k : ℕ) → S →+* truncated_witt_vector p k R} (f_compat : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂), ring_hom.comp (truncated_witt_vector.truncate hk) (f k₂) = f k₁) (g : S →+* witt_vector p R) (g_compat : ∀ (k : ℕ), ring_hom.comp (truncate k) g = f k) : lift (fun (k₂ : ℕ) => f k₂) f_compat = g := sorry

/-- The universal property of `𝕎 R` as projective limit of truncated Witt vector rings. -/
@[simp] theorem lift_equiv_symm_apply_coe {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] (g : S →+* witt_vector p R) (k : ℕ) : coe (coe_fn (equiv.symm lift_equiv) g) k = ring_hom.comp (truncate k) g :=
  Eq.refl (coe (coe_fn (equiv.symm lift_equiv) g) k)

theorem hom_ext {p : ℕ} [hp : fact (nat.prime p)] {R : Type u_1} [comm_ring R] {S : Type u_2} [semiring S] (g₁ : S →+* witt_vector p R) (g₂ : S →+* witt_vector p R) (h : ∀ (k : ℕ), ring_hom.comp (truncate k) g₁ = ring_hom.comp (truncate k) g₂) : g₁ = g₂ :=
  equiv.injective (equiv.symm lift_equiv) (subtype.ext (funext h))

