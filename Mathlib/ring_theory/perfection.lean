/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.char_p.default
import Mathlib.algebra.ring.pi
import Mathlib.analysis.special_functions.pow
import Mathlib.field_theory.perfect_closure
import Mathlib.ring_theory.localization
import Mathlib.ring_theory.subring
import Mathlib.ring_theory.valuation.integers
import Mathlib.PostPort

universes u₁ u₂ l u₃ u₄ 

namespace Mathlib

/-!
# Ring Perfection and Tilt

In this file we define the perfection of a ring of characteristic p, and the tilt of a field
given a valuation to `ℝ≥0`.

## TODO

Define the valuation on the tilt, and define a characteristic predicate for the tilt.

-/

/-- The perfection of a monoid `M`, defined to be the projective limit of `M`
using the `p`-th power maps `M → M` indexed by the natural numbers, implemented as
`{ f : ℕ → M | ∀ n, f (n + 1) ^ p = f n }`. -/
def monoid.perfection (M : Type u₁) [comm_monoid M] (p : ℕ) : submonoid (ℕ → M) :=
  submonoid.mk (set_of fun (f : ℕ → M) => ∀ (n : ℕ), f (n + 1) ^ p = f n) sorry sorry

/-- The perfection of a ring `R` with characteristic `p`,
defined to be the projective limit of `R` using the Frobenius maps `R → R`
indexed by the natural numbers, implemented as `{ f : ℕ → R | ∀ n, f (n + 1) ^ p = f n }`. -/
def ring.perfection (R : Type u₁) [comm_semiring R] (p : ℕ) [hp : fact (nat.prime p)] [char_p R p] : subsemiring (ℕ → R) :=
  subsemiring.mk (submonoid.carrier (monoid.perfection R p)) sorry sorry sorry sorry

namespace perfection


/-- The `n`-th coefficient of an element of the perfection. -/
def coeff (R : Type u₁) [comm_semiring R] (p : ℕ) [hp : fact (nat.prime p)] [char_p R p] (n : ℕ) : ↥(ring.perfection R p) →+* R :=
  ring_hom.mk (fun (f : ↥(ring.perfection R p)) => subtype.val f n) sorry sorry sorry sorry

theorem ext {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] {f : ↥(ring.perfection R p)} {g : ↥(ring.perfection R p)} (h : ∀ (n : ℕ), coe_fn (coeff R p n) f = coe_fn (coeff R p n) g) : f = g :=
  subtype.eq (funext h)

/-- The `p`-th root of an element of the perfection. -/
def pth_root (R : Type u₁) [comm_semiring R] (p : ℕ) [hp : fact (nat.prime p)] [char_p R p] : ↥(ring.perfection R p) →+* ↥(ring.perfection R p) :=
  ring_hom.mk
    (fun (f : ↥(ring.perfection R p)) => { val := fun (n : ℕ) => coe_fn (coeff R p (n + 1)) f, property := sorry }) sorry
    sorry sorry sorry

@[simp] theorem coeff_mk {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ℕ → R) (hf : f ∈ ring.perfection R p) (n : ℕ) : coe_fn (coeff R p n) { val := f, property := hf } = f n :=
  rfl

theorem coeff_pth_root {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ↥(ring.perfection R p)) (n : ℕ) : coe_fn (coeff R p n) (coe_fn (pth_root R p) f) = coe_fn (coeff R p (n + 1)) f :=
  rfl

theorem coeff_pow_p {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ↥(ring.perfection R p)) (n : ℕ) : coe_fn (coeff R p (n + 1)) (f ^ p) = coe_fn (coeff R p n) f := sorry

theorem coeff_pow_p' {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ↥(ring.perfection R p)) (n : ℕ) : coe_fn (coeff R p (n + 1)) f ^ p = coe_fn (coeff R p n) f :=
  subtype.property f n

theorem coeff_frobenius {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ↥(ring.perfection R p)) (n : ℕ) : coe_fn (coeff R p (n + 1)) (coe_fn (frobenius (↥(ring.perfection R p)) p) f) = coe_fn (coeff R p n) f := sorry

theorem coeff_iterate_frobenius {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ↥(ring.perfection R p)) (n : ℕ) (m : ℕ) : coe_fn (coeff R p (n + m)) (nat.iterate (⇑(frobenius (↥(ring.perfection R p)) p)) m f) = coe_fn (coeff R p n) f := sorry

theorem coeff_iterate_frobenius' {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] (f : ↥(ring.perfection R p)) (n : ℕ) (m : ℕ) (hmn : m ≤ n) : coe_fn (coeff R p n) (nat.iterate (⇑(frobenius (↥(ring.perfection R p)) p)) m f) = coe_fn (coeff R p (n - m)) f :=
  Eq.symm (Eq.trans (Eq.symm (coeff_iterate_frobenius f (n - m) m)) (Eq.symm (nat.sub_add_cancel hmn) ▸ rfl))

theorem pth_root_frobenius {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] : ring_hom.comp (pth_root R p) (frobenius (↥(ring.perfection R p)) p) = ring_hom.id ↥(ring.perfection R p) := sorry

theorem frobenius_pth_root {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] : ring_hom.comp (frobenius (↥(ring.perfection R p)) p) (pth_root R p) = ring_hom.id ↥(ring.perfection R p) := sorry

theorem coeff_add_ne_zero {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] {f : ↥(ring.perfection R p)} {n : ℕ} (hfn : coe_fn (coeff R p n) f ≠ 0) (k : ℕ) : coe_fn (coeff R p (n + k)) f ≠ 0 := sorry

theorem coeff_ne_zero_of_le {R : Type u₁} [comm_semiring R] {p : ℕ} [hp : fact (nat.prime p)] [char_p R p] {f : ↥(ring.perfection R p)} {m : ℕ} {n : ℕ} (hfm : coe_fn (coeff R p m) f ≠ 0) (hmn : m ≤ n) : coe_fn (coeff R p n) f ≠ 0 := sorry

protected instance perfect_ring (R : Type u₁) [comm_semiring R] (p : ℕ) [hp : fact (nat.prime p)] [char_p R p] : perfect_ring (↥(ring.perfection R p)) p :=
  perfect_ring.mk ⇑(pth_root R p) sorry sorry

protected instance ring (p : ℕ) [hp : fact (nat.prime p)] (R : Type u₁) [comm_ring R] [char_p R p] : ring ↥(ring.perfection R p) :=
  subring.to_ring (subsemiring.to_subring (ring.perfection R p) sorry)

protected instance comm_ring (p : ℕ) [hp : fact (nat.prime p)] (R : Type u₁) [comm_ring R] [char_p R p] : comm_ring ↥(ring.perfection R p) :=
  subring.to_comm_ring (subsemiring.to_subring (ring.perfection R p) sorry)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* perfection S p`. -/
@[simp] theorem lift_symm_apply (p : ℕ) [hp : fact (nat.prime p)] (R : Type u₁) [comm_semiring R] [char_p R p] [perfect_ring R p] (S : Type u₂) [comm_semiring S] [char_p S p] (hmn : R →+* ↥(ring.perfection S p)) : coe_fn (equiv.symm (lift p R S)) hmn = ring_hom.comp (coeff S p 0) hmn :=
  Eq.refl (coe_fn (equiv.symm (lift p R S)) hmn)

theorem hom_ext (p : ℕ) [hp : fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] [perfect_ring R p] {S : Type u₂} [comm_semiring S] [char_p S p] {f : R →+* ↥(ring.perfection S p)} {g : R →+* ↥(ring.perfection S p)} (hfg : ∀ (x : R), coe_fn (coeff S p 0) (coe_fn f x) = coe_fn (coeff S p 0) (coe_fn g x)) : f = g :=
  equiv.injective (equiv.symm (lift p R S)) (ring_hom.ext hfg)

/-- A ring homomorphism `R →+* S` induces `perfection R p →+* perfection S p` -/
@[simp] theorem map_apply_coe {R : Type u₁} [comm_semiring R] (p : ℕ) [hp : fact (nat.prime p)] [char_p R p] {S : Type u₂} [comm_semiring S] [char_p S p] (φ : R →+* S) (f : ↥(ring.perfection R p)) (n : ℕ) : coe (coe_fn (map p φ) f) n = coe_fn φ (coe_fn (coeff R p n) f) :=
  Eq.refl (coe (coe_fn (map p φ) f) n)

theorem coeff_map {R : Type u₁} [comm_semiring R] (p : ℕ) [hp : fact (nat.prime p)] [char_p R p] {S : Type u₂} [comm_semiring S] [char_p S p] (φ : R →+* S) (f : ↥(ring.perfection R p)) (n : ℕ) : coe_fn (coeff S p n) (coe_fn (map p φ) f) = coe_fn φ (coe_fn (coeff R p n) f) :=
  rfl

end perfection


/-- A perfection map to a ring of characteristic `p` is a map that is isomorphic
to its perfection. -/
structure perfection_map (p : ℕ) [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₂} [comm_semiring P] [char_p P p] [perfect_ring P p] (π : P →+* R) 
where
  injective : ∀ {x y : P},
  (∀ (n : ℕ), coe_fn π (nat.iterate (⇑(pth_root P p)) n x) = coe_fn π (nat.iterate (⇑(pth_root P p)) n y)) → x = y
  surjective : ∀ (f : ℕ → R),
  (∀ (n : ℕ), f (n + 1) ^ p = f n) → ∃ (x : P), ∀ (n : ℕ), coe_fn π (nat.iterate (⇑(pth_root P p)) n x) = f n

namespace perfection_map


/-- Create a `perfection_map` from an isomorphism to the perfection. -/
theorem mk' {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {f : P →+* R} (g : P ≃+* ↥(ring.perfection R p)) (hfg : coe_fn (perfection.lift p P R) f = ↑g) : perfection_map p f := sorry

/-- The canonical perfection map from the perfection of a ring. -/
theorem of (p : ℕ) [fact (nat.prime p)] (R : Type u₁) [comm_semiring R] [char_p R p] : perfection_map p (perfection.coeff R p 0) :=
  mk' (ring_equiv.refl ↥(ring.perfection R p))
    (iff.mpr (equiv.apply_eq_iff_eq_symm_apply (perfection.lift p (↥(ring.perfection R p)) R)) rfl)

/-- For a perfect ring, it itself is the perfection. -/
theorem id (p : ℕ) [fact (nat.prime p)] (R : Type u₁) [comm_semiring R] [char_p R p] [perfect_ring R p] : perfection_map p (ring_hom.id R) := sorry

/-- A perfection map induces an isomorphism to the prefection. -/
def equiv {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {π : P →+* R} (m : perfection_map p π) : P ≃+* ↥(ring.perfection R p) :=
  ring_equiv.of_bijective (coe_fn (perfection.lift p P R) π) sorry

theorem equiv_apply {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {π : P →+* R} (m : perfection_map p π) (x : P) : coe_fn (equiv m) x = coe_fn (coe_fn (perfection.lift p P R) π) x :=
  rfl

theorem comp_equiv {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {π : P →+* R} (m : perfection_map p π) (x : P) : coe_fn (perfection.coeff R p 0) (coe_fn (equiv m) x) = coe_fn π x :=
  rfl

theorem comp_equiv' {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {π : P →+* R} (m : perfection_map p π) : ring_hom.comp (perfection.coeff R p 0) ↑(equiv m) = π :=
  ring_hom.ext fun (x : P) => rfl

theorem comp_symm_equiv {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {π : P →+* R} (m : perfection_map p π) (f : ↥(ring.perfection R p)) : coe_fn π (coe_fn (ring_equiv.symm (equiv m)) f) = coe_fn (perfection.coeff R p 0) f :=
  Eq.trans (Eq.symm (comp_equiv m (coe_fn (ring_equiv.symm (equiv m)) f)))
    (congr_arg (⇑(perfection.coeff R p 0)) (ring_equiv.apply_symm_apply (equiv m) f))

theorem comp_symm_equiv' {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {π : P →+* R} (m : perfection_map p π) : ring_hom.comp π ↑(ring_equiv.symm (equiv m)) = perfection.coeff R p 0 :=
  ring_hom.ext (comp_symm_equiv m)

/-- Given rings `R` and `S` of characteristic `p`, with `R` being perfect,
any homomorphism `R →+* S` can be lifted to a homomorphism `R →+* P`,
where `P` is any perfection of `S`. -/
@[simp] theorem lift_apply (p : ℕ) [fact (nat.prime p)] (R : Type u₁) [comm_semiring R] [char_p R p] [perfect_ring R p] (S : Type u₂) [comm_semiring S] [char_p S p] (P : Type u₃) [comm_semiring P] [char_p P p] [perfect_ring P p] (π : P →+* S) (m : perfection_map p π) (f : R →+* S) : coe_fn (lift p R S P π m) f = ring_hom.comp (↑(ring_equiv.symm (equiv m))) (coe_fn (perfection.lift p R S) f) :=
  Eq.refl (coe_fn (lift p R S P π m) f)

theorem hom_ext {p : ℕ} [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] [perfect_ring R p] {S : Type u₂} [comm_semiring S] [char_p S p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] (π : P →+* S) (m : perfection_map p π) {f : R →+* P} {g : R →+* P} (hfg : ∀ (x : R), coe_fn π (coe_fn f x) = coe_fn π (coe_fn g x)) : f = g :=
  equiv.injective (equiv.symm (lift p R S P π m)) (ring_hom.ext hfg)

/-- A ring homomorphism `R →+* S` induces `P →+* Q`, a map of the respective perfections -/
def map (p : ℕ) [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {S : Type u₂} [comm_semiring S] [char_p S p] {Q : Type u₄} [comm_semiring Q] [char_p Q p] [perfect_ring Q p] {π : P →+* R} (m : perfection_map p π) {σ : Q →+* S} (n : perfection_map p σ) (φ : R →+* S) : P →+* Q :=
  coe_fn (lift p P S Q σ n) (ring_hom.comp φ π)

theorem comp_map (p : ℕ) [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {S : Type u₂} [comm_semiring S] [char_p S p] {Q : Type u₄} [comm_semiring Q] [char_p Q p] [perfect_ring Q p] {π : P →+* R} (m : perfection_map p π) {σ : Q →+* S} (n : perfection_map p σ) (φ : R →+* S) : ring_hom.comp σ (map p m n φ) = ring_hom.comp φ π :=
  equiv.symm_apply_apply (lift p P S Q σ n) (ring_hom.comp φ π)

theorem map_map (p : ℕ) [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {P : Type u₃} [comm_semiring P] [char_p P p] [perfect_ring P p] {S : Type u₂} [comm_semiring S] [char_p S p] {Q : Type u₄} [comm_semiring Q] [char_p Q p] [perfect_ring Q p] {π : P →+* R} (m : perfection_map p π) {σ : Q →+* S} (n : perfection_map p σ) (φ : R →+* S) (x : P) : coe_fn σ (coe_fn (map p m n φ) x) = coe_fn φ (coe_fn π x) :=
  iff.mp ring_hom.ext_iff (comp_map p m n φ) x

-- Why is this slow?

theorem map_eq_map (p : ℕ) [fact (nat.prime p)] {R : Type u₁} [comm_semiring R] [char_p R p] {S : Type u₂} [comm_semiring S] [char_p S p] (φ : R →+* S) : map p (of p R) (of p S) φ = perfection.map p φ := sorry

end perfection_map


/-- `O/(p)` for `O`, ring of integers of `K`. -/
def mod_p (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) :=
  ideal.quotient (ideal.span (singleton ↑p))

namespace mod_p


protected instance comm_ring (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) : comm_ring (mod_p K v O hv p) :=
  ideal.quotient.comm_ring (ideal.span (singleton ↑p))

protected instance char_p (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : char_p (mod_p K v O hv p) p :=
  char_p.quotient O p
    (mt (valuation.integers.one_of_is_unit hv) (Eq.symm (ring_hom.map_nat_cast (algebra_map O K) p) ▸ hvp))

protected instance nontrivial (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : nontrivial (mod_p K v O hv p) :=
  char_p.nontrivial_of_char_ne_one (nat.prime.ne_one hp)

/-- For a field `K` with valuation `v : K → ℝ≥0` and ring of integers `O`,
a function `O/(p) → ℝ≥0` that sends `0` to `0` and `x + (p)` to `v(x)` as long as `x ∉ (p)`. -/
def pre_val (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) (x : mod_p K v O hv p) : nnreal :=
  ite (x = 0) 0 (coe_fn v (coe_fn (algebra_map O K) (quotient.out' x)))

theorem pre_val_mk {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} {x : O} (hx : coe_fn (ideal.quotient.mk (ideal.span (singleton ↑p))) x ≠ 0) : pre_val K v O hv p (coe_fn (ideal.quotient.mk (ideal.span (singleton ↑p))) x) = coe_fn v (coe_fn (algebra_map O K) x) := sorry

theorem pre_val_zero {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} : pre_val K v O hv p 0 = 0 :=
  if_pos rfl

theorem pre_val_mul {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} {x : mod_p K v O hv p} {y : mod_p K v O hv p} (hxy0 : x * y ≠ 0) : pre_val K v O hv p (x * y) = pre_val K v O hv p x * pre_val K v O hv p y := sorry

theorem pre_val_add {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} (x : mod_p K v O hv p) (y : mod_p K v O hv p) : pre_val K v O hv p (x + y) ≤ max (pre_val K v O hv p x) (pre_val K v O hv p y) := sorry

theorem v_p_lt_pre_val {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} {x : mod_p K v O hv p} : coe_fn v ↑p < pre_val K v O hv p x ↔ x ≠ 0 := sorry

theorem pre_val_eq_zero {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} {x : mod_p K v O hv p} : pre_val K v O hv p x = 0 ↔ x = 0 := sorry

theorem v_p_lt_val {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] (hv : valuation.integers v O) {p : ℕ} {x : O} : coe_fn v ↑p < coe_fn v (coe_fn (algebra_map O K) x) ↔ coe_fn (ideal.quotient.mk (ideal.span (singleton ↑p))) x ≠ 0 := sorry

theorem mul_ne_zero_of_pow_p_ne_zero {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] {x : mod_p K v O hv p} {y : mod_p K v O hv p} (hx : x ^ p ≠ 0) (hy : y ^ p ≠ 0) : x * y ≠ 0 := sorry

end mod_p


/-- Perfection of `O/(p)` where `O` is the ring of integers of `K`. -/
def pre_tilt (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : subsemiring (ℕ → mod_p K v O hv p) :=
  ring.perfection (mod_p K v O hv p) p

namespace pre_tilt


protected instance comm_ring (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : comm_ring ↥(pre_tilt K v O hv p) :=
  perfection.comm_ring p (mod_p K v O hv p)

/-- The valuation `Perfection(O/(p)) → ℝ≥0` as a function.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `pre_val(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
def val_aux (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] (f : ↥(pre_tilt K v O hv p)) : nnreal :=
  dite (∃ (n : ℕ), coe_fn (perfection.coeff (mod_p K v O hv p) p n) f ≠ 0)
    (fun (h : ∃ (n : ℕ), coe_fn (perfection.coeff (mod_p K v O hv p) p n) f ≠ 0) =>
      mod_p.pre_val K v O hv p (coe_fn (perfection.coeff (mod_p K v O hv p) p (nat.find h)) f) ^ p ^ nat.find h)
    fun (h : ¬∃ (n : ℕ), coe_fn (perfection.coeff (mod_p K v O hv p) p n) f ≠ 0) => 0

theorem coeff_nat_find_add_ne_zero {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] {f : ↥(pre_tilt K v O hv p)} {h : ∃ (n : ℕ), coe_fn (perfection.coeff (mod_p K v O hv p) p n) f ≠ 0} (k : ℕ) : coe_fn (perfection.coeff (mod_p K v O hv p) p (nat.find h + k)) f ≠ 0 :=
  perfection.coeff_add_ne_zero (nat.find_spec h) k

theorem val_aux_eq {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] {f : ↥(pre_tilt K v O hv p)} {n : ℕ} (hfn : coe_fn (perfection.coeff (mod_p K v O hv p) p n) f ≠ 0) : val_aux K v O hv p f = mod_p.pre_val K v O hv p (coe_fn (perfection.coeff (mod_p K v O hv p) p n) f) ^ p ^ n := sorry

theorem val_aux_zero {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : val_aux K v O hv p 0 = 0 := sorry

theorem val_aux_one {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : val_aux K v O hv p 1 = 1 := sorry

theorem val_aux_mul {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] (f : ↥(pre_tilt K v O hv p)) (g : ↥(pre_tilt K v O hv p)) : val_aux K v O hv p (f * g) = val_aux K v O hv p f * val_aux K v O hv p g := sorry

theorem val_aux_add {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] (f : ↥(pre_tilt K v O hv p)) (g : ↥(pre_tilt K v O hv p)) : val_aux K v O hv p (f + g) ≤ max (val_aux K v O hv p f) (val_aux K v O hv p g) := sorry

/-- The valuation `Perfection(O/(p)) → ℝ≥0`.
Given `f ∈ Perfection(O/(p))`, if `f = 0` then output `0`;
otherwise output `pre_val(f(n))^(p^n)` for any `n` such that `f(n) ≠ 0`. -/
def val (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : valuation (↥(pre_tilt K v O hv p)) nnreal :=
  valuation.mk (val_aux K v O hv p) val_aux_zero val_aux_one val_aux_mul val_aux_add

theorem map_eq_zero {K : Type u₁} [field K] {v : valuation K nnreal} {O : Type u₂} [comm_ring O] [algebra O K] {hv : valuation.integers v O} {p : ℕ} [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] {f : ↥(pre_tilt K v O hv p)} : coe_fn (val K v O hv p) f = 0 ↔ f = 0 := sorry

protected instance integral_domain (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : integral_domain ↥(pre_tilt K v O hv p) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

end pre_tilt


/-- The tilt of a field, as defined in Perfectoid Spaces by Peter Scholze, as in
[scholze2011perfectoid]. Given a field `K` with valuation `K → ℝ≥0` and ring of integers `O`,
this is implemented as the fraction field of the perfection of `O/(p)`. -/
def tilt (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] :=
  fraction_ring ↥(pre_tilt K v O hv p)

namespace tilt


protected instance field (K : Type u₁) [field K] (v : valuation K nnreal) (O : Type u₂) [comm_ring O] [algebra O K] (hv : valuation.integers v O) (p : ℕ) [hp : fact (nat.prime p)] [hvp : fact (coe_fn v ↑p ≠ 1)] : field (tilt K v O hv p) :=
  fraction_ring.field

