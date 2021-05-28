/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau, Joey van Langen, Casper Putz
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.nat.choose.default
import Mathlib.data.int.modeq
import Mathlib.algebra.module.basic
import Mathlib.algebra.iterate_hom
import Mathlib.group_theory.order_of_element
import Mathlib.algebra.group.type_tags
import PostPort

universes u l u_1 u_2 v 

namespace Mathlib

/-!
# Characteristic of semirings
-/

/-- The generator of the kernel of the unique homomorphism ℕ → α for a semiring α -/
class char_p (α : Type u) [semiring α] (p : ℕ) 
where
  cast_eq_zero_iff : ∀ (x : ℕ), ↑x = 0 ↔ p ∣ x

theorem char_p.cast_eq_zero (α : Type u) [semiring α] (p : ℕ) [char_p α p] : ↑p = 0 :=
  iff.mpr (char_p.cast_eq_zero_iff α p p) (dvd_refl p)

@[simp] theorem char_p.cast_card_eq_zero (R : Type u_1) [ring R] [fintype R] : ↑(fintype.card R) = 0 := sorry

theorem char_p.int_cast_eq_zero_iff (R : Type u) [ring R] (p : ℕ) [char_p R p] (a : ℤ) : ↑a = 0 ↔ ↑p ∣ a := sorry

theorem char_p.int_coe_eq_int_coe_iff (R : Type u_1) [ring R] (p : ℕ) [char_p R p] (a : ℤ) (b : ℤ) : ↑a = ↑b ↔ int.modeq (↑p) a b := sorry

theorem char_p.eq (α : Type u) [semiring α] {p : ℕ} {q : ℕ} (c1 : char_p α p) (c2 : char_p α q) : p = q :=
  nat.dvd_antisymm (iff.mp (char_p.cast_eq_zero_iff α p q) (char_p.cast_eq_zero α q))
    (iff.mp (char_p.cast_eq_zero_iff α q p) (char_p.cast_eq_zero α p))

protected instance char_p.of_char_zero (α : Type u) [semiring α] [char_zero α] : char_p α 0 :=
  char_p.mk
    fun (x : ℕ) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0 ↔ 0 ∣ x)) (propext zero_dvd_iff)))
        (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = 0 ↔ x = 0)) (Eq.symm nat.cast_zero)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (↑x = ↑0 ↔ x = 0)) (propext nat.cast_inj))) (iff.refl (x = 0))))

theorem char_p.exists (α : Type u) [semiring α] : ∃ (p : ℕ), char_p α p := sorry

theorem char_p.exists_unique (α : Type u) [semiring α] : exists_unique fun (p : ℕ) => char_p α p := sorry

theorem char_p.congr {R : Type u} [semiring R] {p : ℕ} (q : ℕ) [hq : char_p R q] (h : q = p) : char_p R p :=
  h ▸ hq

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
def ring_char (α : Type u) [semiring α] : ℕ :=
  classical.some (char_p.exists_unique α)

namespace ring_char


theorem spec (R : Type u) [semiring R] (x : ℕ) : ↑x = 0 ↔ ring_char R ∣ x := sorry

theorem eq (R : Type u) [semiring R] {p : ℕ} (C : char_p R p) : p = ring_char R :=
  and.right (classical.some_spec (char_p.exists_unique R)) p C

protected instance char_p (R : Type u) [semiring R] : char_p R (ring_char R) :=
  char_p.mk (spec R)

theorem of_eq {R : Type u} [semiring R] {p : ℕ} (h : ring_char R = p) : char_p R p :=
  char_p.congr (ring_char R) h

theorem eq_iff {R : Type u} [semiring R] {p : ℕ} : ring_char R = p ↔ char_p R p :=
  { mp := of_eq, mpr := Eq.symm ∘ eq R }

theorem dvd {R : Type u} [semiring R] {x : ℕ} (hx : ↑x = 0) : ring_char R ∣ x :=
  iff.mp (spec R x) hx

end ring_char


theorem add_pow_char_of_commute (R : Type u) [semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] (x : R) (y : R) (h : commute x y) : (x + y) ^ p = x ^ p + y ^ p := sorry

theorem add_pow_char_pow_of_commute (R : Type u) [semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] {n : ℕ} (x : R) (y : R) (h : commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := sorry

theorem sub_pow_char_of_commute (R : Type u) [ring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] (x : R) (y : R) (h : commute x y) : (x - y) ^ p = x ^ p - y ^ p := sorry

theorem sub_pow_char_pow_of_commute (R : Type u) [ring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] {n : ℕ} (x : R) (y : R) (h : commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sorry

theorem add_pow_char (α : Type u) [comm_semiring α] {p : ℕ} [fact (nat.prime p)] [char_p α p] (x : α) (y : α) : (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_char_of_commute α x y (commute.all x y)

theorem add_pow_char_pow (R : Type u) [comm_semiring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] {n : ℕ} (x : R) (y : R) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_char_pow_of_commute R x y (commute.all x y)

theorem sub_pow_char (α : Type u) [comm_ring α] {p : ℕ} [fact (nat.prime p)] [char_p α p] (x : α) (y : α) : (x - y) ^ p = x ^ p - y ^ p :=
  sub_pow_char_of_commute α x y (commute.all x y)

theorem sub_pow_char_pow (R : Type u) [comm_ring R] {p : ℕ} [fact (nat.prime p)] [char_p R p] {n : ℕ} (x : R) (y : R) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_char_pow_of_commute R x y (commute.all x y)

theorem eq_iff_modeq_int (R : Type u_1) [ring R] (p : ℕ) [char_p R p] (a : ℤ) (b : ℤ) : ↑a = ↑b ↔ int.modeq (↑p) a b := sorry

theorem char_p.neg_one_ne_one (R : Type u_1) [ring R] (p : ℕ) [char_p R p] [fact (bit0 1 < p)] : -1 ≠ 1 := sorry

theorem ring_hom.char_p_iff_char_p {K : Type u_1} {L : Type u_2} [field K] [field L] (f : K →+* L) (p : ℕ) : char_p K p ↔ char_p L p := sorry

/-- The frobenius map that sends x to x^p -/
def frobenius (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] : R →+* R :=
  ring_hom.mk (fun (x : R) => x ^ p) sorry sorry sorry (add_pow_char R)

theorem frobenius_def {R : Type u} [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (x : R) : coe_fn (frobenius R p) x = x ^ p :=
  rfl

theorem iterate_frobenius {R : Type u} [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (x : R) (n : ℕ) : nat.iterate (⇑(frobenius R p)) n x = x ^ p ^ n := sorry

theorem frobenius_mul {R : Type u} [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (x : R) (y : R) : coe_fn (frobenius R p) (x * y) = coe_fn (frobenius R p) x * coe_fn (frobenius R p) y :=
  ring_hom.map_mul (frobenius R p) x y

theorem frobenius_one {R : Type u} [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] : coe_fn (frobenius R p) 1 = 1 :=
  one_pow p

theorem monoid_hom.map_frobenius {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) (p : ℕ) [fact (nat.prime p)] [char_p R p] [char_p S p] (x : R) : coe_fn f (coe_fn (frobenius R p) x) = coe_fn (frobenius S p) (coe_fn f x) :=
  monoid_hom.map_pow f x p

theorem ring_hom.map_frobenius {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (g : R →+* S) (p : ℕ) [fact (nat.prime p)] [char_p R p] [char_p S p] (x : R) : coe_fn g (coe_fn (frobenius R p) x) = coe_fn (frobenius S p) (coe_fn g x) :=
  ring_hom.map_pow g x p

theorem monoid_hom.map_iterate_frobenius {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (f : R →* S) (p : ℕ) [fact (nat.prime p)] [char_p R p] [char_p S p] (x : R) (n : ℕ) : coe_fn f (nat.iterate (⇑(frobenius R p)) n x) = nat.iterate (⇑(frobenius S p)) n (coe_fn f x) :=
  function.semiconj.iterate_right (monoid_hom.map_frobenius f p) n x

theorem ring_hom.map_iterate_frobenius {R : Type u} [comm_semiring R] {S : Type v} [comm_semiring S] (g : R →+* S) (p : ℕ) [fact (nat.prime p)] [char_p R p] [char_p S p] (x : R) (n : ℕ) : coe_fn g (nat.iterate (⇑(frobenius R p)) n x) = nat.iterate (⇑(frobenius S p)) n (coe_fn g x) :=
  monoid_hom.map_iterate_frobenius (ring_hom.to_monoid_hom g) p x n

theorem monoid_hom.iterate_map_frobenius {R : Type u} [comm_semiring R] (x : R) (f : R →* R) (p : ℕ) [fact (nat.prime p)] [char_p R p] (n : ℕ) : nat.iterate (⇑f) n (coe_fn (frobenius R p) x) = coe_fn (frobenius R p) (nat.iterate (⇑f) n x) :=
  monoid_hom.iterate_map_pow f x n p

theorem ring_hom.iterate_map_frobenius {R : Type u} [comm_semiring R] (x : R) (f : R →+* R) (p : ℕ) [fact (nat.prime p)] [char_p R p] (n : ℕ) : nat.iterate (⇑f) n (coe_fn (frobenius R p) x) = coe_fn (frobenius R p) (nat.iterate (⇑f) n x) :=
  ring_hom.iterate_map_pow f x n p

theorem frobenius_zero (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] : coe_fn (frobenius R p) 0 = 0 :=
  ring_hom.map_zero (frobenius R p)

theorem frobenius_add (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (x : R) (y : R) : coe_fn (frobenius R p) (x + y) = coe_fn (frobenius R p) x + coe_fn (frobenius R p) y :=
  ring_hom.map_add (frobenius R p) x y

theorem frobenius_nat_cast (R : Type u) [comm_semiring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (n : ℕ) : coe_fn (frobenius R p) ↑n = ↑n :=
  ring_hom.map_nat_cast (frobenius R p) n

theorem frobenius_neg (R : Type u) [comm_ring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (x : R) : coe_fn (frobenius R p) (-x) = -coe_fn (frobenius R p) x :=
  ring_hom.map_neg (frobenius R p) x

theorem frobenius_sub (R : Type u) [comm_ring R] (p : ℕ) [fact (nat.prime p)] [char_p R p] (x : R) (y : R) : coe_fn (frobenius R p) (x - y) = coe_fn (frobenius R p) x - coe_fn (frobenius R p) y :=
  ring_hom.map_sub (frobenius R p) x y

theorem frobenius_inj (α : Type u) [comm_ring α] [no_zero_divisors α] (p : ℕ) [fact (nat.prime p)] [char_p α p] : function.injective ⇑(frobenius α p) := sorry

namespace char_p


theorem char_p_to_char_zero (α : Type u) [ring α] [char_p α 0] : char_zero α :=
  char_zero_of_inj_zero fun (n : ℕ) (h0 : ↑n = 0) => eq_zero_of_zero_dvd (iff.mp (cast_eq_zero_iff α 0 n) h0)

theorem cast_eq_mod (α : Type u) [ring α] (p : ℕ) [char_p α p] (k : ℕ) : ↑k = ↑(k % p) := sorry

theorem char_ne_zero_of_fintype (α : Type u) [ring α] (p : ℕ) [hc : char_p α p] [fintype α] : p ≠ 0 :=
  fun (h : p = 0) =>
    (fun (this : char_zero α) => absurd nat.cast_injective (not_injective_infinite_fintype coe)) (char_p_to_char_zero α)

theorem char_ne_one (α : Type u) [integral_domain α] (p : ℕ) [hc : char_p α p] : p ≠ 1 := sorry

theorem char_is_prime_of_two_le (α : Type u) [integral_domain α] (p : ℕ) [hc : char_p α p] (hp : bit0 1 ≤ p) : nat.prime p := sorry

theorem char_is_prime_or_zero (α : Type u) [integral_domain α] (p : ℕ) [hc : char_p α p] : nat.prime p ∨ p = 0 := sorry

theorem char_is_prime_of_pos (α : Type u) [integral_domain α] (p : ℕ) [h : fact (0 < p)] [char_p α p] : fact (nat.prime p) :=
  or.resolve_right (char_is_prime_or_zero α p) (iff.mp pos_iff_ne_zero h)

theorem char_is_prime (α : Type u) [integral_domain α] [fintype α] (p : ℕ) [char_p α p] : nat.prime p :=
  or.resolve_right (char_is_prime_or_zero α p) (char_ne_zero_of_fintype α p)

protected instance subsingleton {R : Type u_1} [semiring R] [char_p R 1] : subsingleton R :=
  subsingleton.intro
    ((fun (this : ∀ (r : R), r = 0) (a b : R) =>
        (fun (this : a = b) => this)
          (eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (this a)))
            (eq.mpr (id (Eq._oldrec (Eq.refl (0 = b)) (this b))) (Eq.refl 0))))
      fun (r : R) =>
        Eq.trans
          (Eq.trans
            (Eq.trans (eq.mpr (id (Eq._oldrec (Eq.refl (r = 1 * r)) (one_mul r))) (Eq.refl r))
              (eq.mpr (id (Eq._oldrec (Eq.refl (1 * r = ↑1 * r)) nat.cast_one)) (Eq.refl (1 * r))))
            (eq.mpr (id (Eq._oldrec (Eq.refl (↑1 * r = 0 * r)) (cast_eq_zero R 1))) (Eq.refl (0 * r))))
          (eq.mpr (id (Eq._oldrec (Eq.refl (0 * r = 0)) (zero_mul r))) (Eq.refl 0)))

theorem false_of_nontrivial_of_char_one {R : Type u_1} [semiring R] [nontrivial R] [char_p R 1] : False :=
  false_of_nontrivial_of_subsingleton R

theorem ring_char_ne_one {R : Type u_1} [semiring R] [nontrivial R] : ring_char R ≠ 1 := sorry

theorem nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) {R : Type u_1} [semiring R] [hr : char_p R v] : nontrivial R := sorry

end char_p


theorem char_p_of_ne_zero (n : ℕ) (R : Type u_1) [comm_ring R] [fintype R] (hn : fintype.card R = n) (hR : ∀ (i : ℕ), i < n → ↑i = 0 → i = 0) : char_p R n := sorry

theorem char_p_of_prime_pow_injective (R : Type u_1) [comm_ring R] [fintype R] (p : ℕ) [hp : fact (nat.prime p)] (n : ℕ) (hn : fintype.card R = p ^ n) (hR : ∀ (i : ℕ), i ≤ n → ↑p ^ i = 0 → i = n) : char_p R (p ^ n) := sorry

