/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Neil Strickland
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.pnat.prime
import Mathlib.data.multiset.sort
import Mathlib.data.int.gcd
import Mathlib.algebra.group.default
import PostPort

namespace Mathlib

/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
def prime_multiset  :=
  multiset nat.primes

namespace prime_multiset


protected instance inhabited : Inhabited prime_multiset :=
  eq.mpr sorry multiset.inhabited

protected instance has_repr : has_repr prime_multiset :=
  id multiset.has_repr

protected instance canonically_ordered_add_monoid : canonically_ordered_add_monoid prime_multiset :=
  id multiset.canonically_ordered_add_monoid

protected instance distrib_lattice : distrib_lattice prime_multiset :=
  id multiset.distrib_lattice

protected instance semilattice_sup_bot : semilattice_sup_bot prime_multiset :=
  id multiset.semilattice_sup_bot

protected instance has_sub : Sub prime_multiset :=
  id multiset.has_sub

theorem add_sub_of_le {u : prime_multiset} {v : prime_multiset} : u ≤ v → u + (v - u) = v :=
  multiset.add_sub_of_le

/-- The multiset consisting of a single prime
-/
def of_prime (p : nat.primes) : prime_multiset :=
  p ::ₘ 0

theorem card_of_prime (p : nat.primes) : coe_fn multiset.card (of_prime p) = 1 :=
  rfl

/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/
def to_nat_multiset : prime_multiset → multiset ℕ :=
  fun (v : prime_multiset) => multiset.map (fun (p : nat.primes) => ↑p) v

protected instance coe_nat : has_coe prime_multiset (multiset ℕ) :=
  has_coe.mk to_nat_multiset

protected instance coe_nat_hom : is_add_monoid_hom coe :=
  eq.mpr
    (id
      ((fun (f f_1 : prime_multiset → multiset ℕ) (e_3 : f = f_1) => congr_arg is_add_monoid_hom e_3) coe to_nat_multiset
        (Eq.trans (Eq.trans (Eq.trans coe.equations._eqn_1 lift_t.equations._eqn_1) coe_t.equations._eqn_1)
          coe_b.equations._eqn_1)))
    (id (multiset.map.is_add_monoid_hom coe))

theorem coe_nat_injective : function.injective coe :=
  multiset.map_injective nat.primes.coe_nat_inj

theorem coe_nat_of_prime (p : nat.primes) : ↑(of_prime p) = ↑p ::ₘ 0 :=
  rfl

theorem coe_nat_prime (v : prime_multiset) (p : ℕ) (h : p ∈ ↑v) : nat.prime p := sorry

/-- Converts a `prime_multiset` to a `multiset ℕ+`. -/
def to_pnat_multiset : prime_multiset → multiset ℕ+ :=
  fun (v : prime_multiset) => multiset.map (fun (p : nat.primes) => ↑p) v

protected instance coe_pnat : has_coe prime_multiset (multiset ℕ+) :=
  has_coe.mk to_pnat_multiset

protected instance coe_pnat_hom : is_add_monoid_hom coe :=
  eq.mpr
    (id
      ((fun (f f_1 : prime_multiset → multiset ℕ+) (e_3 : f = f_1) => congr_arg is_add_monoid_hom e_3) coe
        to_pnat_multiset
        (Eq.trans (Eq.trans (Eq.trans coe.equations._eqn_1 lift_t.equations._eqn_1) coe_t.equations._eqn_1)
          coe_b.equations._eqn_1)))
    (id (multiset.map.is_add_monoid_hom coe))

theorem coe_pnat_injective : function.injective coe :=
  multiset.map_injective nat.primes.coe_pnat_inj

theorem coe_pnat_of_prime (p : nat.primes) : ↑(of_prime p) = ↑p ::ₘ 0 :=
  rfl

theorem coe_pnat_prime (v : prime_multiset) (p : ℕ+) (h : p ∈ ↑v) : pnat.prime p := sorry

protected instance coe_multiset_pnat_nat : has_coe (multiset ℕ+) (multiset ℕ) :=
  has_coe.mk fun (v : multiset ℕ+) => multiset.map (fun (n : ℕ+) => ↑n) v

theorem coe_pnat_nat (v : prime_multiset) : ↑↑v = ↑v := sorry

/-- The product of a `prime_multiset`, as a `ℕ+`. -/
def prod (v : prime_multiset) : ℕ+ :=
  multiset.prod ↑v

theorem coe_prod (v : prime_multiset) : ↑(prod v) = multiset.prod ↑v := sorry

theorem prod_of_prime (p : nat.primes) : prod (of_prime p) = ↑p := sorry

/-- If a `multiset ℕ` consists only of primes, it can be recast as a `prime_multiset`. -/
def of_nat_multiset (v : multiset ℕ) (h : ∀ (p : ℕ), p ∈ v → nat.prime p) : prime_multiset :=
  multiset.pmap (fun (p : ℕ) (hp : nat.prime p) => { val := p, property := hp }) v h

theorem to_of_nat_multiset (v : multiset ℕ) (h : ∀ (p : ℕ), p ∈ v → nat.prime p) : ↑(of_nat_multiset v h) = v := sorry

theorem prod_of_nat_multiset (v : multiset ℕ) (h : ∀ (p : ℕ), p ∈ v → nat.prime p) : ↑(prod (of_nat_multiset v h)) = multiset.prod v :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(prod (of_nat_multiset v h)) = multiset.prod v)) (coe_prod (of_nat_multiset v h))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (multiset.prod ↑(of_nat_multiset v h) = multiset.prod v)) (to_of_nat_multiset v h)))
      (Eq.refl (multiset.prod v)))

/-- If a `multiset ℕ+` consists only of primes, it can be recast as a `prime_multiset`. -/
def of_pnat_multiset (v : multiset ℕ+) (h : ∀ (p : ℕ+), p ∈ v → pnat.prime p) : prime_multiset :=
  multiset.pmap (fun (p : ℕ+) (hp : pnat.prime p) => { val := ↑p, property := hp }) v h

theorem to_of_pnat_multiset (v : multiset ℕ+) (h : ∀ (p : ℕ+), p ∈ v → pnat.prime p) : ↑(of_pnat_multiset v h) = v := sorry

theorem prod_of_pnat_multiset (v : multiset ℕ+) (h : ∀ (p : ℕ+), p ∈ v → pnat.prime p) : prod (of_pnat_multiset v h) = multiset.prod v := sorry

/-- Lists can be coerced to multisets; here we have some results
 about how this interacts with our constructions on multisets.
-/
def of_nat_list (l : List ℕ) (h : ∀ (p : ℕ), p ∈ l → nat.prime p) : prime_multiset :=
  of_nat_multiset (↑l) h

theorem prod_of_nat_list (l : List ℕ) (h : ∀ (p : ℕ), p ∈ l → nat.prime p) : ↑(prod (of_nat_list l h)) = list.prod l :=
  eq.mp (Eq._oldrec (Eq.refl (↑(prod (of_nat_multiset (↑l) h)) = multiset.prod ↑l)) (multiset.coe_prod l))
    (prod_of_nat_multiset (↑l) h)

/-- If a `list ℕ+` consists only of primes, it can be recast as a `prime_multiset` with
  the coercion from lists to multisets. -/
def of_pnat_list (l : List ℕ+) (h : ∀ (p : ℕ+), p ∈ l → pnat.prime p) : prime_multiset :=
  of_pnat_multiset (↑l) h

theorem prod_of_pnat_list (l : List ℕ+) (h : ∀ (p : ℕ+), p ∈ l → pnat.prime p) : prod (of_pnat_list l h) = list.prod l :=
  eq.mp (Eq._oldrec (Eq.refl (prod (of_pnat_multiset (↑l) h) = multiset.prod ↑l)) (multiset.coe_prod l))
    (prod_of_pnat_multiset (↑l) h)

/-- The product map gives a homomorphism from the additive monoid
 of multisets to the multiplicative monoid ℕ+.
-/
theorem prod_zero : prod 0 = 1 :=
  id multiset.prod_zero

theorem prod_add (u : prime_multiset) (v : prime_multiset) : prod (u + v) = prod u * prod v := sorry

theorem prod_smul (d : ℕ) (u : prime_multiset) : prod (d •ℕ u) = prod u ^ d := sorry

end prime_multiset


namespace pnat


/-- The prime factors of n, regarded as a multiset -/
def factor_multiset (n : ℕ+) : prime_multiset :=
  prime_multiset.of_nat_list (nat.factors ↑n) sorry

/-- The product of the factors is the original number -/
theorem prod_factor_multiset (n : ℕ+) : prime_multiset.prod (factor_multiset n) = n := sorry

theorem coe_nat_factor_multiset (n : ℕ+) : ↑(factor_multiset n) = ↑(nat.factors ↑n) :=
  prime_multiset.to_of_nat_multiset (↑(nat.factors ↑n)) nat.mem_factors

end pnat


namespace prime_multiset


/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factor_multiset_prod (v : prime_multiset) : pnat.factor_multiset (prod v) = v := sorry

end prime_multiset


namespace pnat


/-- Positive integers biject with multisets of primes. -/
def factor_multiset_equiv : ℕ+ ≃ prime_multiset :=
  equiv.mk factor_multiset prime_multiset.prod prod_factor_multiset prime_multiset.factor_multiset_prod

/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factor_multiset_one : factor_multiset 1 = 0 :=
  rfl

theorem factor_multiset_mul (n : ℕ+) (m : ℕ+) : factor_multiset (n * m) = factor_multiset n + factor_multiset m := sorry

theorem factor_multiset_pow (n : ℕ+) (m : ℕ) : factor_multiset (n ^ m) = m •ℕ factor_multiset n := sorry

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factor_multiset_of_prime (p : nat.primes) : factor_multiset ↑p = prime_multiset.of_prime p := sorry

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factor_multiset_le_iff {m : ℕ+} {n : ℕ+} : factor_multiset m ≤ factor_multiset n ↔ m ∣ n := sorry

theorem factor_multiset_le_iff' {m : ℕ+} {v : prime_multiset} : factor_multiset m ≤ v ↔ m ∣ prime_multiset.prod v := sorry

end pnat


namespace prime_multiset


theorem prod_dvd_iff {u : prime_multiset} {v : prime_multiset} : prod u ∣ prod v ↔ u ≤ v :=
  let h : pnat.factor_multiset (prod u) ≤ v ↔ prod u ∣ prod v := pnat.factor_multiset_le_iff';
  iff.symm (eq.mp (Eq._oldrec (Eq.refl (pnat.factor_multiset (prod u) ≤ v ↔ prod u ∣ prod v)) (factor_multiset_prod u)) h)

theorem prod_dvd_iff' {u : prime_multiset} {n : ℕ+} : prod u ∣ n ↔ u ≤ pnat.factor_multiset n := sorry

end prime_multiset


namespace pnat


/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets.
-/
theorem factor_multiset_gcd (m : ℕ+) (n : ℕ+) : factor_multiset (gcd m n) = factor_multiset m ⊓ factor_multiset n := sorry

theorem factor_multiset_lcm (m : ℕ+) (n : ℕ+) : factor_multiset (lcm m n) = factor_multiset m ⊔ factor_multiset n := sorry

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factor_multiset (m : ℕ+) (p : nat.primes) (k : ℕ) : ↑p ^ k ∣ m ↔ k ≤ multiset.count p (factor_multiset m) := sorry

end pnat


namespace prime_multiset


theorem prod_inf (u : prime_multiset) (v : prime_multiset) : prod (u ⊓ v) = pnat.gcd (prod u) (prod v) := sorry

theorem prod_sup (u : prime_multiset) (v : prime_multiset) : prod (u ⊔ v) = pnat.lcm (prod u) (prod v) := sorry

