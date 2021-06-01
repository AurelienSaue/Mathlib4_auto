/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Scott Morrison, Ainsley Pahljina
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ring_exp
import Mathlib.tactic.interval_cases
import Mathlib.data.nat.parity
import Mathlib.data.zmod.basic
import Mathlib.group_theory.order_of_element
import Mathlib.ring_theory.fintype
import Mathlib.PostPort

namespace Mathlib

/-!
# The Lucas-Lehmer test for Mersenne primes.

We define `lucas_lehmer_residue : Π p : ℕ, zmod (2^p - 1)`, and
prove `lucas_lehmer_residue p = 0 → prime (mersenne p)`.

We construct a tactic `lucas_lehmer.run_test`, which iteratively certifies the arithmetic
required to calculate the residue, and enables us to prove

```
example : prime (mersenne 127) :=
lucas_lehmer_sufficiency _ (by norm_num) (by lucas_lehmer.run_test)
```

## TODO

- Show reverse implication.
- Speed up the calculations using `n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]`.
- Find some bigger primes!

## History

This development began as a student project by Ainsley Pahljina,
and was then cleaned up for mathlib by Scott Morrison.
The tactic for certified computation of Lucas-Lehmer residues was provided by Mario Carneiro.
-/

/-- The Mersenne numbers, 2^p - 1. -/
def mersenne (p : ℕ) : ℕ := bit0 1 ^ p - 1

theorem mersenne_pos {p : ℕ} (h : 0 < p) : 0 < mersenne p := sorry

@[simp] theorem succ_mersenne (k : ℕ) : mersenne k + 1 = bit0 1 ^ k := sorry

namespace lucas_lehmer


/-!
We now define three(!) different versions of the recurrence
`s (i+1) = (s i)^2 - 2`.

These versions take values either in `ℤ`, in `zmod (2^p - 1)`, or
in `ℤ` but applying `% (2^p - 1)` at each step.

They are each useful at different points in the proof,
so we take a moment setting up the lemmas relating them.
-/

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `ℤ`. -/
def s : ℕ → ℤ := sorry

/-- The recurrence `s (i+1) = (s i)^2 - 2` in `zmod (2^p - 1)`. -/
def s_zmod (p : ℕ) : ℕ → zmod (bit0 1 ^ p - 1) := sorry

/-- The recurrence `s (i+1) = ((s i)^2 - 2) % (2^p - 1)` in `ℤ`. -/
def s_mod (p : ℕ) : ℕ → ℤ := sorry

theorem mersenne_int_ne_zero (p : ℕ) (w : 0 < p) : bit0 1 ^ p - 1 ≠ 0 := sorry

theorem s_mod_nonneg (p : ℕ) (w : 0 < p) (i : ℕ) : 0 ≤ s_mod p i :=
  nat.cases_on i (id (iff.mp sup_eq_left rfl))
    fun (i : ℕ) => id (int.mod_nonneg (s_mod p i ^ bit0 1 - bit0 1) (mersenne_int_ne_zero p w))

theorem s_mod_mod (p : ℕ) (i : ℕ) : s_mod p i % (bit0 1 ^ p - 1) = s_mod p i := sorry

theorem s_mod_lt (p : ℕ) (w : 0 < p) (i : ℕ) : s_mod p i < bit0 1 ^ p - 1 := sorry

theorem s_zmod_eq_s (p' : ℕ) (i : ℕ) : s_zmod (p' + bit0 1) i = ↑(s i) := sorry

-- These next two don't make good `norm_cast` lemmas.

theorem int.coe_nat_pow_pred (b : ℕ) (p : ℕ) (w : 0 < b) : ↑(b ^ p - 1) = ↑b ^ p - 1 := sorry

theorem int.coe_nat_two_pow_pred (p : ℕ) : ↑(bit0 1 ^ p - 1) = bit0 1 ^ p - 1 :=
  int.coe_nat_pow_pred (bit0 1) p (of_as_true trivial)

theorem s_zmod_eq_s_mod (p : ℕ) (i : ℕ) : s_zmod p i = ↑(s_mod p i) := sorry

/-- The Lucas-Lehmer residue is `s p (p-2)` in `zmod (2^p - 1)`. -/
def lucas_lehmer_residue (p : ℕ) : zmod (bit0 1 ^ p - 1) := s_zmod p (p - bit0 1)

theorem residue_eq_zero_iff_s_mod_eq_zero (p : ℕ) (w : 1 < p) :
    lucas_lehmer_residue p = 0 ↔ s_mod p (p - bit0 1) = 0 :=
  sorry

/--
A Mersenne number `2^p-1` is prime if and only if
the Lucas-Lehmer residue `s p (p-2) % (2^p - 1)` is zero.
-/
def lucas_lehmer_test (p : ℕ) := lucas_lehmer_residue p = 0

/-- `q` is defined as the minimum factor of `mersenne p`, bundled as an `ℕ+`. -/
def q (p : ℕ) : ℕ+ := { val := nat.min_fac (mersenne p), property := sorry }

protected instance fact_pnat_pos (q : ℕ+) : fact (0 < ↑q) := subtype.property q

/-- We construct the ring `X q` as ℤ/qℤ + √3 ℤ/qℤ. -/
-- It would be nice to define this as (ℤ/qℤ)[x] / (x^2 - 3),

-- obtaining the ring structure for free,

-- but that seems to be more trouble than it's worth;

-- if it were easy to make the definition,

-- cardinality calculations would be somewhat more involved, too.

def X (q : ℕ+) := zmod ↑q × zmod ↑q

namespace X


theorem ext {q : ℕ+} {x : X q} {y : X q} (h₁ : prod.fst x = prod.fst y)
    (h₂ : prod.snd x = prod.snd y) : x = y :=
  sorry

@[simp] theorem add_fst {q : ℕ+} (x : X q) (y : X q) : prod.fst (x + y) = prod.fst x + prod.fst y :=
  rfl

@[simp] theorem add_snd {q : ℕ+} (x : X q) (y : X q) : prod.snd (x + y) = prod.snd x + prod.snd y :=
  rfl

@[simp] theorem neg_fst {q : ℕ+} (x : X q) : prod.fst (-x) = -prod.fst x := rfl

@[simp] theorem neg_snd {q : ℕ+} (x : X q) : prod.snd (-x) = -prod.snd x := rfl

protected instance has_mul {q : ℕ+} : Mul (X q) :=
  { mul :=
      fun (x y : X q) =>
        (prod.fst x * prod.fst y + bit1 1 * prod.snd x * prod.snd y,
        prod.fst x * prod.snd y + prod.snd x * prod.fst y) }

@[simp] theorem mul_fst {q : ℕ+} (x : X q) (y : X q) :
    prod.fst (x * y) = prod.fst x * prod.fst y + bit1 1 * prod.snd x * prod.snd y :=
  rfl

@[simp] theorem mul_snd {q : ℕ+} (x : X q) (y : X q) :
    prod.snd (x * y) = prod.fst x * prod.snd y + prod.snd x * prod.fst y :=
  rfl

protected instance has_one {q : ℕ+} : HasOne (X q) := { one := (1, 0) }

@[simp] theorem one_fst {q : ℕ+} : prod.fst 1 = 1 := rfl

@[simp] theorem one_snd {q : ℕ+} : prod.snd 1 = 0 := rfl

@[simp] theorem bit0_fst {q : ℕ+} (x : X q) : prod.fst (bit0 x) = bit0 (prod.fst x) := rfl

@[simp] theorem bit0_snd {q : ℕ+} (x : X q) : prod.snd (bit0 x) = bit0 (prod.snd x) := rfl

@[simp] theorem bit1_fst {q : ℕ+} (x : X q) : prod.fst (bit1 x) = bit1 (prod.fst x) := rfl

@[simp] theorem bit1_snd {q : ℕ+} (x : X q) : prod.snd (bit1 x) = bit0 (prod.snd x) := sorry

protected instance monoid {q : ℕ+} : monoid (X q) := monoid.mk Mul.mul sorry (1, 0) sorry sorry

theorem left_distrib {q : ℕ+} (x : X q) (y : X q) (z : X q) : x * (y + z) = x * y + x * z := sorry

theorem right_distrib {q : ℕ+} (x : X q) (y : X q) (z : X q) : (x + y) * z = x * z + y * z := sorry

protected instance ring {q : ℕ+} : ring (X q) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg
    add_comm_group.sub sorry sorry monoid.mul sorry monoid.one sorry sorry left_distrib
    right_distrib

protected instance comm_ring {q : ℕ+} : comm_ring (X q) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry
    ring.one sorry sorry sorry sorry sorry

protected instance nontrivial {q : ℕ+} [fact (1 < ↑q)] : nontrivial (X q) :=
  nontrivial.mk
    (Exists.intro 0
      (Exists.intro 1
        fun (h : 0 = 1) => prod.mk.inj_arrow h fun (h1 : 0 = 1) (ᾰ : 0 = 0) => zero_ne_one h1))

@[simp] theorem nat_coe_fst {q : ℕ+} (n : ℕ) : prod.fst ↑n = ↑n :=
  Nat.rec (Eq.refl (prod.fst ↑0))
    (fun (n_n : ℕ) (n_ih : prod.fst ↑n_n = ↑n_n) =>
      id (eq.mpr (id (propext (add_left_inj 1))) n_ih))
    n

@[simp] theorem nat_coe_snd {q : ℕ+} (n : ℕ) : prod.snd ↑n = 0 := sorry

@[simp] theorem int_coe_fst {q : ℕ+} (n : ℤ) : prod.fst ↑n = ↑n := sorry

@[simp] theorem int_coe_snd {q : ℕ+} (n : ℤ) : prod.snd ↑n = 0 := sorry

theorem coe_mul {q : ℕ+} (n : ℤ) (m : ℤ) : ↑(n * m) = ↑n * ↑m := sorry

theorem coe_nat {q : ℕ+} (n : ℕ) : ↑↑n = ↑n := sorry

/-- The cardinality of `X` is `q^2`. -/
theorem X_card {q : ℕ+} : fintype.card (X q) = ↑q ^ bit0 1 := sorry

/-- There are strictly fewer than `q^2` units, since `0` is not a unit. -/
theorem units_card {q : ℕ+} (w : 1 < q) : fintype.card (units (X q)) < ↑q ^ bit0 1 := sorry

/-- We define `ω = 2 + √3`. -/
/-- We define `ωb = 2 - √3`, which is the inverse of `ω`. -/
def ω {q : ℕ+} : X q := (bit0 1, 1)

def ωb {q : ℕ+} : X q := (bit0 1, -1)

theorem ω_mul_ωb (q : ℕ+) : ω * ωb = 1 := sorry

theorem ωb_mul_ω (q : ℕ+) : ωb * ω = 1 := sorry

/-- A closed form for the recurrence relation. -/
theorem closed_form {q : ℕ+} (i : ℕ) : ↑(s i) = ω ^ bit0 1 ^ i + ωb ^ bit0 1 ^ i := sorry

end X


/-!
Here and below, we introduce `p' = p - 2`, in order to avoid using subtraction in `ℕ`.
-/

/-- If `1 < p`, then `q p`, the smallest prime factor of `mersenne p`, is more than 2. -/
theorem two_lt_q (p' : ℕ) : bit0 1 < q (p' + bit0 1) := sorry

theorem ω_pow_formula (p' : ℕ) (h : lucas_lehmer_residue (p' + bit0 1) = 0) :
    ∃ (k : ℤ), X.ω ^ bit0 1 ^ (p' + 1) = ↑k * ↑(mersenne (p' + bit0 1)) * X.ω ^ bit0 1 ^ p' - 1 :=
  sorry

/-- `q` is the minimum factor of `mersenne p`, so `M p = 0` in `X q`. -/
theorem mersenne_coe_X (p : ℕ) : ↑(mersenne p) = 0 := sorry

theorem ω_pow_eq_neg_one (p' : ℕ) (h : lucas_lehmer_residue (p' + bit0 1) = 0) :
    X.ω ^ bit0 1 ^ (p' + 1) = -1 :=
  sorry

theorem ω_pow_eq_one (p' : ℕ) (h : lucas_lehmer_residue (p' + bit0 1) = 0) :
    X.ω ^ bit0 1 ^ (p' + bit0 1) = 1 :=
  sorry

/-- `ω` as an element of the group of units. -/
def ω_unit (p : ℕ) : units (X (q p)) := units.mk X.ω X.ωb sorry sorry

@[simp] theorem ω_unit_coe (p : ℕ) : ↑(ω_unit p) = X.ω := rfl

/-- The order of `ω` in the unit group is exactly `2^p`. -/
theorem order_ω (p' : ℕ) (h : lucas_lehmer_residue (p' + bit0 1) = 0) :
    order_of (ω_unit (p' + bit0 1)) = bit0 1 ^ (p' + bit0 1) :=
  sorry

theorem order_ineq (p' : ℕ) (h : lucas_lehmer_residue (p' + bit0 1) = 0) :
    bit0 1 ^ (p' + bit0 1) < ↑(q (p' + bit0 1)) ^ bit0 1 :=
  lt_of_le_of_lt (trans_rel_right LessEq (Eq.symm (order_ω p' h)) order_of_le_card_univ)
    (X.units_card (nat.lt_of_succ_lt (two_lt_q p')))

end lucas_lehmer


theorem lucas_lehmer_sufficiency (p : ℕ) (w : 1 < p) :
    lucas_lehmer_test p → nat.prime (mersenne p) :=
  sorry

-- Here we calculate the residue, very inefficiently, using `dec_trivial`. We can do much better.

-- Next we use `norm_num` to calculate each `s p i`.

namespace lucas_lehmer


theorem s_mod_succ {p : ℕ} {a : ℤ} {i : ℕ} {b : ℤ} {c : ℤ} (h1 : bit0 1 ^ p - 1 = a)
    (h2 : s_mod p i = b) (h3 : (b * b - bit0 1) % a = c) : s_mod p (i + 1) = c :=
  sorry

/--
Given a goal of the form `lucas_lehmer_test p`,
attempt to do the calculation using `norm_num` to certify each step.
-/
end lucas_lehmer


/-- We verify that the tactic works to prove `127.prime`. -/
/-!
This implementation works successfully to prove `(2^127 - 1).prime`,
and all the Mersenne primes up to this point appear in [archive/examples/mersenne_primes.lean].

`(2^127 - 1).prime` takes about 5 minutes to run (depending on your CPU!),
and unfortunately the next Mersenne prime `(2^521 - 1)`,
which was the first "computer era" prime,
is out of reach with the current implementation.

There's still low hanging fruit available to do faster computations
based on the formula
  n ≡ (n % 2^p) + (n / 2^p) [MOD 2^p - 1]
and the fact that `% 2^p` and `/ 2^p` can be very efficient on the binary representation.
Someone should do this, too!
-/

-- See https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/help.20finding.20a.20lemma/near/177698446

theorem modeq_mersenne (n : ℕ) (k : ℕ) :
    nat.modeq (bit0 1 ^ n - 1) k (k / bit0 1 ^ n + k % bit0 1 ^ n) :=
  sorry

end Mathlib