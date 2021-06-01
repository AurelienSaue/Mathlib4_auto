/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.int.modeq
import Mathlib.algebra.char_p.basic
import Mathlib.data.nat.totient
import Mathlib.ring_theory.ideal.operations
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Integers mod `n`

Definition of the integers mod n, and the field structure on the integers mod p.


## Definitions

* `zmod n`, which is for integers modulo a nat `n : ℕ`

* `val a` is defined as a natural number:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

* `val_min_abs` returns the integer closest to zero in the equivalence class.

* A coercion `cast` is defined from `zmod n` into any ring.
This is a ring hom if the ring has characteristic dividing `n`

-/

namespace fin


/-!
## Ring structure on `fin n`

We define a commutative ring structure on `fin n`, but we do not register it as instance.
Afterwords, when we define `zmod n` in terms of `fin n`, we use these definitions
to register the ring structure on `zmod n` as type class instance.
-/

/-- Negation on `fin n` -/
def has_neg (n : ℕ) : Neg (fin n) :=
  { neg := fun (a : fin n) => { val := int.nat_mod (-↑(subtype.val a)) ↑n, property := sorry } }

/-- Multiplicative commutative semigroup structure on `fin (n+1)`. -/
def comm_semigroup (n : ℕ) : comm_semigroup (fin (n + 1)) := comm_semigroup.mk Mul.mul sorry sorry

/-- Commutative ring structure on `fin (n+1)`. -/
def comm_ring (n : ℕ) : comm_ring (fin (n + 1)) :=
  comm_ring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry Neg.neg
    (ring.sub._default add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry Neg.neg) sorry
    sorry comm_semigroup.mul sorry 1 fin.one_mul fin.mul_one (left_distrib_aux n) sorry sorry

end fin


/-- The integers modulo `n : ℕ`. -/
def zmod : ℕ → Type := sorry

namespace zmod


protected instance fintype (n : ℕ) [fact (0 < n)] : fintype (zmod n) := sorry

theorem card (n : ℕ) [fact (0 < n)] : fintype.card (zmod n) = n :=
  nat.cases_on n (fun [_inst_1 : fact (0 < 0)] => False._oldrec (nat.not_lt_zero 0 _inst_1))
    (fun (n : ℕ) => fintype.card_fin (n + 1)) _inst_1

protected instance decidable_eq (n : ℕ) : DecidableEq (zmod n) := sorry

protected instance has_repr (n : ℕ) : has_repr (zmod n) := sorry

protected instance comm_ring (n : ℕ) : comm_ring (zmod n) := sorry

protected instance inhabited (n : ℕ) : Inhabited (zmod n) := { default := 0 }

/-- `val a` is a natural number defined as:
  - for `a : zmod 0` it is the absolute value of `a`
  - for `a : zmod n` with `0 < n` it is the least natural number in the equivalence class

See `zmod.val_min_abs` for a variant that takes values in the integers.
-/
def val {n : ℕ} : zmod n → ℕ := sorry

theorem val_lt {n : ℕ} [fact (0 < n)] (a : zmod n) : val a < n :=
  nat.cases_on n
    (fun [_inst_1 : fact (0 < 0)] (a : zmod 0) => False._oldrec (nat.not_lt_zero 0 _inst_1))
    (fun (n : ℕ) (a : zmod (Nat.succ n)) => fin.is_lt a) _inst_1 a

@[simp] theorem val_zero {n : ℕ} : val 0 = 0 :=
  nat.cases_on n (idRhs (val 0 = val 0) rfl) fun (n : ℕ) => idRhs (val 0 = val 0) rfl

theorem val_cast_nat {n : ℕ} (a : ℕ) : val ↑a = a % n := sorry

protected instance char_p (n : ℕ) : char_p (zmod n) n := sorry

@[simp] theorem cast_self (n : ℕ) : ↑n = 0 := char_p.cast_eq_zero (zmod n) n

@[simp] theorem cast_self' (n : ℕ) : ↑n + 1 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n + 1 = 0)) (Eq.symm (nat.cast_add_one n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(n + 1) = 0)) (cast_self (n + 1)))) (Eq.refl 0))

/-- Cast an integer modulo `n` to another semiring.
This function is a morphism if the characteristic of `R` divides `n`.
See `zmod.cast_hom` for a bundled version. -/
def cast {R : Type u_1} [HasZero R] [HasOne R] [Add R] [Neg R] {n : ℕ} : zmod n → R := sorry

-- see Note [coercion into rings]

protected instance has_coe_t {R : Type u_1} [HasZero R] [HasOne R] [Add R] [Neg R] (n : ℕ) :
    has_coe_t (zmod n) R :=
  has_coe_t.mk cast

@[simp] theorem cast_zero {n : ℕ} {R : Type u_1} [HasZero R] [HasOne R] [Add R] [Neg R] : ↑0 = 0 :=
  nat.cases_on n (Eq.refl ↑0) fun (n : ℕ) => Eq.refl ↑0

theorem nat_cast_surjective {n : ℕ} [fact (0 < n)] : function.surjective coe := sorry

theorem int_cast_surjective {n : ℕ} : function.surjective coe := sorry

theorem cast_val {n : ℕ} [fact (0 < n)] (a : zmod n) : ↑(val a) = a := sorry

@[simp] theorem cast_id (n : ℕ) (i : zmod n) : ↑i = i :=
  nat.cases_on n (fun (i : zmod 0) => idRhs (↑i = i) (int.cast_id i))
    (fun (n : ℕ) (i : zmod (Nat.succ n)) => idRhs (↑(val i) = i) (cast_val i)) i

@[simp] theorem nat_cast_val {n : ℕ} {R : Type u_1} [ring R] [fact (0 < n)] (i : zmod n) :
    ↑(val i) = ↑i :=
  nat.cases_on n
    (fun [_inst_2 : fact (0 < 0)] (i : zmod 0) => False._oldrec (nat.not_lt_zero 0 _inst_2))
    (fun (n : ℕ) (i : zmod (Nat.succ n)) => Eq.refl ↑(val i)) _inst_2 i

/-! If the characteristic of `R` divides `n`, then `cast` is a homomorphism. -/

@[simp] theorem cast_one {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n) :
    ↑1 = 1 :=
  sorry

theorem cast_add {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n) (a : zmod n)
    (b : zmod n) : ↑(a + b) = ↑a + ↑b :=
  sorry

theorem cast_mul {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n) (a : zmod n)
    (b : zmod n) : ↑(a * b) = ↑a * ↑b :=
  sorry

/-- The canonical ring homomorphism from `zmod n` to a ring of characteristic `n`. -/
def cast_hom {n : ℕ} {m : ℕ} (h : m ∣ n) (R : Type u_1) [ring R] [char_p R m] : zmod n →+* R :=
  ring_hom.mk coe (cast_one h) (cast_mul h) sorry (cast_add h)

@[simp] theorem cast_hom_apply {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] {h : m ∣ n}
    (i : zmod n) : coe_fn (cast_hom h R) i = ↑i :=
  rfl

@[simp] theorem cast_sub {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n)
    (a : zmod n) (b : zmod n) : ↑(a - b) = ↑a - ↑b :=
  ring_hom.map_sub (cast_hom h R) a b

@[simp] theorem cast_neg {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n)
    (a : zmod n) : ↑(-a) = -↑a :=
  ring_hom.map_neg (cast_hom h R) a

@[simp] theorem cast_pow {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n)
    (a : zmod n) (k : ℕ) : ↑(a ^ k) = ↑a ^ k :=
  ring_hom.map_pow (cast_hom h R) a k

@[simp] theorem cast_nat_cast {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n)
    (k : ℕ) : ↑↑k = ↑k :=
  ring_hom.map_nat_cast (cast_hom h R) k

@[simp] theorem cast_int_cast {n : ℕ} {R : Type u_1} [ring R] {m : ℕ} [char_p R m] (h : m ∣ n)
    (k : ℤ) : ↑↑k = ↑k :=
  ring_hom.map_int_cast (cast_hom h R) k

/-! Some specialised simp lemmas which apply when `R` has characteristic `n`. -/

@[simp] theorem cast_one' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] : ↑1 = 1 :=
  cast_one (dvd_refl n)

@[simp] theorem cast_add' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] (a : zmod n) (b : zmod n) :
    ↑(a + b) = ↑a + ↑b :=
  cast_add (dvd_refl n) a b

@[simp] theorem cast_mul' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] (a : zmod n) (b : zmod n) :
    ↑(a * b) = ↑a * ↑b :=
  cast_mul (dvd_refl n) a b

@[simp] theorem cast_sub' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] (a : zmod n) (b : zmod n) :
    ↑(a - b) = ↑a - ↑b :=
  cast_sub (dvd_refl n) a b

@[simp] theorem cast_pow' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] (a : zmod n) (k : ℕ) :
    ↑(a ^ k) = ↑a ^ k :=
  cast_pow (dvd_refl n) a k

@[simp] theorem cast_nat_cast' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] (k : ℕ) : ↑↑k = ↑k :=
  cast_nat_cast (dvd_refl n) k

@[simp] theorem cast_int_cast' {n : ℕ} {R : Type u_1} [ring R] [char_p R n] (k : ℤ) : ↑↑k = ↑k :=
  cast_int_cast (dvd_refl n) k

protected instance algebra {n : ℕ} (R : Type u_1) [comm_ring R] [char_p R n] : algebra (zmod n) R :=
  ring_hom.to_algebra (cast_hom (dvd_refl n) R)

theorem cast_hom_injective {n : ℕ} (R : Type u_1) [ring R] [char_p R n] :
    function.injective ⇑(cast_hom (dvd_refl n) R) :=
  sorry

theorem cast_hom_bijective {n : ℕ} (R : Type u_1) [ring R] [char_p R n] [fintype R]
    (h : fintype.card R = n) : function.bijective ⇑(cast_hom (dvd_refl n) R) :=
  sorry

/-- The unique ring isomorphism between `zmod n` and a ring `R`
of characteristic `n` and cardinality `n`. -/
def ring_equiv {n : ℕ} (R : Type u_1) [ring R] [char_p R n] [fintype R] (h : fintype.card R = n) :
    zmod n ≃+* R :=
  ring_equiv.of_bijective (cast_hom (dvd_refl n) R) (cast_hom_bijective R h)

theorem int_coe_eq_int_coe_iff (a : ℤ) (b : ℤ) (c : ℕ) : ↑a = ↑b ↔ int.modeq (↑c) a b :=
  char_p.int_coe_eq_int_coe_iff (zmod c) c a b

theorem nat_coe_eq_nat_coe_iff (a : ℕ) (b : ℕ) (c : ℕ) : ↑a = ↑b ↔ nat.modeq c a b := sorry

theorem int_coe_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : ↑a = 0 ↔ ↑b ∣ a := sorry

theorem nat_coe_zmod_eq_zero_iff_dvd (a : ℕ) (b : ℕ) : ↑a = 0 ↔ b ∣ a := sorry

@[simp] theorem cast_mod_int (a : ℤ) (b : ℕ) : ↑(a % ↑b) = ↑a :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (↑(a % ↑b) = ↑a)) (propext (int_coe_eq_int_coe_iff (a % ↑b) a b))))
    (int.modeq.mod_modeq a ↑b)

@[simp] theorem coe_to_nat (p : ℕ) {z : ℤ} (h : 0 ≤ z) : ↑(int.to_nat z) = ↑z := sorry

theorem val_injective (n : ℕ) [fact (0 < n)] : function.injective val :=
  nat.cases_on n
    (fun [_inst_1 : fact (0 < 0)] =>
      id fun (a₁ : zmod 0) => False._oldrec (nat.not_lt_zero 0 _inst_1))
    (fun (n : ℕ) => id fun (a b : zmod (Nat.succ n)) (h : val a = val b) => fin.ext h) _inst_1

theorem val_one_eq_one_mod (n : ℕ) : val 1 = 1 % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (val 1 = 1 % n)) (Eq.symm nat.cast_one)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (val ↑1 = 1 % n)) (val_cast_nat 1))) (Eq.refl (1 % n)))

theorem val_one (n : ℕ) [fact (1 < n)] : val 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (val 1 = 1)) (val_one_eq_one_mod n))) (nat.mod_eq_of_lt _inst_1)

theorem val_add {n : ℕ} [fact (0 < n)] (a : zmod n) (b : zmod n) :
    val (a + b) = (val a + val b) % n :=
  nat.cases_on n
    (fun [_inst_1 : fact (0 < 0)] (a b : zmod 0) => False._oldrec (nat.not_lt_zero 0 _inst_1))
    (fun (n : ℕ) (a b : zmod (Nat.succ n)) => fin.val_add a b) _inst_1 a b

theorem val_mul {n : ℕ} (a : zmod n) (b : zmod n) : val (a * b) = val a * val b % n := sorry

protected instance nontrivial (n : ℕ) [fact (1 < n)] : nontrivial (zmod n) :=
  nontrivial.mk
    (Exists.intro 0
      (Exists.intro 1
        fun (h : 0 = 1) =>
          zero_ne_one
            (Eq.trans
              (Eq.trans (eq.mpr (id (Eq._oldrec (Eq.refl (0 = val 0)) val_zero)) (Eq.refl 0))
                (congr_arg val h))
              (val_one n))))

/-- The inversion on `zmod n`.
It is setup in such a way that `a * a⁻¹` is equal to `gcd a.val n`.
In particular, if `a` is coprime to `n`, and hence a unit, `a * a⁻¹ = 1`. -/
def inv (n : ℕ) : zmod n → zmod n := sorry

protected instance has_inv (n : ℕ) : has_inv (zmod n) := has_inv.mk (inv n)

theorem inv_zero (n : ℕ) : 0⁻¹ = 0 := sorry

theorem mul_inv_eq_gcd {n : ℕ} (a : zmod n) : a * (a⁻¹) = ↑(nat.gcd (val a) n) := sorry

@[simp] theorem cast_mod_nat (n : ℕ) (a : ℕ) : ↑(a % n) = ↑a := sorry

theorem eq_iff_modeq_nat (n : ℕ) {a : ℕ} {b : ℕ} : ↑a = ↑b ↔ nat.modeq n a b := sorry

theorem coe_mul_inv_eq_one {n : ℕ} (x : ℕ) (h : nat.coprime x n) : ↑x * (↑x⁻¹) = 1 := sorry

/-- `unit_of_coprime` makes an element of `units (zmod n)` given
  a natural number `x` and a proof that `x` is coprime to `n`  -/
def unit_of_coprime {n : ℕ} (x : ℕ) (h : nat.coprime x n) : units (zmod n) :=
  units.mk (↑x) (↑x⁻¹) (coe_mul_inv_eq_one x h) sorry

@[simp] theorem cast_unit_of_coprime {n : ℕ} (x : ℕ) (h : nat.coprime x n) :
    ↑(unit_of_coprime x h) = ↑x :=
  rfl

theorem val_coe_unit_coprime {n : ℕ} (u : units (zmod n)) : nat.coprime (val ↑u) n := sorry

@[simp] theorem inv_coe_unit {n : ℕ} (u : units (zmod n)) : ↑u⁻¹ = ↑(u⁻¹) := sorry

theorem mul_inv_of_unit {n : ℕ} (a : zmod n) (h : is_unit a) : a * (a⁻¹) = 1 := sorry

theorem inv_mul_of_unit {n : ℕ} (a : zmod n) (h : is_unit a) : a⁻¹ * a = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a⁻¹ * a = 1)) (mul_comm (a⁻¹) a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * (a⁻¹) = 1)) (mul_inv_of_unit a h))) (Eq.refl 1))

/-- Equivalence between the units of `zmod n` and
the subtype of terms `x : zmod n` for which `x.val` is comprime to `n` -/
def units_equiv_coprime {n : ℕ} [fact (0 < n)] :
    units (zmod n) ≃ Subtype fun (x : zmod n) => nat.coprime (val x) n :=
  equiv.mk (fun (x : units (zmod n)) => { val := ↑x, property := val_coe_unit_coprime x })
    (fun (x : Subtype fun (x : zmod n) => nat.coprime (val x) n) =>
      unit_of_coprime (val (subtype.val x)) sorry)
    sorry sorry

@[simp] theorem card_units_eq_totient (n : ℕ) [fact (0 < n)] :
    fintype.card (units (zmod n)) = nat.totient n :=
  sorry

protected instance subsingleton_units : subsingleton (units (zmod (bit0 1))) :=
  subsingleton.intro
    fun (x y : units (zmod (bit0 1))) =>
      units.cases_on x
        fun (x xi : zmod (bit0 1)) (x_val_inv : x * xi = 1) (x_inv_val : xi * x = 1) =>
          units.cases_on y
            fun (y yi : zmod (bit0 1)) (y_val_inv : y * yi = 1) (y_inv_val : yi * y = 1) =>
              of_as_true trivial x y xi yi x_val_inv x_inv_val y_val_inv y_inv_val

theorem le_div_two_iff_lt_neg (n : ℕ) [hn : fact (n % bit0 1 = 1)] {x : zmod n} (hx0 : x ≠ 0) :
    val x ≤ n / bit0 1 ↔ n / bit0 1 < val (-x) :=
  sorry

theorem ne_neg_self (n : ℕ) [hn : fact (n % bit0 1 = 1)] {a : zmod n} (ha : a ≠ 0) : a ≠ -a := sorry

theorem neg_one_ne_one {n : ℕ} [fact (bit0 1 < n)] : -1 ≠ 1 := char_p.neg_one_ne_one (zmod n) n

@[simp] theorem neg_eq_self_mod_two (a : zmod (bit0 1)) : -a = a := of_as_true trivial

@[simp] theorem nat_abs_mod_two (a : ℤ) : ↑(int.nat_abs a) = ↑a := sorry

@[simp] theorem val_eq_zero {n : ℕ} (a : zmod n) : val a = 0 ↔ a = 0 := sorry

theorem val_cast_of_lt {n : ℕ} {a : ℕ} (h : a < n) : val ↑a = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (val ↑a = a)) (val_cast_nat a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a % n = a)) (nat.mod_eq_of_lt h))) (Eq.refl a))

theorem neg_val' {n : ℕ} [fact (0 < n)] (a : zmod n) : val (-a) = (n - val a) % n := sorry

theorem neg_val {n : ℕ} [fact (0 < n)] (a : zmod n) : val (-a) = ite (a = 0) 0 (n - val a) := sorry

/-- `val_min_abs x` returns the integer in the same equivalence class as `x` that is closest to `0`,
  The result will be in the interval `(-n/2, n/2]`. -/
def val_min_abs {n : ℕ} : zmod n → ℤ := sorry

@[simp] theorem val_min_abs_def_zero (x : zmod 0) : val_min_abs x = x := rfl

theorem val_min_abs_def_pos {n : ℕ} [fact (0 < n)] (x : zmod n) :
    val_min_abs x = ite (val x ≤ n / bit0 1) (↑(val x)) (↑(val x) - ↑n) :=
  nat.cases_on n
    (fun [_inst_1 : fact (0 < 0)] (x : zmod 0) => False._oldrec (nat.not_lt_zero 0 _inst_1))
    (fun (n : ℕ) (x : zmod (Nat.succ n)) => Eq.refl (val_min_abs x)) _inst_1 x

@[simp] theorem coe_val_min_abs {n : ℕ} (x : zmod n) : ↑(val_min_abs x) = x := sorry

theorem nat_abs_val_min_abs_le {n : ℕ} [fact (0 < n)] (x : zmod n) :
    int.nat_abs (val_min_abs x) ≤ n / bit0 1 :=
  sorry

@[simp] theorem val_min_abs_zero (n : ℕ) : val_min_abs 0 = 0 := sorry

@[simp] theorem val_min_abs_eq_zero {n : ℕ} (x : zmod n) : val_min_abs x = 0 ↔ x = 0 := sorry

theorem cast_nat_abs_val_min_abs {n : ℕ} [fact (0 < n)] (a : zmod n) :
    ↑(int.nat_abs (val_min_abs a)) = ite (val a ≤ n / bit0 1) a (-a) :=
  sorry

@[simp] theorem nat_abs_val_min_abs_neg {n : ℕ} (a : zmod n) :
    int.nat_abs (val_min_abs (-a)) = int.nat_abs (val_min_abs a) :=
  sorry

theorem val_eq_ite_val_min_abs {n : ℕ} [fact (0 < n)] (a : zmod n) :
    ↑(val a) = val_min_abs a + ite (val a ≤ n / bit0 1) 0 ↑n :=
  sorry

theorem prime_ne_zero (p : ℕ) (q : ℕ) [hp : fact (nat.prime p)] [hq : fact (nat.prime q)]
    (hpq : p ≠ q) : ↑q ≠ 0 :=
  sorry

end zmod


namespace zmod


/-- Field structure on `zmod p` if `p` is prime. -/
protected instance field (p : ℕ) [fact (nat.prime p)] : field (zmod p) :=
  field.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry
    comm_ring.mul sorry comm_ring.one sorry sorry sorry sorry sorry has_inv.inv sorry
    (mul_inv_cancel_aux p) (inv_zero p)

end zmod


theorem ring_hom.ext_zmod {n : ℕ} {R : Type u_1} [semiring R] (f : zmod n →+* R)
    (g : zmod n →+* R) : f = g :=
  sorry

namespace zmod


protected instance subsingleton_ring_hom {n : ℕ} {R : Type u_1} [semiring R] :
    subsingleton (zmod n →+* R) :=
  subsingleton.intro ring_hom.ext_zmod

protected instance subsingleton_ring_equiv {n : ℕ} {R : Type u_1} [semiring R] :
    subsingleton (zmod n ≃+* R) :=
  subsingleton.intro
    fun (f g : zmod n ≃+* R) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (f = g)) (propext (ring_equiv.coe_ring_hom_inj_iff f g))))
        (ring_hom.ext_zmod ↑f ↑g)

theorem ring_hom_surjective {n : ℕ} {R : Type u_1} [ring R] (f : R →+* zmod n) :
    function.surjective ⇑f :=
  sorry

theorem ring_hom_eq_of_ker_eq {n : ℕ} {R : Type u_1} [comm_ring R] (f : R →+* zmod n)
    (g : R →+* zmod n) (h : ring_hom.ker f = ring_hom.ker g) : f = g :=
  sorry

end Mathlib