/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.encodable.basic
import Mathlib.algebra.euclidean_domain
import Mathlib.data.nat.gcd
import Mathlib.data.int.cast
import PostPort

universes l u 

namespace Mathlib

/-!
# Basics for the Rational Numbers

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

We then define the expected (discrete) field structure on `ℚ` and prove basic lemmas about it.
Moreoever, we provide the expected casts from `ℕ` and `ℤ` into `ℚ`, i.e. `(↑n : ℚ) = n / 1`.

## Main Definitions

- `rat` is the structure encoding `ℚ`.
- `rat.mk n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure rat 
  mk' ::
where (num : ℤ) (denom : ℕ) (pos : 0 < denom) (cop : nat.coprime (int.nat_abs num) denom)

notation:1024 "ℚ" => Mathlib.rat

namespace rat


protected def repr : ℚ → string :=
  sorry

protected instance has_repr : has_repr ℚ :=
  has_repr.mk rat.repr

protected instance has_to_string : has_to_string ℚ :=
  has_to_string.mk rat.repr

protected instance encodable : encodable ℚ :=
  encodable.of_equiv (sigma fun (n : ℤ) => Subtype fun (d : ℕ) => 0 < d ∧ nat.coprime (int.nat_abs n) d)
    (equiv.mk (fun (_x : ℚ) => sorry)
      (fun (_x : sigma fun (n : ℤ) => Subtype fun (d : ℕ) => 0 < d ∧ nat.coprime (int.nat_abs n) d) => sorry) sorry sorry)

/-- Embed an integer as a rational number -/
def of_int (n : ℤ) : ℚ :=
  mk' n 1 nat.one_pos sorry

protected instance has_zero : HasZero ℚ :=
  { zero := of_int 0 }

protected instance has_one : HasOne ℚ :=
  { one := of_int 1 }

protected instance inhabited : Inhabited ℚ :=
  { default := 0 }

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mk_pnat (n : ℤ) : ℕ+ → ℚ :=
  sorry

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mk_nat (n : ℤ) (d : ℕ) : ℚ :=
  dite (d = 0) (fun (d0 : d = 0) => 0) fun (d0 : ¬d = 0) => mk_pnat n { val := d, property := nat.pos_of_ne_zero d0 }

/-- Form the quotient `n / d` where `n d : ℤ`. -/
def mk : ℤ → ℤ → ℚ :=
  sorry

theorem mk_pnat_eq (n : ℤ) (d : ℕ) (h : 0 < d) : mk_pnat n { val := d, property := h } = mk n ↑d := sorry

theorem mk_nat_eq (n : ℤ) (d : ℕ) : mk_nat n d = mk n ↑d :=
  rfl

@[simp] theorem mk_zero (n : ℤ) : mk n 0 = 0 :=
  rfl

@[simp] theorem zero_mk_pnat (n : ℕ+) : mk_pnat 0 n = 0 := sorry

@[simp] theorem zero_mk_nat (n : ℕ) : mk_nat 0 n = 0 := sorry

@[simp] theorem zero_mk (n : ℤ) : mk 0 n = 0 := sorry

@[simp] theorem mk_eq_zero {a : ℤ} {b : ℤ} (b0 : b ≠ 0) : mk a b = 0 ↔ a = 0 := sorry

theorem mk_eq {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0) : mk a b = mk c d ↔ a * d = c * b := sorry

@[simp] theorem div_mk_div_cancel_left {a : ℤ} {b : ℤ} {c : ℤ} (c0 : c ≠ 0) : mk (a * c) (b * c) = mk a b := sorry

@[simp] theorem num_denom {a : ℚ} : mk (num a) ↑(denom a) = a := sorry

theorem num_denom' {n : ℤ} {d : ℕ} {h : 0 < d} {c : nat.coprime (int.nat_abs n) d} : mk' n d h c = mk n ↑d :=
  Eq.symm num_denom

theorem of_int_eq_mk (z : ℤ) : of_int z = mk z 1 :=
  num_denom'

def num_denom_cases_on {C : ℚ → Sort u} (a : ℚ) (H : (n : ℤ) → (d : ℕ) → 0 < d → nat.coprime (int.nat_abs n) d → C (mk n ↑d)) : C a :=
  sorry

def num_denom_cases_on' {C : ℚ → Sort u} (a : ℚ) (H : (n : ℤ) → (d : ℕ) → d ≠ 0 → C (mk n ↑d)) : C a :=
  num_denom_cases_on a fun (n : ℤ) (d : ℕ) (h : 0 < d) (c : nat.coprime (int.nat_abs n) d) => H n d sorry

theorem num_dvd (a : ℤ) {b : ℤ} (b0 : b ≠ 0) : num (mk a b) ∣ a := sorry

theorem denom_dvd (a : ℤ) (b : ℤ) : ↑(denom (mk a b)) ∣ b := sorry

protected def add : ℚ → ℚ → ℚ :=
  sorry

protected instance has_add : Add ℚ :=
  { add := rat.add }

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ) (fv : ∀ {n₁ : ℤ} {d₁ : ℕ} {h₁ : 0 < d₁} {c₁ : nat.coprime (int.nat_abs n₁) d₁} {n₂ : ℤ} {d₂ : ℕ} {h₂ : 0 < d₂}
  {c₂ : nat.coprime (int.nat_abs n₂) d₂},
  f (mk' n₁ d₁ h₁ c₁) (mk' n₂ d₂ h₂ c₂) = mk (f₁ n₁ (↑d₁) n₂ ↑d₂) (f₂ n₁ (↑d₁) n₂ ↑d₂)) (f0 : ∀ {n₁ d₁ n₂ d₂ : ℤ}, d₁ ≠ 0 → d₂ ≠ 0 → f₂ n₁ d₁ n₂ d₂ ≠ 0) (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ) (b0 : b ≠ 0) (d0 : d ≠ 0) (H : ∀ {n₁ d₁ n₂ d₂ : ℤ}, a * d₁ = n₁ * b → c * d₂ = n₂ * d → f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) : f (mk a b) (mk c d) = mk (f₁ a b c d) (f₂ a b c d) := sorry

@[simp] theorem add_def {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : mk a b + mk c d = mk (a * d + c * b) (b * d) := sorry

protected def neg : ℚ → ℚ :=
  sorry

protected instance has_neg : Neg ℚ :=
  { neg := rat.neg }

@[simp] theorem neg_def {a : ℤ} {b : ℤ} : -mk a b = mk (-a) b := sorry

protected def mul : ℚ → ℚ → ℚ :=
  sorry

protected instance has_mul : Mul ℚ :=
  { mul := rat.mul }

@[simp] theorem mul_def {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : mk a b * mk c d = mk (a * c) (b * d) := sorry

protected def inv : ℚ → ℚ :=
  sorry

protected instance has_inv : has_inv ℚ :=
  has_inv.mk rat.inv

@[simp] theorem inv_def {a : ℤ} {b : ℤ} : mk a b⁻¹ = mk b a := sorry

protected theorem add_zero (a : ℚ) : a + 0 = a := sorry

protected theorem zero_add (a : ℚ) : 0 + a = a := sorry

protected theorem add_comm (a : ℚ) (b : ℚ) : a + b = b + a := sorry

protected theorem add_assoc (a : ℚ) (b : ℚ) (c : ℚ) : a + b + c = a + (b + c) := sorry

protected theorem add_left_neg (a : ℚ) : -a + a = 0 := sorry

protected theorem mul_one (a : ℚ) : a * 1 = a := sorry

protected theorem one_mul (a : ℚ) : 1 * a = a := sorry

protected theorem mul_comm (a : ℚ) (b : ℚ) : a * b = b * a := sorry

protected theorem mul_assoc (a : ℚ) (b : ℚ) (c : ℚ) : a * b * c = a * (b * c) := sorry

protected theorem add_mul (a : ℚ) (b : ℚ) (c : ℚ) : (a + b) * c = a * c + b * c := sorry

protected theorem mul_add (a : ℚ) (b : ℚ) (c : ℚ) : a * (b + c) = a * b + a * c := sorry

protected theorem zero_ne_one : 0 ≠ 1 :=
  mt (fun (h : 0 = mk 1 1) => iff.mp (mk_eq_zero one_ne_zero) (Eq.symm h)) one_ne_zero

protected theorem mul_inv_cancel (a : ℚ) : a ≠ 0 → a * (a⁻¹) = 1 := sorry

protected theorem inv_mul_cancel (a : ℚ) (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (rat.mul_comm (a⁻¹) a) (rat.mul_inv_cancel a h)

protected instance decidable_eq : DecidableEq ℚ :=
  id
    fun (_v : ℚ) =>
      cases_on _v
        fun (num : ℤ) (denom : ℕ) (pos : 0 < denom) (cop : nat.coprime (int.nat_abs num) denom) (w : ℚ) =>
          cases_on w
            fun (w_num : ℤ) (w_denom : ℕ) (w_pos : 0 < w_denom) (w_cop : nat.coprime (int.nat_abs w_num) w_denom) =>
              decidable.by_cases
                (fun (ᾰ : num = w_num) =>
                  Eq._oldrec
                    (fun (w_cop : nat.coprime (int.nat_abs num) w_denom) =>
                      decidable.by_cases
                        (fun (ᾰ : denom = w_denom) =>
                          Eq._oldrec
                            (fun (w_pos : 0 < denom) (w_cop : nat.coprime (int.nat_abs num) denom) => is_true sorry) ᾰ
                            w_pos w_cop)
                        fun (ᾰ : ¬denom = w_denom) => isFalse sorry)
                    ᾰ w_cop)
                fun (ᾰ : ¬num = w_num) => isFalse sorry

protected instance field : field ℚ :=
  field.mk rat.add rat.add_assoc 0 rat.zero_add rat.add_zero rat.neg
    (comm_ring.sub._default rat.add rat.add_assoc 0 rat.zero_add rat.add_zero rat.neg) rat.add_left_neg rat.add_comm
    rat.mul rat.mul_assoc 1 rat.one_mul rat.mul_one rat.mul_add rat.add_mul rat.mul_comm rat.inv sorry rat.mul_inv_cancel
    sorry

/- Extra instances to short-circuit type class resolution -/

protected instance division_ring : division_ring ℚ :=
  field.to_division_ring

-- TODO(Mario): this instance slows down data.real.basic

protected instance integral_domain : integral_domain ℚ :=
  field.to_integral_domain

--instance : domain ℚ           := by apply_instance

protected instance nontrivial : nontrivial ℚ :=
  euclidean_domain.to_nontrivial ℚ

--instance : ring ℚ             := by apply_instance

protected instance comm_ring : comm_ring ℚ :=
  euclidean_domain.to_comm_ring ℚ

protected instance comm_semiring : comm_semiring ℚ :=
  comm_ring.to_comm_semiring

protected instance semiring : semiring ℚ :=
  ring.to_semiring

protected instance add_comm_group : add_comm_group ℚ :=
  ring.to_add_comm_group ℚ

protected instance add_group : add_group ℚ :=
  add_comm_group.to_add_group ℚ

protected instance add_comm_monoid : add_comm_monoid ℚ :=
  add_comm_group.to_add_comm_monoid ℚ

protected instance add_monoid : add_monoid ℚ :=
  sub_neg_monoid.to_add_monoid ℚ

protected instance add_left_cancel_semigroup : add_left_cancel_semigroup ℚ :=
  add_left_cancel_monoid.to_add_left_cancel_semigroup ℚ

protected instance add_right_cancel_semigroup : add_right_cancel_semigroup ℚ :=
  add_right_cancel_monoid.to_add_right_cancel_semigroup ℚ

protected instance add_comm_semigroup : add_comm_semigroup ℚ :=
  add_comm_monoid.to_add_comm_semigroup ℚ

protected instance add_semigroup : add_semigroup ℚ :=
  add_monoid.to_add_semigroup ℚ

protected instance comm_monoid : comm_monoid ℚ :=
  comm_semiring.to_comm_monoid ℚ

protected instance monoid : monoid ℚ :=
  ring.to_monoid ℚ

protected instance comm_semigroup : comm_semigroup ℚ :=
  comm_ring.to_comm_semigroup ℚ

protected instance semigroup : semigroup ℚ :=
  monoid.to_semigroup ℚ

theorem sub_def {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : mk a b - mk c d = mk (a * d - c * b) (b * d) := sorry

@[simp] theorem denom_neg_eq_denom (q : ℚ) : denom (-q) = denom q :=
  cases_on q
    fun (q_num : ℤ) (q_denom : ℕ) (q_pos : 0 < q_denom) (q_cop : nat.coprime (int.nat_abs q_num) q_denom) =>
      idRhs (denom (-mk' q_num q_denom q_pos q_cop) = denom (-mk' q_num q_denom q_pos q_cop)) rfl

@[simp] theorem num_neg_eq_neg_num (q : ℚ) : num (-q) = -num q :=
  cases_on q
    fun (q_num : ℤ) (q_denom : ℕ) (q_pos : 0 < q_denom) (q_cop : nat.coprime (int.nat_abs q_num) q_denom) =>
      idRhs (num (-mk' q_num q_denom q_pos q_cop) = num (-mk' q_num q_denom q_pos q_cop)) rfl

@[simp] theorem num_zero : num 0 = 0 :=
  rfl

theorem zero_of_num_zero {q : ℚ} (hq : num q = 0) : q = 0 := sorry

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ num q = 0 := sorry

theorem num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : num q ≠ 0 :=
  fun (this : num q = 0) => h (zero_of_num_zero this)

@[simp] theorem num_one : num 1 = 1 :=
  rfl

@[simp] theorem denom_one : denom 1 = 1 :=
  rfl

theorem denom_ne_zero (q : ℚ) : denom q ≠ 0 :=
  ne_of_gt (pos q)

theorem eq_iff_mul_eq_mul {p : ℚ} {q : ℚ} : p = q ↔ num p * ↑(denom q) = num q * ↑(denom p) := sorry

theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n : ℤ} {d : ℤ} (hq : q ≠ 0) (hqnd : q = mk n d) : n ≠ 0 := sorry

theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n : ℤ} {d : ℤ} (hq : q ≠ 0) (hqnd : q = mk n d) : d ≠ 0 := sorry

theorem mk_ne_zero_of_ne_zero {n : ℤ} {d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : mk n d ≠ 0 :=
  fun (this : mk n d = 0) => h (iff.mp (mk_eq_zero hd) this)

theorem mul_num_denom (q : ℚ) (r : ℚ) : q * r = mk (num q * num r) ↑(denom q * denom r) := sorry

theorem div_num_denom (q : ℚ) (r : ℚ) : q / r = mk (num q * ↑(denom r)) (↑(denom q) * num r) := sorry

theorem num_denom_mk {q : ℚ} {n : ℤ} {d : ℤ} (hn : n ≠ 0) (hd : d ≠ 0) (qdf : q = mk n d) : ∃ (c : ℤ), n = c * num q ∧ d = c * ↑(denom q) := sorry

theorem mk_pnat_num (n : ℤ) (d : ℕ+) : num (mk_pnat n d) = n / ↑(nat.gcd (int.nat_abs n) ↑d) :=
  subtype.cases_on d
    fun (d_val : ℕ) (d_property : 0 < d_val) => Eq.refl (num (mk_pnat n { val := d_val, property := d_property }))

theorem mk_pnat_denom (n : ℤ) (d : ℕ+) : denom (mk_pnat n d) = ↑d / nat.gcd (int.nat_abs n) ↑d :=
  subtype.cases_on d
    fun (d_val : ℕ) (d_property : 0 < d_val) => Eq.refl (denom (mk_pnat n { val := d_val, property := d_property }))

theorem mul_num (q₁ : ℚ) (q₂ : ℚ) : num (q₁ * q₂) = num q₁ * num q₂ / ↑(nat.gcd (int.nat_abs (num q₁ * num q₂)) (denom q₁ * denom q₂)) := sorry

theorem mul_denom (q₁ : ℚ) (q₂ : ℚ) : denom (q₁ * q₂) = denom q₁ * denom q₂ / nat.gcd (int.nat_abs (num q₁ * num q₂)) (denom q₁ * denom q₂) := sorry

theorem mul_self_num (q : ℚ) : num (q * q) = num q * num q := sorry

theorem mul_self_denom (q : ℚ) : denom (q * q) = denom q * denom q := sorry

theorem add_num_denom (q : ℚ) (r : ℚ) : q + r = mk (num q * ↑(denom r) + ↑(denom q) * num r) (↑(denom q) * ↑(denom r)) := sorry

theorem coe_int_eq_mk (z : ℤ) : ↑z = mk z 1 := sorry

theorem mk_eq_div (n : ℤ) (d : ℤ) : mk n d = ↑n / ↑d := sorry

theorem exists_eq_mul_div_num_and_eq_mul_div_denom {n : ℤ} {d : ℤ} (n_ne_zero : n ≠ 0) (d_ne_zero : d ≠ 0) : ∃ (c : ℤ), n = c * num (↑n / ↑d) ∧ d = c * ↑(denom (↑n / ↑d)) :=
  num_denom_mk n_ne_zero d_ne_zero
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑n / ↑d = mk n d)) (Eq.symm (mk_eq_div n d)))) (Eq.refl (mk n d)))

theorem coe_int_eq_of_int (z : ℤ) : ↑z = of_int z :=
  Eq.trans (coe_int_eq_mk z) (Eq.symm (of_int_eq_mk z))

@[simp] theorem coe_int_num (n : ℤ) : num ↑n = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (num ↑n = n)) (coe_int_eq_of_int n))) (Eq.refl (num (of_int n)))

@[simp] theorem coe_int_denom (n : ℤ) : denom ↑n = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (denom ↑n = 1)) (coe_int_eq_of_int n))) (Eq.refl (denom (of_int n)))

theorem coe_int_num_of_denom_eq_one {q : ℚ} (hq : denom q = 1) : ↑(num q) = q := sorry

theorem denom_eq_one_iff (r : ℚ) : denom r = 1 ↔ ↑(num r) = r :=
  { mp := coe_int_num_of_denom_eq_one, mpr := fun (h : ↑(num r) = r) => h ▸ coe_int_denom (num r) }

protected instance int.can_lift : can_lift ℚ ℤ :=
  can_lift.mk coe (fun (q : ℚ) => denom q = 1) sorry

theorem coe_nat_eq_mk (n : ℕ) : ↑n = mk (↑n) 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑n = mk (↑n) 1)) (Eq.symm (int.cast_coe_nat n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑↑n = mk (↑n) 1)) (coe_int_eq_mk ↑n))) (Eq.refl (mk (↑n) 1)))

@[simp] theorem coe_nat_num (n : ℕ) : num ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (num ↑n = ↑n)) (Eq.symm (int.cast_coe_nat n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (num ↑↑n = ↑n)) (coe_int_num ↑n))) (Eq.refl ↑n))

@[simp] theorem coe_nat_denom (n : ℕ) : denom ↑n = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (denom ↑n = 1)) (Eq.symm (int.cast_coe_nat n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (denom ↑↑n = 1)) (coe_int_denom ↑n))) (Eq.refl 1))

-- Will be subsumed by `int.coe_inj` after we have defined

-- `linear_ordered_field ℚ` (which implies characteristic zero).

theorem coe_int_inj (m : ℤ) (n : ℤ) : ↑m = ↑n ↔ m = n := sorry

theorem inv_def' {q : ℚ} : q⁻¹ = ↑(denom q) / ↑(num q) := sorry

@[simp] theorem mul_denom_eq_num {q : ℚ} : q * ↑(denom q) = ↑(num q) := sorry

theorem denom_div_cast_eq_one_iff (m : ℤ) (n : ℤ) (hn : n ≠ 0) : denom (↑m / ↑n) = 1 ↔ n ∣ m := sorry

theorem num_div_eq_of_coprime {a : ℤ} {b : ℤ} (hb0 : 0 < b) (h : nat.coprime (int.nat_abs a) (int.nat_abs b)) : num (↑a / ↑b) = a := sorry

theorem denom_div_eq_of_coprime {a : ℤ} {b : ℤ} (hb0 : 0 < b) (h : nat.coprime (int.nat_abs a) (int.nat_abs b)) : ↑(denom (↑a / ↑b)) = b := sorry

theorem div_int_inj {a : ℤ} {b : ℤ} {c : ℤ} {d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : nat.coprime (int.nat_abs a) (int.nat_abs b)) (h2 : nat.coprime (int.nat_abs c) (int.nat_abs d)) (h : ↑a / ↑b = ↑c / ↑d) : a = c ∧ b = d := sorry

theorem coe_int_div_self (n : ℤ) : ↑(n / n) = ↑n / ↑n := sorry

theorem coe_nat_div_self (n : ℕ) : ↑(n / n) = ↑n / ↑n :=
  coe_int_div_self ↑n

theorem coe_int_div (a : ℤ) (b : ℤ) (h : b ∣ a) : ↑(a / b) = ↑a / ↑b := sorry

theorem coe_nat_div (a : ℕ) (b : ℕ) (h : b ∣ a) : ↑(a / b) = ↑a / ↑b := sorry

protected theorem forall {p : ℚ → Prop} : (∀ (r : ℚ), p r) ↔ ∀ (a b : ℤ), p (↑a / ↑b) := sorry

protected theorem exists {p : ℚ → Prop} : (∃ (r : ℚ), p r) ↔ ∃ (a : ℤ), ∃ (b : ℤ), p (↑a / ↑b) := sorry

