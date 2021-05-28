/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.set_theory.ordinal_arithmetic
import Mathlib.PostPort

universes l u_1 

namespace Mathlib

/-!
# Ordinal notations

constructive ordinal arithmetic for ordinals `< ε₀`.
-/

/-- Recursive definition of an ordinal notation. `zero` denotes the
  ordinal 0, and `oadd e n a` is intended to refer to `ω^e * n + a`.
  For this to be valid Cantor normal form, we must have the exponents
  decrease to the right, but we can't state this condition until we've
  defined `repr`, so it is a separate definition `NF`. -/
inductive onote 
where
| zero : onote
| oadd : onote → ℕ+ → onote → onote

namespace onote


/-- Notation for 0 -/
protected instance has_zero : HasZero onote :=
  { zero := zero }

@[simp] theorem zero_def : zero = 0 :=
  rfl

protected instance inhabited : Inhabited onote :=
  { default := 0 }

/-- Notation for 1 -/
protected instance has_one : HasOne onote :=
  { one := oadd 0 1 0 }

/-- Notation for ω -/
def omega : onote :=
  oadd 1 1 0

/-- The ordinal denoted by a notation -/
@[simp] def repr : onote → ordinal :=
  sorry

/-- Auxiliary definition to print an ordinal notation -/
def to_string_aux1 (e : onote) (n : ℕ) (s : string) : string :=
  ite (e = 0) (to_string n)
    (ite (e = 1) (string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 (bit1 1)))))))))))
        (string.str
              (string.str
                (string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 (bit1 1)))))))))))
                (char.of_nat (bit0 (bit1 (bit1 (bit1 (bit1 (bit0 1))))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit1 (bit0 1)))))) ++
            s ++
          string.str string.empty (char.of_nat (bit1 (bit0 (bit0 (bit1 (bit0 1))))))) ++
      ite (n = 1) string.empty
        (string.str string.empty (char.of_nat (bit0 (bit1 (bit0 (bit1 (bit0 1)))))) ++ to_string n))

/-- Print an ordinal notation -/
def to_string : onote → string :=
  sorry

/-- Print an ordinal notation -/
def repr' : onote → string :=
  sorry

protected instance has_to_string : has_to_string onote :=
  has_to_string.mk to_string

protected instance has_repr : has_repr onote :=
  has_repr.mk repr'

protected instance preorder : preorder onote :=
  preorder.mk (fun (x y : onote) => repr x ≤ repr y) (fun (x y : onote) => repr x < repr y) sorry sorry

theorem lt_def {x : onote} {y : onote} : x < y ↔ repr x < repr y :=
  iff.rfl

theorem le_def {x : onote} {y : onote} : x ≤ y ↔ repr x ≤ repr y :=
  iff.rfl

/-- Convert a `nat` into an ordinal -/
@[simp] def of_nat : ℕ → onote :=
  sorry

@[simp] theorem of_nat_one : of_nat 1 = 1 :=
  rfl

@[simp] theorem repr_of_nat (n : ℕ) : repr (of_nat n) = ↑n := sorry

@[simp] theorem repr_one : repr 1 = 1 := sorry

theorem omega_le_oadd (e : onote) (n : ℕ+) (a : onote) : ordinal.omega ^ repr e ≤ repr (oadd e n a) := sorry

theorem oadd_pos (e : onote) (n : ℕ+) (a : onote) : 0 < oadd e n a :=
  lt_of_lt_of_le (ordinal.power_pos (repr e) ordinal.omega_pos) (omega_le_oadd e n a)

/-- Compare ordinal notations -/
def cmp : onote → onote → ordering :=
  sorry

theorem eq_of_cmp_eq {o₁ : onote} {o₂ : onote} : cmp o₁ o₂ = ordering.eq → o₁ = o₂ := sorry

theorem zero_lt_one : 0 < 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < 1)) (propext lt_def)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (repr 0 < repr 1)) repr.equations._eqn_1))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 < repr 1)) repr_one)) ordinal.zero_lt_one))

/-- `NF_below o b` says that `o` is a normal form ordinal notation
  satisfying `repr o < ω ^ b`. -/
inductive NF_below : onote → ordinal → Prop
where
| zero : ∀ {b : ordinal}, NF_below 0 b
| oadd' : ∀ {e : onote} {n : ℕ+} {a : onote} {eb b : ordinal},
  NF_below e eb → NF_below a (repr e) → repr e < b → NF_below (oadd e n a) b

/-- A normal form ordinal notation has the form

     ω ^ a₁ * n₁ + ω ^ a₂ * n₂ + ... ω ^ aₖ * nₖ
  where `a₁ > a₂ > ... > aₖ` and all the `aᵢ` are
  also in normal form.

  We will essentially only be interested in normal form
  ordinal notations, but to avoid complicating the algorithms
  we define everything over general ordinal notations and
  only prove correctness with normal form as an invariant. -/
def NF (o : onote)  :=
  Exists (NF_below o)

protected instance NF.zero : NF 0 :=
  Exists.intro 0 NF_below.zero

theorem NF_below.oadd {e : onote} {n : ℕ+} {a : onote} {b : ordinal} : NF e → NF_below a (repr e) → repr e < b → NF_below (oadd e n a) b := sorry

theorem NF_below.fst {e : onote} {n : ℕ+} {a : onote} {b : ordinal} (h : NF_below (oadd e n a) b) : NF e := sorry

theorem NF.fst {e : onote} {n : ℕ+} {a : onote} : NF (oadd e n a) → NF e :=
  fun (ᾰ : NF (oadd e n a)) =>
    Exists.dcases_on ᾰ fun (ᾰ_w : ordinal) (ᾰ_h : NF_below (oadd e n a) ᾰ_w) => idRhs (NF e) (NF_below.fst ᾰ_h)

theorem NF_below.snd {e : onote} {n : ℕ+} {a : onote} {b : ordinal} (h : NF_below (oadd e n a) b) : NF_below a (repr e) := sorry

theorem NF.snd' {e : onote} {n : ℕ+} {a : onote} : NF (oadd e n a) → NF_below a (repr e) :=
  fun (ᾰ : NF (oadd e n a)) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : ordinal) (ᾰ_h : NF_below (oadd e n a) ᾰ_w) => idRhs (NF_below a (repr e)) (NF_below.snd ᾰ_h)

theorem NF.snd {e : onote} {n : ℕ+} {a : onote} (h : NF (oadd e n a)) : NF a :=
  Exists.intro (repr e) (NF.snd' h)

theorem NF.oadd {e : onote} {a : onote} (h₁ : NF e) (n : ℕ+) (h₂ : NF_below a (repr e)) : NF (oadd e n a) :=
  Exists.intro (ordinal.succ (repr e)) (NF_below.oadd h₁ h₂ (ordinal.lt_succ_self (repr e)))

protected instance NF.oadd_zero (e : onote) (n : ℕ+) [h : NF e] : NF (oadd e n 0) :=
  NF.oadd h n NF_below.zero

theorem NF_below.lt {e : onote} {n : ℕ+} {a : onote} {b : ordinal} (h : NF_below (oadd e n a) b) : repr e < b := sorry

theorem NF_below_zero {o : onote} : NF_below o 0 ↔ o = 0 := sorry

theorem NF.zero_of_zero {e : onote} {n : ℕ+} {a : onote} (h : NF (oadd e n a)) (e0 : e = 0) : a = 0 := sorry

theorem NF_below.repr_lt {o : onote} {b : ordinal} (h : NF_below o b) : repr o < ordinal.omega ^ b := sorry

theorem NF_below.mono {o : onote} {b₁ : ordinal} {b₂ : ordinal} (bb : b₁ ≤ b₂) (h : NF_below o b₁) : NF_below o b₂ := sorry

theorem NF.below_of_lt {e : onote} {n : ℕ+} {a : onote} {b : ordinal} (H : repr e < b) : NF (oadd e n a) → NF_below (oadd e n a) b := sorry

theorem NF.below_of_lt' {o : onote} {b : ordinal} : repr o < ordinal.omega ^ b → NF o → NF_below o b := sorry

theorem NF_below_of_nat (n : ℕ) : NF_below (of_nat n) 1 :=
  nat.cases_on n (idRhs (NF_below 0 1) NF_below.zero)
    fun (n : ℕ) =>
      idRhs (NF_below (oadd 0 (nat.succ_pnat n) 0) 1) (NF_below.oadd NF.zero NF_below.zero ordinal.zero_lt_one)

protected instance NF_of_nat (n : ℕ) : NF (of_nat n) :=
  Exists.intro 1 (NF_below_of_nat n)

protected instance NF_one : NF 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (NF 1)) (Eq.symm of_nat_one))) (onote.NF_of_nat 1)

theorem oadd_lt_oadd_1 {e₁ : onote} {n₁ : ℕ+} {o₁ : onote} {e₂ : onote} {n₂ : ℕ+} {o₂ : onote} (h₁ : NF (oadd e₁ n₁ o₁)) (h : e₁ < e₂) : oadd e₁ n₁ o₁ < oadd e₂ n₂ o₂ :=
  lt_of_lt_of_le (NF_below.repr_lt (NF.below_of_lt h h₁)) (omega_le_oadd e₂ n₂ o₂)

theorem oadd_lt_oadd_2 {e : onote} {o₁ : onote} {o₂ : onote} {n₁ : ℕ+} {n₂ : ℕ+} (h₁ : NF (oadd e n₁ o₁)) (h : ↑n₁ < ↑n₂) : oadd e n₁ o₁ < oadd e n₂ o₂ := sorry

theorem oadd_lt_oadd_3 {e : onote} {n : ℕ+} {a₁ : onote} {a₂ : onote} (h : a₁ < a₂) : oadd e n a₁ < oadd e n a₂ := sorry

theorem cmp_compares (a : onote) (b : onote) [NF a] [NF b] : ordering.compares (cmp a b) a b := sorry

theorem repr_inj {a : onote} {b : onote} [NF a] [NF b] : repr a = repr b ↔ a = b := sorry

theorem NF.of_dvd_omega_power {b : ordinal} {e : onote} {n : ℕ+} {a : onote} (h : NF (oadd e n a)) (d : ordinal.omega ^ b ∣ repr (oadd e n a)) : b ≤ repr e ∧ ordinal.omega ^ b ∣ repr a := sorry

theorem NF.of_dvd_omega {e : onote} {n : ℕ+} {a : onote} (h : NF (oadd e n a)) : ordinal.omega ∣ repr (oadd e n a) → repr e ≠ 0 ∧ ordinal.omega ∣ repr a := sorry

/-- `top_below b o` asserts that the largest exponent in `o`, if
  it exists, is less than `b`. This is an auxiliary definition
  for decidability of `NF`. -/
def top_below (b : onote) : onote → Prop :=
  sorry

protected instance decidable_top_below : DecidableRel top_below :=
  id
    fun (b o : onote) =>
      onote.cases_on o (id decidable.true)
        fun (o_ᾰ : onote) (o_ᾰ_1 : ℕ+) (o_ᾰ_2 : onote) => id (ordering.decidable_eq (cmp o_ᾰ b) ordering.lt)

theorem NF_below_iff_top_below {b : onote} [NF b] {o : onote} : NF_below o (repr b) ↔ NF o ∧ top_below b o := sorry

protected instance decidable_NF : decidable_pred NF :=
  sorry

/-- Addition of ordinal notations (correct only for normal input) -/
def add : onote → onote → onote :=
  sorry

protected instance has_add : Add onote :=
  { add := add }

@[simp] theorem zero_add (o : onote) : 0 + o = o :=
  rfl

theorem oadd_add (e : onote) (n : ℕ+) (a : onote) (o : onote) : oadd e n a + o = add._match_1 e n (a + o) :=
  rfl

/-- Subtraction of ordinal notations (correct only for normal input) -/
def sub : onote → onote → onote :=
  sorry

protected instance has_sub : Sub onote :=
  { sub := sub }

theorem add_NF_below {b : ordinal} {o₁ : onote} {o₂ : onote} : NF_below o₁ b → NF_below o₂ b → NF_below (o₁ + o₂) b := sorry

protected instance add_NF (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : NF (o₁ + o₂) :=
  sorry

@[simp] theorem repr_add (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : repr (o₁ + o₂) = repr o₁ + repr o₂ := sorry

theorem sub_NF_below {o₁ : onote} {o₂ : onote} {b : ordinal} : NF_below o₁ b → NF o₂ → NF_below (o₁ - o₂) b := sorry

protected instance sub_NF (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : NF (o₁ - o₂) :=
  sorry

@[simp] theorem repr_sub (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : repr (o₁ - o₂) = repr o₁ - repr o₂ := sorry

/-- Multiplication of ordinal notations (correct only for normal input) -/
def mul : onote → onote → onote :=
  sorry

protected instance has_mul : Mul onote :=
  { mul := mul }

@[simp] theorem zero_mul (o : onote) : 0 * o = 0 :=
  onote.cases_on o (Eq.refl (0 * zero))
    fun (o_ᾰ : onote) (o_ᾰ_1 : ℕ+) (o_ᾰ_2 : onote) => Eq.refl (0 * oadd o_ᾰ o_ᾰ_1 o_ᾰ_2)

@[simp] theorem mul_zero (o : onote) : o * 0 = 0 :=
  onote.cases_on o (Eq.refl (zero * 0))
    fun (o_ᾰ : onote) (o_ᾰ_1 : ℕ+) (o_ᾰ_2 : onote) => Eq.refl (oadd o_ᾰ o_ᾰ_1 o_ᾰ_2 * 0)

theorem oadd_mul (e₁ : onote) (n₁ : ℕ+) (a₁ : onote) (e₂ : onote) (n₂ : ℕ+) (a₂ : onote) : oadd e₁ n₁ a₁ * oadd e₂ n₂ a₂ = ite (e₂ = 0) (oadd e₁ (n₁ * n₂) a₁) (oadd (e₁ + e₂) n₂ (oadd e₁ n₁ a₁ * a₂)) :=
  rfl

theorem oadd_mul_NF_below {e₁ : onote} {n₁ : ℕ+} {a₁ : onote} {b₁ : ordinal} (h₁ : NF_below (oadd e₁ n₁ a₁) b₁) {o₂ : onote} {b₂ : ordinal} : NF_below o₂ b₂ → NF_below (oadd e₁ n₁ a₁ * o₂) (repr e₁ + b₂) := sorry

protected instance mul_NF (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : NF (o₁ * o₂) :=
  sorry

@[simp] theorem repr_mul (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : repr (o₁ * o₂) = repr o₁ * repr o₂ := sorry

/-- Calculate division and remainder of `o` mod ω.
  `split' o = (a, n)` means `o = ω * a + n`. -/
def split' : onote → onote × ℕ :=
  sorry

/-- Calculate division and remainder of `o` mod ω.
  `split o = (a, n)` means `o = a + n`, where `ω ∣ a`. -/
def split : onote → onote × ℕ :=
  sorry

/-- `scale x o` is the ordinal notation for `ω ^ x * o`. -/
def scale (x : onote) : onote → onote :=
  sorry

/-- `mul_nat o n` is the ordinal notation for `o * n`. -/
def mul_nat : onote → ℕ → onote :=
  sorry

/-- Auxiliary definition to compute the ordinal notation for the ordinal
exponentiation in `power` -/
def power_aux (e : onote) (a0 : onote) (a : onote) : ℕ → ℕ → onote :=
  sorry

/-- `power o₁ o₂` calculates the ordinal notation for
  the ordinal exponential `o₁ ^ o₂`. -/
def power (o₁ : onote) (o₂ : onote) : onote :=
  sorry

protected instance has_pow : has_pow onote onote :=
  has_pow.mk power

theorem power_def (o₁ : onote) (o₂ : onote) : o₁ ^ o₂ = power._match_1 o₂ (split o₁) :=
  rfl

theorem split_eq_scale_split' {o : onote} {o' : onote} {m : ℕ} [NF o] : split' o = (o', m) → split o = (scale 1 o', m) := sorry

theorem NF_repr_split' {o : onote} {o' : onote} {m : ℕ} [NF o] : split' o = (o', m) → NF o' ∧ repr o = ordinal.omega * repr o' + ↑m := sorry

theorem scale_eq_mul (x : onote) [NF x] (o : onote) [NF o] : scale x o = oadd x 1 0 * o := sorry

protected instance NF_scale (x : onote) [NF x] (o : onote) [NF o] : NF (scale x o) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (NF (scale x o))) (scale_eq_mul x o))) (onote.mul_NF (oadd x 1 0) o)

@[simp] theorem repr_scale (x : onote) [NF x] (o : onote) [NF o] : repr (scale x o) = ordinal.omega ^ repr x * repr o := sorry

theorem NF_repr_split {o : onote} {o' : onote} {m : ℕ} [NF o] (h : split o = (o', m)) : NF o' ∧ repr o = repr o' + ↑m := sorry

theorem split_dvd {o : onote} {o' : onote} {m : ℕ} [NF o] (h : split o = (o', m)) : ordinal.omega ∣ repr o' := sorry

theorem split_add_lt {o : onote} {e : onote} {n : ℕ+} {a : onote} {m : ℕ} [NF o] (h : split o = (oadd e n a, m)) : repr a + ↑m < ordinal.omega ^ repr e := sorry

@[simp] theorem mul_nat_eq_mul (n : ℕ) (o : onote) : mul_nat o n = o * of_nat n := sorry

protected instance NF_mul_nat (o : onote) [NF o] (n : ℕ) : NF (mul_nat o n) :=
  eq.mpr
    (id ((fun (o o_1 : onote) (e_1 : o = o_1) => congr_arg NF e_1) (mul_nat o n) (o * of_nat n) (mul_nat_eq_mul n o)))
    (onote.mul_NF o (of_nat n))

protected instance NF_power_aux (e : onote) (a0 : onote) (a : onote) [NF e] [NF a0] [NF a] (k : ℕ) (m : ℕ) : NF (power_aux e a0 a k m) :=
  sorry

protected instance NF_power (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : NF (o₁ ^ o₂) := sorry

theorem scale_power_aux (e : onote) (a0 : onote) (a : onote) [NF e] [NF a0] [NF a] (k : ℕ) (m : ℕ) : repr (power_aux e a0 a k m) = ordinal.omega ^ repr e * repr (power_aux 0 a0 a k m) := sorry

theorem repr_power_aux₁ {e : onote} {a : onote} [Ne : NF e] [Na : NF a] {a' : ordinal} (e0 : repr e ≠ 0) (h : a' < ordinal.omega ^ repr e) (aa : repr a = a') (n : ℕ+) : (ordinal.omega ^ repr e * ↑↑n + a') ^ ordinal.omega = (ordinal.omega ^ repr e) ^ ordinal.omega := sorry

theorem repr_power_aux₂ {a0 : onote} {a' : onote} [N0 : NF a0] [Na' : NF a'] (m : ℕ) (d : ordinal.omega ∣ repr a') (e0 : repr a0 ≠ 0) (h : repr a' + ↑m < ordinal.omega ^ repr a0) (n : ℕ+) (k : ℕ) : let R : ordinal := repr (power_aux 0 a0 (oadd a0 n a' * of_nat m) k m);
(k ≠ 0 → R < (ordinal.omega ^ repr a0) ^ ordinal.succ ↑k) ∧
  (ordinal.omega ^ repr a0) ^ ↑k * (ordinal.omega ^ repr a0 * ↑↑n + repr a') + R =
    (ordinal.omega ^ repr a0 * ↑↑n + repr a' + ↑m) ^ ordinal.succ ↑k := sorry

theorem repr_power (o₁ : onote) (o₂ : onote) [NF o₁] [NF o₂] : repr (o₁ ^ o₂) = repr o₁ ^ repr o₂ := sorry

end onote


/-- The type of normal ordinal notations. (It would have been
  nicer to define this right in the inductive type, but `NF o`
  requires `repr` which requires `onote`, so all these things
  would have to be defined at once, which messes up the VM
  representation.) -/
def nonote  :=
  Subtype fun (o : onote) => onote.NF o

protected instance nonote.decidable_eq : DecidableEq nonote :=
  eq.mpr sorry fun (a b : Subtype fun (o : onote) => onote.NF o) => subtype.decidable_eq a b

namespace nonote


protected instance NF (o : nonote) : onote.NF (subtype.val o) :=
  subtype.property o

/-- Construct a `nonote` from an ordinal notation
  (and infer normality) -/
def mk (o : onote) [h : onote.NF o] : nonote :=
  { val := o, property := h }

/-- The ordinal represented by an ordinal notation.
  (This function is noncomputable because ordinal
  arithmetic is noncomputable. In computational applications
  `nonote` can be used exclusively without reference
  to `ordinal`, but this function allows for correctness
  results to be stated.) -/
def repr (o : nonote) : ordinal :=
  onote.repr (subtype.val o)

protected instance has_to_string : has_to_string nonote :=
  has_to_string.mk fun (x : nonote) => onote.to_string (subtype.val x)

protected instance has_repr : has_repr nonote :=
  has_repr.mk fun (x : nonote) => onote.repr' (subtype.val x)

protected instance preorder : preorder nonote :=
  preorder.mk (fun (x y : nonote) => repr x ≤ repr y) (fun (x y : nonote) => repr x < repr y) sorry sorry

protected instance has_zero : HasZero nonote :=
  { zero := { val := 0, property := onote.NF.zero } }

protected instance inhabited : Inhabited nonote :=
  { default := 0 }

/-- Convert a natural number to an ordinal notation -/
def of_nat (n : ℕ) : nonote :=
  { val := onote.of_nat n, property := sorry }

/-- Compare ordinal notations -/
def cmp (a : nonote) (b : nonote) : ordering :=
  onote.cmp (subtype.val a) (subtype.val b)

theorem cmp_compares (a : nonote) (b : nonote) : ordering.compares (cmp a b) a b := sorry

protected instance linear_order : linear_order nonote :=
  linear_order_of_compares cmp cmp_compares

/-- Asserts that `repr a < ω ^ repr b`. Used in `nonote.rec_on` -/
def old_below (a : nonote) (b : nonote)  :=
  onote.NF_below (subtype.val a) (repr b)

/-- The `oadd` pseudo-constructor for `nonote` -/
def oadd (e : nonote) (n : ℕ+) (a : nonote) (h : old_below a e) : nonote :=
  { val := onote.oadd (subtype.val e) n (subtype.val a), property := sorry }

/-- This is a recursor-like theorem for `nonote` suggesting an
  inductive definition, which can't actually be defined this
  way due to conflicting dependencies. -/
def rec_on {C : nonote → Sort u_1} (o : nonote) (H0 : C 0) (H1 : (e : nonote) → (n : ℕ+) → (a : nonote) → (h : old_below a e) → C e → C a → C (oadd e n a h)) : C o :=
  subtype.cases_on o
    fun (o : onote) (h : onote.NF o) =>
      onote.rec (fun (h : onote.NF onote.zero) => H0)
        (fun (e : onote) (n : ℕ+) (a : onote) (IHe : (h : onote.NF e) → C { val := e, property := h })
          (IHa : (h : onote.NF a) → C { val := a, property := h }) (h : onote.NF (onote.oadd e n a)) =>
          H1 { val := e, property := onote.NF.fst h } n { val := a, property := onote.NF.snd h } (onote.NF.snd' h)
            (IHe (onote.NF.fst h)) (IHa (onote.NF.snd h)))
        o h

/-- Addition of ordinal notations -/
protected instance has_add : Add nonote :=
  { add := fun (x y : nonote) => mk (subtype.val x + subtype.val y) }

theorem repr_add (a : nonote) (b : nonote) : repr (a + b) = repr a + repr b :=
  onote.repr_add (subtype.val a) (subtype.val b)

/-- Subtraction of ordinal notations -/
protected instance has_sub : Sub nonote :=
  { sub := fun (x y : nonote) => mk (subtype.val x - subtype.val y) }

theorem repr_sub (a : nonote) (b : nonote) : repr (a - b) = repr a - repr b :=
  onote.repr_sub (subtype.val a) (subtype.val b)

/-- Multiplication of ordinal notations -/
protected instance has_mul : Mul nonote :=
  { mul := fun (x y : nonote) => mk (subtype.val x * subtype.val y) }

theorem repr_mul (a : nonote) (b : nonote) : repr (a * b) = repr a * repr b :=
  onote.repr_mul (subtype.val a) (subtype.val b)

/-- Exponentiation of ordinal notations -/
def power (x : nonote) (y : nonote) : nonote :=
  mk (onote.power (subtype.val x) (subtype.val y))

theorem repr_power (a : nonote) (b : nonote) : repr (power a b) = ordinal.power (repr a) (repr b) :=
  onote.repr_power (subtype.val a) (subtype.val b)

