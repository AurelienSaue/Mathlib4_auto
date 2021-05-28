/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.associated
import Mathlib.tactic.ring
import Mathlib.PostPort

universes l 

namespace Mathlib

/-- The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case,
  but of course both parts are real here since `d` is nonnegative. -/
structure zsqrtd (d : ℤ) 
where
  re : ℤ
  im : ℤ

prefix:100 "ℤ√" => Mathlib.zsqrtd

namespace zsqrtd


protected instance decidable_eq {d : ℤ} : DecidableEq (ℤ√d) :=
  id
    fun (_v : ℤ√d) =>
      cases_on _v
        fun (re im : ℤ) (w : ℤ√d) =>
          cases_on w
            fun (w_re w_im : ℤ) =>
              decidable.by_cases
                (fun (ᾰ : re = w_re) =>
                  Eq._oldrec
                    (decidable.by_cases (fun (ᾰ : im = w_im) => Eq._oldrec (is_true sorry) ᾰ)
                      fun (ᾰ : ¬im = w_im) => isFalse sorry)
                    ᾰ)
                fun (ᾰ : ¬re = w_re) => isFalse sorry

theorem ext {d : ℤ} {z : ℤ√d} {w : ℤ√d} : z = w ↔ re z = re w ∧ im z = im w := sorry

/-- Convert an integer to a `ℤ√d` -/
def of_int {d : ℤ} (n : ℤ) : ℤ√d :=
  mk n 0

theorem of_int_re {d : ℤ} (n : ℤ) : re (of_int n) = n :=
  rfl

theorem of_int_im {d : ℤ} (n : ℤ) : im (of_int n) = 0 :=
  rfl

/-- The zero of the ring -/
def zero {d : ℤ} : ℤ√d :=
  of_int 0

protected instance has_zero {d : ℤ} : HasZero (ℤ√d) :=
  { zero := zero }

@[simp] theorem zero_re {d : ℤ} : re 0 = 0 :=
  rfl

@[simp] theorem zero_im {d : ℤ} : im 0 = 0 :=
  rfl

protected instance inhabited {d : ℤ} : Inhabited (ℤ√d) :=
  { default := 0 }

/-- The one of the ring -/
def one {d : ℤ} : ℤ√d :=
  of_int 1

protected instance has_one {d : ℤ} : HasOne (ℤ√d) :=
  { one := one }

@[simp] theorem one_re {d : ℤ} : re 1 = 1 :=
  rfl

@[simp] theorem one_im {d : ℤ} : im 1 = 0 :=
  rfl

/-- The representative of `√d` in the ring -/
def sqrtd {d : ℤ} : ℤ√d :=
  mk 0 1

@[simp] theorem sqrtd_re {d : ℤ} : re sqrtd = 0 :=
  rfl

@[simp] theorem sqrtd_im {d : ℤ} : im sqrtd = 1 :=
  rfl

/-- Addition of elements of `ℤ√d` -/
def add {d : ℤ} : ℤ√d → ℤ√d → ℤ√d :=
  sorry

protected instance has_add {d : ℤ} : Add (ℤ√d) :=
  { add := add }

@[simp] theorem add_def {d : ℤ} (x : ℤ) (y : ℤ) (x' : ℤ) (y' : ℤ) : mk x y + mk x' y' = mk (x + x') (y + y') :=
  rfl

@[simp] theorem add_re {d : ℤ} (z : ℤ√d) (w : ℤ√d) : re (z + w) = re z + re w :=
  cases_on z
    fun (z_re z_im : ℤ) =>
      cases_on w fun (w_re w_im : ℤ) => idRhs (re (mk z_re z_im + mk w_re w_im) = re (mk z_re z_im + mk w_re w_im)) rfl

@[simp] theorem add_im {d : ℤ} (z : ℤ√d) (w : ℤ√d) : im (z + w) = im z + im w :=
  cases_on z
    fun (z_re z_im : ℤ) =>
      cases_on w fun (w_re w_im : ℤ) => idRhs (im (mk z_re z_im + mk w_re w_im) = im (mk z_re z_im + mk w_re w_im)) rfl

@[simp] theorem bit0_re {d : ℤ} (z : ℤ√d) : re (bit0 z) = bit0 (re z) :=
  add_re z z

@[simp] theorem bit0_im {d : ℤ} (z : ℤ√d) : im (bit0 z) = bit0 (im z) :=
  add_im z z

@[simp] theorem bit1_re {d : ℤ} (z : ℤ√d) : re (bit1 z) = bit1 (re z) := sorry

@[simp] theorem bit1_im {d : ℤ} (z : ℤ√d) : im (bit1 z) = bit0 (im z) := sorry

/-- Negation in `ℤ√d` -/
def neg {d : ℤ} : ℤ√d → ℤ√d :=
  sorry

protected instance has_neg {d : ℤ} : Neg (ℤ√d) :=
  { neg := neg }

@[simp] theorem neg_re {d : ℤ} (z : ℤ√d) : re (-z) = -re z :=
  cases_on z fun (z_re z_im : ℤ) => idRhs (re (-mk z_re z_im) = re (-mk z_re z_im)) rfl

@[simp] theorem neg_im {d : ℤ} (z : ℤ√d) : im (-z) = -im z :=
  cases_on z fun (z_re z_im : ℤ) => idRhs (im (-mk z_re z_im) = im (-mk z_re z_im)) rfl

/-- Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`. -/
def conj {d : ℤ} : ℤ√d → ℤ√d :=
  sorry

@[simp] theorem conj_re {d : ℤ} (z : ℤ√d) : re (conj z) = re z :=
  cases_on z fun (z_re z_im : ℤ) => idRhs (re (conj (mk z_re z_im)) = re (conj (mk z_re z_im))) rfl

@[simp] theorem conj_im {d : ℤ} (z : ℤ√d) : im (conj z) = -im z :=
  cases_on z fun (z_re z_im : ℤ) => idRhs (im (conj (mk z_re z_im)) = im (conj (mk z_re z_im))) rfl

/-- Multiplication in `ℤ√d` -/
def mul {d : ℤ} : ℤ√d → ℤ√d → ℤ√d :=
  sorry

protected instance has_mul {d : ℤ} : Mul (ℤ√d) :=
  { mul := mul }

@[simp] theorem mul_re {d : ℤ} (z : ℤ√d) (w : ℤ√d) : re (z * w) = re z * re w + d * im z * im w :=
  cases_on z
    fun (z_re z_im : ℤ) =>
      cases_on w fun (w_re w_im : ℤ) => idRhs (re (mk z_re z_im * mk w_re w_im) = re (mk z_re z_im * mk w_re w_im)) rfl

@[simp] theorem mul_im {d : ℤ} (z : ℤ√d) (w : ℤ√d) : im (z * w) = re z * im w + im z * re w :=
  cases_on z
    fun (z_re z_im : ℤ) =>
      cases_on w fun (w_re w_im : ℤ) => idRhs (im (mk z_re z_im * mk w_re w_im) = im (mk z_re z_im * mk w_re w_im)) rfl

protected instance comm_ring {d : ℤ} : comm_ring (ℤ√d) :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg (fun (a b : ℤ√d) => a + -b) sorry sorry Mul.mul sorry 1 sorry sorry
    sorry sorry sorry

protected instance add_comm_monoid {d : ℤ} : add_comm_monoid (ℤ√d) :=
  add_comm_group.to_add_comm_monoid (ℤ√d)

protected instance add_monoid {d : ℤ} : add_monoid (ℤ√d) :=
  sub_neg_monoid.to_add_monoid (ℤ√d)

protected instance monoid {d : ℤ} : monoid (ℤ√d) :=
  ring.to_monoid (ℤ√d)

protected instance comm_monoid {d : ℤ} : comm_monoid (ℤ√d) :=
  comm_semiring.to_comm_monoid (ℤ√d)

protected instance comm_semigroup {d : ℤ} : comm_semigroup (ℤ√d) :=
  comm_ring.to_comm_semigroup (ℤ√d)

protected instance semigroup {d : ℤ} : semigroup (ℤ√d) :=
  monoid.to_semigroup (ℤ√d)

protected instance add_comm_semigroup {d : ℤ} : add_comm_semigroup (ℤ√d) :=
  add_comm_monoid.to_add_comm_semigroup (ℤ√d)

protected instance add_semigroup {d : ℤ} : add_semigroup (ℤ√d) :=
  add_monoid.to_add_semigroup (ℤ√d)

protected instance comm_semiring {d : ℤ} : comm_semiring (ℤ√d) :=
  comm_ring.to_comm_semiring

protected instance semiring {d : ℤ} : semiring (ℤ√d) :=
  ring.to_semiring

protected instance ring {d : ℤ} : ring (ℤ√d) :=
  comm_ring.to_ring (ℤ√d)

protected instance distrib {d : ℤ} : distrib (ℤ√d) :=
  ring.to_distrib (ℤ√d)

protected instance nontrivial {d : ℤ} : nontrivial (ℤ√d) :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 (of_as_true trivial)))

@[simp] theorem coe_nat_re {d : ℤ} (n : ℕ) : re ↑n = ↑n := sorry

@[simp] theorem coe_nat_im {d : ℤ} (n : ℕ) : im ↑n = 0 := sorry

theorem coe_nat_val {d : ℤ} (n : ℕ) : ↑n = mk (↑n) 0 := sorry

@[simp] theorem coe_int_re {d : ℤ} (n : ℤ) : re ↑n = n := sorry

@[simp] theorem coe_int_im {d : ℤ} (n : ℤ) : im ↑n = 0 := sorry

theorem coe_int_val {d : ℤ} (n : ℤ) : ↑n = mk n 0 := sorry

protected instance char_zero {d : ℤ} : char_zero (ℤ√d) := sorry

@[simp] theorem of_int_eq_coe {d : ℤ} (n : ℤ) : of_int n = ↑n := sorry

@[simp] theorem smul_val {d : ℤ} (n : ℤ) (x : ℤ) (y : ℤ) : ↑n * mk x y = mk (n * x) (n * y) := sorry

@[simp] theorem muld_val {d : ℤ} (x : ℤ) (y : ℤ) : sqrtd * mk x y = mk (d * y) x := sorry

@[simp] theorem dmuld {d : ℤ} : sqrtd * sqrtd = ↑d := sorry

@[simp] theorem smuld_val {d : ℤ} (n : ℤ) (x : ℤ) (y : ℤ) : sqrtd * ↑n * mk x y = mk (d * n * y) (n * x) := sorry

theorem decompose {d : ℤ} {x : ℤ} {y : ℤ} : mk x y = ↑x + sqrtd * ↑y := sorry

theorem mul_conj {d : ℤ} {x : ℤ} {y : ℤ} : mk x y * conj (mk x y) = ↑x * ↑x - ↑d * ↑y * ↑y := sorry

theorem conj_mul {d : ℤ} {a : ℤ√d} {b : ℤ√d} : conj (a * b) = conj a * conj b := sorry

protected theorem coe_int_add {d : ℤ} (m : ℤ) (n : ℤ) : ↑(m + n) = ↑m + ↑n :=
  ring_hom.map_add (int.cast_ring_hom (ℤ√d)) m n

protected theorem coe_int_sub {d : ℤ} (m : ℤ) (n : ℤ) : ↑(m - n) = ↑m - ↑n :=
  ring_hom.map_sub (int.cast_ring_hom (ℤ√d)) m n

protected theorem coe_int_mul {d : ℤ} (m : ℤ) (n : ℤ) : ↑(m * n) = ↑m * ↑n :=
  ring_hom.map_mul (int.cast_ring_hom (ℤ√d)) m n

protected theorem coe_int_inj {d : ℤ} {m : ℤ} {n : ℤ} (h : ↑m = ↑n) : m = n := sorry

/-- Read `sq_le a c b d` as `a √c ≤ b √d` -/
def sq_le (a : ℕ) (c : ℕ) (b : ℕ) (d : ℕ)  :=
  c * a * a ≤ d * b * b

theorem sq_le_of_le {c : ℕ} {d : ℕ} {x : ℕ} {y : ℕ} {z : ℕ} {w : ℕ} (xz : z ≤ x) (yw : y ≤ w) (xy : sq_le x c y d) : sq_le z c w d :=
  le_trans (mul_le_mul (nat.mul_le_mul_left c xz) xz (nat.zero_le z) (nat.zero_le (c * x)))
    (le_trans xy (mul_le_mul (nat.mul_le_mul_left d yw) yw (nat.zero_le y) (nat.zero_le (d * w))))

theorem sq_le_add_mixed {c : ℕ} {d : ℕ} {x : ℕ} {y : ℕ} {z : ℕ} {w : ℕ} (xy : sq_le x c y d) (zw : sq_le z c w d) : c * (x * z) ≤ d * (y * w) := sorry

theorem sq_le_add {c : ℕ} {d : ℕ} {x : ℕ} {y : ℕ} {z : ℕ} {w : ℕ} (xy : sq_le x c y d) (zw : sq_le z c w d) : sq_le (x + z) c (y + w) d := sorry

theorem sq_le_cancel {c : ℕ} {d : ℕ} {x : ℕ} {y : ℕ} {z : ℕ} {w : ℕ} (zw : sq_le y d x c) (h : sq_le (x + z) c (y + w) d) : sq_le z c w d := sorry

theorem sq_le_smul {c : ℕ} {d : ℕ} {x : ℕ} {y : ℕ} (n : ℕ) (xy : sq_le x c y d) : sq_le (n * x) c (n * y) d := sorry

theorem sq_le_mul {d : ℕ} {x : ℕ} {y : ℕ} {z : ℕ} {w : ℕ} : (sq_le x 1 y d → sq_le z 1 w d → sq_le (x * w + y * z) d (x * z + d * y * w) 1) ∧
  (sq_le x 1 y d → sq_le w d z 1 → sq_le (x * z + d * y * w) 1 (x * w + y * z) d) ∧
    (sq_le y d x 1 → sq_le z 1 w d → sq_le (x * z + d * y * w) 1 (x * w + y * z) d) ∧
      (sq_le y d x 1 → sq_le w d z 1 → sq_le (x * w + y * z) d (x * z + d * y * w) 1) := sorry

/-- "Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
  we are interested in the case `c = 1` but this is more symmetric -/
def nonnegg (c : ℕ) (d : ℕ) : ℤ → ℤ → Prop :=
  sorry

theorem nonnegg_comm {c : ℕ} {d : ℕ} {x : ℤ} {y : ℤ} : nonnegg c d x y = nonnegg d c y x := sorry

theorem nonnegg_neg_pos {c : ℕ} {d : ℕ} {a : ℕ} {b : ℕ} : nonnegg c d (-↑a) ↑b ↔ sq_le a d b c := sorry

theorem nonnegg_pos_neg {c : ℕ} {d : ℕ} {a : ℕ} {b : ℕ} : nonnegg c d (↑a) (-↑b) ↔ sq_le b c a d :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nonnegg c d (↑a) (-↑b) ↔ sq_le b c a d)) nonnegg_comm)) nonnegg_neg_pos

theorem nonnegg_cases_right {c : ℕ} {d : ℕ} {a : ℕ} {b : ℤ} : (∀ (x : ℕ), b = -↑x → sq_le x c a d) → nonnegg c d (↑a) b :=
  fun (ᾰ : ∀ (x : ℕ), b = -↑x → sq_le x c a d) =>
    int.cases_on b (fun (b : ℕ) (ᾰ : ∀ (x : ℕ), Int.ofNat b = -↑x → sq_le x c a d) => idRhs True trivial)
      (fun (b : ℕ) (ᾰ : ∀ (x : ℕ), Int.negSucc b = -↑x → sq_le x c a d) => idRhs (sq_le (b + 1) c a d) (ᾰ (b + 1) rfl)) ᾰ

theorem nonnegg_cases_left {c : ℕ} {d : ℕ} {b : ℕ} {a : ℤ} (h : ∀ (x : ℕ), a = -↑x → sq_le x d b c) : nonnegg c d a ↑b :=
  cast nonnegg_comm (nonnegg_cases_right h)

def norm {d : ℤ} (n : ℤ√d) : ℤ :=
  re n * re n - d * im n * im n

@[simp] theorem norm_zero {d : ℤ} : norm 0 = 0 := sorry

@[simp] theorem norm_one {d : ℤ} : norm 1 = 1 := sorry

@[simp] theorem norm_int_cast {d : ℤ} (n : ℤ) : norm ↑n = n * n := sorry

@[simp] theorem norm_nat_cast {d : ℤ} (n : ℕ) : norm ↑n = ↑n * ↑n :=
  norm_int_cast ↑n

@[simp] theorem norm_mul {d : ℤ} (n : ℤ√d) (m : ℤ√d) : norm (n * m) = norm n * norm m := sorry

theorem norm_eq_mul_conj {d : ℤ} (n : ℤ√d) : ↑(norm n) = n * conj n := sorry

protected instance norm.is_monoid_hom {d : ℤ} : is_monoid_hom norm :=
  is_monoid_hom.mk norm_one

theorem norm_nonneg {d : ℤ} (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ norm n := sorry

theorem norm_eq_one_iff {d : ℤ} {x : ℤ√d} : int.nat_abs (norm x) = 1 ↔ is_unit x := sorry

/-- Nonnegativity of an element of `ℤ√d`. -/
def nonneg {d : ℕ} : ℤ√↑d → Prop :=
  sorry

protected def le {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d)  :=
  nonneg (b - a)

protected instance has_le {d : ℕ} : HasLessEq (ℤ√↑d) :=
  { LessEq := zsqrtd.le }

protected def lt {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d)  :=
  ¬b ≤ a

protected instance has_lt {d : ℕ} : HasLess (ℤ√↑d) :=
  { Less := zsqrtd.lt }

protected instance decidable_nonnegg (c : ℕ) (d : ℕ) (a : ℤ) (b : ℤ) : Decidable (nonnegg c d a b) :=
  int.cases_on a
    (fun (a : ℕ) =>
      int.cases_on b (fun (b : ℕ) => eq.mpr sorry (eq.mpr sorry (eq.mpr sorry decidable.true)))
        fun (b : ℕ) => eq.mpr sorry (eq.mpr sorry (nat.decidable_le (c * (b + 1) * (b + 1)) (d * a * a))))
    fun (a : ℕ) =>
      int.cases_on b (fun (b : ℕ) => eq.mpr sorry (eq.mpr sorry (nat.decidable_le (d * (a + 1) * (a + 1)) (c * b * b))))
        fun (b : ℕ) => eq.mpr sorry decidable.false

protected instance decidable_nonneg {d : ℕ} (a : ℤ√↑d) : Decidable (nonneg a) :=
  sorry

protected instance decidable_le {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d) : Decidable (a ≤ b) :=
  zsqrtd.decidable_nonneg (b - a)

theorem nonneg_cases {d : ℕ} {a : ℤ√↑d} : nonneg a → ∃ (x : ℕ), ∃ (y : ℕ), a = mk ↑x ↑y ∨ a = mk (↑x) (-↑y) ∨ a = mk (-↑x) ↑y := sorry

theorem nonneg_add_lem {d : ℕ} {x : ℕ} {y : ℕ} {z : ℕ} {w : ℕ} (xy : nonneg (mk (↑x) (-↑y))) (zw : nonneg (mk (-↑z) ↑w)) : nonneg (mk (↑x) (-↑y) + mk (-↑z) ↑w) := sorry

theorem nonneg_add {d : ℕ} {a : ℤ√↑d} {b : ℤ√↑d} (ha : nonneg a) (hb : nonneg b) : nonneg (a + b) := sorry

theorem le_refl {d : ℕ} (a : ℤ√↑d) : a ≤ a :=
  (fun (this : nonneg (a - a)) => this)
    (eq.mpr (id ((fun (ᾰ ᾰ_1 : ℤ√↑d) (e_1 : ᾰ = ᾰ_1) => congr_arg nonneg e_1) (a - a) 0 (sub_self a))) trivial)

protected theorem le_trans {d : ℕ} {a : ℤ√↑d} {b : ℤ√↑d} {c : ℤ√↑d} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := sorry

theorem nonneg_iff_zero_le {d : ℕ} {a : ℤ√↑d} : nonneg a ↔ 0 ≤ a := sorry

theorem le_of_le_le {d : ℕ} {x : ℤ} {y : ℤ} {z : ℤ} {w : ℤ} (xz : x ≤ z) (yw : y ≤ w) : mk x y ≤ mk z w := sorry

theorem le_arch {d : ℕ} (a : ℤ√↑d) : ∃ (n : ℕ), a ≤ ↑n := sorry

protected theorem nonneg_total {d : ℕ} (a : ℤ√↑d) : nonneg a ∨ nonneg (-a) := sorry

protected theorem le_total {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d) : a ≤ b ∨ b ≤ a :=
  let t : nonneg (b - a) ∨ nonneg (-(b - a)) := zsqrtd.nonneg_total (b - a);
  eq.mp
    (Eq._oldrec (Eq.refl (nonneg (b - a) ∨ nonneg (-(b - a)))) ((fun (this : -(b - a) = a - b) => this) (neg_sub b a))) t

protected instance preorder {d : ℕ} : preorder (ℤ√↑d) :=
  preorder.mk zsqrtd.le zsqrtd.lt le_refl zsqrtd.le_trans

protected theorem add_le_add_left {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d) (ab : a ≤ b) (c : ℤ√↑d) : c + a ≤ c + b :=
  (fun (this : nonneg (c + b - (c + a))) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (nonneg (c + b - (c + a)))) (add_sub_add_left_eq_sub b a c))) ab)

protected theorem le_of_add_le_add_left {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d) (c : ℤ√↑d) (h : c + a ≤ c + b) : a ≤ b := sorry

protected theorem add_lt_add_left {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d) (h : a < b) (c : ℤ√↑d) : c + a < c + b :=
  fun (h' : c + b ≤ c + a) => h (zsqrtd.le_of_add_le_add_left b a c h')

theorem nonneg_smul {d : ℕ} {a : ℤ√↑d} {n : ℕ} (ha : nonneg a) : nonneg (↑n * a) := sorry

theorem nonneg_muld {d : ℕ} {a : ℤ√↑d} (ha : nonneg a) : nonneg (sqrtd * a) := sorry

theorem nonneg_mul_lem {d : ℕ} {x : ℕ} {y : ℕ} {a : ℤ√↑d} (ha : nonneg a) : nonneg (mk ↑x ↑y * a) := sorry

theorem nonneg_mul {d : ℕ} {a : ℤ√↑d} {b : ℤ√↑d} (ha : nonneg a) (hb : nonneg b) : nonneg (a * b) := sorry

protected theorem mul_nonneg {d : ℕ} (a : ℤ√↑d) (b : ℤ√↑d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := sorry

theorem not_sq_le_succ (c : ℕ) (d : ℕ) (y : ℕ) (h : 0 < c) : ¬sq_le (y + 1) c 0 d :=
  not_le_of_gt (mul_pos (mul_pos h (nat.succ_pos y)) (nat.succ_pos y))

/-- A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory. -/
class nonsquare (x : ℕ) 
where
  ns : ∀ (n : ℕ), x ≠ n * n

theorem d_pos {d : ℕ} [dnsq : nonsquare d] : 0 < d :=
  lt_of_le_of_ne (nat.zero_le d) (ne.symm (nonsquare.ns d 0))

theorem divides_sq_eq_zero {d : ℕ} [dnsq : nonsquare d] {x : ℕ} {y : ℕ} (h : x * x = d * y * y) : x = 0 ∧ y = 0 := sorry

theorem divides_sq_eq_zero_z {d : ℕ} [dnsq : nonsquare d] {x : ℤ} {y : ℤ} (h : x * x = ↑d * y * y) : x = 0 ∧ y = 0 := sorry

theorem not_divides_square {d : ℕ} [dnsq : nonsquare d] (x : ℕ) (y : ℕ) : (x + 1) * (x + 1) ≠ d * (y + 1) * (y + 1) :=
  fun (e : (x + 1) * (x + 1) = d * (y + 1) * (y + 1)) => nat.no_confusion (and.left (divides_sq_eq_zero e))

theorem nonneg_antisymm {d : ℕ} [dnsq : nonsquare d] {a : ℤ√↑d} : nonneg a → nonneg (-a) → a = 0 := sorry

theorem le_antisymm {d : ℕ} [dnsq : nonsquare d] {a : ℤ√↑d} {b : ℤ√↑d} (ab : a ≤ b) (ba : b ≤ a) : a = b :=
  eq_of_sub_eq_zero (nonneg_antisymm ba (eq.mpr (id (Eq._oldrec (Eq.refl (nonneg (-(a - b)))) (neg_sub a b))) ab))

protected instance linear_order {d : ℕ} [dnsq : nonsquare d] : linear_order (ℤ√↑d) :=
  linear_order.mk preorder.le preorder.lt sorry sorry le_antisymm zsqrtd.le_total zsqrtd.decidable_le
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero {d : ℕ} [dnsq : nonsquare d] {a : ℤ√↑d} {b : ℤ√↑d} : a * b = 0 → a = 0 ∨ b = 0 := sorry

protected instance integral_domain {d : ℕ} [dnsq : nonsquare d] : integral_domain (ℤ√↑d) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero

protected theorem mul_pos {d : ℕ} [dnsq : nonsquare d] (a : ℤ√↑d) (b : ℤ√↑d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := sorry

protected instance linear_ordered_comm_ring {d : ℕ} [dnsq : nonsquare d] : linear_ordered_comm_ring (ℤ√↑d) :=
  linear_ordered_comm_ring.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry
    comm_ring.mul sorry comm_ring.one sorry sorry sorry sorry linear_order.le linear_order.lt sorry sorry sorry
    zsqrtd.add_le_add_left sorry zsqrtd.mul_pos sorry linear_order.decidable_le linear_order.decidable_eq
    linear_order.decidable_lt sorry sorry

protected instance linear_ordered_semiring {d : ℕ} [dnsq : nonsquare d] : linear_ordered_semiring (ℤ√↑d) :=
  linear_ordered_comm_ring.to_linear_ordered_semiring

protected instance ordered_semiring {d : ℕ} [dnsq : nonsquare d] : ordered_semiring (ℤ√↑d) :=
  ordered_ring.to_ordered_semiring

theorem norm_eq_zero {d : ℤ} (h_nonsquare : ∀ (n : ℤ), d ≠ n * n) (a : ℤ√d) : norm a = 0 ↔ a = 0 := sorry

theorem hom_ext {R : Type} [comm_ring R] {d : ℤ} (f : ℤ√d →+* R) (g : ℤ√d →+* R) (h : coe_fn f sqrtd = coe_fn g sqrtd) : f = g := sorry

/-- The unique `ring_hom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` with the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` in `R`. -/
@[simp] theorem lift_symm_apply_coe {R : Type} [comm_ring R] {d : ℤ} (f : ℤ√d →+* R) : ↑(coe_fn (equiv.symm lift) f) = coe_fn f sqrtd :=
  Eq.refl ↑(coe_fn (equiv.symm lift) f)

/-- `lift r` is injective if `d` is non-square, and R has characteristic zero (that is, the map from
`ℤ` into `R` is injective). -/
theorem lift_injective {R : Type} [comm_ring R] [char_zero R] {d : ℤ} (r : Subtype fun (r : R) => r * r = ↑d) (hd : ∀ (n : ℤ), d ≠ n * n) : function.injective ⇑(coe_fn lift r) := sorry

