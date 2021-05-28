/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.real.sqrt
import Mathlib.PostPort

universes l u_1 

namespace Mathlib

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way.
-/

/-! ### Definition and basic arithmmetic -/

/-- Complex numbers consist of two `real`s: a real part `re` and an imaginary part `im`. -/
structure complex 
where
  re : ℝ
  im : ℝ

notation:1024 "ℂ" => Mathlib.complex

namespace complex


protected instance decidable_eq : DecidableEq ℂ :=
  classical.dec_eq ℂ

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
def equiv_real_prod : ℂ ≃ ℝ × ℝ :=
  equiv.mk (fun (z : ℂ) => (re z, im z)) (fun (p : ℝ × ℝ) => mk (prod.fst p) (prod.snd p)) sorry sorry

@[simp] theorem equiv_real_prod_apply (z : ℂ) : coe_fn equiv_real_prod z = (re z, im z) :=
  rfl

theorem equiv_real_prod_symm_re (x : ℝ) (y : ℝ) : re (coe_fn (equiv.symm equiv_real_prod) (x, y)) = x :=
  rfl

theorem equiv_real_prod_symm_im (x : ℝ) (y : ℝ) : im (coe_fn (equiv.symm equiv_real_prod) (x, y)) = y :=
  rfl

@[simp] theorem eta (z : ℂ) : mk (re z) (im z) = z :=
  cases_on z
    fun (z_re z_im : ℝ) =>
      idRhs (mk (re (mk z_re z_im)) (im (mk z_re z_im)) = mk (re (mk z_re z_im)) (im (mk z_re z_im))) rfl

theorem ext {z : ℂ} {w : ℂ} : re z = re w → im z = im w → z = w := sorry

theorem ext_iff {z : ℂ} {w : ℂ} : z = w ↔ re z = re w ∧ im z = im w := sorry

protected instance has_coe : has_coe ℝ ℂ :=
  has_coe.mk fun (r : ℝ) => mk r 0

@[simp] theorem of_real_re (r : ℝ) : re ↑r = r :=
  rfl

@[simp] theorem of_real_im (r : ℝ) : im ↑r = 0 :=
  rfl

@[simp] theorem of_real_inj {z : ℝ} {w : ℝ} : ↑z = ↑w ↔ z = w :=
  { mp := congr_arg re, mpr := congr_arg fun {z : ℝ} => ↑z }

protected instance has_zero : HasZero ℂ :=
  { zero := ↑0 }

protected instance inhabited : Inhabited ℂ :=
  { default := 0 }

@[simp] theorem zero_re : re 0 = 0 :=
  rfl

@[simp] theorem zero_im : im 0 = 0 :=
  rfl

@[simp] theorem of_real_zero : ↑0 = 0 :=
  rfl

@[simp] theorem of_real_eq_zero {z : ℝ} : ↑z = 0 ↔ z = 0 :=
  of_real_inj

theorem of_real_ne_zero {z : ℝ} : ↑z ≠ 0 ↔ z ≠ 0 :=
  not_congr of_real_eq_zero

protected instance has_one : HasOne ℂ :=
  { one := ↑1 }

@[simp] theorem one_re : re 1 = 1 :=
  rfl

@[simp] theorem one_im : im 1 = 0 :=
  rfl

@[simp] theorem of_real_one : ↑1 = 1 :=
  rfl

protected instance has_add : Add ℂ :=
  { add := fun (z w : ℂ) => mk (re z + re w) (im z + im w) }

@[simp] theorem add_re (z : ℂ) (w : ℂ) : re (z + w) = re z + re w :=
  rfl

@[simp] theorem add_im (z : ℂ) (w : ℂ) : im (z + w) = im z + im w :=
  rfl

@[simp] theorem bit0_re (z : ℂ) : re (bit0 z) = bit0 (re z) :=
  rfl

@[simp] theorem bit1_re (z : ℂ) : re (bit1 z) = bit1 (re z) :=
  rfl

@[simp] theorem bit0_im (z : ℂ) : im (bit0 z) = bit0 (im z) :=
  Eq.refl (im (bit0 z))

@[simp] theorem bit1_im (z : ℂ) : im (bit1 z) = bit0 (im z) :=
  add_zero (im (bit0 z))

@[simp] theorem of_real_add (r : ℝ) (s : ℝ) : ↑(r + s) = ↑r + ↑s := sorry

@[simp] theorem of_real_bit0 (r : ℝ) : ↑(bit0 r) = bit0 ↑r := sorry

@[simp] theorem of_real_bit1 (r : ℝ) : ↑(bit1 r) = bit1 ↑r := sorry

protected instance has_neg : Neg ℂ :=
  { neg := fun (z : ℂ) => mk (-re z) (-im z) }

@[simp] theorem neg_re (z : ℂ) : re (-z) = -re z :=
  rfl

@[simp] theorem neg_im (z : ℂ) : im (-z) = -im z :=
  rfl

@[simp] theorem of_real_neg (r : ℝ) : ↑(-r) = -↑r := sorry

protected instance has_sub : Sub ℂ :=
  { sub := fun (z w : ℂ) => mk (re z - re w) (im z - im w) }

protected instance has_mul : Mul ℂ :=
  { mul := fun (z w : ℂ) => mk (re z * re w - im z * im w) (re z * im w + im z * re w) }

@[simp] theorem mul_re (z : ℂ) (w : ℂ) : re (z * w) = re z * re w - im z * im w :=
  rfl

@[simp] theorem mul_im (z : ℂ) (w : ℂ) : im (z * w) = re z * im w + im z * re w :=
  rfl

@[simp] theorem of_real_mul (r : ℝ) (s : ℝ) : ↑(r * s) = ↑r * ↑s := sorry

theorem smul_re (r : ℝ) (z : ℂ) : re (↑r * z) = r * re z := sorry

theorem smul_im (r : ℝ) (z : ℂ) : im (↑r * z) = r * im z := sorry

theorem of_real_smul (r : ℝ) (z : ℂ) : ↑r * z = mk (r * re z) (r * im z) :=
  ext (smul_re r z) (smul_im r z)

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
def I : ℂ :=
  mk 0 1

@[simp] theorem I_re : re I = 0 :=
  rfl

@[simp] theorem I_im : im I = 1 :=
  rfl

@[simp] theorem I_mul_I : I * I = -1 := sorry

theorem I_mul (z : ℂ) : I * z = mk (-im z) (re z) := sorry

theorem I_ne_zero : I ≠ 0 :=
  mt (congr_arg im) (ne.symm zero_ne_one)

theorem mk_eq_add_mul_I (a : ℝ) (b : ℝ) : mk a b = ↑a + ↑b * I := sorry

@[simp] theorem re_add_im (z : ℂ) : ↑(re z) + ↑(im z) * I = z := sorry

/-! ### Commutative ring instance and lemmas -/

protected instance comm_ring : comm_ring ℂ :=
  comm_ring.mk Add.add sorry 0 sorry sorry Neg.neg Sub.sub sorry sorry Mul.mul sorry 1 sorry sorry sorry sorry sorry

protected instance re.is_add_group_hom : is_add_group_hom re :=
  is_add_group_hom.mk

protected instance im.is_add_group_hom : is_add_group_hom im :=
  is_add_group_hom.mk

@[simp] theorem I_pow_bit0 (n : ℕ) : I ^ bit0 n = (-1) ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ^ bit0 n = (-1) ^ n)) (pow_bit0' I n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((I * I) ^ n = (-1) ^ n)) I_mul_I)) (Eq.refl ((-1) ^ n)))

@[simp] theorem I_pow_bit1 (n : ℕ) : I ^ bit1 n = (-1) ^ n * I :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ^ bit1 n = (-1) ^ n * I)) (pow_bit1' I n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((I * I) ^ n * I = (-1) ^ n * I)) I_mul_I)) (Eq.refl ((-1) ^ n * I)))

/-! ### Complex conjugation -/

/-- The complex conjugate. -/
def conj : ℂ →+* ℂ :=
  ring_hom.mk (fun (z : ℂ) => mk (re z) (-im z)) sorry sorry sorry sorry

@[simp] theorem conj_re (z : ℂ) : re (coe_fn conj z) = re z :=
  rfl

@[simp] theorem conj_im (z : ℂ) : im (coe_fn conj z) = -im z :=
  rfl

@[simp] theorem conj_of_real (r : ℝ) : coe_fn conj ↑r = ↑r := sorry

@[simp] theorem conj_I : coe_fn conj I = -I := sorry

@[simp] theorem conj_bit0 (z : ℂ) : coe_fn conj (bit0 z) = bit0 (coe_fn conj z) := sorry

@[simp] theorem conj_bit1 (z : ℂ) : coe_fn conj (bit1 z) = bit1 (coe_fn conj z) := sorry

@[simp] theorem conj_neg_I : coe_fn conj (-I) = I := sorry

@[simp] theorem conj_conj (z : ℂ) : coe_fn conj (coe_fn conj z) = z := sorry

theorem conj_involutive : function.involutive ⇑conj :=
  conj_conj

theorem conj_bijective : function.bijective ⇑conj :=
  function.involutive.bijective conj_involutive

theorem conj_inj {z : ℂ} {w : ℂ} : coe_fn conj z = coe_fn conj w ↔ z = w :=
  function.injective.eq_iff (and.left conj_bijective)

@[simp] theorem conj_eq_zero {z : ℂ} : coe_fn conj z = 0 ↔ z = 0 := sorry

theorem eq_conj_iff_real {z : ℂ} : coe_fn conj z = z ↔ ∃ (r : ℝ), z = ↑r := sorry

theorem eq_conj_iff_re {z : ℂ} : coe_fn conj z = z ↔ ↑(re z) = z := sorry

protected instance star_ring : star_ring ℂ :=
  star_ring.mk sorry

/-! ### Norm squared -/

/-- The norm squared function. -/
def norm_sq : monoid_with_zero_hom ℂ ℝ :=
  monoid_with_zero_hom.mk (fun (z : ℂ) => re z * re z + im z * im z) sorry sorry sorry

theorem norm_sq_apply (z : ℂ) : coe_fn norm_sq z = re z * re z + im z * im z :=
  rfl

@[simp] theorem norm_sq_of_real (r : ℝ) : coe_fn norm_sq ↑r = r * r := sorry

theorem norm_sq_zero : coe_fn norm_sq 0 = 0 :=
  monoid_with_zero_hom.map_zero norm_sq

theorem norm_sq_one : coe_fn norm_sq 1 = 1 :=
  monoid_with_zero_hom.map_one norm_sq

@[simp] theorem norm_sq_I : coe_fn norm_sq I = 1 := sorry

theorem norm_sq_nonneg (z : ℂ) : 0 ≤ coe_fn norm_sq z :=
  add_nonneg (mul_self_nonneg (re z)) (mul_self_nonneg (im z))

theorem norm_sq_eq_zero {z : ℂ} : coe_fn norm_sq z = 0 ↔ z = 0 := sorry

@[simp] theorem norm_sq_pos {z : ℂ} : 0 < coe_fn norm_sq z ↔ z ≠ 0 :=
  iff.trans (has_le.le.lt_iff_ne (norm_sq_nonneg z)) (not_congr (iff.trans eq_comm norm_sq_eq_zero))

@[simp] theorem norm_sq_neg (z : ℂ) : coe_fn norm_sq (-z) = coe_fn norm_sq z := sorry

@[simp] theorem norm_sq_conj (z : ℂ) : coe_fn norm_sq (coe_fn conj z) = coe_fn norm_sq z := sorry

theorem norm_sq_mul (z : ℂ) (w : ℂ) : coe_fn norm_sq (z * w) = coe_fn norm_sq z * coe_fn norm_sq w :=
  monoid_with_zero_hom.map_mul norm_sq z w

theorem norm_sq_add (z : ℂ) (w : ℂ) : coe_fn norm_sq (z + w) = coe_fn norm_sq z + coe_fn norm_sq w + bit0 1 * re (z * coe_fn conj w) := sorry

theorem re_sq_le_norm_sq (z : ℂ) : re z * re z ≤ coe_fn norm_sq z :=
  le_add_of_nonneg_right (mul_self_nonneg (im z))

theorem im_sq_le_norm_sq (z : ℂ) : im z * im z ≤ coe_fn norm_sq z :=
  le_add_of_nonneg_left (mul_self_nonneg (re z))

theorem mul_conj (z : ℂ) : z * coe_fn conj z = ↑(coe_fn norm_sq z) := sorry

theorem add_conj (z : ℂ) : z + coe_fn conj z = ↑(bit0 1 * re z) := sorry

/-- The coercion `ℝ → ℂ` as a `ring_hom`. -/
def of_real : ℝ →+* ℂ :=
  ring_hom.mk coe of_real_one of_real_mul of_real_zero of_real_add

@[simp] theorem of_real_eq_coe (r : ℝ) : coe_fn of_real r = ↑r :=
  rfl

@[simp] theorem I_sq : I ^ bit0 1 = -1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ^ bit0 1 = -1)) (pow_two I)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (I * I = -1)) I_mul_I)) (Eq.refl (-1)))

@[simp] theorem sub_re (z : ℂ) (w : ℂ) : re (z - w) = re z - re w :=
  rfl

@[simp] theorem sub_im (z : ℂ) (w : ℂ) : im (z - w) = im z - im w :=
  rfl

@[simp] theorem of_real_sub (r : ℝ) (s : ℝ) : ↑(r - s) = ↑r - ↑s := sorry

@[simp] theorem of_real_pow (r : ℝ) (n : ℕ) : ↑(r ^ n) = ↑r ^ n := sorry

theorem sub_conj (z : ℂ) : z - coe_fn conj z = ↑(bit0 1 * im z) * I := sorry

theorem norm_sq_sub (z : ℂ) (w : ℂ) : coe_fn norm_sq (z - w) = coe_fn norm_sq z + coe_fn norm_sq w - bit0 1 * re (z * coe_fn conj w) := sorry

/-! ### Inversion -/

protected instance has_inv : has_inv ℂ :=
  has_inv.mk fun (z : ℂ) => coe_fn conj z * ↑(coe_fn norm_sq z⁻¹)

theorem inv_def (z : ℂ) : z⁻¹ = coe_fn conj z * ↑(coe_fn norm_sq z⁻¹) :=
  rfl

@[simp] theorem inv_re (z : ℂ) : re (z⁻¹) = re z / coe_fn norm_sq z := sorry

@[simp] theorem inv_im (z : ℂ) : im (z⁻¹) = -im z / coe_fn norm_sq z := sorry

@[simp] theorem of_real_inv (r : ℝ) : ↑(r⁻¹) = (↑r⁻¹) := sorry

protected theorem inv_zero : 0⁻¹ = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0⁻¹ = 0)) (Eq.symm of_real_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑0⁻¹ = ↑0)) (Eq.symm (of_real_inv 0))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑(0⁻¹) = ↑0)) inv_zero)) (Eq.refl ↑0)))

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * (z⁻¹) = 1 := sorry

/-! ### Field instance and lemmas -/

protected instance field : field ℂ :=
  field.mk comm_ring.add comm_ring.add_assoc comm_ring.zero comm_ring.zero_add comm_ring.add_zero comm_ring.neg
    comm_ring.sub comm_ring.add_left_neg comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc comm_ring.one
    comm_ring.one_mul comm_ring.mul_one comm_ring.left_distrib comm_ring.right_distrib comm_ring.mul_comm has_inv.inv
    sorry complex.mul_inv_cancel complex.inv_zero

@[simp] theorem I_fpow_bit0 (n : ℤ) : I ^ bit0 n = (-1) ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ^ bit0 n = (-1) ^ n)) (fpow_bit0' I n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((I * I) ^ n = (-1) ^ n)) I_mul_I)) (Eq.refl ((-1) ^ n)))

@[simp] theorem I_fpow_bit1 (n : ℤ) : I ^ bit1 n = (-1) ^ n * I :=
  eq.mpr (id (Eq._oldrec (Eq.refl (I ^ bit1 n = (-1) ^ n * I)) (fpow_bit1' I n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((I * I) ^ n * I = (-1) ^ n * I)) I_mul_I)) (Eq.refl ((-1) ^ n * I)))

theorem div_re (z : ℂ) (w : ℂ) : re (z / w) = re z * re w / coe_fn norm_sq w + im z * im w / coe_fn norm_sq w := sorry

theorem div_im (z : ℂ) (w : ℂ) : im (z / w) = im z * re w / coe_fn norm_sq w - re z * im w / coe_fn norm_sq w := sorry

@[simp] theorem of_real_div (r : ℝ) (s : ℝ) : ↑(r / s) = ↑r / ↑s :=
  ring_hom.map_div of_real r s

@[simp] theorem of_real_fpow (r : ℝ) (n : ℤ) : ↑(r ^ n) = ↑r ^ n :=
  ring_hom.map_fpow of_real r n

@[simp] theorem div_I (z : ℂ) : z / I = -(z * I) := sorry

@[simp] theorem inv_I : I⁻¹ = -I := sorry

@[simp] theorem norm_sq_inv (z : ℂ) : coe_fn norm_sq (z⁻¹) = (coe_fn norm_sq z⁻¹) :=
  monoid_with_zero_hom.map_inv' norm_sq z

@[simp] theorem norm_sq_div (z : ℂ) (w : ℂ) : coe_fn norm_sq (z / w) = coe_fn norm_sq z / coe_fn norm_sq w :=
  monoid_with_zero_hom.map_div norm_sq z w

/-! ### Cast lemmas -/

@[simp] theorem of_real_nat_cast (n : ℕ) : ↑↑n = ↑n :=
  ring_hom.map_nat_cast of_real n

@[simp] theorem nat_cast_re (n : ℕ) : re ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (re ↑n = ↑n)) (Eq.symm (of_real_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (re ↑↑n = ↑n)) (of_real_re ↑n))) (Eq.refl ↑n))

@[simp] theorem nat_cast_im (n : ℕ) : im ↑n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im ↑n = 0)) (Eq.symm (of_real_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑↑n = 0)) (of_real_im ↑n))) (Eq.refl 0))

@[simp] theorem of_real_int_cast (n : ℤ) : ↑↑n = ↑n :=
  ring_hom.map_int_cast of_real n

@[simp] theorem int_cast_re (n : ℤ) : re ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (re ↑n = ↑n)) (Eq.symm (of_real_int_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (re ↑↑n = ↑n)) (of_real_re ↑n))) (Eq.refl ↑n))

@[simp] theorem int_cast_im (n : ℤ) : im ↑n = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im ↑n = 0)) (Eq.symm (of_real_int_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑↑n = 0)) (of_real_im ↑n))) (Eq.refl 0))

@[simp] theorem of_real_rat_cast (n : ℚ) : ↑↑n = ↑n :=
  ring_hom.map_rat_cast of_real n

@[simp] theorem rat_cast_re (q : ℚ) : re ↑q = ↑q :=
  eq.mpr (id (Eq._oldrec (Eq.refl (re ↑q = ↑q)) (Eq.symm (of_real_rat_cast q))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (re ↑↑q = ↑q)) (of_real_re ↑q))) (Eq.refl ↑q))

@[simp] theorem rat_cast_im (q : ℚ) : im ↑q = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im ↑q = 0)) (Eq.symm (of_real_rat_cast q))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑↑q = 0)) (of_real_im ↑q))) (Eq.refl 0))

/-! ### Characteristic zero -/

protected instance char_zero_complex : char_zero ℂ :=
  char_zero_of_inj_zero
    fun (n : ℕ) (h : ↑n = 0) =>
      eq.mp (Eq._oldrec (Eq.refl (↑n = 0)) (propext nat.cast_eq_zero))
        (eq.mp (Eq._oldrec (Eq.refl (↑↑n = 0)) (propext of_real_eq_zero))
          (eq.mp (Eq._oldrec (Eq.refl (↑n = 0)) (Eq.symm (of_real_nat_cast n))) h))

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : ↑(re z) = (z + coe_fn conj z) / bit0 1 := sorry

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : ↑(im z) = (z - coe_fn conj z) / (bit0 1 * I) := sorry

/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/
def abs (z : ℂ) : ℝ :=
  real.sqrt (coe_fn norm_sq z)

@[simp] theorem abs_of_real (r : ℝ) : abs ↑r = abs r := sorry

theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : abs ↑r = r :=
  Eq.trans (abs_of_real r) (abs_of_nonneg h)

theorem abs_of_nat (n : ℕ) : abs ↑n = ↑n :=
  Eq.trans (eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑n = abs ↑↑n)) (of_real_nat_cast n))) (Eq.refl (abs ↑n)))
    (abs_of_nonneg (nat.cast_nonneg n))

theorem mul_self_abs (z : ℂ) : abs z * abs z = coe_fn norm_sq z :=
  real.mul_self_sqrt (norm_sq_nonneg z)

@[simp] theorem abs_zero : abs 0 = 0 := sorry

@[simp] theorem abs_one : abs 1 = 1 := sorry

@[simp] theorem abs_I : abs I = 1 := sorry

@[simp] theorem abs_two : abs (bit0 1) = bit0 1 := sorry

theorem abs_nonneg (z : ℂ) : 0 ≤ abs z :=
  real.sqrt_nonneg (coe_fn norm_sq z)

@[simp] theorem abs_eq_zero {z : ℂ} : abs z = 0 ↔ z = 0 :=
  iff.trans (real.sqrt_eq_zero (norm_sq_nonneg z)) norm_sq_eq_zero

theorem abs_ne_zero {z : ℂ} : abs z ≠ 0 ↔ z ≠ 0 :=
  not_congr abs_eq_zero

@[simp] theorem abs_conj (z : ℂ) : abs (coe_fn conj z) = abs z := sorry

@[simp] theorem abs_mul (z : ℂ) (w : ℂ) : abs (z * w) = abs z * abs w := sorry

theorem abs_re_le_abs (z : ℂ) : abs (re z) ≤ abs z := sorry

theorem abs_im_le_abs (z : ℂ) : abs (im z) ≤ abs z := sorry

theorem re_le_abs (z : ℂ) : re z ≤ abs z :=
  and.right (iff.mp abs_le (abs_re_le_abs z))

theorem im_le_abs (z : ℂ) : im z ≤ abs z :=
  and.right (iff.mp abs_le (abs_im_le_abs z))

theorem abs_add (z : ℂ) (w : ℂ) : abs (z + w) ≤ abs z + abs w := sorry

protected instance abs.is_absolute_value : is_absolute_value abs :=
  is_absolute_value.mk abs_nonneg (fun (_x : ℂ) => abs_eq_zero) abs_add abs_mul

@[simp] theorem abs_abs (z : ℂ) : abs (abs z) = abs z :=
  abs_of_nonneg (abs_nonneg z)

@[simp] theorem abs_pos {z : ℂ} : 0 < abs z ↔ z ≠ 0 :=
  is_absolute_value.abv_pos abs

@[simp] theorem abs_neg (z : ℂ) : abs (-z) = abs z :=
  is_absolute_value.abv_neg abs

theorem abs_sub (z : ℂ) (w : ℂ) : abs (z - w) = abs (w - z) :=
  is_absolute_value.abv_sub abs

theorem abs_sub_le (a : ℂ) (b : ℂ) (c : ℂ) : abs (a - c) ≤ abs (a - b) + abs (b - c) :=
  is_absolute_value.abv_sub_le abs

@[simp] theorem abs_inv (z : ℂ) : abs (z⁻¹) = (abs z⁻¹) :=
  is_absolute_value.abv_inv abs

@[simp] theorem abs_div (z : ℂ) (w : ℂ) : abs (z / w) = abs z / abs w :=
  is_absolute_value.abv_div abs

theorem abs_abs_sub_le_abs_sub (z : ℂ) (w : ℂ) : abs (abs z - abs w) ≤ abs (z - w) :=
  is_absolute_value.abs_abv_sub_le_abv_sub abs

theorem abs_le_abs_re_add_abs_im (z : ℂ) : abs z ≤ abs (re z) + abs (im z) := sorry

theorem abs_re_div_abs_le_one (z : ℂ) : abs (re z / abs z) ≤ 1 := sorry

theorem abs_im_div_abs_le_one (z : ℂ) : abs (im z / abs z) ≤ 1 := sorry

@[simp] theorem abs_cast_nat (n : ℕ) : abs ↑n = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑n = ↑n)) (Eq.symm (of_real_nat_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (abs ↑↑n = ↑n)) (abs_of_nonneg (nat.cast_nonneg n)))) (Eq.refl ↑n))

@[simp] theorem int_cast_abs (n : ℤ) : ↑(abs n) = abs ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(abs n) = abs ↑n)) (Eq.symm (of_real_int_cast n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(abs n) = abs ↑↑n)) (abs_of_real ↑n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (↑(abs n) = abs ↑n)) int.cast_abs)) (Eq.refl (abs ↑n))))

theorem norm_sq_eq_abs (x : ℂ) : coe_fn norm_sq x = abs x ^ bit0 1 := sorry

/-! ### Cauchy sequences -/

theorem is_cau_seq_re (f : cau_seq ℂ abs) : is_cau_seq abs fun (n : ℕ) => re (coe_fn f n) := sorry

theorem is_cau_seq_im (f : cau_seq ℂ abs) : is_cau_seq abs fun (n : ℕ) => im (coe_fn f n) := sorry

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
def cau_seq_re (f : cau_seq ℂ abs) : cau_seq ℝ abs :=
  { val := fun (n : ℕ) => re (coe_fn f n), property := is_cau_seq_re f }

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
def cau_seq_im (f : cau_seq ℂ abs) : cau_seq ℝ abs :=
  { val := fun (n : ℕ) => im (coe_fn f n), property := is_cau_seq_im f }

theorem is_cau_seq_abs {f : ℕ → ℂ} (hf : is_cau_seq abs f) : is_cau_seq abs (abs ∘ f) := sorry

/-- The limit of a Cauchy sequence of complex numbers. -/
def lim_aux (f : cau_seq ℂ abs) : ℂ :=
  mk (cau_seq.lim (cau_seq_re f)) (cau_seq.lim (cau_seq_im f))

theorem equiv_lim_aux (f : cau_seq ℂ abs) : f ≈ cau_seq.const abs (lim_aux f) := sorry

protected instance abs.cau_seq.is_complete : cau_seq.is_complete ℂ abs :=
  cau_seq.is_complete.mk sorry

theorem lim_eq_lim_im_add_lim_re (f : cau_seq ℂ abs) : cau_seq.lim f = ↑(cau_seq.lim (cau_seq_re f)) + ↑(cau_seq.lim (cau_seq_im f)) * I := sorry

theorem lim_re (f : cau_seq ℂ abs) : cau_seq.lim (cau_seq_re f) = re (cau_seq.lim f) := sorry

theorem lim_im (f : cau_seq ℂ abs) : cau_seq.lim (cau_seq_im f) = im (cau_seq.lim f) := sorry

theorem is_cau_seq_conj (f : cau_seq ℂ abs) : is_cau_seq abs fun (n : ℕ) => coe_fn conj (coe_fn f n) := sorry

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
def cau_seq_conj (f : cau_seq ℂ abs) : cau_seq ℂ abs :=
  { val := fun (n : ℕ) => coe_fn conj (coe_fn f n), property := is_cau_seq_conj f }

theorem lim_conj (f : cau_seq ℂ abs) : cau_seq.lim (cau_seq_conj f) = coe_fn conj (cau_seq.lim f) := sorry

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
def cau_seq_abs (f : cau_seq ℂ abs) : cau_seq ℝ abs :=
  { val := abs ∘ subtype.val f, property := sorry }

theorem lim_abs (f : cau_seq ℂ abs) : cau_seq.lim (cau_seq_abs f) = abs (cau_seq.lim f) := sorry

@[simp] theorem of_real_prod {α : Type u_1} (s : finset α) (f : α → ℝ) : ↑(finset.prod s fun (i : α) => f i) = finset.prod s fun (i : α) => ↑(f i) :=
  ring_hom.map_prod of_real (fun (x : α) => f x) s

@[simp] theorem of_real_sum {α : Type u_1} (s : finset α) (f : α → ℝ) : ↑(finset.sum s fun (i : α) => f i) = finset.sum s fun (i : α) => ↑(f i) :=
  ring_hom.map_sum of_real (fun (x : α) => f x) s

