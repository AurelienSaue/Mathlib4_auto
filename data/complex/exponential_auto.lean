/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.geom_sum
import Mathlib.data.nat.choose.sum
import Mathlib.data.complex.basic
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Exponential, trigonometric and hyperbolic trigonometric functions

This file contains the definitions of the real and complex exponential, sine, cosine, tangent,
hyperbolic sine, hyperbolic cosine, and hyperbolic tangent functions.

-/

theorem forall_ge_le_of_forall_le_succ {α : Type u_1} [preorder α] (f : ℕ → α) {m : ℕ} (h : ∀ (n : ℕ), n ≥ m → f (Nat.succ n) ≤ f n) {l : ℕ} (k : ℕ) (H : k ≥ m) : k ≤ l → f l ≤ f k := sorry

theorem is_cau_of_decreasing_bounded {α : Type u_1} [linear_ordered_field α] [archimedean α] (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ (n : ℕ), n ≥ m → abs (f n) ≤ a) (hnm : ∀ (n : ℕ), n ≥ m → f (Nat.succ n) ≤ f n) : is_cau_seq abs f := sorry

theorem is_cau_of_mono_bounded {α : Type u_1} [linear_ordered_field α] [archimedean α] (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ (n : ℕ), n ≥ m → abs (f n) ≤ a) (hnm : ∀ (n : ℕ), n ≥ m → f n ≤ f (Nat.succ n)) : is_cau_seq abs f := sorry

theorem is_cau_series_of_abv_le_cau {α : Type u_1} {β : Type u_2} [ring β] [linear_ordered_field α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} {g : ℕ → α} (n : ℕ) : (∀ (m : ℕ), n ≤ m → abv (f m) ≤ g m) →
  (is_cau_seq abs fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => g i) →
    is_cau_seq abv fun (n : ℕ) => finset.sum (finset.range n) fun (i : ℕ) => f i := sorry

theorem is_cau_series_of_abv_cau {α : Type u_1} {β : Type u_2} [ring β] [linear_ordered_field α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} : (is_cau_seq abs fun (m : ℕ) => finset.sum (finset.range m) fun (n : ℕ) => abv (f n)) →
  is_cau_seq abv fun (m : ℕ) => finset.sum (finset.range m) fun (n : ℕ) => f n :=
  is_cau_series_of_abv_le_cau 0 fun (n : ℕ) (h : 0 ≤ n) => le_refl (abv (f n))

theorem is_cau_geo_series {α : Type u_1} [linear_ordered_field α] [archimedean α] {β : Type u_2} [field β] {abv : β → α} [is_absolute_value abv] (x : β) (hx1 : abv x < 1) : is_cau_seq abv fun (n : ℕ) => finset.sum (finset.range n) fun (m : ℕ) => x ^ m := sorry

theorem is_cau_geo_series_const {α : Type u_1} [linear_ordered_field α] [archimedean α] (a : α) {x : α} (hx1 : abs x < 1) : is_cau_seq abs fun (m : ℕ) => finset.sum (finset.range m) fun (n : ℕ) => a * x ^ n := sorry

theorem series_ratio_test {α : Type u_1} {β : Type u_2} [ring β] [linear_ordered_field α] [archimedean α] {abv : β → α} [is_absolute_value abv] {f : ℕ → β} (n : ℕ) (r : α) (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ (m : ℕ), n ≤ m → abv (f (Nat.succ m)) ≤ r * abv (f m)) : is_cau_seq abv fun (m : ℕ) => finset.sum (finset.range m) fun (n : ℕ) => f n := sorry

theorem sum_range_diag_flip {α : Type u_1} [add_comm_monoid α] (n : ℕ) (f : ℕ → ℕ → α) : (finset.sum (finset.range n) fun (m : ℕ) => finset.sum (finset.range (m + 1)) fun (k : ℕ) => f k (m - k)) =
  finset.sum (finset.range n) fun (m : ℕ) => finset.sum (finset.range (n - m)) fun (k : ℕ) => f m k := sorry

theorem sum_range_sub_sum_range {α : Type u_1} [add_comm_group α] {f : ℕ → α} {n : ℕ} {m : ℕ} (hnm : n ≤ m) : ((finset.sum (finset.range m) fun (k : ℕ) => f k) - finset.sum (finset.range n) fun (k : ℕ) => f k) =
  finset.sum (finset.filter (fun (k : ℕ) => n ≤ k) (finset.range m)) fun (k : ℕ) => f k := sorry

theorem abv_sum_le_sum_abv {α : Type u_1} {β : Type u_2} [ring β] [linear_ordered_field α] {abv : β → α} [is_absolute_value abv] {γ : Type u_3} (f : γ → β) (s : finset γ) : abv (finset.sum s fun (k : γ) => f k) ≤ finset.sum s fun (k : γ) => abv (f k) := sorry

theorem cauchy_product {α : Type u_1} {β : Type u_2} [ring β] [linear_ordered_field α] {abv : β → α} [is_absolute_value abv] {a : ℕ → β} {b : ℕ → β} (ha : is_cau_seq abs fun (m : ℕ) => finset.sum (finset.range m) fun (n : ℕ) => abv (a n)) (hb : is_cau_seq abv fun (m : ℕ) => finset.sum (finset.range m) fun (n : ℕ) => b n) (ε : α) (ε0 : 0 < ε) : ∃ (i : ℕ),
  ∀ (j : ℕ),
    j ≥ i →
      abv
          (((finset.sum (finset.range j) fun (k : ℕ) => a k) * finset.sum (finset.range j) fun (n : ℕ) => b n) -
            finset.sum (finset.range j)
              fun (n : ℕ) => finset.sum (finset.range (n + 1)) fun (m : ℕ) => a m * b (n - m)) <
        ε := sorry

namespace complex


theorem is_cau_abs_exp (z : ℂ) : is_cau_seq abs fun (n : ℕ) => finset.sum (finset.range n) fun (m : ℕ) => abs (z ^ m / ↑(nat.factorial m)) := sorry

theorem is_cau_exp (z : ℂ) : is_cau_seq abs fun (n : ℕ) => finset.sum (finset.range n) fun (m : ℕ) => z ^ m / ↑(nat.factorial m) :=
  is_cau_series_of_abv_cau (is_cau_abs_exp z)

/-- The Cauchy sequence consisting of partial sums of the Taylor series of
the complex exponential function -/
def exp' (z : ℂ) : cau_seq ℂ abs :=
  { val := fun (n : ℕ) => finset.sum (finset.range n) fun (m : ℕ) => z ^ m / ↑(nat.factorial m),
    property := is_cau_exp z }

/-- The complex exponential function, defined via its Taylor series -/
def exp (z : ℂ) : ℂ :=
  cau_seq.lim (exp' z)

/-- The complex sine function, defined via `exp` -/
def sin (z : ℂ) : ℂ :=
  (exp (-z * I) - exp (z * I)) * I / bit0 1

/-- The complex cosine function, defined via `exp` -/
def cos (z : ℂ) : ℂ :=
  (exp (z * I) + exp (-z * I)) / bit0 1

/-- The complex tangent function, defined as `sin z / cos z` -/
def tan (z : ℂ) : ℂ :=
  sin z / cos z

/-- The complex hyperbolic sine function, defined via `exp` -/
def sinh (z : ℂ) : ℂ :=
  (exp z - exp (-z)) / bit0 1

/-- The complex hyperbolic cosine function, defined via `exp` -/
def cosh (z : ℂ) : ℂ :=
  (exp z + exp (-z)) / bit0 1

/-- The complex hyperbolic tangent function, defined as `sinh z / cosh z` -/
def tanh (z : ℂ) : ℂ :=
  sinh z / cosh z

end complex


namespace real


/-- The real exponential function, defined as the real part of the complex exponential -/
def exp (x : ℝ) : ℝ :=
  complex.re (complex.exp ↑x)

/-- The real sine function, defined as the real part of the complex sine -/
def sin (x : ℝ) : ℝ :=
  complex.re (complex.sin ↑x)

/-- The real cosine function, defined as the real part of the complex cosine -/
def cos (x : ℝ) : ℝ :=
  complex.re (complex.cos ↑x)

/-- The real tangent function, defined as the real part of the complex tangent -/
def tan (x : ℝ) : ℝ :=
  complex.re (complex.tan ↑x)

/-- The real hypebolic sine function, defined as the real part of the complex hyperbolic sine -/
def sinh (x : ℝ) : ℝ :=
  complex.re (complex.sinh ↑x)

/-- The real hypebolic cosine function, defined as the real part of the complex hyperbolic cosine -/
def cosh (x : ℝ) : ℝ :=
  complex.re (complex.cosh ↑x)

/-- The real hypebolic tangent function, defined as the real part of
the complex hyperbolic tangent -/
def tanh (x : ℝ) : ℝ :=
  complex.re (complex.tanh ↑x)

end real


namespace complex


@[simp] theorem exp_zero : exp 0 = 1 := sorry

theorem exp_add (x : ℂ) (y : ℂ) : exp (x + y) = exp x * exp y := sorry

theorem exp_list_sum (l : List ℂ) : exp (list.sum l) = list.prod (list.map exp l) :=
  monoid_hom.map_list_prod (monoid_hom.mk exp exp_zero exp_add) l

theorem exp_multiset_sum (s : multiset ℂ) : exp (multiset.sum s) = multiset.prod (multiset.map exp s) :=
  monoid_hom.map_multiset_prod (monoid_hom.mk exp exp_zero exp_add) s

theorem exp_sum {α : Type u_1} (s : finset α) (f : α → ℂ) : exp (finset.sum s fun (x : α) => f x) = finset.prod s fun (x : α) => exp (f x) :=
  monoid_hom.map_prod (monoid_hom.mk exp exp_zero exp_add) f s

theorem exp_nat_mul (x : ℂ) (n : ℕ) : exp (↑n * x) = exp x ^ n := sorry

theorem exp_ne_zero (x : ℂ) : exp x ≠ 0 := sorry

theorem exp_neg (x : ℂ) : exp (-x) = (exp x⁻¹) := sorry

theorem exp_sub (x : ℂ) (y : ℂ) : exp (x - y) = exp x / exp y := sorry

@[simp] theorem exp_conj (x : ℂ) : exp (coe_fn conj x) = coe_fn conj (exp x) := sorry

@[simp] theorem of_real_exp_of_real_re (x : ℝ) : ↑(re (exp ↑x)) = exp ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (exp ↑x) = exp ↑x)) (Eq.symm (exp_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (exp (coe_fn conj ↑x) = exp ↑x)) (conj_of_real x))) (Eq.refl (exp ↑x))))

@[simp] theorem of_real_exp (x : ℝ) : ↑(real.exp x) = exp ↑x :=
  of_real_exp_of_real_re x

@[simp] theorem exp_of_real_im (x : ℝ) : im (exp ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (exp ↑x) = 0)) (Eq.symm (of_real_exp_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (exp ↑x)) = 0)) (of_real_im (re (exp ↑x))))) (Eq.refl 0))

theorem exp_of_real_re (x : ℝ) : re (exp ↑x) = real.exp x :=
  rfl

theorem two_sinh (x : ℂ) : bit0 1 * sinh x = exp x - exp (-x) :=
  mul_div_cancel' (exp x - exp (-x)) two_ne_zero'

theorem two_cosh (x : ℂ) : bit0 1 * cosh x = exp x + exp (-x) :=
  mul_div_cancel' (exp x + exp (-x)) two_ne_zero'

@[simp] theorem sinh_zero : sinh 0 = 0 := sorry

@[simp] theorem sinh_neg (x : ℂ) : sinh (-x) = -sinh x := sorry

theorem sinh_add (x : ℂ) (y : ℂ) : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := sorry

@[simp] theorem cosh_zero : cosh 0 = 1 := sorry

@[simp] theorem cosh_neg (x : ℂ) : cosh (-x) = cosh x := sorry

theorem cosh_add (x : ℂ) (y : ℂ) : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := sorry

theorem sinh_sub (x : ℂ) (y : ℂ) : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := sorry

theorem cosh_sub (x : ℂ) (y : ℂ) : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := sorry

theorem sinh_conj (x : ℂ) : sinh (coe_fn conj x) = coe_fn conj (sinh x) := sorry

@[simp] theorem of_real_sinh_of_real_re (x : ℝ) : ↑(re (sinh ↑x)) = sinh ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (sinh ↑x) = sinh ↑x)) (Eq.symm (sinh_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (sinh (coe_fn conj ↑x) = sinh ↑x)) (conj_of_real x))) (Eq.refl (sinh ↑x))))

@[simp] theorem of_real_sinh (x : ℝ) : ↑(real.sinh x) = sinh ↑x :=
  of_real_sinh_of_real_re x

@[simp] theorem sinh_of_real_im (x : ℝ) : im (sinh ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (sinh ↑x) = 0)) (Eq.symm (of_real_sinh_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (sinh ↑x)) = 0)) (of_real_im (re (sinh ↑x))))) (Eq.refl 0))

theorem sinh_of_real_re (x : ℝ) : re (sinh ↑x) = real.sinh x :=
  rfl

theorem cosh_conj (x : ℂ) : cosh (coe_fn conj x) = coe_fn conj (cosh x) := sorry

@[simp] theorem of_real_cosh_of_real_re (x : ℝ) : ↑(re (cosh ↑x)) = cosh ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (cosh ↑x) = cosh ↑x)) (Eq.symm (cosh_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (cosh (coe_fn conj ↑x) = cosh ↑x)) (conj_of_real x))) (Eq.refl (cosh ↑x))))

@[simp] theorem of_real_cosh (x : ℝ) : ↑(real.cosh x) = cosh ↑x :=
  of_real_cosh_of_real_re x

@[simp] theorem cosh_of_real_im (x : ℝ) : im (cosh ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (cosh ↑x) = 0)) (Eq.symm (of_real_cosh_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (cosh ↑x)) = 0)) (of_real_im (re (cosh ↑x))))) (Eq.refl 0))

theorem cosh_of_real_re (x : ℝ) : re (cosh ↑x) = real.cosh x :=
  rfl

theorem tanh_eq_sinh_div_cosh (x : ℂ) : tanh x = sinh x / cosh x :=
  rfl

@[simp] theorem tanh_zero : tanh 0 = 0 := sorry

@[simp] theorem tanh_neg (x : ℂ) : tanh (-x) = -tanh x := sorry

theorem tanh_conj (x : ℂ) : tanh (coe_fn conj x) = coe_fn conj (tanh x) := sorry

@[simp] theorem of_real_tanh_of_real_re (x : ℝ) : ↑(re (tanh ↑x)) = tanh ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (tanh ↑x) = tanh ↑x)) (Eq.symm (tanh_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (tanh (coe_fn conj ↑x) = tanh ↑x)) (conj_of_real x))) (Eq.refl (tanh ↑x))))

@[simp] theorem of_real_tanh (x : ℝ) : ↑(real.tanh x) = tanh ↑x :=
  of_real_tanh_of_real_re x

@[simp] theorem tanh_of_real_im (x : ℝ) : im (tanh ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (tanh ↑x) = 0)) (Eq.symm (of_real_tanh_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (tanh ↑x)) = 0)) (of_real_im (re (tanh ↑x))))) (Eq.refl 0))

theorem tanh_of_real_re (x : ℝ) : re (tanh ↑x) = real.tanh x :=
  rfl

theorem cosh_add_sinh (x : ℂ) : cosh x + sinh x = exp x := sorry

theorem sinh_add_cosh (x : ℂ) : sinh x + cosh x = exp x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sinh x + cosh x = exp x)) (add_comm (sinh x) (cosh x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (cosh x + sinh x = exp x)) (cosh_add_sinh x))) (Eq.refl (exp x)))

theorem cosh_sub_sinh (x : ℂ) : cosh x - sinh x = exp (-x) := sorry

theorem cosh_sq_sub_sinh_sq (x : ℂ) : cosh x ^ bit0 1 - sinh x ^ bit0 1 = 1 := sorry

theorem cosh_square (x : ℂ) : cosh x ^ bit0 1 = sinh x ^ bit0 1 + 1 := sorry

theorem sinh_square (x : ℂ) : sinh x ^ bit0 1 = cosh x ^ bit0 1 - 1 := sorry

theorem cosh_two_mul (x : ℂ) : cosh (bit0 1 * x) = cosh x ^ bit0 1 + sinh x ^ bit0 1 := sorry

theorem sinh_two_mul (x : ℂ) : sinh (bit0 1 * x) = bit0 1 * sinh x * cosh x := sorry

theorem cosh_three_mul (x : ℂ) : cosh (bit1 1 * x) = bit0 (bit0 1) * cosh x ^ bit1 1 - bit1 1 * cosh x := sorry

theorem sinh_three_mul (x : ℂ) : sinh (bit1 1 * x) = bit0 (bit0 1) * sinh x ^ bit1 1 + bit1 1 * sinh x := sorry

@[simp] theorem sin_zero : sin 0 = 0 := sorry

@[simp] theorem sin_neg (x : ℂ) : sin (-x) = -sin x := sorry

theorem two_sin (x : ℂ) : bit0 1 * sin x = (exp (-x * I) - exp (x * I)) * I :=
  mul_div_cancel' ((exp (-x * I) - exp (x * I)) * I) two_ne_zero'

theorem two_cos (x : ℂ) : bit0 1 * cos x = exp (x * I) + exp (-x * I) :=
  mul_div_cancel' (exp (x * I) + exp (-x * I)) two_ne_zero'

theorem sinh_mul_I (x : ℂ) : sinh (x * I) = sin x * I := sorry

theorem cosh_mul_I (x : ℂ) : cosh (x * I) = cos x := sorry

theorem tanh_mul_I (x : ℂ) : tanh (x * I) = tan x * I := sorry

theorem cos_mul_I (x : ℂ) : cos (x * I) = cosh x := sorry

theorem sin_mul_I (x : ℂ) : sin (x * I) = sinh x * I := sorry

theorem tan_mul_I (x : ℂ) : tan (x * I) = tanh x * I := sorry

theorem sin_add (x : ℂ) (y : ℂ) : sin (x + y) = sin x * cos y + cos x * sin y := sorry

@[simp] theorem cos_zero : cos 0 = 1 := sorry

@[simp] theorem cos_neg (x : ℂ) : cos (-x) = cos x := sorry

theorem cos_add (x : ℂ) (y : ℂ) : cos (x + y) = cos x * cos y - sin x * sin y := sorry

theorem sin_sub (x : ℂ) (y : ℂ) : sin (x - y) = sin x * cos y - cos x * sin y := sorry

theorem cos_sub (x : ℂ) (y : ℂ) : cos (x - y) = cos x * cos y + sin x * sin y := sorry

theorem sin_add_mul_I (x : ℂ) (y : ℂ) : sin (x + y * I) = sin x * cosh y + cos x * sinh y * I := sorry

theorem sin_eq (z : ℂ) : sin z = sin ↑(re z) * cosh ↑(im z) + cos ↑(re z) * sinh ↑(im z) * I := sorry

theorem cos_add_mul_I (x : ℂ) (y : ℂ) : cos (x + y * I) = cos x * cosh y - sin x * sinh y * I := sorry

theorem cos_eq (z : ℂ) : cos z = cos ↑(re z) * cosh ↑(im z) - sin ↑(re z) * sinh ↑(im z) * I := sorry

theorem sin_sub_sin (x : ℂ) (y : ℂ) : sin x - sin y = bit0 1 * sin ((x - y) / bit0 1) * cos ((x + y) / bit0 1) := sorry

theorem cos_sub_cos (x : ℂ) (y : ℂ) : cos x - cos y = -bit0 1 * sin ((x + y) / bit0 1) * sin ((x - y) / bit0 1) := sorry

theorem cos_add_cos (x : ℂ) (y : ℂ) : cos x + cos y = bit0 1 * cos ((x + y) / bit0 1) * cos ((x - y) / bit0 1) := sorry

theorem sin_conj (x : ℂ) : sin (coe_fn conj x) = coe_fn conj (sin x) := sorry

@[simp] theorem of_real_sin_of_real_re (x : ℝ) : ↑(re (sin ↑x)) = sin ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (sin ↑x) = sin ↑x)) (Eq.symm (sin_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (sin (coe_fn conj ↑x) = sin ↑x)) (conj_of_real x))) (Eq.refl (sin ↑x))))

@[simp] theorem of_real_sin (x : ℝ) : ↑(real.sin x) = sin ↑x :=
  of_real_sin_of_real_re x

@[simp] theorem sin_of_real_im (x : ℝ) : im (sin ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (sin ↑x) = 0)) (Eq.symm (of_real_sin_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (sin ↑x)) = 0)) (of_real_im (re (sin ↑x))))) (Eq.refl 0))

theorem sin_of_real_re (x : ℝ) : re (sin ↑x) = real.sin x :=
  rfl

theorem cos_conj (x : ℂ) : cos (coe_fn conj x) = coe_fn conj (cos x) := sorry

@[simp] theorem of_real_cos_of_real_re (x : ℝ) : ↑(re (cos ↑x)) = cos ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (cos ↑x) = cos ↑x)) (Eq.symm (cos_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (cos (coe_fn conj ↑x) = cos ↑x)) (conj_of_real x))) (Eq.refl (cos ↑x))))

@[simp] theorem of_real_cos (x : ℝ) : ↑(real.cos x) = cos ↑x :=
  of_real_cos_of_real_re x

@[simp] theorem cos_of_real_im (x : ℝ) : im (cos ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (cos ↑x) = 0)) (Eq.symm (of_real_cos_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (cos ↑x)) = 0)) (of_real_im (re (cos ↑x))))) (Eq.refl 0))

theorem cos_of_real_re (x : ℝ) : re (cos ↑x) = real.cos x :=
  rfl

@[simp] theorem tan_zero : tan 0 = 0 := sorry

theorem tan_eq_sin_div_cos (x : ℂ) : tan x = sin x / cos x :=
  rfl

theorem tan_mul_cos {x : ℂ} (hx : cos x ≠ 0) : tan x * cos x = sin x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tan x * cos x = sin x)) (tan_eq_sin_div_cos x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin x / cos x * cos x = sin x)) (div_mul_cancel (sin x) hx))) (Eq.refl (sin x)))

@[simp] theorem tan_neg (x : ℂ) : tan (-x) = -tan x := sorry

theorem tan_conj (x : ℂ) : tan (coe_fn conj x) = coe_fn conj (tan x) := sorry

@[simp] theorem of_real_tan_of_real_re (x : ℝ) : ↑(re (tan ↑x)) = tan ↑x :=
  iff.mp eq_conj_iff_re
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn conj (tan ↑x) = tan ↑x)) (Eq.symm (tan_conj ↑x))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (tan (coe_fn conj ↑x) = tan ↑x)) (conj_of_real x))) (Eq.refl (tan ↑x))))

@[simp] theorem of_real_tan (x : ℝ) : ↑(real.tan x) = tan ↑x :=
  of_real_tan_of_real_re x

@[simp] theorem tan_of_real_im (x : ℝ) : im (tan ↑x) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (im (tan ↑x) = 0)) (Eq.symm (of_real_tan_of_real_re x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (im ↑(re (tan ↑x)) = 0)) (of_real_im (re (tan ↑x))))) (Eq.refl 0))

theorem tan_of_real_re (x : ℝ) : re (tan ↑x) = real.tan x :=
  rfl

theorem cos_add_sin_I (x : ℂ) : cos x + sin x * I = exp (x * I) := sorry

theorem cos_sub_sin_I (x : ℂ) : cos x - sin x * I = exp (-x * I) := sorry

@[simp] theorem sin_sq_add_cos_sq (x : ℂ) : sin x ^ bit0 1 + cos x ^ bit0 1 = 1 := sorry

@[simp] theorem cos_sq_add_sin_sq (x : ℂ) : cos x ^ bit0 1 + sin x ^ bit0 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cos x ^ bit0 1 + sin x ^ bit0 1 = 1)) (add_comm (cos x ^ bit0 1) (sin x ^ bit0 1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin x ^ bit0 1 + cos x ^ bit0 1 = 1)) (sin_sq_add_cos_sq x))) (Eq.refl 1))

theorem cos_two_mul' (x : ℂ) : cos (bit0 1 * x) = cos x ^ bit0 1 - sin x ^ bit0 1 := sorry

theorem cos_two_mul (x : ℂ) : cos (bit0 1 * x) = bit0 1 * cos x ^ bit0 1 - 1 := sorry

theorem sin_two_mul (x : ℂ) : sin (bit0 1 * x) = bit0 1 * sin x * cos x := sorry

theorem cos_square (x : ℂ) : cos x ^ bit0 1 = 1 / bit0 1 + cos (bit0 1 * x) / bit0 1 := sorry

theorem cos_square' (x : ℂ) : cos x ^ bit0 1 = 1 - sin x ^ bit0 1 := sorry

theorem sin_square (x : ℂ) : sin x ^ bit0 1 = 1 - cos x ^ bit0 1 := sorry

theorem inv_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : 1 + tan x ^ bit0 1⁻¹ = cos x ^ bit0 1 := sorry

theorem tan_sq_div_one_add_tan_sq {x : ℂ} (hx : cos x ≠ 0) : tan x ^ bit0 1 / (1 + tan x ^ bit0 1) = sin x ^ bit0 1 := sorry

theorem cos_three_mul (x : ℂ) : cos (bit1 1 * x) = bit0 (bit0 1) * cos x ^ bit1 1 - bit1 1 * cos x := sorry

theorem sin_three_mul (x : ℂ) : sin (bit1 1 * x) = bit1 1 * sin x - bit0 (bit0 1) * sin x ^ bit1 1 := sorry

theorem exp_mul_I (x : ℂ) : exp (x * I) = cos x + sin x * I :=
  Eq.symm (cos_add_sin_I x)

theorem exp_add_mul_I (x : ℂ) (y : ℂ) : exp (x + y * I) = exp x * (cos y + sin y * I) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp (x + y * I) = exp x * (cos y + sin y * I))) (exp_add x (y * I))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp x * exp (y * I) = exp x * (cos y + sin y * I))) (exp_mul_I y)))
      (Eq.refl (exp x * (cos y + sin y * I))))

theorem exp_eq_exp_re_mul_sin_add_cos (x : ℂ) : exp x = exp ↑(re x) * (cos ↑(im x) + sin ↑(im x) * I) := sorry

/-- De Moivre's formula -/
theorem cos_add_sin_mul_I_pow (n : ℕ) (z : ℂ) : (cos z + sin z * I) ^ n = cos (↑n * z) + sin (↑n * z) * I := sorry

end complex


namespace real


@[simp] theorem exp_zero : exp 0 = 1 := sorry

theorem exp_add (x : ℝ) (y : ℝ) : exp (x + y) = exp x * exp y := sorry

theorem exp_list_sum (l : List ℝ) : exp (list.sum l) = list.prod (list.map exp l) :=
  monoid_hom.map_list_prod (monoid_hom.mk exp exp_zero exp_add) l

theorem exp_multiset_sum (s : multiset ℝ) : exp (multiset.sum s) = multiset.prod (multiset.map exp s) :=
  monoid_hom.map_multiset_prod (monoid_hom.mk exp exp_zero exp_add) s

theorem exp_sum {α : Type u_1} (s : finset α) (f : α → ℝ) : exp (finset.sum s fun (x : α) => f x) = finset.prod s fun (x : α) => exp (f x) :=
  monoid_hom.map_prod (monoid_hom.mk exp exp_zero exp_add) f s

theorem exp_nat_mul (x : ℝ) (n : ℕ) : exp (↑n * x) = exp x ^ n := sorry

theorem exp_ne_zero (x : ℝ) : exp x ≠ 0 := sorry

theorem exp_neg (x : ℝ) : exp (-x) = (exp x⁻¹) := sorry

theorem exp_sub (x : ℝ) (y : ℝ) : exp (x - y) = exp x / exp y := sorry

@[simp] theorem sin_zero : sin 0 = 0 := sorry

@[simp] theorem sin_neg (x : ℝ) : sin (-x) = -sin x := sorry

theorem sin_add (x : ℝ) (y : ℝ) : sin (x + y) = sin x * cos y + cos x * sin y := sorry

@[simp] theorem cos_zero : cos 0 = 1 := sorry

@[simp] theorem cos_neg (x : ℝ) : cos (-x) = cos x := sorry

theorem cos_add (x : ℝ) (y : ℝ) : cos (x + y) = cos x * cos y - sin x * sin y := sorry

theorem sin_sub (x : ℝ) (y : ℝ) : sin (x - y) = sin x * cos y - cos x * sin y := sorry

theorem cos_sub (x : ℝ) (y : ℝ) : cos (x - y) = cos x * cos y + sin x * sin y := sorry

theorem sin_sub_sin (x : ℝ) (y : ℝ) : sin x - sin y = bit0 1 * sin ((x - y) / bit0 1) * cos ((x + y) / bit0 1) := sorry

theorem cos_sub_cos (x : ℝ) (y : ℝ) : cos x - cos y = -bit0 1 * sin ((x + y) / bit0 1) * sin ((x - y) / bit0 1) := sorry

theorem cos_add_cos (x : ℝ) (y : ℝ) : cos x + cos y = bit0 1 * cos ((x + y) / bit0 1) * cos ((x - y) / bit0 1) := sorry

theorem tan_eq_sin_div_cos (x : ℝ) : tan x = sin x / cos x := sorry

theorem tan_mul_cos {x : ℝ} (hx : cos x ≠ 0) : tan x * cos x = sin x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (tan x * cos x = sin x)) (tan_eq_sin_div_cos x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin x / cos x * cos x = sin x)) (div_mul_cancel (sin x) hx))) (Eq.refl (sin x)))

@[simp] theorem tan_zero : tan 0 = 0 := sorry

@[simp] theorem tan_neg (x : ℝ) : tan (-x) = -tan x := sorry

@[simp] theorem sin_sq_add_cos_sq (x : ℝ) : sin x ^ bit0 1 + cos x ^ bit0 1 = 1 := sorry

@[simp] theorem cos_sq_add_sin_sq (x : ℝ) : cos x ^ bit0 1 + sin x ^ bit0 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cos x ^ bit0 1 + sin x ^ bit0 1 = 1)) (add_comm (cos x ^ bit0 1) (sin x ^ bit0 1))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sin x ^ bit0 1 + cos x ^ bit0 1 = 1)) (sin_sq_add_cos_sq x))) (Eq.refl 1))

theorem sin_sq_le_one (x : ℝ) : sin x ^ bit0 1 ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sin x ^ bit0 1 ≤ 1)) (Eq.symm (sin_sq_add_cos_sq x))))
    (le_add_of_nonneg_right (pow_two_nonneg (cos x)))

theorem cos_sq_le_one (x : ℝ) : cos x ^ bit0 1 ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cos x ^ bit0 1 ≤ 1)) (Eq.symm (sin_sq_add_cos_sq x))))
    (le_add_of_nonneg_left (pow_two_nonneg (sin x)))

theorem abs_sin_le_one (x : ℝ) : abs (sin x) ≤ 1 := sorry

theorem abs_cos_le_one (x : ℝ) : abs (cos x) ≤ 1 := sorry

theorem sin_le_one (x : ℝ) : sin x ≤ 1 :=
  and.right (iff.mp abs_le (abs_sin_le_one x))

theorem cos_le_one (x : ℝ) : cos x ≤ 1 :=
  and.right (iff.mp abs_le (abs_cos_le_one x))

theorem neg_one_le_sin (x : ℝ) : -1 ≤ sin x :=
  and.left (iff.mp abs_le (abs_sin_le_one x))

theorem neg_one_le_cos (x : ℝ) : -1 ≤ cos x :=
  and.left (iff.mp abs_le (abs_cos_le_one x))

theorem cos_two_mul (x : ℝ) : cos (bit0 1 * x) = bit0 1 * cos x ^ bit0 1 - 1 := sorry

theorem cos_two_mul' (x : ℝ) : cos (bit0 1 * x) = cos x ^ bit0 1 - sin x ^ bit0 1 := sorry

theorem sin_two_mul (x : ℝ) : sin (bit0 1 * x) = bit0 1 * sin x * cos x := sorry

theorem cos_square (x : ℝ) : cos x ^ bit0 1 = 1 / bit0 1 + cos (bit0 1 * x) / bit0 1 := sorry

theorem cos_square' (x : ℝ) : cos x ^ bit0 1 = 1 - sin x ^ bit0 1 := sorry

theorem sin_square (x : ℝ) : sin x ^ bit0 1 = 1 - cos x ^ bit0 1 :=
  iff.mpr eq_sub_iff_add_eq (sin_sq_add_cos_sq x)

theorem inv_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : 1 + tan x ^ bit0 1⁻¹ = cos x ^ bit0 1 := sorry

theorem tan_sq_div_one_add_tan_sq {x : ℝ} (hx : cos x ≠ 0) : tan x ^ bit0 1 / (1 + tan x ^ bit0 1) = sin x ^ bit0 1 := sorry

theorem inv_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : sqrt (1 + tan x ^ bit0 1)⁻¹ = cos x := sorry

theorem tan_div_sqrt_one_add_tan_sq {x : ℝ} (hx : 0 < cos x) : tan x / sqrt (1 + tan x ^ bit0 1) = sin x := sorry

theorem cos_three_mul (x : ℝ) : cos (bit1 1 * x) = bit0 (bit0 1) * cos x ^ bit1 1 - bit1 1 * cos x := sorry

theorem sin_three_mul (x : ℝ) : sin (bit1 1 * x) = bit1 1 * sin x - bit0 (bit0 1) * sin x ^ bit1 1 := sorry

/-- The definition of `sinh` in terms of `exp`. -/
theorem sinh_eq (x : ℝ) : sinh x = (exp x - exp (-x)) / bit0 1 := sorry

@[simp] theorem sinh_zero : sinh 0 = 0 := sorry

@[simp] theorem sinh_neg (x : ℝ) : sinh (-x) = -sinh x := sorry

theorem sinh_add (x : ℝ) (y : ℝ) : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := sorry

/-- The definition of `cosh` in terms of `exp`. -/
theorem cosh_eq (x : ℝ) : cosh x = (exp x + exp (-x)) / bit0 1 := sorry

@[simp] theorem cosh_zero : cosh 0 = 1 := sorry

@[simp] theorem cosh_neg (x : ℝ) : cosh (-x) = cosh x := sorry

theorem cosh_add (x : ℝ) (y : ℝ) : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := sorry

theorem sinh_sub (x : ℝ) (y : ℝ) : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := sorry

theorem cosh_sub (x : ℝ) (y : ℝ) : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := sorry

theorem tanh_eq_sinh_div_cosh (x : ℝ) : tanh x = sinh x / cosh x := sorry

@[simp] theorem tanh_zero : tanh 0 = 0 := sorry

@[simp] theorem tanh_neg (x : ℝ) : tanh (-x) = -tanh x := sorry

theorem cosh_add_sinh (x : ℝ) : cosh x + sinh x = exp x := sorry

theorem sinh_add_cosh (x : ℝ) : sinh x + cosh x = exp x := sorry

theorem cosh_sq_sub_sinh_sq (x : ℝ) : cosh x ^ bit0 1 - sinh x ^ bit0 1 = 1 := sorry

theorem cosh_square (x : ℝ) : cosh x ^ bit0 1 = sinh x ^ bit0 1 + 1 := sorry

theorem sinh_square (x : ℝ) : sinh x ^ bit0 1 = cosh x ^ bit0 1 - 1 := sorry

theorem cosh_two_mul (x : ℝ) : cosh (bit0 1 * x) = cosh x ^ bit0 1 + sinh x ^ bit0 1 := sorry

theorem sinh_two_mul (x : ℝ) : sinh (bit0 1 * x) = bit0 1 * sinh x * cosh x := sorry

theorem cosh_three_mul (x : ℝ) : cosh (bit1 1 * x) = bit0 (bit0 1) * cosh x ^ bit1 1 - bit1 1 * cosh x := sorry

theorem sinh_three_mul (x : ℝ) : sinh (bit1 1 * x) = bit0 (bit0 1) * sinh x ^ bit1 1 + bit1 1 * sinh x := sorry

/- TODO make this private and prove ∀ x -/

theorem add_one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x + 1 ≤ exp x := sorry

theorem one_le_exp {x : ℝ} (hx : 0 ≤ x) : 1 ≤ exp x := sorry

theorem exp_pos (x : ℝ) : 0 < exp x := sorry

@[simp] theorem abs_exp (x : ℝ) : abs (exp x) = exp x :=
  abs_of_pos (exp_pos x)

theorem exp_strict_mono : strict_mono exp := sorry

theorem exp_monotone {x : ℝ} {y : ℝ} : x ≤ y → exp x ≤ exp y :=
  strict_mono.monotone exp_strict_mono

@[simp] theorem exp_lt_exp {x : ℝ} {y : ℝ} : exp x < exp y ↔ x < y :=
  strict_mono.lt_iff_lt exp_strict_mono

@[simp] theorem exp_le_exp {x : ℝ} {y : ℝ} : exp x ≤ exp y ↔ x ≤ y :=
  strict_mono.le_iff_le exp_strict_mono

theorem exp_injective : function.injective exp :=
  strict_mono.injective exp_strict_mono

@[simp] theorem exp_eq_exp {x : ℝ} {y : ℝ} : exp x = exp y ↔ x = y :=
  function.injective.eq_iff exp_injective

@[simp] theorem exp_eq_one_iff (x : ℝ) : exp x = 1 ↔ x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp x = 1 ↔ x = 0)) (Eq.symm exp_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp x = exp 0 ↔ x = 0)) (propext (function.injective.eq_iff exp_injective))))
      (iff.refl (x = 0)))

@[simp] theorem one_lt_exp_iff {x : ℝ} : 1 < exp x ↔ 0 < x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < exp x ↔ 0 < x)) (Eq.symm exp_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp 0 < exp x ↔ 0 < x)) (propext exp_lt_exp))) (iff.refl (0 < x)))

@[simp] theorem exp_lt_one_iff {x : ℝ} : exp x < 1 ↔ x < 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp x < 1 ↔ x < 0)) (Eq.symm exp_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp x < exp 0 ↔ x < 0)) (propext exp_lt_exp))) (iff.refl (x < 0)))

@[simp] theorem exp_le_one_iff {x : ℝ} : exp x ≤ 1 ↔ x ≤ 0 :=
  exp_zero ▸ exp_le_exp

@[simp] theorem one_le_exp_iff {x : ℝ} : 1 ≤ exp x ↔ 0 ≤ x :=
  exp_zero ▸ exp_le_exp

/-- `real.cosh` is always positive -/
theorem cosh_pos (x : ℝ) : 0 < cosh x :=
  Eq.symm (cosh_eq x) ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

end real


namespace complex


theorem sum_div_factorial_le {α : Type u_1} [linear_ordered_field α] (n : ℕ) (j : ℕ) (hn : 0 < n) : (finset.sum (finset.filter (fun (k : ℕ) => n ≤ k) (finset.range j)) fun (m : ℕ) => 1 / ↑(nat.factorial m)) ≤
  ↑(Nat.succ n) * (↑(nat.factorial n) * ↑n⁻¹) := sorry

theorem exp_bound {x : ℂ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) : abs (exp x - finset.sum (finset.range n) fun (m : ℕ) => x ^ m / ↑(nat.factorial m)) ≤
  abs x ^ n * (↑(Nat.succ n) * (↑(nat.factorial n) * ↑n⁻¹)) := sorry

theorem abs_exp_sub_one_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1) ≤ bit0 1 * abs x := sorry

theorem abs_exp_sub_one_sub_id_le {x : ℂ} (hx : abs x ≤ 1) : abs (exp x - 1 - x) ≤ abs x ^ bit0 1 := sorry

end complex


namespace real


theorem exp_bound {x : ℝ} (hx : abs x ≤ 1) {n : ℕ} (hn : 0 < n) : abs (exp x - finset.sum (finset.range n) fun (m : ℕ) => x ^ m / ↑(nat.factorial m)) ≤
  abs x ^ n * (↑(Nat.succ n) / (↑(nat.factorial n) * ↑n)) := sorry

/-- A finite initial segment of the exponential series, followed by an arbitrary tail.
For fixed `n` this is just a linear map wrt `r`, and each map is a simple linear function
of the previous (see `exp_near_succ`), with `exp_near n x r ⟶ exp x` as `n ⟶ ∞`,
for any `r`. -/
def exp_near (n : ℕ) (x : ℝ) (r : ℝ) : ℝ :=
  (finset.sum (finset.range n) fun (m : ℕ) => x ^ m / ↑(nat.factorial m)) + x ^ n / ↑(nat.factorial n) * r

@[simp] theorem exp_near_zero (x : ℝ) (r : ℝ) : exp_near 0 x r = r := sorry

@[simp] theorem exp_near_succ (n : ℕ) (x : ℝ) (r : ℝ) : exp_near (n + 1) x r = exp_near n x (1 + x / (↑n + 1) * r) := sorry

theorem exp_near_sub (n : ℕ) (x : ℝ) (r₁ : ℝ) (r₂ : ℝ) : exp_near n x r₁ - exp_near n x r₂ = x ^ n / ↑(nat.factorial n) * (r₁ - r₂) := sorry

theorem exp_approx_end (n : ℕ) (m : ℕ) (x : ℝ) (e₁ : n + 1 = m) (h : abs x ≤ 1) : abs (exp x - exp_near m x 0) ≤ abs x ^ m / ↑(nat.factorial m) * ((↑m + 1) / ↑m) := sorry

theorem exp_approx_succ {n : ℕ} {x : ℝ} {a₁ : ℝ} {b₁ : ℝ} (m : ℕ) (e₁ : n + 1 = m) (a₂ : ℝ) (b₂ : ℝ) (e : abs (1 + x / ↑m * a₂ - a₁) ≤ b₁ - abs x / ↑m * b₂) (h : abs (exp x - exp_near m x a₂) ≤ abs x ^ m / ↑(nat.factorial m) * b₂) : abs (exp x - exp_near n x a₁) ≤ abs x ^ n / ↑(nat.factorial n) * b₁ := sorry

theorem exp_approx_end' {n : ℕ} {x : ℝ} {a : ℝ} {b : ℝ} (m : ℕ) (e₁ : n + 1 = m) (rm : ℝ) (er : ↑m = rm) (h : abs x ≤ 1) (e : abs (1 - a) ≤ b - abs x / rm * ((rm + 1) / rm)) : abs (exp x - exp_near n x a) ≤ abs x ^ n / ↑(nat.factorial n) * b := sorry

theorem exp_1_approx_succ_eq {n : ℕ} {a₁ : ℝ} {b₁ : ℝ} {m : ℕ} (en : n + 1 = m) {rm : ℝ} (er : ↑m = rm) (h : abs (exp 1 - exp_near m 1 ((a₁ - 1) * rm)) ≤ abs 1 ^ m / ↑(nat.factorial m) * (b₁ * rm)) : abs (exp 1 - exp_near n 1 a₁) ≤ abs 1 ^ n / ↑(nat.factorial n) * b₁ := sorry

theorem exp_approx_start (x : ℝ) (a : ℝ) (b : ℝ) (h : abs (exp x - exp_near 0 x a) ≤ abs x ^ 0 / ↑(nat.factorial 0) * b) : abs (exp x - a) ≤ b := sorry

theorem cos_bound {x : ℝ} (hx : abs x ≤ 1) : abs (cos x - (1 - x ^ bit0 1 / bit0 1)) ≤
  abs x ^ bit0 (bit0 1) * (bit1 (bit0 1) / bit0 (bit0 (bit0 (bit0 (bit0 (bit1 1)))))) := sorry

theorem sin_bound {x : ℝ} (hx : abs x ≤ 1) : abs (sin x - (x - x ^ bit1 1 / bit0 (bit1 1))) ≤
  abs x ^ bit0 (bit0 1) * (bit1 (bit0 1) / bit0 (bit0 (bit0 (bit0 (bit0 (bit1 1)))))) := sorry

theorem cos_pos_of_le_one {x : ℝ} (hx : abs x ≤ 1) : 0 < cos x := sorry

theorem sin_pos_of_pos_of_le_one {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1) : 0 < sin x := sorry

theorem sin_pos_of_pos_of_le_two {x : ℝ} (hx0 : 0 < x) (hx : x ≤ bit0 1) : 0 < sin x := sorry

theorem cos_one_le : cos 1 ≤ bit0 1 / bit1 1 := sorry

theorem cos_one_pos : 0 < cos 1 := sorry

theorem cos_two_neg : cos (bit0 1) < 0 := sorry

end real


namespace complex


theorem abs_cos_add_sin_mul_I (x : ℝ) : abs (cos ↑x + sin ↑x * I) = 1 := sorry

theorem abs_exp_eq_iff_re_eq {x : ℂ} {y : ℂ} : abs (exp x) = abs (exp y) ↔ re x = re y := sorry

@[simp] theorem abs_exp_of_real (x : ℝ) : abs (exp ↑x) = real.exp x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (abs (exp ↑x) = real.exp x)) (Eq.symm (of_real_exp x))))
    (abs_of_nonneg (le_of_lt (real.exp_pos x)))

