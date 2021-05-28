/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.special_functions.trigonometric
import Mathlib.analysis.calculus.extend_deriv
import PostPort

universes u_1 

namespace Mathlib

/-!
# Power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ennreal`

We construct the power functions `x ^ y` where
* `x` and `y` are complex numbers,
* or `x` and `y` are real numbers,
* or `x` is a nonnegative real number and `y` is a real number;
* or `x` is a number from `[0, +∞]` (a.k.a. `ennreal`) and `y` is a real number.

We also prove basic properties of these functions.
-/

namespace complex


/-- The complex power function `x^y`, given by `x^y = exp(y log x)` (where `log` is the principal
determination of the logarithm), unless `x = 0` where one sets `0^0 = 1` and `0^y = 0` for
`y ≠ 0`. -/
def cpow (x : ℂ) (y : ℂ) : ℂ :=
  ite (x = 0) (ite (y = 0) 1 0) (exp (log x * y))

protected instance has_pow : has_pow ℂ ℂ :=
  has_pow.mk cpow

@[simp] theorem cpow_eq_pow (x : ℂ) (y : ℂ) : cpow x y = x ^ y :=
  rfl

theorem cpow_def (x : ℂ) (y : ℂ) : x ^ y = ite (x = 0) (ite (y = 0) 1 0) (exp (log x * y)) :=
  rfl

@[simp] theorem cpow_zero (x : ℂ) : x ^ 0 = 1 := sorry

@[simp] theorem cpow_eq_zero_iff (x : ℂ) (y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := sorry

@[simp] theorem zero_cpow {x : ℂ} (h : x ≠ 0) : 0 ^ x = 0 := sorry

@[simp] theorem cpow_one (x : ℂ) : x ^ 1 = x := sorry

@[simp] theorem one_cpow (x : ℂ) : 1 ^ x = 1 := sorry

theorem cpow_add {x : ℂ} (y : ℂ) (z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := sorry

theorem cpow_mul {x : ℂ} {y : ℂ} (z : ℂ) (h₁ : -real.pi < im (log x * y)) (h₂ : im (log x * y) ≤ real.pi) : x ^ (y * z) = (x ^ y) ^ z := sorry

theorem cpow_neg (x : ℂ) (y : ℂ) : x ^ (-y) = (x ^ y⁻¹) := sorry

theorem cpow_neg_one (x : ℂ) : x ^ (-1) = (x⁻¹) := sorry

@[simp] theorem cpow_nat_cast (x : ℂ) (n : ℕ) : x ^ ↑n = x ^ n := sorry

@[simp] theorem cpow_int_cast (x : ℂ) (n : ℤ) : x ^ ↑n = x ^ n := sorry

theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : 0 < n) : (x ^ (↑n⁻¹)) ^ n = x := sorry

end complex


namespace real


/-- The real power function `x^y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp(y log x)`. For `x = 0`, one sets `0^0=1` and `0^y=0` for `y ≠ 0`.
For `x < 0`, the definition is somewhat arbitary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (πy)`. -/
def rpow (x : ℝ) (y : ℝ) : ℝ :=
  complex.re (↑x ^ ↑y)

protected instance has_pow : has_pow ℝ ℝ :=
  has_pow.mk rpow

@[simp] theorem rpow_eq_pow (x : ℝ) (y : ℝ) : rpow x y = x ^ y :=
  rfl

theorem rpow_def (x : ℝ) (y : ℝ) : x ^ y = complex.re (↑x ^ ↑y) :=
  rfl

theorem rpow_def_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ y = ite (x = 0) (ite (y = 0) 1 0) (exp (log x * y)) := sorry

theorem rpow_def_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : x ^ y = exp (log x * y) := sorry

theorem exp_mul (x : ℝ) (y : ℝ) : exp (x * y) = exp x ^ y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (exp (x * y) = exp x ^ y)) (rpow_def_of_pos (exp_pos x) y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (exp (x * y) = exp (log (exp x) * y))) (log_exp x))) (Eq.refl (exp (x * y))))

theorem rpow_eq_zero_iff_of_nonneg {x : ℝ} {y : ℝ} (hx : 0 ≤ x) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := sorry

theorem rpow_def_of_neg {x : ℝ} (hx : x < 0) (y : ℝ) : x ^ y = exp (log x * y) * cos (y * pi) := sorry

theorem rpow_def_of_nonpos {x : ℝ} (hx : x ≤ 0) (y : ℝ) : x ^ y = ite (x = 0) (ite (y = 0) 1 0) (exp (log x * y) * cos (y * pi)) := sorry

theorem rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < x ^ y)) (rpow_def_of_pos hx y))) (exp_pos (log x * y))

@[simp] theorem rpow_zero (x : ℝ) : x ^ 0 = 1 := sorry

@[simp] theorem zero_rpow {x : ℝ} (h : x ≠ 0) : 0 ^ x = 0 := sorry

@[simp] theorem rpow_one (x : ℝ) : x ^ 1 = x := sorry

@[simp] theorem one_rpow (x : ℝ) : 1 ^ x = 1 := sorry

theorem zero_rpow_le_one (x : ℝ) : 0 ^ x ≤ 1 := sorry

theorem zero_rpow_nonneg (x : ℝ) : 0 ≤ 0 ^ x := sorry

theorem rpow_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y := sorry

theorem abs_rpow_le_abs_rpow (x : ℝ) (y : ℝ) : abs (x ^ y) ≤ abs x ^ y := sorry

end real


namespace complex


theorem of_real_cpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : ↑(x ^ y) = ↑x ^ ↑y := sorry

@[simp] theorem abs_cpow_real (x : ℂ) (y : ℝ) : abs (x ^ ↑y) = abs x ^ y := sorry

@[simp] theorem abs_cpow_inv_nat (x : ℂ) (n : ℕ) : abs (x ^ (↑n⁻¹)) = abs x ^ (↑n⁻¹) := sorry

end complex


namespace real


theorem rpow_add {x : ℝ} (hx : 0 < x) (y : ℝ) (z : ℝ) : x ^ (y + z) = x ^ y * x ^ z := sorry

theorem rpow_add' {x : ℝ} (hx : 0 ≤ x) {y : ℝ} {z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := sorry

/-- For `0 ≤ x`, the only problematic case in the equality `x ^ y * x ^ z = x ^ (y + z)` is for
`x = 0` and `y + z = 0`, where the right hand side is `1` while the left hand side can vanish.
The inequality is always true, though, and given in this lemma. -/
theorem le_rpow_add {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℝ) : x ^ y * x ^ z ≤ x ^ (y + z) := sorry

theorem rpow_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := sorry

theorem rpow_neg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x ^ (-y) = (x ^ y⁻¹) := sorry

theorem rpow_sub {x : ℝ} (hx : 0 < x) (y : ℝ) (z : ℝ) : x ^ (y - z) = x ^ y / x ^ z := sorry

theorem rpow_sub' {x : ℝ} (hx : 0 ≤ x) {y : ℝ} {z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := sorry

@[simp] theorem rpow_nat_cast (x : ℝ) (n : ℕ) : x ^ ↑n = x ^ n := sorry

@[simp] theorem rpow_int_cast (x : ℝ) (n : ℤ) : x ^ ↑n = x ^ n := sorry

theorem rpow_neg_one (x : ℝ) : x ^ (-1) = (x⁻¹) := sorry

theorem mul_rpow {x : ℝ} {y : ℝ} {z : ℝ} (h : 0 ≤ x) (h₁ : 0 ≤ y) : (x * y) ^ z = x ^ z * y ^ z := sorry

theorem inv_rpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : x⁻¹ ^ y = (x ^ y⁻¹) := sorry

theorem div_rpow {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z := sorry

theorem log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x := sorry

theorem rpow_lt_rpow {x : ℝ} {y : ℝ} {z : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hz : 0 < z) : x ^ z < y ^ z := sorry

theorem rpow_le_rpow {x : ℝ} {y : ℝ} {z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := sorry

theorem rpow_lt_rpow_iff {x : ℝ} {y : ℝ} {z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  { mp := lt_imp_lt_of_le_imp_le fun (h : y ≤ x) => rpow_le_rpow hy h (le_of_lt hz),
    mpr := fun (h : x < y) => rpow_lt_rpow hx h hz }

theorem rpow_le_rpow_iff {x : ℝ} {y : ℝ} {z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  iff.mpr le_iff_le_iff_lt_iff_lt (rpow_lt_rpow_iff hy hx hz)

theorem rpow_lt_rpow_of_exponent_lt {x : ℝ} {y : ℝ} {z : ℝ} (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z := sorry

theorem rpow_le_rpow_of_exponent_le {x : ℝ} {y : ℝ} {z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := sorry

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ} {y : ℝ} {z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := sorry

theorem rpow_le_rpow_of_exponent_ge {x : ℝ} {y : ℝ} {z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := sorry

theorem rpow_lt_one {x : ℝ} {z : ℝ} (hx1 : 0 ≤ x) (hx2 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ^ z < 1)) (Eq.symm (one_rpow z)))) (rpow_lt_rpow hx1 hx2 hz)

theorem rpow_le_one {x : ℝ} {z : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ^ z ≤ 1)) (Eq.symm (one_rpow z)))) (rpow_le_rpow hx1 hx2 hz)

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := sorry

theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 := sorry

theorem one_lt_rpow {x : ℝ} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < x ^ z)) (Eq.symm (one_rpow z)))) (rpow_lt_rpow zero_le_one hx hz)

theorem one_le_rpow {x : ℝ} {z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ x ^ z)) (Eq.symm (one_rpow z)))) (rpow_le_rpow zero_le_one hx hz)

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z := sorry

theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) : 1 ≤ x ^ z := sorry

theorem rpow_lt_one_iff_of_pos {x : ℝ} {y : ℝ} (hx : 0 < x) : x ^ y < 1 ↔ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := sorry

theorem rpow_lt_one_iff {x : ℝ} {y : ℝ} (hx : 0 ≤ x) : x ^ y < 1 ↔ x = 0 ∧ y ≠ 0 ∨ 1 < x ∧ y < 0 ∨ x < 1 ∧ 0 < y := sorry

theorem one_lt_rpow_iff_of_pos {x : ℝ} {y : ℝ} (hx : 0 < x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ x < 1 ∧ y < 0 := sorry

theorem one_lt_rpow_iff {x : ℝ} {y : ℝ} (hx : 0 ≤ x) : 1 < x ^ y ↔ 1 < x ∧ 0 < y ∨ 0 < x ∧ x < 1 ∧ y < 0 := sorry

theorem rpow_le_one_iff_of_pos {x : ℝ} {y : ℝ} (hx : 0 < x) : x ^ y ≤ 1 ↔ 1 ≤ x ∧ y ≤ 0 ∨ x ≤ 1 ∧ 0 ≤ y := sorry

theorem pow_nat_rpow_nat_inv {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) : (x ^ n) ^ (↑n⁻¹) = x := sorry

theorem rpow_nat_inv_pow_nat {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) : (x ^ (↑n⁻¹)) ^ n = x := sorry

theorem continuous_rpow_aux1 : continuous fun (p : Subtype fun (p : ℝ × ℝ) => 0 < prod.fst p) => prod.fst (subtype.val p) ^ prod.snd (subtype.val p) := sorry

theorem continuous_rpow_aux2 : continuous fun (p : Subtype fun (p : ℝ × ℝ) => prod.fst p < 0) => prod.fst (subtype.val p) ^ prod.snd (subtype.val p) := sorry

theorem continuous_at_rpow_of_ne_zero {x : ℝ} (hx : x ≠ 0) (y : ℝ) : continuous_at (fun (p : ℝ × ℝ) => prod.fst p ^ prod.snd p) (x, y) := sorry

theorem continuous_rpow_aux3 : continuous fun (p : Subtype fun (p : ℝ × ℝ) => 0 < prod.snd p) => prod.fst (subtype.val p) ^ prod.snd (subtype.val p) := sorry

theorem continuous_at_rpow_of_pos {y : ℝ} (hy : 0 < y) (x : ℝ) : continuous_at (fun (p : ℝ × ℝ) => prod.fst p ^ prod.snd p) (x, y) := sorry

theorem continuous_at_rpow {x : ℝ} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) : continuous_at (fun (p : ℝ × ℝ) => prod.fst p ^ prod.snd p) (x, y) :=
  or.dcases_on h (fun (h : x ≠ 0) => continuous_at_rpow_of_ne_zero h y) fun (h : 0 < y) => continuous_at_rpow_of_pos h x

/--
`real.rpow` is continuous at all points except for the lower half of the y-axis.
In other words, the function `λp:ℝ×ℝ, p.1^p.2` is continuous at `(x, y)` if `x ≠ 0` or `y > 0`.

Multiple forms of the claim is provided in the current section.
-/
theorem continuous_rpow {α : Type u_1} [topological_space α] {f : α → ℝ} {g : α → ℝ} (h : ∀ (a : α), f a ≠ 0 ∨ 0 < g a) (hf : continuous f) (hg : continuous g) : continuous fun (a : α) => f a ^ g a := sorry

theorem continuous_rpow_of_ne_zero {α : Type u_1} [topological_space α] {f : α → ℝ} {g : α → ℝ} (h : ∀ (a : α), f a ≠ 0) (hf : continuous f) (hg : continuous g) : continuous fun (a : α) => f a ^ g a :=
  continuous_rpow (fun (a : α) => Or.inl (h a)) hf hg

theorem continuous_rpow_of_pos {α : Type u_1} [topological_space α] {f : α → ℝ} {g : α → ℝ} (h : ∀ (a : α), 0 < g a) (hf : continuous f) (hg : continuous g) : continuous fun (a : α) => f a ^ g a :=
  continuous_rpow (fun (a : α) => Or.inr (h a)) hf hg

theorem has_deriv_at_rpow_of_pos {x : ℝ} (h : 0 < x) (p : ℝ) : has_deriv_at (fun (x : ℝ) => x ^ p) (p * x ^ (p - 1)) x := sorry

theorem has_deriv_at_rpow_of_neg {x : ℝ} (h : x < 0) (p : ℝ) : has_deriv_at (fun (x : ℝ) => x ^ p) (p * x ^ (p - 1)) x := sorry

theorem has_deriv_at_rpow {x : ℝ} (h : x ≠ 0) (p : ℝ) : has_deriv_at (fun (x : ℝ) => x ^ p) (p * x ^ (p - 1)) x :=
  or.dcases_on (lt_trichotomy x 0) (fun (H : x < 0) => has_deriv_at_rpow_of_neg H p)
    fun (h_1 : x = 0 ∨ 0 < x) =>
      or.dcases_on h_1 (fun (H : x = 0) => false.elim (h H)) fun (H : 0 < x) => has_deriv_at_rpow_of_pos H p

theorem has_deriv_at_rpow_zero_of_one_le {p : ℝ} (h : 1 ≤ p) : has_deriv_at (fun (x : ℝ) => x ^ p) (p * 0 ^ (p - 1)) 0 := sorry

theorem has_deriv_at_rpow_of_one_le (x : ℝ) {p : ℝ} (h : 1 ≤ p) : has_deriv_at (fun (x : ℝ) => x ^ p) (p * x ^ (p - 1)) x := sorry

theorem sqrt_eq_rpow : sqrt = fun (x : ℝ) => x ^ (1 / bit0 1) := sorry

end real


theorem real.measurable_rpow : measurable fun (p : ℝ × ℝ) => prod.fst p ^ prod.snd p := sorry

theorem measurable.rpow {α : Type u_1} [measurable_space α] {f : α → ℝ} {g : α → ℝ} (hf : measurable f) (hg : measurable g) : measurable fun (a : α) => f a ^ g a :=
  id (measurable.comp real.measurable_rpow (measurable.prod hf hg))

theorem real.measurable_rpow_const {y : ℝ} : measurable fun (x : ℝ) => x ^ y :=
  id (measurable.comp real.measurable_rpow (measurable.prod measurable_id (id measurable_const)))

theorem measurable.rpow_const {α : Type u_1} [measurable_space α] {f : α → ℝ} (hf : measurable f) {y : ℝ} : measurable fun (a : α) => f a ^ y :=
  measurable.rpow hf measurable_const

/- Differentiability statements for the power of a function, when the function does not vanish
and the exponent is arbitrary-/

theorem has_deriv_within_at.rpow {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} {s : set ℝ} (p : ℝ) (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) : has_deriv_within_at (fun (y : ℝ) => f y ^ p) (f' * p * f x ^ (p - 1)) s x := sorry

theorem has_deriv_at.rpow {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} (p : ℝ) (hf : has_deriv_at f f' x) (hx : f x ≠ 0) : has_deriv_at (fun (y : ℝ) => f y ^ p) (f' * p * f x ^ (p - 1)) x := sorry

theorem differentiable_within_at.rpow {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (p : ℝ) (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) : differentiable_within_at ℝ (fun (x : ℝ) => f x ^ p) s x :=
  has_deriv_within_at.differentiable_within_at
    (has_deriv_within_at.rpow p (differentiable_within_at.has_deriv_within_at hf) hx)

@[simp] theorem differentiable_at.rpow {f : ℝ → ℝ} {x : ℝ} (p : ℝ) (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) : differentiable_at ℝ (fun (x : ℝ) => f x ^ p) x :=
  has_deriv_at.differentiable_at (has_deriv_at.rpow p (differentiable_at.has_deriv_at hf) hx)

theorem differentiable_on.rpow {f : ℝ → ℝ} {s : set ℝ} (p : ℝ) (hf : differentiable_on ℝ f s) (hx : ∀ (x : ℝ), x ∈ s → f x ≠ 0) : differentiable_on ℝ (fun (x : ℝ) => f x ^ p) s :=
  fun (x : ℝ) (h : x ∈ s) => differentiable_within_at.rpow p (hf x h) (hx x h)

@[simp] theorem differentiable.rpow {f : ℝ → ℝ} (p : ℝ) (hf : differentiable ℝ f) (hx : ∀ (x : ℝ), f x ≠ 0) : differentiable ℝ fun (x : ℝ) => f x ^ p :=
  fun (x : ℝ) => differentiable_at.rpow p (hf x) (hx x)

theorem deriv_within_rpow {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (p : ℝ) (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => f x ^ p) s x = deriv_within f s x * p * f x ^ (p - 1) :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.rpow p (differentiable_within_at.has_deriv_within_at hf) hx) hxs

@[simp] theorem deriv_rpow {f : ℝ → ℝ} {x : ℝ} (p : ℝ) (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) : deriv (fun (x : ℝ) => f x ^ p) x = deriv f x * p * f x ^ (p - 1) :=
  has_deriv_at.deriv (has_deriv_at.rpow p (differentiable_at.has_deriv_at hf) hx)

/- Differentiability statements for the power of a function, when the function may vanish
but the exponent is at least one. -/

theorem has_deriv_within_at.rpow_of_one_le {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} {s : set ℝ} {p : ℝ} (hf : has_deriv_within_at f f' s x) (hp : 1 ≤ p) : has_deriv_within_at (fun (y : ℝ) => f y ^ p) (f' * p * f x ^ (p - 1)) s x := sorry

theorem has_deriv_at.rpow_of_one_le {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} {p : ℝ} (hf : has_deriv_at f f' x) (hp : 1 ≤ p) : has_deriv_at (fun (y : ℝ) => f y ^ p) (f' * p * f x ^ (p - 1)) x := sorry

theorem differentiable_within_at.rpow_of_one_le {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} {p : ℝ} (hf : differentiable_within_at ℝ f s x) (hp : 1 ≤ p) : differentiable_within_at ℝ (fun (x : ℝ) => f x ^ p) s x :=
  has_deriv_within_at.differentiable_within_at
    (has_deriv_within_at.rpow_of_one_le (differentiable_within_at.has_deriv_within_at hf) hp)

@[simp] theorem differentiable_at.rpow_of_one_le {f : ℝ → ℝ} {x : ℝ} {p : ℝ} (hf : differentiable_at ℝ f x) (hp : 1 ≤ p) : differentiable_at ℝ (fun (x : ℝ) => f x ^ p) x :=
  has_deriv_at.differentiable_at (has_deriv_at.rpow_of_one_le (differentiable_at.has_deriv_at hf) hp)

theorem differentiable_on.rpow_of_one_le {f : ℝ → ℝ} {s : set ℝ} {p : ℝ} (hf : differentiable_on ℝ f s) (hp : 1 ≤ p) : differentiable_on ℝ (fun (x : ℝ) => f x ^ p) s :=
  fun (x : ℝ) (h : x ∈ s) => differentiable_within_at.rpow_of_one_le (hf x h) hp

@[simp] theorem differentiable.rpow_of_one_le {f : ℝ → ℝ} {p : ℝ} (hf : differentiable ℝ f) (hp : 1 ≤ p) : differentiable ℝ fun (x : ℝ) => f x ^ p :=
  fun (x : ℝ) => differentiable_at.rpow_of_one_le (hf x) hp

theorem deriv_within_rpow_of_one_le {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} {p : ℝ} (hf : differentiable_within_at ℝ f s x) (hp : 1 ≤ p) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => f x ^ p) s x = deriv_within f s x * p * f x ^ (p - 1) :=
  has_deriv_within_at.deriv_within
    (has_deriv_within_at.rpow_of_one_le (differentiable_within_at.has_deriv_within_at hf) hp) hxs

@[simp] theorem deriv_rpow_of_one_le {f : ℝ → ℝ} {x : ℝ} {p : ℝ} (hf : differentiable_at ℝ f x) (hp : 1 ≤ p) : deriv (fun (x : ℝ) => f x ^ p) x = deriv f x * p * f x ^ (p - 1) :=
  has_deriv_at.deriv (has_deriv_at.rpow_of_one_le (differentiable_at.has_deriv_at hf) hp)

/- Differentiability statements for the square root of a function, when the function does not
vanish -/

theorem has_deriv_within_at.sqrt {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} {s : set ℝ} (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) : has_deriv_within_at (fun (y : ℝ) => real.sqrt (f y)) (f' / (bit0 1 * real.sqrt (f x))) s x := sorry

theorem has_deriv_at.sqrt {f : ℝ → ℝ} {x : ℝ} {f' : ℝ} (hf : has_deriv_at f f' x) (hx : f x ≠ 0) : has_deriv_at (fun (y : ℝ) => real.sqrt (f y)) (f' / (bit0 1 * real.sqrt (f x))) x := sorry

theorem differentiable_within_at.sqrt {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) : differentiable_within_at ℝ (fun (x : ℝ) => real.sqrt (f x)) s x :=
  has_deriv_within_at.differentiable_within_at
    (has_deriv_within_at.sqrt (differentiable_within_at.has_deriv_within_at hf) hx)

@[simp] theorem differentiable_at.sqrt {f : ℝ → ℝ} {x : ℝ} (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) : differentiable_at ℝ (fun (x : ℝ) => real.sqrt (f x)) x :=
  has_deriv_at.differentiable_at (has_deriv_at.sqrt (differentiable_at.has_deriv_at hf) hx)

theorem differentiable_on.sqrt {f : ℝ → ℝ} {s : set ℝ} (hf : differentiable_on ℝ f s) (hx : ∀ (x : ℝ), x ∈ s → f x ≠ 0) : differentiable_on ℝ (fun (x : ℝ) => real.sqrt (f x)) s :=
  fun (x : ℝ) (h : x ∈ s) => differentiable_within_at.sqrt (hf x h) (hx x h)

@[simp] theorem differentiable.sqrt {f : ℝ → ℝ} (hf : differentiable ℝ f) (hx : ∀ (x : ℝ), f x ≠ 0) : differentiable ℝ fun (x : ℝ) => real.sqrt (f x) :=
  fun (x : ℝ) => differentiable_at.sqrt (hf x) (hx x)

theorem deriv_within_sqrt {f : ℝ → ℝ} {x : ℝ} {s : set ℝ} (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) (hxs : unique_diff_within_at ℝ s x) : deriv_within (fun (x : ℝ) => real.sqrt (f x)) s x = deriv_within f s x / (bit0 1 * real.sqrt (f x)) :=
  has_deriv_within_at.deriv_within (has_deriv_within_at.sqrt (differentiable_within_at.has_deriv_within_at hf) hx) hxs

@[simp] theorem deriv_sqrt {f : ℝ → ℝ} {x : ℝ} (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) : deriv (fun (x : ℝ) => real.sqrt (f x)) x = deriv f x / (bit0 1 * real.sqrt (f x)) :=
  has_deriv_at.deriv (has_deriv_at.sqrt (differentiable_at.has_deriv_at hf) hx)

/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) : filter.tendsto (fun (x : ℝ) => x ^ y) filter.at_top filter.at_top := sorry

/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_neg_at_top {y : ℝ} (hy : 0 < y) : filter.tendsto (fun (x : ℝ) => x ^ (-y)) filter.at_top (nhds 0) := sorry

/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
theorem tendsto_rpow_div_mul_add (a : ℝ) (b : ℝ) (c : ℝ) (hb : 0 ≠ b) : filter.tendsto (fun (x : ℝ) => x ^ (a / (b * x + c))) filter.at_top (nhds 1) := sorry

/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_div : filter.tendsto (fun (x : ℝ) => x ^ (1 / x)) filter.at_top (nhds 1) := sorry

/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_neg_div : filter.tendsto (fun (x : ℝ) => x ^ (-1 / x)) filter.at_top (nhds 1) := sorry

namespace nnreal


/-- The nonnegative real power function `x^y`, defined for `x : ℝ≥0` and `y : ℝ ` as the
restriction of the real power function. For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`,
one sets `0 ^ 0 = 1` and `0 ^ y = 0` for `y ≠ 0`. -/
def rpow (x : nnreal) (y : ℝ) : nnreal :=
  { val := ↑x ^ y, property := sorry }

protected instance real.has_pow : has_pow nnreal ℝ :=
  has_pow.mk rpow

@[simp] theorem rpow_eq_pow (x : nnreal) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp] theorem coe_rpow (x : nnreal) (y : ℝ) : ↑(x ^ y) = ↑x ^ y :=
  rfl

@[simp] theorem rpow_zero (x : nnreal) : x ^ 0 = 1 :=
  nnreal.eq (real.rpow_zero ↑x)

@[simp] theorem rpow_eq_zero_iff {x : nnreal} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := sorry

@[simp] theorem zero_rpow {x : ℝ} (h : x ≠ 0) : 0 ^ x = 0 :=
  nnreal.eq (real.zero_rpow h)

@[simp] theorem rpow_one (x : nnreal) : x ^ 1 = x :=
  nnreal.eq (real.rpow_one ↑x)

@[simp] theorem one_rpow (x : ℝ) : 1 ^ x = 1 :=
  nnreal.eq (real.one_rpow x)

theorem rpow_add {x : nnreal} (hx : x ≠ 0) (y : ℝ) (z : ℝ) : x ^ (y + z) = x ^ y * x ^ z :=
  nnreal.eq (real.rpow_add (iff.mpr pos_iff_ne_zero hx) y z)

theorem rpow_add' (x : nnreal) {y : ℝ} {z : ℝ} (h : y + z ≠ 0) : x ^ (y + z) = x ^ y * x ^ z :=
  nnreal.eq (real.rpow_add' (subtype.property x) h)

theorem rpow_mul (x : nnreal) (y : ℝ) (z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  nnreal.eq (real.rpow_mul (subtype.property x) y z)

theorem rpow_neg (x : nnreal) (y : ℝ) : x ^ (-y) = (x ^ y⁻¹) :=
  nnreal.eq (real.rpow_neg (subtype.property x) y)

theorem rpow_neg_one (x : nnreal) : x ^ (-1) = (x⁻¹) := sorry

theorem rpow_sub {x : nnreal} (hx : x ≠ 0) (y : ℝ) (z : ℝ) : x ^ (y - z) = x ^ y / x ^ z :=
  nnreal.eq (real.rpow_sub (iff.mpr pos_iff_ne_zero hx) y z)

theorem rpow_sub' (x : nnreal) {y : ℝ} {z : ℝ} (h : y - z ≠ 0) : x ^ (y - z) = x ^ y / x ^ z :=
  nnreal.eq (real.rpow_sub' (subtype.property x) h)

theorem inv_rpow (x : nnreal) (y : ℝ) : x⁻¹ ^ y = (x ^ y⁻¹) :=
  nnreal.eq (real.inv_rpow (subtype.property x) y)

theorem div_rpow (x : nnreal) (y : nnreal) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  nnreal.eq (real.div_rpow (subtype.property x) (subtype.property y) z)

@[simp] theorem rpow_nat_cast (x : nnreal) (n : ℕ) : x ^ ↑n = x ^ n := sorry

theorem mul_rpow {x : nnreal} {y : nnreal} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  nnreal.eq (real.mul_rpow (subtype.property x) (subtype.property y))

theorem rpow_le_rpow {x : nnreal} {y : nnreal} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  real.rpow_le_rpow (subtype.property x) h₁ h₂

theorem rpow_lt_rpow {x : nnreal} {y : nnreal} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  real.rpow_lt_rpow (subtype.property x) h₁ h₂

theorem rpow_lt_rpow_iff {x : nnreal} {y : nnreal} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  real.rpow_lt_rpow_iff (subtype.property x) (subtype.property y) hz

theorem rpow_le_rpow_iff {x : nnreal} {y : nnreal} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  real.rpow_le_rpow_iff (subtype.property x) (subtype.property y) hz

theorem rpow_lt_rpow_of_exponent_lt {x : nnreal} {y : ℝ} {z : ℝ} (hx : 1 < x) (hyz : y < z) : x ^ y < x ^ z :=
  real.rpow_lt_rpow_of_exponent_lt hx hyz

theorem rpow_le_rpow_of_exponent_le {x : nnreal} {y : ℝ} {z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z :=
  real.rpow_le_rpow_of_exponent_le hx hyz

theorem rpow_lt_rpow_of_exponent_gt {x : nnreal} {y : ℝ} {z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z :=
  real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

theorem rpow_le_rpow_of_exponent_ge {x : nnreal} {y : ℝ} {z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z :=
  real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

theorem rpow_lt_one {x : nnreal} {z : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  real.rpow_lt_one hx hx1 hz

theorem rpow_le_one {x : nnreal} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  real.rpow_le_one (subtype.property x) hx2 hz

theorem rpow_lt_one_of_one_lt_of_neg {x : nnreal} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  real.rpow_lt_one_of_one_lt_of_neg hx hz

theorem rpow_le_one_of_one_le_of_nonpos {x : nnreal} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  real.rpow_le_one_of_one_le_of_nonpos hx hz

theorem one_lt_rpow {x : nnreal} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  real.one_lt_rpow hx hz

theorem one_le_rpow {x : nnreal} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  real.one_le_rpow h h₁

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : nnreal} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z :=
  real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : nnreal} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z ≤ 0) : 1 ≤ x ^ z :=
  real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

theorem pow_nat_rpow_nat_inv (x : nnreal) {n : ℕ} (hn : 0 < n) : (x ^ n) ^ (↑n⁻¹) = x := sorry

theorem rpow_nat_inv_pow_nat (x : nnreal) {n : ℕ} (hn : 0 < n) : (x ^ (↑n⁻¹)) ^ n = x := sorry

theorem continuous_at_rpow {x : nnreal} {y : ℝ} (h : x ≠ 0 ∨ 0 < y) : continuous_at (fun (p : nnreal × ℝ) => prod.fst p ^ prod.snd p) (x, y) := sorry

theorem of_real_rpow_of_nonneg {x : ℝ} {y : ℝ} (hx : 0 ≤ x) : nnreal.of_real (x ^ y) = nnreal.of_real x ^ y := sorry

end nnreal


theorem nnreal.measurable_rpow : measurable fun (p : nnreal × ℝ) => prod.fst p ^ prod.snd p := sorry

theorem measurable.nnreal_rpow {α : Type u_1} [measurable_space α] {f : α → nnreal} (hf : measurable f) {g : α → ℝ} (hg : measurable g) : measurable fun (a : α) => f a ^ g a :=
  id (measurable.comp nnreal.measurable_rpow (measurable.prod hf hg))

theorem nnreal.measurable_rpow_const {y : ℝ} : measurable fun (a : nnreal) => a ^ y := sorry

theorem measurable.nnreal_rpow_const {α : Type u_1} [measurable_space α] {f : α → nnreal} (hf : measurable f) {y : ℝ} : measurable fun (a : α) => f a ^ y :=
  measurable.nnreal_rpow hf measurable_const

theorem filter.tendsto.nnrpow {α : Type u_1} {f : filter α} {u : α → nnreal} {v : α → ℝ} {x : nnreal} {y : ℝ} (hx : filter.tendsto u f (nhds x)) (hy : filter.tendsto v f (nhds y)) (h : x ≠ 0 ∨ 0 < y) : filter.tendsto (fun (a : α) => u a ^ v a) f (nhds (x ^ y)) :=
  filter.tendsto.comp (nnreal.continuous_at_rpow h) (filter.tendsto.prod_mk_nhds hx hy)

namespace nnreal


theorem continuous_at_rpow_const {x : nnreal} {y : ℝ} (h : x ≠ 0 ∨ 0 ≤ y) : continuous_at (fun (z : nnreal) => z ^ y) x := sorry

theorem continuous_rpow_const {y : ℝ} (h : 0 ≤ y) : continuous fun (x : nnreal) => x ^ y :=
  iff.mpr continuous_iff_continuous_at fun (x : nnreal) => continuous_at_rpow_const (Or.inr h)

end nnreal


namespace ennreal


/-- The real power function `x^y` on extended nonnegative reals, defined for `x : ennreal` and
`y : ℝ` as the restriction of the real power function if `0 < x < ⊤`, and with the natural values
for `0` and `⊤` (i.e., `0 ^ x = 0` for `x > 0`, `1` for `x = 0` and `⊤` for `x < 0`, and
`⊤ ^ x = 1 / 0 ^ x`). -/
def rpow : ennreal → ℝ → ennreal :=
  sorry

protected instance real.has_pow : has_pow ennreal ℝ :=
  has_pow.mk rpow

@[simp] theorem rpow_eq_pow (x : ennreal) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp] theorem rpow_zero {x : ennreal} : x ^ 0 = 1 := sorry

theorem top_rpow_def (y : ℝ) : ⊤ ^ y = ite (0 < y) ⊤ (ite (y = 0) 1 0) :=
  rfl

@[simp] theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : ⊤ ^ y = ⊤ := sorry

@[simp] theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : ⊤ ^ y = 0 := sorry

@[simp] theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : 0 ^ y = 0 := sorry

@[simp] theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : 0 ^ y = ⊤ := sorry

theorem zero_rpow_def (y : ℝ) : 0 ^ y = ite (0 < y) 0 (ite (y = 0) 1 ⊤) := sorry

theorem coe_rpow_of_ne_zero {x : nnreal} (h : x ≠ 0) (y : ℝ) : ↑x ^ y = ↑(x ^ y) := sorry

theorem coe_rpow_of_nonneg (x : nnreal) {y : ℝ} (h : 0 ≤ y) : ↑x ^ y = ↑(x ^ y) := sorry

theorem coe_rpow_def (x : nnreal) (y : ℝ) : ↑x ^ y = ite (x = 0 ∧ y < 0) ⊤ ↑(x ^ y) :=
  rfl

@[simp] theorem rpow_one (x : ennreal) : x ^ 1 = x := sorry

@[simp] theorem one_rpow (x : ℝ) : 1 ^ x = 1 := sorry

@[simp] theorem rpow_eq_zero_iff {x : ennreal} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 := sorry

@[simp] theorem rpow_eq_top_iff {x : ennreal} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y := sorry

theorem rpow_eq_top_iff_of_pos {x : ennreal} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := sorry

theorem rpow_eq_top_of_nonneg (x : ennreal) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ := sorry

theorem rpow_ne_top_of_nonneg {x : ennreal} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (rpow_eq_top_of_nonneg x hy0) h

theorem rpow_lt_top_of_nonneg {x : ennreal} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  iff.mpr ennreal.lt_top_iff_ne_top (rpow_ne_top_of_nonneg hy0 h)

theorem rpow_add {x : ennreal} (y : ℝ) (z : ℝ) (hx : x ≠ 0) (h'x : x ≠ ⊤) : x ^ (y + z) = x ^ y * x ^ z := sorry

theorem rpow_neg (x : ennreal) (y : ℝ) : x ^ (-y) = (x ^ y⁻¹) := sorry

theorem rpow_neg_one (x : ennreal) : x ^ (-1) = (x⁻¹) := sorry

theorem rpow_mul (x : ennreal) (y : ℝ) (z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := sorry

@[simp] theorem rpow_nat_cast (x : ennreal) (n : ℕ) : x ^ ↑n = x ^ n := sorry

theorem coe_mul_rpow (x : nnreal) (y : nnreal) (z : ℝ) : (↑x * ↑y) ^ z = ↑x ^ z * ↑y ^ z := sorry

theorem mul_rpow_of_ne_top {x : ennreal} {y : ennreal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) : (x * y) ^ z = x ^ z * y ^ z := sorry

theorem mul_rpow_of_ne_zero {x : ennreal} {y : ennreal} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) : (x * y) ^ z = x ^ z * y ^ z := sorry

theorem mul_rpow_of_nonneg (x : ennreal) (y : ennreal) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := sorry

theorem inv_rpow_of_pos {x : ennreal} {y : ℝ} (hy : 0 < y) : x⁻¹ ^ y = (x ^ y⁻¹) := sorry

theorem div_rpow_of_nonneg (x : ennreal) (y : ennreal) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := sorry

theorem rpow_le_rpow {x : ennreal} {y : ennreal} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z := sorry

theorem rpow_lt_rpow {x : ennreal} {y : ennreal} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z := sorry

theorem rpow_le_rpow_iff {x : ennreal} {y : ennreal} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y := sorry

theorem rpow_lt_rpow_iff {x : ennreal} {y : ennreal} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y := sorry

theorem le_rpow_one_div_iff {x : ennreal} {y : ennreal} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := sorry

theorem lt_rpow_one_div_iff {x : ennreal} {y : ennreal} {z : ℝ} (hz : 0 < z) : x < y ^ (1 / z) ↔ x ^ z < y := sorry

theorem rpow_lt_rpow_of_exponent_lt {x : ennreal} {y : ℝ} {z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) : x ^ y < x ^ z := sorry

theorem rpow_le_rpow_of_exponent_le {x : ennreal} {y : ℝ} {z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z := sorry

theorem rpow_lt_rpow_of_exponent_gt {x : ennreal} {y : ℝ} {z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z := sorry

theorem rpow_le_rpow_of_exponent_ge {x : ennreal} {y : ℝ} {z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) : x ^ y ≤ x ^ z := sorry

theorem rpow_le_self_of_le_one {x : ennreal} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x :=
  eq.mpr (id (congr_arg (LessEq (x ^ z)) (Eq._oldrec (Eq.refl x) (Eq.symm (rpow_one x)))))
    (rpow_le_rpow_of_exponent_ge hx h_one_le)

theorem le_rpow_self_of_one_le {x : ennreal} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z :=
  eq.mpr (id (congr_fun (congr_arg LessEq (Eq._oldrec (Eq.refl x) (Eq.symm (rpow_one x)))) (x ^ z)))
    (rpow_le_rpow_of_exponent_le hx h_one_le)

theorem rpow_pos_of_nonneg {p : ℝ} {x : ennreal} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p := sorry

theorem rpow_pos {p : ℝ} {x : ennreal} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p := sorry

theorem rpow_lt_one {x : ennreal} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := sorry

theorem rpow_le_one {x : ennreal} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := sorry

theorem rpow_lt_one_of_one_lt_of_neg {x : ennreal} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := sorry

theorem rpow_le_one_of_one_le_of_neg {x : ennreal} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 := sorry

theorem one_lt_rpow {x : ennreal} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := sorry

theorem one_le_rpow {x : ennreal} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z := sorry

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ennreal} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1) (hz : z < 0) : 1 < x ^ z := sorry

theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ennreal} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1) (hz : z < 0) : 1 ≤ x ^ z := sorry

theorem to_nnreal_rpow (x : ennreal) (z : ℝ) : ennreal.to_nnreal x ^ z = ennreal.to_nnreal (x ^ z) := sorry

theorem to_real_rpow (x : ennreal) (z : ℝ) : ennreal.to_real x ^ z = ennreal.to_real (x ^ z) := sorry

theorem rpow_left_injective {x : ℝ} (hx : x ≠ 0) : function.injective fun (y : ennreal) => y ^ x := sorry

theorem rpow_left_surjective {x : ℝ} (hx : x ≠ 0) : function.surjective fun (y : ennreal) => y ^ x := sorry

theorem rpow_left_bijective {x : ℝ} (hx : x ≠ 0) : function.bijective fun (y : ennreal) => y ^ x :=
  { left := rpow_left_injective hx, right := rpow_left_surjective hx }

theorem rpow_left_monotone_of_nonneg {x : ℝ} (hx : 0 ≤ x) : monotone fun (y : ennreal) => y ^ x :=
  fun (y z : ennreal) (hyz : y ≤ z) => rpow_le_rpow hyz hx

theorem rpow_left_strict_mono_of_pos {x : ℝ} (hx : 0 < x) : strict_mono fun (y : ennreal) => y ^ x :=
  fun (y z : ennreal) (hyz : y < z) => rpow_lt_rpow hyz hx

end ennreal


theorem ennreal.measurable_rpow : measurable fun (p : ennreal × ℝ) => prod.fst p ^ prod.snd p := sorry

theorem measurable.ennreal_rpow {α : Type u_1} [measurable_space α] {f : α → ennreal} (hf : measurable f) {g : α → ℝ} (hg : measurable g) : measurable fun (a : α) => f a ^ g a :=
  id (measurable.comp ennreal.measurable_rpow (measurable.prod hf hg))

theorem ennreal.measurable_rpow_const {y : ℝ} : measurable fun (a : ennreal) => a ^ y :=
  id (measurable.comp ennreal.measurable_rpow (measurable.prod measurable_id (id measurable_const)))

theorem measurable.ennreal_rpow_const {α : Type u_1} [measurable_space α] {f : α → ennreal} (hf : measurable f) {y : ℝ} : measurable fun (a : α) => f a ^ y :=
  measurable.ennreal_rpow hf measurable_const

theorem ae_measurable.ennreal_rpow_const {α : Type u_1} [measurable_space α] {f : α → ennreal} {μ : measure_theory.measure α} (hf : ae_measurable f) {y : ℝ} : ae_measurable fun (a : α) => f a ^ y :=
  measurable.comp_ae_measurable ennreal.measurable_rpow_const hf

