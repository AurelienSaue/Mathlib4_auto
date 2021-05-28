/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.instances.nnreal
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Square root of a real number

In this file we define

* `nnreal.sqrt` to be the square root of a nonnegative real number.
* `real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `nnreal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `nnreal.sqrt x` exists. As a side
effect, `nnreal.sqrt` is a bundled `order_iso`, so for `nnreal` numbers we get continuity as well as
theorems like `sqrt x ≤ y ↔ x * x ≤ y` for free.

Then we define `real.sqrt x` to be `nnreal.sqrt (nnreal.of_real x)`. We also define a Cauchy
sequence `real.sqrt_aux (f : cau_seq ℚ abs)` which converges to `sqrt (mk f)` but do not prove (yet)
that this sequence actually converges to `sqrt (mk f)`.

## Tags

square root
-/

namespace nnreal


/-- Square root of a nonnegative real number. -/
def sqrt : nnreal ≃o nnreal :=
  order_iso.symm (strict_mono.order_iso_of_surjective (fun (x : nnreal) => x * x) sorry sorry)

theorem sqrt_eq_iff_sqr_eq {x : nnreal} {y : nnreal} : coe_fn sqrt x = y ↔ y * y = x :=
  iff.trans (equiv.apply_eq_iff_eq_symm_apply (rel_iso.to_equiv sqrt)) eq_comm

theorem sqrt_le_iff {x : nnreal} {y : nnreal} : coe_fn sqrt x ≤ y ↔ x ≤ y * y :=
  order_iso.to_galois_connection sqrt x y

theorem le_sqrt_iff {x : nnreal} {y : nnreal} : x ≤ coe_fn sqrt y ↔ x * x ≤ y :=
  iff.symm (order_iso.to_galois_connection (order_iso.symm sqrt) x y)

@[simp] theorem sqrt_eq_zero {x : nnreal} : coe_fn sqrt x = 0 ↔ x = 0 :=
  iff.trans sqrt_eq_iff_sqr_eq
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 * 0 = x ↔ x = 0)) (propext eq_comm)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (x = 0 * 0 ↔ x = 0)) (zero_mul 0))) (iff.refl (x = 0))))

@[simp] theorem sqrt_zero : coe_fn sqrt 0 = 0 :=
  iff.mpr sqrt_eq_zero rfl

@[simp] theorem sqrt_one : coe_fn sqrt 1 = 1 :=
  iff.mpr sqrt_eq_iff_sqr_eq (mul_one 1)

@[simp] theorem mul_sqrt_self (x : nnreal) : coe_fn sqrt x * coe_fn sqrt x = x :=
  order_iso.symm_apply_apply sqrt x

@[simp] theorem sqrt_mul_self (x : nnreal) : coe_fn sqrt (x * x) = x :=
  order_iso.apply_symm_apply sqrt x

theorem sqrt_mul (x : nnreal) (y : nnreal) : coe_fn sqrt (x * y) = coe_fn sqrt x * coe_fn sqrt y := sorry

/-- `nnreal.sqrt` as a `monoid_with_zero_hom`. -/
def sqrt_hom : monoid_with_zero_hom nnreal nnreal :=
  monoid_with_zero_hom.mk (⇑sqrt) sqrt_zero sqrt_one sqrt_mul

theorem sqrt_inv (x : nnreal) : coe_fn sqrt (x⁻¹) = (coe_fn sqrt x⁻¹) :=
  monoid_with_zero_hom.map_inv' sqrt_hom x

theorem sqrt_div (x : nnreal) (y : nnreal) : coe_fn sqrt (x / y) = coe_fn sqrt x / coe_fn sqrt y :=
  monoid_with_zero_hom.map_div sqrt_hom x y

theorem continuous_sqrt : continuous ⇑sqrt :=
  order_iso.continuous sqrt

end nnreal


namespace real


/-- An auxiliary sequence of rational numbers that converges to `real.sqrt (mk f)`.
Currently this sequence is not used in `mathlib`.  -/
def sqrt_aux (f : cau_seq ℚ abs) : ℕ → ℚ :=
  sorry

theorem sqrt_aux_nonneg (f : cau_seq ℚ abs) (i : ℕ) : 0 ≤ sqrt_aux f i := sorry

/- TODO(Mario): finish the proof
theorem sqrt_aux_converges (f : cau_seq ℚ abs) : ∃ h x, 0 ≤ x ∧ x * x = max 0 (mk f) ∧
  mk ⟨sqrt_aux f, h⟩ = x :=
begin
  rcases sqrt_exists (le_max_left 0 (mk f)) with ⟨x, x0, hx⟩,
  suffices : ∃ h, mk ⟨sqrt_aux f, h⟩ = x,
  { exact this.imp (λ h e, ⟨x, x0, hx, e⟩) },
  apply of_near,

  suffices : ∃ δ > 0, ∀ i, abs (↑(sqrt_aux f i) - x) < δ / 2 ^ i,
  { rcases this with ⟨δ, δ0, hδ⟩,
    intros,
     }
end -/

/-- The square root of a real number. This returns 0 for negative inputs. -/
def sqrt (x : ℝ) : ℝ :=
  ↑(coe_fn nnreal.sqrt (nnreal.of_real x))

/-quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr' 1, exact quotient.sound e
  end)-/

theorem continuous_sqrt : continuous sqrt :=
  continuous.comp nnreal.continuous_coe (continuous.comp (order_iso.continuous nnreal.sqrt) nnreal.continuous_of_real)

theorem sqrt_eq_zero_of_nonpos {x : ℝ} (h : x ≤ 0) : sqrt x = 0 := sorry

theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x :=
  nnreal.coe_nonneg (coe_fn nnreal.sqrt (nnreal.of_real x))

@[simp] theorem mul_self_sqrt {x : ℝ} (h : 0 ≤ x) : sqrt x * sqrt x = x := sorry

@[simp] theorem sqrt_mul_self {x : ℝ} (h : 0 ≤ x) : sqrt (x * x) = x :=
  iff.mp (mul_self_inj_of_nonneg (sqrt_nonneg (x * x)) h) (mul_self_sqrt (mul_self_nonneg x))

theorem sqrt_eq_iff_mul_self_eq {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = y ↔ y * y = x := sorry

@[simp] theorem sqr_sqrt {x : ℝ} (h : 0 ≤ x) : sqrt x ^ bit0 1 = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sqrt x ^ bit0 1 = x)) (pow_two (sqrt x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sqrt x * sqrt x = x)) (mul_self_sqrt h))) (Eq.refl x))

@[simp] theorem sqrt_sqr {x : ℝ} (h : 0 ≤ x) : sqrt (x ^ bit0 1) = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sqrt (x ^ bit0 1) = x)) (pow_two x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sqrt (x * x) = x)) (sqrt_mul_self h))) (Eq.refl x))

theorem sqrt_eq_iff_sqr_eq {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = y ↔ y ^ bit0 1 = x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sqrt x = y ↔ y ^ bit0 1 = x)) (pow_two y)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sqrt x = y ↔ y * y = x)) (propext (sqrt_eq_iff_mul_self_eq hx hy))))
      (iff.refl (y * y = x)))

theorem sqrt_mul_self_eq_abs (x : ℝ) : sqrt (x * x) = abs x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sqrt (x * x) = abs x)) (Eq.symm (abs_mul_abs_self x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sqrt (abs x * abs x) = abs x)) (sqrt_mul_self (abs_nonneg x)))) (Eq.refl (abs x)))

theorem sqrt_sqr_eq_abs (x : ℝ) : sqrt (x ^ bit0 1) = abs x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sqrt (x ^ bit0 1) = abs x)) (pow_two x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (sqrt (x * x) = abs x)) (sqrt_mul_self_eq_abs x))) (Eq.refl (abs x)))

@[simp] theorem sqrt_zero : sqrt 0 = 0 := sorry

@[simp] theorem sqrt_one : sqrt 1 = 1 := sorry

@[simp] theorem sqrt_le {x : ℝ} {y : ℝ} (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y := sorry

@[simp] theorem sqrt_lt {x : ℝ} {y : ℝ} (hx : 0 ≤ x) : sqrt x < sqrt y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le hx)

theorem sqrt_le_sqrt {x : ℝ} {y : ℝ} (h : x ≤ y) : sqrt x ≤ sqrt y := sorry

theorem sqrt_le_left {x : ℝ} {y : ℝ} (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ bit0 1 := sorry

theorem sqrt_le_iff {x : ℝ} {y : ℝ} : sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ bit0 1 := sorry

/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sqr_le`.
   if you have `x > 0`, consider using `le_sqrt'` -/

theorem le_sqrt {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ bit0 1 ≤ y := sorry

theorem le_sqrt' {x : ℝ} {y : ℝ} (hx : 0 < x) : x ≤ sqrt y ↔ x ^ bit0 1 ≤ y := sorry

theorem le_sqrt_of_sqr_le {x : ℝ} {y : ℝ} (h : x ^ bit0 1 ≤ y) : x ≤ sqrt y :=
  or.dcases_on (lt_or_ge 0 x)
    (fun (hx : 0 < x) => eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ sqrt y)) (propext (le_sqrt' hx)))) h)
    fun (hx : 0 ≥ x) => le_trans hx (sqrt_nonneg y)

@[simp] theorem sqrt_inj {x : ℝ} {y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y := sorry

@[simp] theorem sqrt_eq_zero {x : ℝ} (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 := sorry

theorem sqrt_eq_zero' {x : ℝ} : sqrt x = 0 ↔ x ≤ 0 := sorry

@[simp] theorem sqrt_pos {x : ℝ} : 0 < sqrt x ↔ 0 < x := sorry

@[simp] theorem sqrt_mul {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y := sorry

@[simp] theorem sqrt_mul' (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y := sorry

@[simp] theorem sqrt_inv (x : ℝ) : sqrt (x⁻¹) = (sqrt x⁻¹) := sorry

@[simp] theorem sqrt_div {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y := sorry

end real


theorem filter.tendsto.sqrt {α : Type u_1} {f : α → ℝ} {l : filter α} {x : ℝ} (h : filter.tendsto f l (nhds x)) : filter.tendsto (fun (x : α) => real.sqrt (f x)) l (nhds (real.sqrt x)) :=
  filter.tendsto.comp (continuous.tendsto real.continuous_sqrt x) h

theorem continuous_within_at.sqrt {α : Type u_1} [topological_space α] {f : α → ℝ} {s : set α} {x : α} (h : continuous_within_at f s x) : continuous_within_at (fun (x : α) => real.sqrt (f x)) s x :=
  filter.tendsto.sqrt h

theorem continuous_at.sqrt {α : Type u_1} [topological_space α] {f : α → ℝ} {x : α} (h : continuous_at f x) : continuous_at (fun (x : α) => real.sqrt (f x)) x :=
  filter.tendsto.sqrt h

theorem continuous_on.sqrt {α : Type u_1} [topological_space α] {f : α → ℝ} {s : set α} (h : continuous_on f s) : continuous_on (fun (x : α) => real.sqrt (f x)) s :=
  fun (x : α) (hx : x ∈ s) => continuous_within_at.sqrt (h x hx)

theorem continuous.sqrt {α : Type u_1} [topological_space α] {f : α → ℝ} (h : continuous f) : continuous fun (x : α) => real.sqrt (f x) :=
  continuous.comp real.continuous_sqrt h

