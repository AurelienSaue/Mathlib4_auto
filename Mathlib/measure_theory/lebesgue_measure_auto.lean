/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.pi
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Lebesgue measure on the real line and on `ℝⁿ`
-/

namespace measure_theory


/-!
### Preliminary definitions
-/

/-- Length of an interval. This is the largest monotonic function which correctly
  measures all intervals. -/
def lebesgue_length (s : set ℝ) : ennreal :=
  infi fun (a : ℝ) => infi fun (b : ℝ) => infi fun (h : s ⊆ set.Ico a b) => ennreal.of_real (b - a)

@[simp] theorem lebesgue_length_empty : lebesgue_length ∅ = 0 := sorry

@[simp] theorem lebesgue_length_Ico (a : ℝ) (b : ℝ) :
    lebesgue_length (set.Ico a b) = ennreal.of_real (b - a) :=
  sorry

theorem lebesgue_length_mono {s₁ : set ℝ} {s₂ : set ℝ} (h : s₁ ⊆ s₂) :
    lebesgue_length s₁ ≤ lebesgue_length s₂ :=
  sorry

theorem lebesgue_length_eq_infi_Ioo (s : set ℝ) :
    lebesgue_length s =
        infi
          fun (a : ℝ) =>
            infi fun (b : ℝ) => infi fun (h : s ⊆ set.Ioo a b) => ennreal.of_real (b - a) :=
  sorry

@[simp] theorem lebesgue_length_Ioo (a : ℝ) (b : ℝ) :
    lebesgue_length (set.Ioo a b) = ennreal.of_real (b - a) :=
  sorry

theorem lebesgue_length_eq_infi_Icc (s : set ℝ) :
    lebesgue_length s =
        infi
          fun (a : ℝ) =>
            infi fun (b : ℝ) => infi fun (h : s ⊆ set.Icc a b) => ennreal.of_real (b - a) :=
  sorry

@[simp] theorem lebesgue_length_Icc (a : ℝ) (b : ℝ) :
    lebesgue_length (set.Icc a b) = ennreal.of_real (b - a) :=
  sorry

/-- The Lebesgue outer measure, as an outer measure of ℝ. -/
def lebesgue_outer : outer_measure ℝ :=
  outer_measure.of_function lebesgue_length lebesgue_length_empty

theorem lebesgue_outer_le_length (s : set ℝ) : coe_fn lebesgue_outer s ≤ lebesgue_length s :=
  outer_measure.of_function_le s

theorem lebesgue_length_subadditive {a : ℝ} {b : ℝ} {c : ℕ → ℝ} {d : ℕ → ℝ}
    (ss : set.Icc a b ⊆ set.Union fun (i : ℕ) => set.Ioo (c i) (d i)) :
    ennreal.of_real (b - a) ≤ tsum fun (i : ℕ) => ennreal.of_real (d i - c i) :=
  sorry

@[simp] theorem lebesgue_outer_Icc (a : ℝ) (b : ℝ) :
    coe_fn lebesgue_outer (set.Icc a b) = ennreal.of_real (b - a) :=
  sorry

@[simp] theorem lebesgue_outer_singleton (a : ℝ) : coe_fn lebesgue_outer (singleton a) = 0 := sorry

@[simp] theorem lebesgue_outer_Ico (a : ℝ) (b : ℝ) :
    coe_fn lebesgue_outer (set.Ico a b) = ennreal.of_real (b - a) :=
  sorry

@[simp] theorem lebesgue_outer_Ioo (a : ℝ) (b : ℝ) :
    coe_fn lebesgue_outer (set.Ioo a b) = ennreal.of_real (b - a) :=
  sorry

@[simp] theorem lebesgue_outer_Ioc (a : ℝ) (b : ℝ) :
    coe_fn lebesgue_outer (set.Ioc a b) = ennreal.of_real (b - a) :=
  sorry

theorem is_lebesgue_measurable_Iio {c : ℝ} :
    measurable_space.is_measurable' (outer_measure.caratheodory lebesgue_outer) (set.Iio c) :=
  sorry

theorem lebesgue_outer_trim : outer_measure.trim lebesgue_outer = lebesgue_outer := sorry

theorem borel_le_lebesgue_measurable : borel ℝ ≤ outer_measure.caratheodory lebesgue_outer := sorry

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/

/-- Lebesgue measure on the Borel sets

The outer Lebesgue measure is the completion of this measure. (TODO: proof this)
-/
protected instance real.measure_space : measure_space ℝ :=
  measure_space.mk (measure.mk lebesgue_outer sorry lebesgue_outer_trim)

@[simp] theorem lebesgue_to_outer_measure : measure.to_outer_measure volume = lebesgue_outer := rfl

end measure_theory


namespace real


theorem volume_val (s : set ℝ) : coe_fn volume s = coe_fn measure_theory.lebesgue_outer s := rfl

protected instance has_no_atoms_volume : measure_theory.has_no_atoms volume :=
  measure_theory.has_no_atoms.mk measure_theory.lebesgue_outer_singleton

@[simp] theorem volume_Ico {a : ℝ} {b : ℝ} :
    coe_fn volume (set.Ico a b) = ennreal.of_real (b - a) :=
  measure_theory.lebesgue_outer_Ico a b

@[simp] theorem volume_Icc {a : ℝ} {b : ℝ} :
    coe_fn volume (set.Icc a b) = ennreal.of_real (b - a) :=
  measure_theory.lebesgue_outer_Icc a b

@[simp] theorem volume_Ioo {a : ℝ} {b : ℝ} :
    coe_fn volume (set.Ioo a b) = ennreal.of_real (b - a) :=
  measure_theory.lebesgue_outer_Ioo a b

@[simp] theorem volume_Ioc {a : ℝ} {b : ℝ} :
    coe_fn volume (set.Ioc a b) = ennreal.of_real (b - a) :=
  measure_theory.lebesgue_outer_Ioc a b

@[simp] theorem volume_singleton {a : ℝ} : coe_fn volume (singleton a) = 0 :=
  measure_theory.lebesgue_outer_singleton a

@[simp] theorem volume_interval {a : ℝ} {b : ℝ} :
    coe_fn volume (set.interval a b) = ennreal.of_real (abs (b - a)) :=
  sorry

@[simp] theorem volume_Ioi {a : ℝ} : coe_fn volume (set.Ioi a) = ⊤ := sorry

@[simp] theorem volume_Ici {a : ℝ} : coe_fn volume (set.Ici a) = ⊤ := sorry

@[simp] theorem volume_Iio {a : ℝ} : coe_fn volume (set.Iio a) = ⊤ := sorry

@[simp] theorem volume_Iic {a : ℝ} : coe_fn volume (set.Iic a) = ⊤ := sorry

protected instance locally_finite_volume : measure_theory.locally_finite_measure volume :=
  measure_theory.locally_finite_measure.mk
    fun (x : ℝ) =>
      Exists.intro (set.Ioo (x - 1) (x + 1))
        (Exists.intro
          (mem_nhds_sets is_open_Ioo
            { left := sub_lt_self x zero_lt_one, right := lt_add_of_pos_right x zero_lt_one })
          (eq.mpr
            (id
              (Eq.trans
                ((fun (ᾰ ᾰ_1 : ennreal) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ennreal) (e_3 : ᾰ_2 = ᾰ_3) =>
                    congr (congr_arg Less e_2) e_3)
                  (coe_fn volume (set.Ioo (x - 1) (x + 1))) (ennreal.of_real (x + 1 - (x - 1)))
                  volume_Ioo ⊤ ⊤ (Eq.refl ⊤))
                (propext (iff_true_intro ennreal.of_real_lt_top))))
            trivial))

/-!
### Volume of a box in `ℝⁿ`
-/

theorem volume_Icc_pi {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ} :
    coe_fn volume (set.Icc a b) =
        finset.prod finset.univ fun (i : ι) => ennreal.of_real (b i - a i) :=
  sorry

@[simp] theorem volume_Icc_pi_to_real {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ}
    (h : a ≤ b) :
    ennreal.to_real (coe_fn volume (set.Icc a b)) =
        finset.prod finset.univ fun (i : ι) => b i - a i :=
  sorry

theorem volume_pi_Ioo {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ} :
    coe_fn volume (set.pi set.univ fun (i : ι) => set.Ioo (a i) (b i)) =
        finset.prod finset.univ fun (i : ι) => ennreal.of_real (b i - a i) :=
  Eq.trans (measure_theory.measure_congr measure_theory.measure.univ_pi_Ioo_ae_eq_Icc) volume_Icc_pi

@[simp] theorem volume_pi_Ioo_to_real {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ}
    (h : a ≤ b) :
    ennreal.to_real (coe_fn volume (set.pi set.univ fun (i : ι) => set.Ioo (a i) (b i))) =
        finset.prod finset.univ fun (i : ι) => b i - a i :=
  sorry

theorem volume_pi_Ioc {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ} :
    coe_fn volume (set.pi set.univ fun (i : ι) => set.Ioc (a i) (b i)) =
        finset.prod finset.univ fun (i : ι) => ennreal.of_real (b i - a i) :=
  Eq.trans (measure_theory.measure_congr measure_theory.measure.univ_pi_Ioc_ae_eq_Icc) volume_Icc_pi

@[simp] theorem volume_pi_Ioc_to_real {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ}
    (h : a ≤ b) :
    ennreal.to_real (coe_fn volume (set.pi set.univ fun (i : ι) => set.Ioc (a i) (b i))) =
        finset.prod finset.univ fun (i : ι) => b i - a i :=
  sorry

theorem volume_pi_Ico {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ} :
    coe_fn volume (set.pi set.univ fun (i : ι) => set.Ico (a i) (b i)) =
        finset.prod finset.univ fun (i : ι) => ennreal.of_real (b i - a i) :=
  Eq.trans (measure_theory.measure_congr measure_theory.measure.univ_pi_Ico_ae_eq_Icc) volume_Icc_pi

@[simp] theorem volume_pi_Ico_to_real {ι : Type u_1} [fintype ι] {a : ι → ℝ} {b : ι → ℝ}
    (h : a ≤ b) :
    ennreal.to_real (coe_fn volume (set.pi set.univ fun (i : ι) => set.Ico (a i) (b i))) =
        finset.prod finset.univ fun (i : ι) => b i - a i :=
  sorry

/-!
### Images of the Lebesgue measure under translation/multiplication/...
-/

theorem map_volume_add_left (a : ℝ) :
    coe_fn (measure_theory.measure.map (Add.add a)) volume = volume :=
  sorry

theorem map_volume_add_right (a : ℝ) :
    coe_fn (measure_theory.measure.map fun (_x : ℝ) => _x + a) volume = volume :=
  sorry

theorem smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    ennreal.of_real (abs a) • coe_fn (measure_theory.measure.map (Mul.mul a)) volume = volume :=
  sorry

theorem map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    coe_fn (measure_theory.measure.map (Mul.mul a)) volume = ennreal.of_real (abs (a⁻¹)) • volume :=
  sorry

theorem smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
    ennreal.of_real (abs a) • coe_fn (measure_theory.measure.map fun (_x : ℝ) => _x * a) volume =
        volume :=
  sorry

theorem map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
    coe_fn (measure_theory.measure.map fun (_x : ℝ) => _x * a) volume =
        ennreal.of_real (abs (a⁻¹)) • volume :=
  sorry

@[simp] theorem map_volume_neg : coe_fn (measure_theory.measure.map Neg.neg) volume = volume :=
  sorry

end real


theorem filter.eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ}
    (h : filter.eventually (fun (x : ℝ) => p x) (nhds a)) :
    0 < coe_fn volume (set_of fun (x : ℝ) => p x) :=
  sorry

end Mathlib