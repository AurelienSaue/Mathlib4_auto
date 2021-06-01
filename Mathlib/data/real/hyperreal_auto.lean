/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.filter_product
import Mathlib.analysis.specific_limits
import Mathlib.PostPort

namespace Mathlib

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.
-/

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
def hyperreal := filter.germ ↑(filter.hyperfilter ℕ) ℝ

notation:1024 "ℝ*" => Mathlib.hyperreal

namespace hyperreal


protected instance has_coe_t : has_coe_t ℝ ℝ* := has_coe_t.mk fun (x : ℝ) => ↑x

@[simp] theorem coe_eq_coe {x : ℝ} {y : ℝ} : ↑x = ↑y ↔ x = y := filter.germ.const_inj

@[simp] theorem coe_eq_zero {x : ℝ} : ↑x = 0 ↔ x = 0 := coe_eq_coe

@[simp] theorem coe_eq_one {x : ℝ} : ↑x = 1 ↔ x = 1 := coe_eq_coe

@[simp] theorem coe_one : ↑1 = 1 := rfl

@[simp] theorem coe_zero : ↑0 = 0 := rfl

@[simp] theorem coe_inv (x : ℝ) : ↑(x⁻¹) = (↑x⁻¹) := rfl

@[simp] theorem coe_neg (x : ℝ) : ↑(-x) = -↑x := rfl

@[simp] theorem coe_add (x : ℝ) (y : ℝ) : ↑(x + y) = ↑x + ↑y := rfl

@[simp] theorem coe_bit0 (x : ℝ) : ↑(bit0 x) = bit0 ↑x := rfl

@[simp] theorem coe_bit1 (x : ℝ) : ↑(bit1 x) = bit1 ↑x := rfl

@[simp] theorem coe_mul (x : ℝ) (y : ℝ) : ↑(x * y) = ↑x * ↑y := rfl

@[simp] theorem coe_div (x : ℝ) (y : ℝ) : ↑(x / y) = ↑x / ↑y := rfl

@[simp] theorem coe_sub (x : ℝ) (y : ℝ) : ↑(x - y) = ↑x - ↑y := rfl

@[simp] theorem coe_lt_coe {x : ℝ} {y : ℝ} : ↑x < ↑y ↔ x < y := filter.germ.const_lt

@[simp] theorem coe_pos {x : ℝ} : 0 < ↑x ↔ 0 < x := coe_lt_coe

@[simp] theorem coe_le_coe {x : ℝ} {y : ℝ} : ↑x ≤ ↑y ↔ x ≤ y := filter.germ.const_le_iff

@[simp] theorem coe_abs (x : ℝ) : ↑(abs x) = abs ↑x := filter.germ.const_abs x

@[simp] theorem coe_max (x : ℝ) (y : ℝ) : ↑(max x y) = max ↑x ↑y := filter.germ.const_max x y

@[simp] theorem coe_min (x : ℝ) (y : ℝ) : ↑(min x y) = min ↑x ↑y := filter.germ.const_min x y

/-- Construct a hyperreal number from a sequence of real numbers. -/
def of_seq (f : ℕ → ℝ) : ℝ* := ↑f

/-- A sample infinitesimal hyperreal-/
def epsilon : ℝ* := of_seq fun (n : ℕ) => ↑n⁻¹

/-- A sample infinite hyperreal-/
def omega : ℝ* := of_seq coe

theorem epsilon_eq_inv_omega : epsilon = (omega⁻¹) := rfl

theorem inv_epsilon_eq_omega : epsilon⁻¹ = omega := inv_inv' omega

theorem epsilon_pos : 0 < epsilon := sorry

theorem epsilon_ne_zero : epsilon ≠ 0 := ne_of_gt epsilon_pos

theorem omega_pos : 0 < omega :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < omega)) (Eq.symm inv_epsilon_eq_omega)))
    (iff.mpr inv_pos epsilon_pos)

theorem omega_ne_zero : omega ≠ 0 := ne_of_gt omega_pos

theorem epsilon_mul_omega : epsilon * omega = 1 := inv_mul_cancel omega_ne_zero

theorem lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : filter.tendsto f filter.at_top (nhds 0))
    {r : ℝ} : 0 < r → of_seq f < ↑r :=
  sorry

theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : filter.tendsto f filter.at_top (nhds 0))
    {r : ℝ} : 0 < r → -↑r < of_seq f :=
  sorry

theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : filter.tendsto f filter.at_top (nhds 0))
    {r : ℝ} : r < 0 → ↑r < of_seq f :=
  sorry

theorem epsilon_lt_pos (x : ℝ) : 0 < x → epsilon < ↑x :=
  lt_of_tendsto_zero_of_pos tendsto_inverse_at_top_nhds_0_nat

/-- Standard part predicate -/
def is_st (x : ℝ*) (r : ℝ) := ∀ (δ : ℝ), 0 < δ → ↑r - ↑δ < x ∧ x < ↑r + ↑δ

/-- Standard part function: like a "round" to ℝ instead of ℤ -/
def st : ℝ* → ℝ :=
  fun (x : ℝ*) =>
    dite (∃ (r : ℝ), is_st x r) (fun (h : ∃ (r : ℝ), is_st x r) => classical.some h)
      fun (h : ¬∃ (r : ℝ), is_st x r) => 0

/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def infinitesimal (x : ℝ*) := is_st x 0

/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def infinite_pos (x : ℝ*) := ∀ (r : ℝ), ↑r < x

/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def infinite_neg (x : ℝ*) := ∀ (r : ℝ), x < ↑r

/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def infinite (x : ℝ*) := infinite_pos x ∨ infinite_neg x

/-!
### Some facts about `st`
-/

theorem is_st_unique {x : ℝ*} {r : ℝ} {s : ℝ} (hr : is_st x r) (hs : is_st x s) : r = s :=
  or.dcases_on (lt_trichotomy r s) (fun (h : r < s) => false.elim (is_st_unique' x r s hr hs h))
    fun (h : r = s ∨ s < r) =>
      or.dcases_on h (fun (h : r = s) => h)
        fun (h : s < r) => false.elim (is_st_unique' x s r hs hr h)

theorem not_infinite_of_exists_st {x : ℝ*} : (∃ (r : ℝ), is_st x r) → ¬infinite x := sorry

theorem is_st_Sup {x : ℝ*} (hni : ¬infinite x) : is_st x (Sup (set_of fun (y : ℝ) => ↑y < x)) :=
  sorry

theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬infinite x) : ∃ (r : ℝ), is_st x r :=
  Exists.intro (Sup (set_of fun (y : ℝ) => ↑y < x)) (is_st_Sup hni)

theorem st_eq_Sup {x : ℝ*} : st x = Sup (set_of fun (y : ℝ) => ↑y < x) := sorry

theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ (r : ℝ), is_st x r) ↔ ¬infinite x :=
  { mp := not_infinite_of_exists_st, mpr := exists_st_of_not_infinite }

theorem infinite_iff_not_exists_st {x : ℝ*} : infinite x ↔ ¬∃ (r : ℝ), is_st x r :=
  iff.mp iff_not_comm exists_st_iff_not_infinite

theorem st_infinite {x : ℝ*} (hi : infinite x) : st x = 0 := sorry

theorem st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : st x = r := sorry

theorem is_st_st_of_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st x (st x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_st x (st x))) (st_of_is_st hxr))) hxr

theorem is_st_st_of_exists_st {x : ℝ*} (hx : ∃ (r : ℝ), is_st x r) : is_st x (st x) :=
  Exists.dcases_on hx fun (r : ℝ) => is_st_st_of_is_st

theorem is_st_st {x : ℝ*} (hx : st x ≠ 0) : is_st x (st x) := sorry

theorem is_st_st' {x : ℝ*} (hx : ¬infinite x) : is_st x (st x) :=
  is_st_st_of_exists_st (exists_st_of_not_infinite hx)

theorem is_st_refl_real (r : ℝ) : is_st (↑r) r :=
  fun (δ : ℝ) (hδ : 0 < δ) =>
    { left := sub_lt_self (↑r) (iff.mpr coe_lt_coe hδ),
      right := lt_add_of_pos_right (↑r) (iff.mpr coe_lt_coe hδ) }

theorem st_id_real (r : ℝ) : st ↑r = r := st_of_is_st (is_st_refl_real r)

theorem eq_of_is_st_real {r : ℝ} {s : ℝ} : is_st (↑r) s → r = s := is_st_unique (is_st_refl_real r)

theorem is_st_real_iff_eq {r : ℝ} {s : ℝ} : is_st (↑r) s ↔ r = s :=
  { mp := eq_of_is_st_real,
    mpr :=
      fun (hrs : r = s) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (is_st (↑r) s)) hrs)) (is_st_refl_real s) }

theorem is_st_symm_real {r : ℝ} {s : ℝ} : is_st (↑r) s ↔ is_st (↑s) r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_st (↑r) s ↔ is_st (↑s) r)) (propext is_st_real_iff_eq)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (r = s ↔ is_st (↑s) r)) (propext is_st_real_iff_eq)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (r = s ↔ s = r)) (propext eq_comm))) (iff.refl (s = r))))

theorem is_st_trans_real {r : ℝ} {s : ℝ} {t : ℝ} : is_st (↑r) s → is_st (↑s) t → is_st (↑r) t :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (is_st (↑r) s → is_st (↑s) t → is_st (↑r) t))
        (propext is_st_real_iff_eq)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (r = s → is_st (↑s) t → is_st (↑r) t)) (propext is_st_real_iff_eq)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (r = s → s = t → is_st (↑r) t)) (propext is_st_real_iff_eq)))
        Eq.trans))

theorem is_st_inj_real {r₁ : ℝ} {r₂ : ℝ} {s : ℝ} (h1 : is_st (↑r₁) s) (h2 : is_st (↑r₂) s) :
    r₁ = r₂ :=
  Eq.trans (eq_of_is_st_real h1) (Eq.symm (eq_of_is_st_real h2))

theorem is_st_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} :
    is_st x r ↔ ∀ (δ : ℝ), 0 < δ → abs (x - ↑r) < ↑δ :=
  sorry

theorem is_st_add {x : ℝ*} {y : ℝ*} {r : ℝ} {s : ℝ} :
    is_st x r → is_st y s → is_st (x + y) (r + s) :=
  sorry

theorem is_st_neg {x : ℝ*} {r : ℝ} (hxr : is_st x r) : is_st (-x) (-r) := sorry

theorem is_st_sub {x : ℝ*} {y : ℝ*} {r : ℝ} {s : ℝ} :
    is_st x r → is_st y s → is_st (x - y) (r - s) :=
  fun (hxr : is_st x r) (hys : is_st y s) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (is_st (x - y) (r - s))) (sub_eq_add_neg x y)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (is_st (x + -y) (r - s))) (sub_eq_add_neg r s)))
        (is_st_add hxr (is_st_neg hys)))

/- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y) -/

theorem lt_of_is_st_lt {x : ℝ*} {y : ℝ*} {r : ℝ} {s : ℝ} (hxr : is_st x r) (hys : is_st y s) :
    r < s → x < y :=
  sorry

theorem is_st_le_of_le {x : ℝ*} {y : ℝ*} {r : ℝ} {s : ℝ} (hrx : is_st x r) (hsy : is_st y s) :
    x ≤ y → r ≤ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ≤ y → r ≤ s)) (Eq.symm (propext not_lt))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬y < x → r ≤ s)) (Eq.symm (propext not_lt))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬y < x → ¬s < r)) (propext not_imp_not)))
        (lt_of_is_st_lt hsy hrx)))

theorem st_le_of_le {x : ℝ*} {y : ℝ*} (hix : ¬infinite x) (hiy : ¬infinite y) :
    x ≤ y → st x ≤ st y :=
  (fun (hx' : is_st x (st x)) =>
      (fun (hy' : is_st y (st y)) => is_st_le_of_le hx' hy') (is_st_st' hiy))
    (is_st_st' hix)

theorem lt_of_st_lt {x : ℝ*} {y : ℝ*} (hix : ¬infinite x) (hiy : ¬infinite y) :
    st x < st y → x < y :=
  (fun (hx' : is_st x (st x)) =>
      (fun (hy' : is_st y (st y)) => lt_of_is_st_lt hx' hy') (is_st_st' hiy))
    (is_st_st' hix)

/-!
### Basic lemmas about infinite
-/

theorem infinite_pos_def {x : ℝ*} : infinite_pos x ↔ ∀ (r : ℝ), ↑r < x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (infinite_pos x ↔ ∀ (r : ℝ), ↑r < x)) iff_eq_eq))
    (Eq.refl (infinite_pos x))

theorem infinite_neg_def {x : ℝ*} : infinite_neg x ↔ ∀ (r : ℝ), x < ↑r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (infinite_neg x ↔ ∀ (r : ℝ), x < ↑r)) iff_eq_eq))
    (Eq.refl (infinite_neg x))

theorem ne_zero_of_infinite {x : ℝ*} : infinite x → x ≠ 0 := sorry

theorem not_infinite_zero : ¬infinite 0 := fun (hI : infinite 0) => ne_zero_of_infinite hI rfl

theorem pos_of_infinite_pos {x : ℝ*} : infinite_pos x → 0 < x := fun (hip : infinite_pos x) => hip 0

theorem neg_of_infinite_neg {x : ℝ*} : infinite_neg x → x < 0 := fun (hin : infinite_neg x) => hin 0

theorem not_infinite_pos_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬infinite_pos x :=
  fun (hn : infinite_neg x) (hp : infinite_pos x) => not_lt_of_lt (hn 1) (hp 1)

theorem not_infinite_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬infinite_neg x :=
  iff.mp imp_not_comm not_infinite_pos_of_infinite_neg

theorem infinite_neg_neg_of_infinite_pos {x : ℝ*} : infinite_pos x → infinite_neg (-x) :=
  fun (hp : infinite_pos x) (r : ℝ) => iff.mp neg_lt (hp (-r))

theorem infinite_pos_neg_of_infinite_neg {x : ℝ*} : infinite_neg x → infinite_pos (-x) :=
  fun (hp : infinite_neg x) (r : ℝ) => iff.mp lt_neg (hp (-r))

theorem infinite_pos_iff_infinite_neg_neg {x : ℝ*} : infinite_pos x ↔ infinite_neg (-x) :=
  { mp := infinite_neg_neg_of_infinite_pos,
    mpr := fun (hin : infinite_neg (-x)) => neg_neg x ▸ infinite_pos_neg_of_infinite_neg hin }

theorem infinite_neg_iff_infinite_pos_neg {x : ℝ*} : infinite_neg x ↔ infinite_pos (-x) :=
  { mp := infinite_pos_neg_of_infinite_neg,
    mpr := fun (hin : infinite_pos (-x)) => neg_neg x ▸ infinite_neg_neg_of_infinite_pos hin }

theorem infinite_iff_infinite_neg {x : ℝ*} : infinite x ↔ infinite (-x) := sorry

theorem not_infinite_of_infinitesimal {x : ℝ*} : infinitesimal x → ¬infinite x := sorry

theorem not_infinitesimal_of_infinite {x : ℝ*} : infinite x → ¬infinitesimal x :=
  iff.mp imp_not_comm not_infinite_of_infinitesimal

theorem not_infinitesimal_of_infinite_pos {x : ℝ*} : infinite_pos x → ¬infinitesimal x :=
  fun (hp : infinite_pos x) => not_infinitesimal_of_infinite (Or.inl hp)

theorem not_infinitesimal_of_infinite_neg {x : ℝ*} : infinite_neg x → ¬infinitesimal x :=
  fun (hn : infinite_neg x) => not_infinitesimal_of_infinite (Or.inr hn)

theorem infinite_pos_iff_infinite_and_pos {x : ℝ*} : infinite_pos x ↔ infinite x ∧ 0 < x := sorry

theorem infinite_neg_iff_infinite_and_neg {x : ℝ*} : infinite_neg x ↔ infinite x ∧ x < 0 := sorry

theorem infinite_pos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : infinite_pos x ↔ infinite x :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (infinite_pos x ↔ infinite x))
        (propext infinite_pos_iff_infinite_and_pos)))
    { mp := fun (hI : infinite x ∧ 0 < x) => and.left hI,
      mpr := fun (hI : infinite x) => { left := hI, right := hp } }

theorem infinite_pos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : infinite_pos x ↔ infinite x :=
  sorry

theorem infinite_neg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : infinite_neg x ↔ infinite x :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (infinite_neg x ↔ infinite x))
        (propext infinite_neg_iff_infinite_and_neg)))
    { mp := fun (hI : infinite x ∧ x < 0) => and.left hI,
      mpr := fun (hI : infinite x) => { left := hI, right := hn } }

theorem infinite_pos_abs_iff_infinite_abs {x : ℝ*} : infinite_pos (abs x) ↔ infinite (abs x) :=
  infinite_pos_iff_infinite_of_nonneg (abs_nonneg x)

theorem infinite_iff_infinite_pos_abs {x : ℝ*} : infinite x ↔ infinite_pos (abs x) := sorry

theorem infinite_iff_infinite_abs {x : ℝ*} : infinite x ↔ infinite (abs x) := sorry

theorem infinite_iff_abs_lt_abs {x : ℝ*} : infinite x ↔ ∀ (r : ℝ), abs ↑r < abs x := sorry

theorem infinite_pos_add_not_infinite_neg {x : ℝ*} {y : ℝ*} :
    infinite_pos x → ¬infinite_neg y → infinite_pos (x + y) :=
  sorry

theorem not_infinite_neg_add_infinite_pos {x : ℝ*} {y : ℝ*} :
    ¬infinite_neg x → infinite_pos y → infinite_pos (x + y) :=
  fun (hx : ¬infinite_neg x) (hy : infinite_pos y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite_pos (x + y))) (add_comm x y)))
      (infinite_pos_add_not_infinite_neg hy hx)

theorem infinite_neg_add_not_infinite_pos {x : ℝ*} {y : ℝ*} :
    infinite_neg x → ¬infinite_pos y → infinite_neg (x + y) :=
  sorry

theorem not_infinite_pos_add_infinite_neg {x : ℝ*} {y : ℝ*} :
    ¬infinite_pos x → infinite_neg y → infinite_neg (x + y) :=
  fun (hx : ¬infinite_pos x) (hy : infinite_neg y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite_neg (x + y))) (add_comm x y)))
      (infinite_neg_add_not_infinite_pos hy hx)

theorem infinite_pos_add_infinite_pos {x : ℝ*} {y : ℝ*} :
    infinite_pos x → infinite_pos y → infinite_pos (x + y) :=
  fun (hx : infinite_pos x) (hy : infinite_pos y) =>
    infinite_pos_add_not_infinite_neg hx (not_infinite_neg_of_infinite_pos hy)

theorem infinite_neg_add_infinite_neg {x : ℝ*} {y : ℝ*} :
    infinite_neg x → infinite_neg y → infinite_neg (x + y) :=
  fun (hx : infinite_neg x) (hy : infinite_neg y) =>
    infinite_neg_add_not_infinite_pos hx (not_infinite_pos_of_infinite_neg hy)

theorem infinite_pos_add_not_infinite {x : ℝ*} {y : ℝ*} :
    infinite_pos x → ¬infinite y → infinite_pos (x + y) :=
  fun (hx : infinite_pos x) (hy : ¬infinite y) =>
    infinite_pos_add_not_infinite_neg hx (and.right (iff.mp not_or_distrib hy))

theorem infinite_neg_add_not_infinite {x : ℝ*} {y : ℝ*} :
    infinite_neg x → ¬infinite y → infinite_neg (x + y) :=
  fun (hx : infinite_neg x) (hy : ¬infinite y) =>
    infinite_neg_add_not_infinite_pos hx (and.left (iff.mp not_or_distrib hy))

theorem infinite_pos_of_tendsto_top {f : ℕ → ℝ}
    (hf : filter.tendsto f filter.at_top filter.at_top) : infinite_pos (of_seq f) :=
  sorry

theorem infinite_neg_of_tendsto_bot {f : ℕ → ℝ}
    (hf : filter.tendsto f filter.at_top filter.at_bot) : infinite_neg (of_seq f) :=
  sorry

theorem not_infinite_neg {x : ℝ*} : ¬infinite x → ¬infinite (-x) :=
  iff.mpr not_imp_not (iff.mpr infinite_iff_infinite_neg)

theorem not_infinite_add {x : ℝ*} {y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) :
    ¬infinite (x + y) :=
  sorry

theorem not_infinite_iff_exist_lt_gt {x : ℝ*} :
    ¬infinite x ↔ ∃ (r : ℝ), ∃ (s : ℝ), ↑r < x ∧ x < ↑s :=
  sorry

theorem not_infinite_real (r : ℝ) : ¬infinite ↑r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬infinite ↑r)) (propext not_infinite_iff_exist_lt_gt)))
    (Exists.intro (r - 1)
      (Exists.intro (r + 1)
        { left := iff.mpr coe_lt_coe (sub_one_lt r), right := iff.mpr coe_lt_coe (lt_add_one r) }))

theorem not_real_of_infinite {x : ℝ*} : infinite x → ∀ (r : ℝ), x ≠ ↑r :=
  fun (hi : infinite x) (r : ℝ) (hr : x = ↑r) => not_infinite_real r (hr ▸ hi)

/-!
### Facts about `st` that require some infinite machinery
-/

theorem is_st_mul {x : ℝ*} {y : ℝ*} {r : ℝ} {s : ℝ} (hxr : is_st x r) (hys : is_st y s) :
    is_st (x * y) (r * s) :=
  sorry

--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY

theorem not_infinite_mul {x : ℝ*} {y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) :
    ¬infinite (x * y) :=
  sorry

---

theorem st_add {x : ℝ*} {y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) : st (x + y) = st x + st y :=
  sorry

theorem st_neg (x : ℝ*) : st (-x) = -st x := sorry

theorem st_mul {x : ℝ*} {y : ℝ*} (hx : ¬infinite x) (hy : ¬infinite y) : st (x * y) = st x * st y :=
  sorry

/-!
### Basic lemmas about infinitesimal
-/

theorem infinitesimal_def {x : ℝ*} : infinitesimal x ↔ ∀ (r : ℝ), 0 < r → -↑r < x ∧ x < ↑r := sorry

theorem lt_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ (r : ℝ), 0 < r → x < ↑r :=
  fun (hi : infinitesimal x) (r : ℝ) (hr : 0 < r) => and.right (iff.mp infinitesimal_def hi r hr)

theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ (r : ℝ), 0 < r → -↑r < x :=
  fun (hi : infinitesimal x) (r : ℝ) (hr : 0 < r) => and.left (iff.mp infinitesimal_def hi r hr)

theorem gt_of_neg_of_infinitesimal {x : ℝ*} : infinitesimal x → ∀ (r : ℝ), r < 0 → ↑r < x := sorry

theorem abs_lt_real_iff_infinitesimal {x : ℝ*} :
    infinitesimal x ↔ ∀ (r : ℝ), r ≠ 0 → abs x < abs ↑r :=
  sorry

theorem infinitesimal_zero : infinitesimal 0 := is_st_refl_real 0

theorem zero_of_infinitesimal_real {r : ℝ} : infinitesimal ↑r → r = 0 := eq_of_is_st_real

theorem zero_iff_infinitesimal_real {r : ℝ} : infinitesimal ↑r ↔ r = 0 :=
  { mp := zero_of_infinitesimal_real,
    mpr :=
      fun (hr : r = 0) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (infinitesimal ↑r)) hr)) infinitesimal_zero }

theorem infinitesimal_add {x : ℝ*} {y : ℝ*} (hx : infinitesimal x) (hy : infinitesimal y) :
    infinitesimal (x + y) :=
  sorry

theorem infinitesimal_neg {x : ℝ*} (hx : infinitesimal x) : infinitesimal (-x) := sorry

theorem infinitesimal_neg_iff {x : ℝ*} : infinitesimal x ↔ infinitesimal (-x) :=
  { mp := infinitesimal_neg,
    mpr := fun (h : infinitesimal (-x)) => neg_neg x ▸ infinitesimal_neg h }

theorem infinitesimal_mul {x : ℝ*} {y : ℝ*} (hx : infinitesimal x) (hy : infinitesimal y) :
    infinitesimal (x * y) :=
  sorry

theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} :
    filter.tendsto f filter.at_top (nhds 0) → infinitesimal (of_seq f) :=
  sorry

theorem infinitesimal_epsilon : infinitesimal epsilon :=
  infinitesimal_of_tendsto_zero tendsto_inverse_at_top_nhds_0_nat

theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : infinitesimal x → x ≠ 0 → ∀ (r : ℝ), x ≠ ↑r :=
  fun (hi : infinitesimal x) (hx : x ≠ 0) (r : ℝ) (hr : x = ↑r) =>
    hx (Eq.trans hr (iff.mpr coe_eq_zero (is_st_unique (Eq.symm hr ▸ is_st_refl_real r) hi)))

theorem infinitesimal_sub_is_st {x : ℝ*} {r : ℝ} (hxr : is_st x r) : infinitesimal (x - ↑r) := sorry

theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬infinite x) : infinitesimal (x - ↑(st x)) :=
  infinitesimal_sub_is_st (is_st_st' hx)

theorem infinite_pos_iff_infinitesimal_inv_pos {x : ℝ*} :
    infinite_pos x ↔ infinitesimal (x⁻¹) ∧ 0 < (x⁻¹) :=
  sorry

theorem infinite_neg_iff_infinitesimal_inv_neg {x : ℝ*} :
    infinite_neg x ↔ infinitesimal (x⁻¹) ∧ x⁻¹ < 0 :=
  sorry

theorem infinitesimal_inv_of_infinite {x : ℝ*} : infinite x → infinitesimal (x⁻¹) :=
  fun (hi : infinite x) =>
    or.cases_on hi
      (fun (hip : infinite_pos x) => and.left (iff.mp infinite_pos_iff_infinitesimal_inv_pos hip))
      fun (hin : infinite_neg x) => and.left (iff.mp infinite_neg_iff_infinitesimal_inv_neg hin)

theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : infinitesimal (x⁻¹)) :
    infinite x :=
  sorry

theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : infinite x ↔ infinitesimal (x⁻¹) :=
  { mp := infinitesimal_inv_of_infinite, mpr := infinite_of_infinitesimal_inv h0 }

theorem infinitesimal_pos_iff_infinite_pos_inv {x : ℝ*} :
    infinite_pos (x⁻¹) ↔ infinitesimal x ∧ 0 < x :=
  sorry

theorem infinitesimal_neg_iff_infinite_neg_inv {x : ℝ*} :
    infinite_neg (x⁻¹) ↔ infinitesimal x ∧ x < 0 :=
  sorry

theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : infinitesimal x ↔ infinite (x⁻¹) :=
  sorry

/-!
### `st` stuff that requires infinitesimal machinery
-/

theorem is_st_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : filter.tendsto f filter.at_top (nhds r)) :
    is_st (of_seq f) r :=
  sorry

theorem is_st_inv {x : ℝ*} {r : ℝ} (hi : ¬infinitesimal x) : is_st x r → is_st (x⁻¹) (r⁻¹) := sorry

theorem st_inv (x : ℝ*) : st (x⁻¹) = (st x⁻¹) := sorry

/-!
### Infinite stuff that requires infinitesimal machinery
-/

theorem infinite_pos_omega : infinite_pos omega :=
  iff.mpr infinite_pos_iff_infinitesimal_inv_pos
    { left := infinitesimal_epsilon, right := epsilon_pos }

theorem infinite_omega : infinite omega :=
  iff.mpr (infinite_iff_infinitesimal_inv omega_ne_zero) infinitesimal_epsilon

theorem infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos {x : ℝ*} {y : ℝ*} :
    infinite_pos x → ¬infinitesimal y → 0 < y → infinite_pos (x * y) :=
  sorry

theorem infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos {x : ℝ*} {y : ℝ*} :
    ¬infinitesimal x → 0 < x → infinite_pos y → infinite_pos (x * y) :=
  fun (hx : ¬infinitesimal x) (hp : 0 < x) (hy : infinite_pos y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite_pos (x * y))) (mul_comm x y)))
      (infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp)

theorem infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg {x : ℝ*} {y : ℝ*} :
    infinite_neg x → ¬infinitesimal y → y < 0 → infinite_pos (x * y) :=
  sorry

theorem infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg {x : ℝ*} {y : ℝ*} :
    ¬infinitesimal x → x < 0 → infinite_neg y → infinite_pos (x * y) :=
  fun (hx : ¬infinitesimal x) (hp : x < 0) (hy : infinite_neg y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite_pos (x * y))) (mul_comm x y)))
      (infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp)

theorem infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg {x : ℝ*} {y : ℝ*} :
    infinite_pos x → ¬infinitesimal y → y < 0 → infinite_neg (x * y) :=
  sorry

theorem infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos {x : ℝ*} {y : ℝ*} :
    ¬infinitesimal x → x < 0 → infinite_pos y → infinite_neg (x * y) :=
  fun (hx : ¬infinitesimal x) (hp : x < 0) (hy : infinite_pos y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite_neg (x * y))) (mul_comm x y)))
      (infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp)

theorem infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos {x : ℝ*} {y : ℝ*} :
    infinite_neg x → ¬infinitesimal y → 0 < y → infinite_neg (x * y) :=
  sorry

theorem infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg {x : ℝ*} {y : ℝ*} :
    ¬infinitesimal x → 0 < x → infinite_neg y → infinite_neg (x * y) :=
  fun (hx : ¬infinitesimal x) (hp : 0 < x) (hy : infinite_neg y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite_neg (x * y))) (mul_comm x y)))
      (infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp)

theorem infinite_pos_mul_infinite_pos {x : ℝ*} {y : ℝ*} :
    infinite_pos x → infinite_pos y → infinite_pos (x * y) :=
  fun (hx : infinite_pos x) (hy : infinite_pos y) =>
    infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy)
      (hy 0)

theorem infinite_neg_mul_infinite_neg {x : ℝ*} {y : ℝ*} :
    infinite_neg x → infinite_neg y → infinite_pos (x * y) :=
  fun (hx : infinite_neg x) (hy : infinite_neg y) =>
    infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy)
      (hy 0)

theorem infinite_pos_mul_infinite_neg {x : ℝ*} {y : ℝ*} :
    infinite_pos x → infinite_neg y → infinite_neg (x * y) :=
  fun (hx : infinite_pos x) (hy : infinite_neg y) =>
    infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hx (not_infinitesimal_of_infinite_neg hy)
      (hy 0)

theorem infinite_neg_mul_infinite_pos {x : ℝ*} {y : ℝ*} :
    infinite_neg x → infinite_pos y → infinite_neg (x * y) :=
  fun (hx : infinite_neg x) (hy : infinite_pos y) =>
    infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hx (not_infinitesimal_of_infinite_pos hy)
      (hy 0)

theorem infinite_mul_of_infinite_not_infinitesimal {x : ℝ*} {y : ℝ*} :
    infinite x → ¬infinitesimal y → infinite (x * y) :=
  sorry

theorem infinite_mul_of_not_infinitesimal_infinite {x : ℝ*} {y : ℝ*} :
    ¬infinitesimal x → infinite y → infinite (x * y) :=
  fun (hx : ¬infinitesimal x) (hy : infinite y) =>
    eq.mpr (id (Eq._oldrec (Eq.refl (infinite (x * y))) (mul_comm x y)))
      (infinite_mul_of_infinite_not_infinitesimal hy hx)

theorem infinite_mul_infinite {x : ℝ*} {y : ℝ*} : infinite x → infinite y → infinite (x * y) :=
  fun (hx : infinite x) (hy : infinite y) =>
    infinite_mul_of_infinite_not_infinitesimal hx (not_infinitesimal_of_infinite hy)

end Mathlib