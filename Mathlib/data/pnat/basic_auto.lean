/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Neil Strickland
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# The positive natural numbers

This file defines the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
-/

/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def pnat := Subtype fun (n : ℕ) => 0 < n

notation:1024 "ℕ+" => Mathlib.pnat

protected instance coe_pnat_nat : has_coe ℕ+ ℕ := has_coe.mk subtype.val

protected instance pnat.has_repr : has_repr ℕ+ := has_repr.mk fun (n : ℕ+) => repr (subtype.val n)

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def pnat.nat_pred (i : ℕ+) : ℕ := ↑i - 1

namespace nat


/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def to_pnat (n : ℕ)
    (h :
      autoParam (0 < n)
        (Lean.Syntax.ident Lean.SourceInfo.none
          (String.toSubstring "Mathlib.tactic.exact_dec_trivial")
          (Lean.Name.mkStr
            (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic")
            "exact_dec_trivial")
          [])) :
    ℕ+ :=
  { val := n, property := h }

/-- Write a successor as an element of `ℕ+`. -/
def succ_pnat (n : ℕ) : ℕ+ := { val := Nat.succ n, property := succ_pos n }

@[simp] theorem succ_pnat_coe (n : ℕ) : ↑(succ_pnat n) = Nat.succ n := rfl

theorem succ_pnat_inj {n : ℕ} {m : ℕ} : succ_pnat n = succ_pnat m → n = m :=
  fun (h : succ_pnat n = succ_pnat m) =>
    let h' : ↑(succ_pnat n) = ↑(succ_pnat m) := congr_arg coe h;
    succ.inj h'

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def to_pnat' (n : ℕ) : ℕ+ := succ_pnat (Nat.pred n)

@[simp] theorem to_pnat'_coe (n : ℕ) : ↑(to_pnat' n) = ite (0 < n) n 1 := sorry

end nat


namespace pnat


/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
protected instance decidable_eq : DecidableEq ℕ+ := fun (a b : ℕ+) => subtype.decidable_eq a b

protected instance linear_order : linear_order ℕ+ := subtype.linear_order fun (n : ℕ) => 0 < n

@[simp] theorem mk_le_mk (n : ℕ) (k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    { val := n, property := hn } ≤ { val := k, property := hk } ↔ n ≤ k :=
  iff.rfl

@[simp] theorem mk_lt_mk (n : ℕ) (k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    { val := n, property := hn } < { val := k, property := hk } ↔ n < k :=
  iff.rfl

@[simp] theorem coe_le_coe (n : ℕ+) (k : ℕ+) : ↑n ≤ ↑k ↔ n ≤ k := iff.rfl

@[simp] theorem coe_lt_coe (n : ℕ+) (k : ℕ+) : ↑n < ↑k ↔ n < k := iff.rfl

@[simp] theorem pos (n : ℕ+) : 0 < ↑n := subtype.property n

theorem eq {m : ℕ+} {n : ℕ+} : ↑m = ↑n → m = n := subtype.eq

@[simp] theorem coe_inj {m : ℕ+} {n : ℕ+} : ↑m = ↑n ↔ m = n := set_coe.ext_iff

@[simp] theorem mk_coe (n : ℕ) (h : 0 < n) : ↑{ val := n, property := h } = n := rfl

protected instance add_comm_semigroup : add_comm_semigroup ℕ+ :=
  add_comm_semigroup.mk (fun (a b : ℕ+) => { val := ↑a + ↑b, property := sorry }) sorry sorry

@[simp] theorem add_coe (m : ℕ+) (n : ℕ+) : ↑(m + n) = ↑m + ↑n := rfl

protected instance coe_add_hom : is_add_hom coe := is_add_hom.mk add_coe

protected instance add_left_cancel_semigroup : add_left_cancel_semigroup ℕ+ :=
  add_left_cancel_semigroup.mk add_comm_semigroup.add add_comm_semigroup.add_assoc sorry

protected instance add_right_cancel_semigroup : add_right_cancel_semigroup ℕ+ :=
  add_right_cancel_semigroup.mk add_comm_semigroup.add add_comm_semigroup.add_assoc sorry

@[simp] theorem ne_zero (n : ℕ+) : ↑n ≠ 0 := ne_of_gt (subtype.property n)

theorem to_pnat'_coe {n : ℕ} : 0 < n → ↑(nat.to_pnat' n) = n := nat.succ_pred_eq_of_pos

@[simp] theorem coe_to_pnat' (n : ℕ+) : nat.to_pnat' ↑n = n := eq (to_pnat'_coe (pos n))

protected instance comm_monoid : comm_monoid ℕ+ :=
  comm_monoid.mk (fun (m n : ℕ+) => { val := subtype.val m * subtype.val n, property := sorry })
    sorry (nat.succ_pnat 0) sorry sorry sorry

theorem lt_add_one_iff {a : ℕ+} {b : ℕ+} : a < b + 1 ↔ a ≤ b := nat.lt_add_one_iff

theorem add_one_le_iff {a : ℕ+} {b : ℕ+} : a + 1 ≤ b ↔ a < b := nat.add_one_le_iff

@[simp] theorem one_le (n : ℕ+) : 1 ≤ n := subtype.property n

protected instance order_bot : order_bot ℕ+ :=
  order_bot.mk 1 partial_order.le partial_order.lt sorry sorry sorry sorry

@[simp] theorem bot_eq_zero : ⊥ = 1 := rfl

protected instance inhabited : Inhabited ℕ+ := { default := 1 }

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.

@[simp] theorem mk_one {h : 0 < 1} : { val := 1, property := h } = 1 := rfl

@[simp] theorem mk_bit0 (n : ℕ) {h : 0 < bit0 n} :
    { val := bit0 n, property := h } = bit0 { val := n, property := nat.pos_of_bit0_pos h } :=
  rfl

@[simp] theorem mk_bit1 (n : ℕ) {h : 0 < bit1 n} {k : 0 < n} :
    { val := bit1 n, property := h } = bit1 { val := n, property := k } :=
  rfl

-- Some lemmas that rewrite inequalities between explicit numerals in `pnat`

-- into the corresponding inequalities in `nat`.

-- TODO: perhaps this should not be attempted by `simp`,

-- and instead we should expect `norm_num` to take care of these directly?

-- TODO: these lemmas are perhaps incomplete:

-- * 1 is not represented as a bit0 or bit1

-- * strict inequalities?

@[simp] theorem bit0_le_bit0 (n : ℕ+) (m : ℕ+) : bit0 n ≤ bit0 m ↔ bit0 ↑n ≤ bit0 ↑m := iff.rfl

@[simp] theorem bit0_le_bit1 (n : ℕ+) (m : ℕ+) : bit0 n ≤ bit1 m ↔ bit0 ↑n ≤ bit1 ↑m := iff.rfl

@[simp] theorem bit1_le_bit0 (n : ℕ+) (m : ℕ+) : bit1 n ≤ bit0 m ↔ bit1 ↑n ≤ bit0 ↑m := iff.rfl

@[simp] theorem bit1_le_bit1 (n : ℕ+) (m : ℕ+) : bit1 n ≤ bit1 m ↔ bit1 ↑n ≤ bit1 ↑m := iff.rfl

@[simp] theorem one_coe : ↑1 = 1 := rfl

@[simp] theorem mul_coe (m : ℕ+) (n : ℕ+) : ↑(m * n) = ↑m * ↑n := rfl

protected instance coe_mul_hom : is_monoid_hom coe := is_monoid_hom.mk one_coe

@[simp] theorem coe_eq_one_iff {m : ℕ+} : ↑m = 1 ↔ m = 1 := sorry

@[simp] theorem coe_bit0 (a : ℕ+) : ↑(bit0 a) = bit0 ↑a := rfl

@[simp] theorem coe_bit1 (a : ℕ+) : ↑(bit1 a) = bit1 ↑a := rfl

@[simp] theorem pow_coe (m : ℕ+) (n : ℕ) : ↑(m ^ n) = ↑m ^ n := sorry

protected instance left_cancel_semigroup : left_cancel_semigroup ℕ+ :=
  left_cancel_semigroup.mk comm_monoid.mul comm_monoid.mul_assoc sorry

protected instance right_cancel_semigroup : right_cancel_semigroup ℕ+ :=
  right_cancel_semigroup.mk comm_monoid.mul comm_monoid.mul_assoc sorry

protected instance ordered_cancel_comm_monoid : ordered_cancel_comm_monoid ℕ+ :=
  ordered_cancel_comm_monoid.mk left_cancel_semigroup.mul left_cancel_semigroup.mul_assoc
    left_cancel_semigroup.mul_left_cancel comm_monoid.one comm_monoid.one_mul comm_monoid.mul_one
    comm_monoid.mul_comm right_cancel_semigroup.mul_right_cancel linear_order.le linear_order.lt
    linear_order.le_refl linear_order.le_trans linear_order.le_antisymm sorry sorry

protected instance distrib : distrib ℕ+ :=
  distrib.mk comm_monoid.mul add_comm_semigroup.add sorry sorry

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
protected instance has_sub : Sub ℕ+ := { sub := fun (a b : ℕ+) => nat.to_pnat' (↑a - ↑b) }

theorem sub_coe (a : ℕ+) (b : ℕ+) : ↑(a - b) = ite (b < a) (↑a - ↑b) 1 := sorry

theorem add_sub_of_lt {a : ℕ+} {b : ℕ+} : a < b → a + (b - a) = b := sorry

protected instance has_well_founded : has_well_founded ℕ+ := has_well_founded.mk Less sorry

/-- Strong induction on `pnat`. -/
theorem strong_induction_on {p : ℕ+ → Prop} (n : ℕ+)
    (h : ∀ (k : ℕ+), (∀ (m : ℕ+), m < k → p m) → p k) : p n :=
  sorry

/-- If `(n : pnat)` is different from `1`, then it is the successor of some `(k : pnat)`. -/
theorem exists_eq_succ_of_ne_one {n : ℕ+} (h1 : n ≠ 1) : ∃ (k : ℕ+), n = k + 1 := sorry

theorem case_strong_induction_on {p : ℕ+ → Prop} (a : ℕ+) (hz : p 1)
    (hi : ∀ (n : ℕ+), (∀ (m : ℕ+), m ≤ n → p m) → p (n + 1)) : p a :=
  sorry

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div_aux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ := sorry

theorem mod_div_aux_spec (k : ℕ+) (r : ℕ) (q : ℕ) (h : ¬(r = 0 ∧ q = 0)) :
    ↑(prod.fst (mod_div_aux k r q)) + ↑k * prod.snd (mod_div_aux k r q) = r + ↑k * q :=
  sorry

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def mod_div (m : ℕ+) (k : ℕ+) : ℕ+ × ℕ := mod_div_aux k (↑m % ↑k) (↑m / ↑k)

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m : ℕ+) (k : ℕ+) : ℕ+ := prod.fst (mod_div m k)

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m : ℕ+) (k : ℕ+) : ℕ := prod.snd (mod_div m k)

theorem mod_add_div (m : ℕ+) (k : ℕ+) : ↑(mod m k) + ↑k * div m k = ↑m := sorry

theorem div_add_mod (m : ℕ+) (k : ℕ+) : ↑k * div m k + ↑(mod m k) = ↑m :=
  Eq.trans (add_comm (↑k * div m k) ↑(mod m k)) (mod_add_div m k)

theorem mod_coe (m : ℕ+) (k : ℕ+) : ↑(mod m k) = ite (↑m % ↑k = 0) (↑k) (↑m % ↑k) := sorry

theorem div_coe (m : ℕ+) (k : ℕ+) : div m k = ite (↑m % ↑k = 0) (Nat.pred (↑m / ↑k)) (↑m / ↑k) :=
  sorry

theorem mod_le (m : ℕ+) (k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k := sorry

theorem dvd_iff {k : ℕ+} {m : ℕ+} : k ∣ m ↔ ↑k ∣ ↑m := sorry

theorem dvd_iff' {k : ℕ+} {m : ℕ+} : k ∣ m ↔ mod m k = k := sorry

theorem le_of_dvd {m : ℕ+} {n : ℕ+} : m ∣ n → m ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m ∣ n → m ≤ n)) (propext dvd_iff')))
    fun (h : mod n m = m) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (m ≤ n)) (Eq.symm h))) (and.left (mod_le n m))

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def div_exact (m : ℕ+) (k : ℕ+) : ℕ+ := { val := Nat.succ (div m k), property := sorry }

theorem mul_div_exact {m : ℕ+} {k : ℕ+} (h : k ∣ m) : k * div_exact m k = m := sorry

theorem dvd_antisymm {m : ℕ+} {n : ℕ+} : m ∣ n → n ∣ m → m = n :=
  fun (hmn : m ∣ n) (hnm : n ∣ m) => le_antisymm (le_of_dvd hmn) (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  { mp := fun (h : n ∣ 1) => dvd_antisymm h (one_dvd n),
    mpr := fun (h : n = 1) => Eq.symm h ▸ dvd_refl 1 }

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ ↑n) : 0 < a :=
  iff.mpr pos_iff_ne_zero
    (id
      fun (hzero : a = 0) =>
        ne_zero n (eq_zero_of_zero_dvd (eq.mp (Eq._oldrec (Eq.refl (a ∣ ↑n)) hzero) h)))

end Mathlib