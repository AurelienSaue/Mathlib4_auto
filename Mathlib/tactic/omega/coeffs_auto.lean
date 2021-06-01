/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.func
import Mathlib.tactic.ring
import Mathlib.tactic.omega.misc
import Mathlib.PostPort

namespace Mathlib

/-
Non-constant terms of linear constraints are represented
by storing their coefficients in integer lists.
-/

namespace omega


namespace coeffs


/-- `val_between v as l o` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping all
    subterms that include variables outside the range `[l,l+o)` -/
@[simp] def val_between (v : ℕ → ℤ) (as : List ℤ) (l : ℕ) : ℕ → ℤ := sorry

@[simp] theorem val_between_nil {v : ℕ → ℤ} {l : ℕ} (m : ℕ) : val_between v [] l m = 0 := sorry

/-- Evaluation of the nonconstant component of a normalized linear arithmetic term. -/
def val (v : ℕ → ℤ) (as : List ℤ) : ℤ := val_between v as 0 (list.length as)

@[simp] theorem val_nil {v : ℕ → ℤ} : val v [] = 0 := rfl

theorem val_between_eq_of_le {v : ℕ → ℤ} {as : List ℤ} {l : ℕ} (m : ℕ) :
    list.length as ≤ l + m → val_between v as l m = val_between v as l (list.length as - l) :=
  sorry

theorem val_eq_of_le {v : ℕ → ℤ} {as : List ℤ} {k : ℕ} :
    list.length as ≤ k → val v as = val_between v as 0 k :=
  sorry

theorem val_between_eq_val_between {v : ℕ → ℤ} {w : ℕ → ℤ} {as : List ℤ} {bs : List ℤ} {l : ℕ}
    {m : ℕ} :
    (∀ (x : ℕ), l ≤ x → x < l + m → v x = w x) →
        (∀ (x : ℕ), l ≤ x → x < l + m → list.func.get x as = list.func.get x bs) →
          val_between v as l m = val_between w bs l m :=
  sorry

theorem val_between_set {v : ℕ → ℤ} {a : ℤ} {l : ℕ} {n : ℕ} {m : ℕ} :
    l ≤ n → n < l + m → val_between v (list.func.set a [] n) l m = a * v n :=
  sorry

@[simp] theorem val_set {v : ℕ → ℤ} {m : ℕ} {a : ℤ} : val v (list.func.set a [] m) = a * v m :=
  sorry

theorem val_between_neg {v : ℕ → ℤ} {as : List ℤ} {l : ℕ} {o : ℕ} :
    val_between v (list.func.neg as) l o = -val_between v as l o :=
  sorry

@[simp] theorem val_neg {v : ℕ → ℤ} {as : List ℤ} : val v (list.func.neg as) = -val v as := sorry

theorem val_between_add {v : ℕ → ℤ} {is : List ℤ} {js : List ℤ} {l : ℕ} (m : ℕ) :
    val_between v (list.func.add is js) l m = val_between v is l m + val_between v js l m :=
  sorry

@[simp] theorem val_add {v : ℕ → ℤ} {is : List ℤ} {js : List ℤ} :
    val v (list.func.add is js) = val v is + val v js :=
  sorry

theorem val_between_sub {v : ℕ → ℤ} {is : List ℤ} {js : List ℤ} {l : ℕ} (m : ℕ) :
    val_between v (list.func.sub is js) l m = val_between v is l m - val_between v js l m :=
  sorry

@[simp] theorem val_sub {v : ℕ → ℤ} {is : List ℤ} {js : List ℤ} :
    val v (list.func.sub is js) = val v is - val v js :=
  sorry

/-- `val_except k v as` is the value (under valuation `v`) of the term
    obtained taking the term represented by `(0, as)` and dropping the
    subterm that includes the `k`th variable. -/
def val_except (k : ℕ) (v : ℕ → ℤ) (as : List ℤ) : ℤ :=
  val_between v as 0 k + val_between v as (k + 1) (list.length as - (k + 1))

theorem val_except_eq_val_except {k : ℕ} {is : List ℤ} {js : List ℤ} {v : ℕ → ℤ} {w : ℕ → ℤ} :
    (∀ (x : ℕ), x ≠ k → v x = w x) →
        (∀ (x : ℕ), x ≠ k → list.func.get x is = list.func.get x js) →
          val_except k v is = val_except k w js :=
  sorry

theorem val_except_update_set {v : ℕ → ℤ} {n : ℕ} {as : List ℤ} {i : ℤ} {j : ℤ} :
    val_except n (update n i v) (list.func.set j as n) = val_except n v as :=
  val_except_eq_val_except update_eq_of_ne (list.func.get_set_eq_of_ne n)

theorem val_between_add_val_between {v : ℕ → ℤ} {as : List ℤ} {l : ℕ} {m : ℕ} {n : ℕ} :
    val_between v as l m + val_between v as (l + m) n = val_between v as l (m + n) :=
  sorry

theorem val_except_add_eq {v : ℕ → ℤ} (n : ℕ) {as : List ℤ} :
    val_except n v as + list.func.get n as * v n = val v as :=
  sorry

@[simp] theorem val_between_map_mul {v : ℕ → ℤ} {i : ℤ} {as : List ℤ} {l : ℕ} {m : ℕ} :
    val_between v (list.map (Mul.mul i) as) l m = i * val_between v as l m :=
  sorry

theorem forall_val_dvd_of_forall_mem_dvd {i : ℤ} {as : List ℤ} :
    (∀ (x : ℤ), x ∈ as → i ∣ x) → ∀ (n : ℕ), i ∣ list.func.get n as :=
  fun (ᾰ : ∀ (x : ℤ), x ∈ as → i ∣ x) (n : ℕ) =>
    idRhs ((fun (x : ℤ) => i ∣ x) (list.func.get n as))
      (list.func.forall_val_of_forall_mem (dvd_zero i) ᾰ n)

theorem dvd_val_between {v : ℕ → ℤ} {i : ℤ} {as : List ℤ} {l : ℕ} {m : ℕ} :
    (∀ (x : ℤ), x ∈ as → i ∣ x) → i ∣ val_between v as l m :=
  sorry

theorem dvd_val {v : ℕ → ℤ} {as : List ℤ} {i : ℤ} : (∀ (x : ℤ), x ∈ as → i ∣ x) → i ∣ val v as :=
  dvd_val_between

@[simp] theorem val_between_map_div {v : ℕ → ℤ} {as : List ℤ} {i : ℤ} {l : ℕ}
    (h1 : ∀ (x : ℤ), x ∈ as → i ∣ x) {m : ℕ} :
    val_between v (list.map (fun (x : ℤ) => x / i) as) l m = val_between v as l m / i :=
  sorry

@[simp] theorem val_map_div {v : ℕ → ℤ} {as : List ℤ} {i : ℤ} :
    (∀ (x : ℤ), x ∈ as → i ∣ x) → val v (list.map (fun (x : ℤ) => x / i) as) = val v as / i :=
  sorry

theorem val_between_eq_zero {v : ℕ → ℤ} {is : List ℤ} {l : ℕ} {m : ℕ} :
    (∀ (x : ℤ), x ∈ is → x = 0) → val_between v is l m = 0 :=
  sorry

theorem val_eq_zero {v : ℕ → ℤ} {is : List ℤ} : (∀ (x : ℤ), x ∈ is → x = 0) → val v is = 0 :=
  val_between_eq_zero

end Mathlib