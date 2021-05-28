/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.bitvec.core
import Mathlib.data.fin
import Mathlib.tactic.norm_num
import Mathlib.tactic.monotonicity.default
import Mathlib.PostPort

namespace Mathlib

namespace bitvec


protected instance preorder (n : ℕ) : preorder (bitvec n) :=
  preorder.lift bitvec.to_nat

/-- convert `fin` to `bitvec` -/
def of_fin {n : ℕ} (i : fin (bit0 1 ^ n)) : bitvec n :=
  bitvec.of_nat n (subtype.val i)

theorem of_fin_val {n : ℕ} (i : fin (bit0 1 ^ n)) : bitvec.to_nat (of_fin i) = subtype.val i := sorry

/-- convert `bitvec` to `fin` -/
def to_fin {n : ℕ} (i : bitvec n) : fin (bit0 1 ^ n) :=
  fin.of_nat' (bitvec.to_nat i)

theorem add_lsb_eq_twice_add_one {x : ℕ} {b : Bool} : add_lsb x b = bit0 1 * x + cond b 1 0 := sorry

theorem to_nat_eq_foldr_reverse {n : ℕ} (v : bitvec n) : bitvec.to_nat v = list.foldr (flip add_lsb) 0 (list.reverse (vector.to_list v)) := sorry

theorem to_nat_lt {n : ℕ} (v : bitvec n) : bitvec.to_nat v < bit0 1 ^ n := sorry

theorem add_lsb_div_two {x : ℕ} {b : Bool} : add_lsb x b / bit0 1 = x := sorry

theorem to_bool_add_lsb_mod_two {x : ℕ} {b : Bool} : to_bool (add_lsb x b % bit0 1 = 1) = b := sorry

theorem of_nat_to_nat {n : ℕ} (v : bitvec n) : bitvec.of_nat n (bitvec.to_nat v) = v := sorry

theorem to_fin_val {n : ℕ} (v : bitvec n) : ↑(to_fin v) = bitvec.to_nat v := sorry

theorem to_fin_le_to_fin_of_le {n : ℕ} {v₀ : bitvec n} {v₁ : bitvec n} (h : v₀ ≤ v₁) : to_fin v₀ ≤ to_fin v₁ :=
  (fun (this : ↑(to_fin v₀) ≤ ↑(to_fin v₁)) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (↑(to_fin v₀) ≤ ↑(to_fin v₁))) (to_fin_val v₀)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (bitvec.to_nat v₀ ≤ ↑(to_fin v₁))) (to_fin_val v₁))) h))

theorem of_fin_le_of_fin_of_le {n : ℕ} {i : fin (bit0 1 ^ n)} {j : fin (bit0 1 ^ n)} (h : i ≤ j) : of_fin i ≤ of_fin j := sorry

theorem to_fin_of_fin {n : ℕ} (i : fin (bit0 1 ^ n)) : to_fin (of_fin i) = i := sorry

theorem of_fin_to_fin {n : ℕ} (v : bitvec n) : of_fin (to_fin v) = v :=
  id
    (eq.mpr (id (Eq._oldrec (Eq.refl (bitvec.of_nat n ↑(to_fin v) = v)) (to_fin_val v)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (bitvec.of_nat n (bitvec.to_nat v) = v)) (of_nat_to_nat v))) (Eq.refl v)))

