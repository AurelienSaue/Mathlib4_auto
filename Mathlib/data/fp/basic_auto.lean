/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.rat.default
import Mathlib.data.semiquot
import PostPort

universes l u_1 

namespace Mathlib

/-!
# Implementation of floating-point numbers (experimental).
-/

def int.shift2 (a : ℕ) (b : ℕ) : ℤ → ℕ × ℕ :=
  sorry

namespace fp


structure rmode 
  NE ::
where

class float_cfg 
where
  prec : ℕ
  emax : ℕ
  prec_pos : 0 < prec
  prec_max : prec ≤ emax

def prec [C : float_cfg] : ℕ :=
  float_cfg.prec

def emax [C : float_cfg] : ℕ :=
  float_cfg.emax

def emin [C : float_cfg] : ℤ :=
  1 - ↑float_cfg.emax

def valid_finite [C : float_cfg] (e : ℤ) (m : ℕ)  :=
  emin ≤ e + ↑prec - 1 ∧ e + ↑prec - 1 ≤ ↑emax ∧ e = max (e + ↑(nat.size m) - ↑prec) emin

protected instance dec_valid_finite [C : float_cfg] (e : ℤ) (m : ℕ) : Decidable (valid_finite e m) :=
  eq.mpr sorry and.decidable

inductive float [C : float_cfg] 
where
| inf : Bool → float
| nan : float
| finite : Bool → (e : ℤ) → (m : ℕ) → valid_finite e m → float

def float.is_finite [C : float_cfg] : float → Bool :=
  sorry

def to_rat [C : float_cfg] (f : float) : ↥(float.is_finite f) → ℚ :=
  sorry

theorem float.zero.valid [C : float_cfg] : valid_finite emin 0 := sorry

def float.zero [C : float_cfg] (s : Bool) : float :=
  float.finite s emin 0 sorry

protected instance float.inhabited [C : float_cfg] : Inhabited float :=
  { default := float.zero tt }

protected def float.sign' [C : float_cfg] : float → semiquot Bool :=
  sorry

protected def float.sign [C : float_cfg] : float → Bool :=
  sorry

protected def float.is_zero [C : float_cfg] : float → Bool :=
  sorry

protected def float.neg [C : float_cfg] : float → float :=
  sorry

def div_nat_lt_two_pow [C : float_cfg] (n : ℕ) (d : ℕ) : ℤ → Bool :=
  sorry

-- TODO(Mario): Prove these and drop 'meta'

namespace float


protected instance has_neg [C : float_cfg] : Neg float :=
  { neg := float.neg }

