/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

Definitions and properties of gcd, lcm, and coprime.
-/
import PrePort
import Lean3Lib.init.data.nat.lemmas
import Lean3Lib.init.meta.well_founded_tactics
import PostPort

namespace Mathlib

namespace nat


/- gcd -/

def gcd : ℕ → ℕ → ℕ :=
  sorry

@[simp] theorem gcd_zero_left (x : ℕ) : gcd 0 x = x := sorry

@[simp] theorem gcd_succ (x : ℕ) (y : ℕ) : gcd (Nat.succ x) y = gcd (y % Nat.succ x) (Nat.succ x) := sorry

@[simp] theorem gcd_one_left (n : ℕ) : gcd 1 n = 1 := sorry

theorem gcd_def (x : ℕ) (y : ℕ) : gcd x y = ite (x = 0) y (gcd (y % x) x) := sorry

@[simp] theorem gcd_self (n : ℕ) : gcd n n = n := sorry

@[simp] theorem gcd_zero_right (n : ℕ) : gcd n 0 = n := sorry

theorem gcd_rec (m : ℕ) (n : ℕ) : gcd m n = gcd (n % m) m := sorry

theorem gcd.induction {P : ℕ → ℕ → Prop} (m : ℕ) (n : ℕ) (H0 : ∀ (n : ℕ), P 0 n) (H1 : ∀ (m n : ℕ), 0 < m → P (n % m) m → P m n) : P m n := sorry

def lcm (m : ℕ) (n : ℕ) : ℕ :=
  m * n / gcd m n

def coprime (m : ℕ) (n : ℕ)  :=
  gcd m n = 1

