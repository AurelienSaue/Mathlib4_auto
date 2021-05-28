/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.prime
import Mathlib.data.int.basic
import Mathlib.PostPort

namespace Mathlib

/-!
# Lemmas about nat.prime using `int`s
-/

namespace int


theorem not_prime_of_int_mul {a : ℤ} {b : ℤ} {c : ℕ} (ha : 1 < nat_abs a) (hb : 1 < nat_abs b) (hc : a * b = ↑c) : ¬nat.prime c :=
  nat.not_prime_mul' (nat_abs_mul_nat_abs_eq hc) ha hb

