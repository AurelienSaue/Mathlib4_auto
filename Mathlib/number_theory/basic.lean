/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.geom_sum
import Mathlib.ring_theory.ideal.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

theorem dvd_sub_pow_of_dvd_sub {R : Type u_1} [comm_ring R] {p : ℕ} {a : R} {b : R} (h : ↑p ∣ a - b) (k : ℕ) : ↑p ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k := sorry

