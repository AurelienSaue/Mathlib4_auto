/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.wf
import Lean3Lib.init.data.nat.basic
import PostPort

namespace Mathlib

namespace nat


protected def div (x : ℕ) : ℕ → ℕ :=
  well_founded.fix lt_wf div.F

protected instance has_div : Div ℕ :=
  { div := nat.div }

theorem div_def_aux (x : ℕ) (y : ℕ) : x / y = dite (0 < y ∧ y ≤ x) (fun (h : 0 < y ∧ y ≤ x) => (x - y) / y + 1) fun (h : ¬(0 < y ∧ y ≤ x)) => 0 :=
  congr_fun (well_founded.fix_eq lt_wf div.F x) y

protected def mod (x : ℕ) : ℕ → ℕ :=
  well_founded.fix lt_wf mod.F

protected instance has_mod : Mod ℕ :=
  { mod := nat.mod }

theorem mod_def_aux (x : ℕ) (y : ℕ) : x % y = dite (0 < y ∧ y ≤ x) (fun (h : 0 < y ∧ y ≤ x) => (x - y) % y) fun (h : ¬(0 < y ∧ y ≤ x)) => x :=
  congr_fun (well_founded.fix_eq lt_wf mod.F x) y

