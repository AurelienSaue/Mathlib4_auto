/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.big_operators.basic
import Mathlib.data.nat.enat
import PostPort

universes u_1 

namespace Mathlib

/-!
# Big operators in `enat`

A simple lemma about sums in `enat`.
-/

namespace finset


theorem sum_nat_coe_enat {α : Type u_1} (s : finset α) (f : α → ℕ) : (finset.sum s fun (x : α) => ↑(f x)) = ↑(finset.sum s fun (x : α) => f x) :=
  Eq.symm (add_monoid_hom.map_sum enat.coe_hom (fun (x : α) => f x) s)

