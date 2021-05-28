/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.default
import Mathlib.data.set.finite
import Mathlib.data.pnat.intervals
import Mathlib.PostPort

namespace Mathlib

/-!
# fintype instances for intervals

We provide `fintype` instances for `Ico l u`, for `l u : ℕ`, and for `l u : ℤ`.
-/

namespace set


protected instance Ico_ℕ_fintype (l : ℕ) (u : ℕ) : fintype ↥(Ico l u) :=
  fintype.of_finset (finset.Ico l u) sorry

@[simp] theorem Ico_ℕ_card (l : ℕ) (u : ℕ) : fintype.card ↥(Ico l u) = u - l :=
  Eq.trans (fintype.card_of_finset (finset.Ico l u) (Ico_ℕ_fintype._proof_1 l u)) (finset.Ico.card l u)

protected instance Ico_pnat_fintype (l : ℕ+) (u : ℕ+) : fintype ↥(Ico l u) :=
  fintype.of_finset (pnat.Ico l u) sorry

@[simp] theorem Ico_pnat_card (l : ℕ+) (u : ℕ+) : fintype.card ↥(Ico l u) = ↑u - ↑l :=
  Eq.trans (fintype.card_of_finset (pnat.Ico l u) (Ico_pnat_fintype._proof_1 l u)) (pnat.Ico.card l u)

protected instance Ico_ℤ_fintype (l : ℤ) (u : ℤ) : fintype ↥(Ico l u) :=
  fintype.of_finset (finset.Ico_ℤ l u) sorry

@[simp] theorem Ico_ℤ_card (l : ℤ) (u : ℤ) : fintype.card ↥(Ico l u) = int.to_nat (u - l) :=
  Eq.trans (fintype.card_of_finset (finset.Ico_ℤ l u) (Ico_ℤ_fintype._proof_1 l u)) (finset.Ico_ℤ.card l u)

