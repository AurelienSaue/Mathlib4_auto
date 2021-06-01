/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.finite
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side.
-/

namespace set


theorem Ioo.infinite {α : Type u_1} [preorder α] [densely_ordered α] {a : α} {b : α} (h : a < b) :
    infinite (Ioo a b) :=
  sorry

theorem Ico.infinite {α : Type u_1} [preorder α] [densely_ordered α] {a : α} {b : α} (h : a < b) :
    infinite (Ico a b) :=
  infinite_mono Ioo_subset_Ico_self (Ioo.infinite h)

theorem Ioc.infinite {α : Type u_1} [preorder α] [densely_ordered α] {a : α} {b : α} (h : a < b) :
    infinite (Ioc a b) :=
  infinite_mono Ioo_subset_Ioc_self (Ioo.infinite h)

theorem Icc.infinite {α : Type u_1} [preorder α] [densely_ordered α] {a : α} {b : α} (h : a < b) :
    infinite (Icc a b) :=
  infinite_mono Ioo_subset_Icc_self (Ioo.infinite h)

theorem Iio.infinite {α : Type u_1} [preorder α] [no_bot_order α] {b : α} : infinite (Iio b) :=
  sorry

theorem Iic.infinite {α : Type u_1} [preorder α] [no_bot_order α] {b : α} : infinite (Iic b) :=
  infinite_mono Iio_subset_Iic_self Iio.infinite

theorem Ioi.infinite {α : Type u_1} [preorder α] [no_top_order α] {a : α} : infinite (Ioi a) :=
  Iio.infinite

theorem Ici.infinite {α : Type u_1} [preorder α] [no_top_order α] {a : α} : infinite (Ici a) :=
  infinite_mono Ioi_subset_Ici_self Ioi.infinite

end Mathlib