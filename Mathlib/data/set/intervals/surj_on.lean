/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Heather Macbeth
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.basic
import Mathlib.data.set.function
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `set.surj_on`, and provided for all
permutations of interval endpoints.
-/

theorem surj_on_Ioo_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) (b : α) : set.surj_on f (set.Ioo a b) (set.Ioo (f a) (f b)) := sorry

theorem surj_on_Ico_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) (b : α) : set.surj_on f (set.Ico a b) (set.Ico (f a) (f b)) := sorry

theorem surj_on_Ioc_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) (b : α) : set.surj_on f (set.Ioc a b) (set.Ioc (f a) (f b)) := sorry

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function

theorem surj_on_Icc_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) {a : α} {b : α} (hab : a ≤ b) : set.surj_on f (set.Icc a b) (set.Icc (f a) (f b)) := sorry

theorem surj_on_Ioi_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) : set.surj_on f (set.Ioi a) (set.Ioi (f a)) := sorry

theorem surj_on_Iio_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) : set.surj_on f (set.Iio a) (set.Iio (f a)) :=
  surj_on_Ioi_of_monotone_surjective (monotone.order_dual h_mono) h_surj a

theorem surj_on_Ici_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) : set.surj_on f (set.Ici a) (set.Ici (f a)) := sorry

theorem surj_on_Iic_of_monotone_surjective {α : Type u_1} {β : Type u_2} [linear_order α] [partial_order β] {f : α → β} (h_mono : monotone f) (h_surj : function.surjective f) (a : α) : set.surj_on f (set.Iic a) (set.Iic (f a)) :=
  surj_on_Ici_of_monotone_surjective (monotone.order_dual h_mono) h_surj a

