/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.analysis.normed_space.basic
import PostPort

universes v u 

namespace Mathlib

/-!
# Completeness in terms of `cauchy` filters vs `is_cau_seq` sequences

In this file we apply `metric.complete_of_cauchy_seq_tendsto` to prove that a `normed_ring`
is complete in terms of `cauchy` filter if and only if it is complete in terms
of `cau_seq` Cauchy sequences.
-/

theorem cau_seq.tendsto_limit {β : Type v} [normed_ring β] [hn : is_absolute_value norm] (f : cau_seq β norm) [cau_seq.is_complete β norm] : filter.tendsto (⇑f) filter.at_top (nhds (cau_seq.lim f)) := sorry

/-
 This section shows that if we have a uniform space generated by an absolute value, topological
 completeness and Cauchy sequence completeness coincide. The problem is that there isn't
 a good notion of "uniform space generated by an absolute value", so right now this is
 specific to norm. Furthermore, norm only instantiates is_absolute_value on normed_field.
 This needs to be fixed, since it prevents showing that ℤ_[hp] is complete
-/

protected instance normed_field.is_absolute_value {β : Type v} [normed_field β] : is_absolute_value norm :=
  is_absolute_value.mk norm_nonneg (fun (_x : β) => norm_eq_zero) norm_add_le normed_field.norm_mul

theorem cauchy_seq.is_cau_seq {β : Type v} [normed_field β] {f : ℕ → β} (hf : cauchy_seq f) : is_cau_seq norm f := sorry

theorem cau_seq.cauchy_seq {β : Type v} [normed_field β] (f : cau_seq β norm) : cauchy_seq ⇑f := sorry

/-- In a normed field, `cau_seq` coincides with the usual notion of Cauchy sequences. -/
theorem cau_seq_iff_cauchy_seq {α : Type u} [normed_field α] {u : ℕ → α} : is_cau_seq norm u ↔ cauchy_seq u :=
  { mp := fun (h : is_cau_seq norm u) => cau_seq.cauchy_seq { val := u, property := h },
    mpr := fun (h : cauchy_seq u) => cauchy_seq.is_cau_seq h }

/-- A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness. -/
protected instance complete_space_of_cau_seq_complete {β : Type v} [normed_field β] [cau_seq.is_complete β norm] : complete_space β := sorry

