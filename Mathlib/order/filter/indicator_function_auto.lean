/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.indicator_function
import Mathlib.order.filter.at_top_bot
import PostPort

universes u_1 u_3 u_2 

namespace Mathlib

/-!
# Indicator function and filters

Properties of indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/

theorem indicator_eventually_eq {α : Type u_1} {M : Type u_3} [HasZero M] {s : set α} {t : set α} {f : α → M} {g : α → M} {l : filter α} (hf : filter.eventually_eq (l ⊓ filter.principal s) f g) (hs : filter.eventually_eq l s t) : filter.eventually_eq l (set.indicator s f) (set.indicator t g) := sorry

theorem indicator_union_eventually_eq {α : Type u_1} {M : Type u_3} [add_monoid M] {s : set α} {t : set α} {f : α → M} {l : filter α} (h : filter.eventually (fun (a : α) => ¬a ∈ s ∩ t) l) : filter.eventually_eq l (set.indicator (s ∪ t) f) (set.indicator s f + set.indicator t f) :=
  filter.eventually.mono h fun (a : α) (ha : ¬a ∈ s ∩ t) => set.indicator_union_of_not_mem_inter ha f

theorem indicator_eventually_le_indicator {α : Type u_1} {β : Type u_2} [HasZero β] [preorder β] {s : set α} {f : α → β} {g : α → β} {l : filter α} (h : filter.eventually_le (l ⊓ filter.principal s) f g) : filter.eventually_le l (set.indicator s f) (set.indicator s g) :=
  filter.eventually.mono (iff.mp filter.eventually_inf_principal h)
    fun (a : α) (h : a ∈ s → f a ≤ g a) => set.indicator_rel_indicator (le_refl 0) h

theorem tendsto_indicator_of_monotone {α : Type u_1} {β : Type u_2} {ι : Type u_3} [preorder ι] [HasZero β] (s : ι → set α) (hs : monotone s) (f : α → β) (a : α) : filter.tendsto (fun (i : ι) => set.indicator (s i) f a) filter.at_top
  (pure (set.indicator (set.Union fun (i : ι) => s i) f a)) := sorry

theorem tendsto_indicator_of_antimono {α : Type u_1} {β : Type u_2} {ι : Type u_3} [preorder ι] [HasZero β] (s : ι → set α) (hs : ∀ {i j : ι}, i ≤ j → s j ⊆ s i) (f : α → β) (a : α) : filter.tendsto (fun (i : ι) => set.indicator (s i) f a) filter.at_top
  (pure (set.indicator (set.Inter fun (i : ι) => s i) f a)) := sorry

theorem tendsto_indicator_bUnion_finset {α : Type u_1} {β : Type u_2} {ι : Type u_3} [HasZero β] (s : ι → set α) (f : α → β) (a : α) : filter.tendsto (fun (n : finset ι) => set.indicator (set.Union fun (i : ι) => set.Union fun (H : i ∈ n) => s i) f a)
  filter.at_top (pure (set.indicator (set.Union s) f a)) := sorry

