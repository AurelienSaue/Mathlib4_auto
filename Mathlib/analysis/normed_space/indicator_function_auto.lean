/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.indicator_function
import Mathlib.analysis.normed_space.basic
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Indicator function and norm

This file contains a few simple lemmas about `set.indicator` and `norm`.

## Tags
indicator, norm
-/

theorem norm_indicator_eq_indicator_norm {α : Type u_1} {E : Type u_2} [normed_group E] {s : set α}
    (f : α → E) (a : α) :
    norm (set.indicator s f a) = set.indicator s (fun (a : α) => norm (f a)) a :=
  flip congr_fun a (Eq.symm (set.indicator_comp_of_zero norm_zero))

theorem nnnorm_indicator_eq_indicator_nnnorm {α : Type u_1} {E : Type u_2} [normed_group E]
    {s : set α} (f : α → E) (a : α) :
    nnnorm (set.indicator s f a) = set.indicator s (fun (a : α) => nnnorm (f a)) a :=
  flip congr_fun a (Eq.symm (set.indicator_comp_of_zero nnnorm_zero))

theorem norm_indicator_le_of_subset {α : Type u_1} {E : Type u_2} [normed_group E] {s : set α}
    {t : set α} (h : s ⊆ t) (f : α → E) (a : α) :
    norm (set.indicator s f a) ≤ norm (set.indicator t f a) :=
  sorry

theorem indicator_norm_le_norm_self {α : Type u_1} {E : Type u_2} [normed_group E] {s : set α}
    (f : α → E) (a : α) : set.indicator s (fun (a : α) => norm (f a)) a ≤ norm (f a) :=
  set.indicator_le_self' (fun (_x : α) (_x : ¬_x ∈ s) => norm_nonneg (f a)) a

theorem norm_indicator_le_norm_self {α : Type u_1} {E : Type u_2} [normed_group E] {s : set α}
    (f : α → E) (a : α) : norm (set.indicator s f a) ≤ norm (f a) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (norm (set.indicator s f a) ≤ norm (f a)))
        (norm_indicator_eq_indicator_norm f a)))
    (indicator_norm_le_norm_self (fun (a : α) => f a) a)

end Mathlib