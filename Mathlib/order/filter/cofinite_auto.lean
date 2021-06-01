/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.at_top_bot
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# The cofinite filter

In this file we define

`cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `at_top`.

## TODO

Define filters for other cardinalities of the complement.
-/

namespace filter


/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite {α : Type u_1} : filter α :=
  mk (set_of fun (s : set α) => set.finite (sᶜ)) sorry sorry sorry

@[simp] theorem mem_cofinite {α : Type u_1} {s : set α} : s ∈ cofinite ↔ set.finite (sᶜ) := iff.rfl

@[simp] theorem eventually_cofinite {α : Type u_1} {p : α → Prop} :
    filter.eventually (fun (x : α) => p x) cofinite ↔ set.finite (set_of fun (x : α) => ¬p x) :=
  iff.rfl

protected instance cofinite_ne_bot {α : Type u_1} [infinite α] : ne_bot cofinite :=
  mt (iff.mpr empty_in_sets_eq_bot)
    (eq.mpr
      (id
        ((fun (a a_1 : Prop) (e_1 : a = a_1) => congr_arg Not e_1) (∅ ∈ cofinite)
          (set.finite set.univ)
          (Eq.trans (propext mem_cofinite)
            ((fun (s s_1 : set α) (e_1 : s = s_1) => congr_arg set.finite e_1) (∅ᶜ) set.univ
              set.compl_empty))))
      set.infinite_univ)

theorem frequently_cofinite_iff_infinite {α : Type u_1} {p : α → Prop} :
    filter.frequently (fun (x : α) => p x) cofinite ↔ set.infinite (set_of fun (x : α) => p x) :=
  sorry

end filter


theorem set.finite.compl_mem_cofinite {α : Type u_1} {s : set α} (hs : set.finite s) :
    sᶜ ∈ filter.cofinite :=
  iff.mpr filter.mem_cofinite (Eq.symm (compl_compl s) ▸ hs)

theorem set.finite.eventually_cofinite_nmem {α : Type u_1} {s : set α} (hs : set.finite s) :
    filter.eventually (fun (x : α) => ¬x ∈ s) filter.cofinite :=
  set.finite.compl_mem_cofinite hs

theorem finset.eventually_cofinite_nmem {α : Type u_1} (s : finset α) :
    filter.eventually (fun (x : α) => ¬x ∈ s) filter.cofinite :=
  set.finite.eventually_cofinite_nmem (finset.finite_to_set s)

theorem set.infinite_iff_frequently_cofinite {α : Type u_1} {s : set α} :
    set.infinite s ↔ filter.frequently (fun (x : α) => x ∈ s) filter.cofinite :=
  iff.symm filter.frequently_cofinite_iff_infinite

theorem filter.eventually_cofinite_ne {α : Type u_1} (x : α) :
    filter.eventually (fun (a : α) => a ≠ x) filter.cofinite :=
  set.finite.eventually_cofinite_nmem (set.finite_singleton x)

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
theorem nat.cofinite_eq_at_top : filter.cofinite = filter.at_top := sorry

theorem nat.frequently_at_top_iff_infinite {p : ℕ → Prop} :
    filter.frequently (fun (n : ℕ) => p n) filter.at_top ↔
        set.infinite (set_of fun (n : ℕ) => p n) :=
  sorry

end Mathlib