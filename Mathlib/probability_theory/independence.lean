/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.measure_space
import Mathlib.algebra.big_operators.intervals
import Mathlib.data.finset.intervals
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space α` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* TODO: `Indep_of_Indep_sets`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent.
* `indep_of_indep_sets`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set α)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space α`,
* `Indep_set`: independence of a family of sets `s : ι → set α`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), α → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space α]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

namespace probability_theory


/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def Indep_sets {α : Type u_1} {ι : Type u_2} [measurable_space α] (π : ι → set (set α)) (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  ∀ (s : finset ι) {f : ι → set α} (H : ∀ (i : ι), i ∈ s → f i ∈ π i),
    coe_fn μ (set.Inter fun (i : ι) => set.Inter fun (H : i ∈ s) => f i) = finset.prod s fun (i : ι) => coe_fn μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep_sets {α : Type u_1} [measurable_space α] (s1 : set (set α)) (s2 : set (set α)) (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  ∀ (t1 t2 : set α), t1 ∈ s1 → t2 ∈ s2 → coe_fn μ (t1 ∩ t2) = coe_fn μ t1 * coe_fn μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space α` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep {α : Type u_1} {ι : Type u_2} (m : ι → measurable_space α) [measurable_space α] (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  Indep_sets fun (x : ι) => measurable_space.is_measurable' (m x)

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep {α : Type u_1} (m₁ : measurable_space α) (m₂ : measurable_space α) [measurable_space α] (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  indep_sets (measurable_space.is_measurable' m₁) (measurable_space.is_measurable' m₂)

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_set {α : Type u_1} {ι : Type u_2} [measurable_space α] (s : ι → set α) (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  Indep fun (i : ι) => measurable_space.generate_from (singleton (s i))

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set {α : Type u_1} [measurable_space α] {s : set α} {t : set α} (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  indep (measurable_space.generate_from (singleton s)) (measurable_space.generate_from (singleton t))

/-- A family of functions defined on the same space `α` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `α` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_fun {α : Type u_1} {ι : Type u_2} [measurable_space α] {β : ι → Type u_3} (m : (x : ι) → measurable_space (β x)) (f : (x : ι) → α → β x) (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  Indep fun (x : ι) => measurable_space.comap (f x) (m x)

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_fun {α : Type u_1} {β : Type u_2} {γ : Type u_3} [measurable_space α] (mβ : measurable_space β) (mγ : measurable_space γ) {f : α → β} {g : α → γ} (μ : autoParam (measure_theory.measure α)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.measure_theory.volume_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "measure_theory") "volume_tac")
    []))  :=
  indep (measurable_space.comap f mβ) (measurable_space.comap g mγ)

theorem indep_sets.symm {α : Type u_1} {s₁ : set (set α)} {s₂ : set (set α)} [measurable_space α] {μ : measure_theory.measure α} (h : indep_sets s₁ s₂) : indep_sets s₂ s₁ := sorry

theorem indep.symm {α : Type u_1} {m₁ : measurable_space α} {m₂ : measurable_space α} [measurable_space α] {μ : measure_theory.measure α} (h : indep m₁ m₂) : indep m₂ m₁ :=
  indep_sets.symm h

theorem indep_sets_of_indep_sets_of_le_left {α : Type u_1} {s₁ : set (set α)} {s₂ : set (set α)} {s₃ : set (set α)} [measurable_space α] {μ : measure_theory.measure α} (h_indep : indep_sets s₁ s₂) (h31 : s₃ ⊆ s₁) : indep_sets s₃ s₂ :=
  fun (t1 t2 : set α) (ht1 : t1 ∈ s₃) (ht2 : t2 ∈ s₂) => h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

theorem indep_sets_of_indep_sets_of_le_right {α : Type u_1} {s₁ : set (set α)} {s₂ : set (set α)} {s₃ : set (set α)} [measurable_space α] {μ : measure_theory.measure α} (h_indep : indep_sets s₁ s₂) (h32 : s₃ ⊆ s₂) : indep_sets s₁ s₃ :=
  fun (t1 t2 : set α) (ht1 : t1 ∈ s₁) (ht2 : t2 ∈ s₃) => h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

theorem indep_of_indep_of_le_left {α : Type u_1} {m₁ : measurable_space α} {m₂ : measurable_space α} {m₃ : measurable_space α} [measurable_space α] {μ : measure_theory.measure α} (h_indep : indep m₁ m₂) (h31 : m₃ ≤ m₁) : indep m₃ m₂ :=
  fun (t1 t2 : set α) (ht1 : t1 ∈ measurable_space.is_measurable' m₃) (ht2 : t2 ∈ measurable_space.is_measurable' m₂) =>
    h_indep t1 t2 (h31 t1 ht1) ht2

theorem indep_of_indep_of_le_right {α : Type u_1} {m₁ : measurable_space α} {m₂ : measurable_space α} {m₃ : measurable_space α} [measurable_space α] {μ : measure_theory.measure α} (h_indep : indep m₁ m₂) (h32 : m₃ ≤ m₂) : indep m₁ m₃ :=
  fun (t1 t2 : set α) (ht1 : t1 ∈ measurable_space.is_measurable' m₁) (ht2 : t2 ∈ measurable_space.is_measurable' m₃) =>
    h_indep t1 t2 ht1 (h32 t2 ht2)

theorem indep_sets.union {α : Type u_1} [measurable_space α] {s₁ : set (set α)} {s₂ : set (set α)} {s' : set (set α)} {μ : measure_theory.measure α} (h₁ : indep_sets s₁ s') (h₂ : indep_sets s₂ s') : indep_sets (s₁ ∪ s₂) s' := sorry

@[simp] theorem indep_sets.union_iff {α : Type u_1} [measurable_space α] {s₁ : set (set α)} {s₂ : set (set α)} {s' : set (set α)} {μ : measure_theory.measure α} : indep_sets (s₁ ∪ s₂) s' ↔ indep_sets s₁ s' ∧ indep_sets s₂ s' := sorry

theorem indep_sets.Union {α : Type u_1} {ι : Sort u_2} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)} {μ : measure_theory.measure α} (hyp : ∀ (n : ι), indep_sets (s n) s') : indep_sets (set.Union fun (n : ι) => s n) s' := sorry

theorem indep_sets.inter {α : Type u_1} [measurable_space α] {s₁ : set (set α)} {s' : set (set α)} (s₂ : set (set α)) {μ : measure_theory.measure α} (h₁ : indep_sets s₁ s') : indep_sets (s₁ ∩ s₂) s' :=
  fun (t1 t2 : set α) (ht1 : t1 ∈ s₁ ∩ s₂) (ht2 : t2 ∈ s') =>
    h₁ t1 t2 (and.left (iff.mp (set.mem_inter_iff t1 s₁ s₂) ht1)) ht2

theorem indep_sets.Inter {α : Type u_1} {ι : Sort u_2} [measurable_space α] {s : ι → set (set α)} {s' : set (set α)} {μ : measure_theory.measure α} (h : ∃ (n : ι), indep_sets (s n) s') : indep_sets (set.Inter fun (n : ι) => s n) s' :=
  id
    fun (t1 t2 : set α) (ht1 : t1 ∈ set.Inter fun (n : ι) => s n) (ht2 : t2 ∈ s') =>
      Exists.dcases_on h fun (n : ι) (h : indep_sets (s n) s') => h t1 t2 (iff.mp set.mem_Inter ht1 n) ht2

/-! ### Deducing `indep` from `Indep` -/

theorem Indep_sets.indep_sets {α : Type u_1} {ι : Type u_2} {s : ι → set (set α)} [measurable_space α] {μ : measure_theory.measure α} (h_indep : Indep_sets s) {i : ι} {j : ι} (hij : i ≠ j) : indep_sets (s i) (s j) := sorry

theorem Indep.indep {α : Type u_1} {ι : Type u_2} {m : ι → measurable_space α} [measurable_space α] {μ : measure_theory.measure α} (h_indep : Indep m) {i : ι} {j : ι} (hij : i ≠ j) : indep (m i) (m j) :=
  id (Indep_sets.indep_sets h_indep hij)

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

/-! ### Independence of measurable space structures implies independence of generating π-systems -/

theorem Indep.Indep_sets {α : Type u_1} {ι : Type u_2} [measurable_space α] {μ : measure_theory.measure α} {m : ι → measurable_space α} {s : ι → set (set α)} (hms : ∀ (n : ι), m n = measurable_space.generate_from (s n)) (h_indep : Indep m) : Indep_sets s := sorry

theorem indep.indep_sets {α : Type u_1} [measurable_space α] {μ : measure_theory.measure α} {s1 : set (set α)} {s2 : set (set α)} (h_indep : indep (measurable_space.generate_from s1) (measurable_space.generate_from s2)) : indep_sets s1 s2 :=
  fun (t1 t2 : set α) (ht1 : t1 ∈ s1) (ht2 : t2 ∈ s2) =>
    h_indep t1 t2 (measurable_space.is_measurable_generate_from ht1) (measurable_space.is_measurable_generate_from ht2)

/-! ### Independence of generating π-systems implies independence of measurable space structures -/

theorem indep_sets.indep {α : Type u_1} {m1 : measurable_space α} {m2 : measurable_space α} {m : measurable_space α} {μ : measure_theory.measure α} [measure_theory.probability_measure μ] {p1 : set (set α)} {p2 : set (set α)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = measurable_space.generate_from p1) (hpm2 : m2 = measurable_space.generate_from p2) (hyp : indep_sets p1 p2) : indep m1 m2 := sorry

