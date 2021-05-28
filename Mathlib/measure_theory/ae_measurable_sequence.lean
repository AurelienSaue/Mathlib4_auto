/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.measure_theory.measure_space
import Mathlib.PostPort

universes u_1 u_2 u_4 

namespace Mathlib

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`ae_measurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, ae_measurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (λ n, f n x)`, we define a sequence of measurable functions `ae_seq hf p`
and a measurable set `ae_seq_set hf p`, such that
* `μ (ae_seq_set hf p)ᶜ = 0`
* `x ∈ ae_seq_set hf p → ∀ i : ι, ae_seq hf hp i x = f i x`
* `x ∈ ae_seq_set hf p → p x (λ n, f n x)`
-/

/-- If we have the additional hypothesis `∀ᵐ x ∂μ, p x (λ n, f n x)`, this is a measurable set
whose complement has measure 0 such that for all `x ∈ ae_seq_set`, `f i x` is equal to
`(hf i).mk (f i) x` for all `i` and we have the pointwise property `p x (λ n, f n x)`. -/
def ae_seq_set {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} (hf : ∀ (i : ι), ae_measurable (f i)) (p : α → (ι → β) → Prop) : set α :=
  measure_theory.to_measurable μ
      ((set_of fun (x : α) => (∀ (i : ι), f i x = ae_measurable.mk (f i) (hf i) x) ∧ p x fun (n : ι) => f n x)ᶜ)ᶜ

/-- A sequence of measurable functions that are equal to `f` and verify property `p` on the
measurable set `ae_seq_set hf p`. -/
def ae_seq {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} (hf : ∀ (i : ι), ae_measurable (f i)) (p : α → (ι → β) → Prop) : ι → α → β :=
  fun (i : ι) (x : α) => ite (x ∈ ae_seq_set hf p) (ae_measurable.mk (f i) (hf i) x) (nonempty.some sorry)

namespace ae_seq


theorem mk_eq_fun_of_mem_ae_seq_set {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} (hf : ∀ (i : ι), ae_measurable (f i)) {x : α} (hx : x ∈ ae_seq_set hf p) (i : ι) : ae_measurable.mk (f i) (hf i) x = f i x := sorry

theorem ae_seq_eq_mk_of_mem_ae_seq_set {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} (hf : ∀ (i : ι), ae_measurable (f i)) {x : α} (hx : x ∈ ae_seq_set hf p) (i : ι) : ae_seq hf p i x = ae_measurable.mk (f i) (hf i) x := sorry

theorem ae_seq_eq_fun_of_mem_ae_seq_set {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} (hf : ∀ (i : ι), ae_measurable (f i)) {x : α} (hx : x ∈ ae_seq_set hf p) (i : ι) : ae_seq hf p i x = f i x := sorry

theorem prop_of_mem_ae_seq_set {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} (hf : ∀ (i : ι), ae_measurable (f i)) {x : α} (hx : x ∈ ae_seq_set hf p) : p x fun (n : ι) => ae_seq hf p n x := sorry

theorem fun_prop_of_mem_ae_seq_set {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} (hf : ∀ (i : ι), ae_measurable (f i)) {x : α} (hx : x ∈ ae_seq_set hf p) : p x fun (n : ι) => f n x := sorry

theorem ae_seq_set_is_measurable {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} {hf : ∀ (i : ι), ae_measurable (f i)} : is_measurable (ae_seq_set hf p) := sorry

theorem measurable {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} (hf : ∀ (i : ι), ae_measurable (f i)) (p : α → (ι → β) → Prop) (i : ι) : measurable (ae_seq hf p i) :=
  measurable.ite ae_seq_set_is_measurable (ae_measurable.measurable_mk (hf i))
    (dite (Nonempty α) (fun (hα : Nonempty α) => measurable_const)
      fun (hα : ¬Nonempty α) => measurable_of_not_nonempty hα fun (x : α) => nonempty.some (_proof_1 i x))

theorem measure_compl_ae_seq_set_eq_zero {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} [encodable ι] (hf : ∀ (i : ι), ae_measurable (f i)) (hp : filter.eventually (fun (x : α) => p x fun (n : ι) => f n x) (measure_theory.measure.ae μ)) : coe_fn μ (ae_seq_set hf pᶜ) = 0 := sorry

theorem ae_seq_eq_mk_ae {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} [encodable ι] (hf : ∀ (i : ι), ae_measurable (f i)) (hp : filter.eventually (fun (x : α) => p x fun (n : ι) => f n x) (measure_theory.measure.ae μ)) : filter.eventually (fun (a : α) => ∀ (i : ι), ae_seq hf p i a = ae_measurable.mk (f i) (hf i) a)
  (measure_theory.measure.ae μ) := sorry

theorem ae_seq_eq_fun_ae {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} [encodable ι] (hf : ∀ (i : ι), ae_measurable (f i)) (hp : filter.eventually (fun (x : α) => p x fun (n : ι) => f n x) (measure_theory.measure.ae μ)) : filter.eventually (fun (a : α) => ∀ (i : ι), ae_seq hf p i a = f i a) (measure_theory.measure.ae μ) :=
  measure_theory.measure_mono_null
    (fun (x : α) => mt fun (hx : x ∈ ae_seq_set hf p) (i : ι) => ae_seq_eq_fun_of_mem_ae_seq_set hf hx i)
    (measure_compl_ae_seq_set_eq_zero hf hp)

theorem ae_seq_n_eq_fun_n_ae {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} [encodable ι] (hf : ∀ (i : ι), ae_measurable (f i)) (hp : filter.eventually (fun (x : α) => p x fun (n : ι) => f n x) (measure_theory.measure.ae μ)) (n : ι) : filter.eventually_eq (measure_theory.measure.ae μ) (ae_seq hf p n) (f n) :=
  iff.mp measure_theory.ae_all_iff (ae_seq_eq_fun_ae hf hp) n

theorem supr {α : Type u_1} {β : Type u_2} {ι : Type u_4} [measurable_space α] [measurable_space β] {f : ι → α → β} {μ : measure_theory.measure α} {p : α → (ι → β) → Prop} [complete_lattice β] [encodable ι] (hf : ∀ (i : ι), ae_measurable (f i)) (hp : filter.eventually (fun (x : α) => p x fun (n : ι) => f n x) (measure_theory.measure.ae μ)) : filter.eventually_eq (measure_theory.measure.ae μ) (supr fun (n : ι) => ae_seq hf p n) (supr fun (i : ι) => f i) := sorry

