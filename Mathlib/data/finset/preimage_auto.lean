/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.finite
import Mathlib.algebra.big_operators.basic
import Mathlib.PostPort

universes u v u_1 x 

namespace Mathlib

/-!
# Preimage of a `finset` under an injective map.
-/

namespace finset


/-- Preimage of `s : finset β` under a map `f` injective of `f ⁻¹' s` as a `finset`.  -/
def preimage {α : Type u} {β : Type v} (s : finset β) (f : α → β) (hf : set.inj_on f (f ⁻¹' ↑s)) :
    finset α :=
  set.finite.to_finset sorry

@[simp] theorem mem_preimage {α : Type u} {β : Type v} {f : α → β} {s : finset β}
    {hf : set.inj_on f (f ⁻¹' ↑s)} {x : α} : x ∈ preimage s f hf ↔ f x ∈ s :=
  set.finite.mem_to_finset

@[simp] theorem coe_preimage {α : Type u} {β : Type v} {f : α → β} (s : finset β)
    (hf : set.inj_on f (f ⁻¹' ↑s)) : ↑(preimage s f hf) = f ⁻¹' ↑s :=
  set.finite.coe_to_finset (preimage._proof_1 s f hf)

@[simp] theorem preimage_empty {α : Type u} {β : Type v} {f : α → β} :
    preimage ∅ f
          (eq.mpr
            (id
              (Eq.trans
                (Eq.trans
                  (Eq.trans
                    ((fun (f f_1 : α → β) (e_1 : f = f_1) (s s_1 : set α) (e_2 : s = s_1) =>
                        congr (congr_arg set.inj_on e_1) e_2)
                      f f (Eq.refl f) (f ⁻¹' ↑∅) ∅
                      (Eq.trans
                        ((fun (f f_1 : α → β) (e_1 : f = f_1) (s s_1 : set β) (e_2 : s = s_1) =>
                            congr (congr_arg set.preimage e_1) e_2)
                          f f (Eq.refl f) ↑∅ ∅ coe_empty)
                        set.preimage_empty))
                    (set.inj_on.equations._eqn_1 f ∅))
                  (forall_congr_eq
                    fun (x₁ : α) =>
                      Eq.trans
                        (imp_congr_eq (set.mem_empty_eq x₁)
                          (Eq.trans
                            (forall_congr_eq
                              fun (x₂ : α) =>
                                Eq.trans
                                  (imp_congr_eq (set.mem_empty_eq x₂)
                                    (Eq.refl (f x₁ = f x₂ → x₁ = x₂)))
                                  (propext
                                    (forall_prop_of_false (iff.mpr not_false_iff True.intro))))
                            (propext forall_true_iff)))
                        (propext (forall_prop_of_false (iff.mpr not_false_iff True.intro)))))
                (propext forall_true_iff)))
            trivial) =
        ∅ :=
  sorry

@[simp] theorem preimage_univ {α : Type u} {β : Type v} {f : α → β} [fintype α] [fintype β]
    (hf : set.inj_on f (f ⁻¹' ↑univ)) : preimage univ f hf = univ :=
  sorry

@[simp] theorem preimage_inter {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s : finset β} {t : finset β} (hs : set.inj_on f (f ⁻¹' ↑s)) (ht : set.inj_on f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f
          fun (x₁ : α) (hx₁ : x₁ ∈ f ⁻¹' ↑(s ∩ t)) (x₂ : α) (hx₂ : x₂ ∈ f ⁻¹' ↑(s ∩ t)) =>
            hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
        preimage s f hs ∩ preimage t f ht :=
  sorry

@[simp] theorem preimage_union {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] {f : α → β}
    {s : finset β} {t : finset β} (hst : set.inj_on f (f ⁻¹' ↑(s ∪ t))) :
    preimage (s ∪ t) f hst =
        (preimage s f
            fun (x₁ : α) (hx₁ : x₁ ∈ f ⁻¹' ↑s) (x₂ : α) (hx₂ : x₂ ∈ f ⁻¹' ↑s) =>
              hst (mem_union_left t hx₁) (mem_union_left t hx₂)) ∪
          preimage t f
            fun (x₁ : α) (hx₁ : x₁ ∈ f ⁻¹' ↑t) (x₂ : α) (hx₂ : x₂ ∈ f ⁻¹' ↑t) =>
              hst (mem_union_right s hx₁) (mem_union_right s hx₂) :=
  sorry

@[simp] theorem preimage_compl {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] [fintype α]
    [fintype β] {f : α → β} (s : finset β) (hf : function.injective f) :
    preimage (sᶜ) f (function.injective.inj_on hf (f ⁻¹' ↑(sᶜ))) =
        (preimage s f (function.injective.inj_on hf (f ⁻¹' ↑s))ᶜ) :=
  sorry

theorem monotone_preimage {α : Type u} {β : Type v} {f : α → β} (h : function.injective f) :
    monotone fun (s : finset β) => preimage s f (function.injective.inj_on h (f ⁻¹' ↑s)) :=
  fun (s t : finset β) (hst : s ≤ t) (x : α)
    (hx : x ∈ (fun (s : finset β) => preimage s f (function.injective.inj_on h (f ⁻¹' ↑s))) s) =>
    iff.mpr mem_preimage (hst (iff.mp mem_preimage hx))

theorem image_subset_iff_subset_preimage {α : Type u} {β : Type v} [DecidableEq β] {f : α → β}
    {s : finset α} {t : finset β} (hf : set.inj_on f (f ⁻¹' ↑t)) :
    image f s ⊆ t ↔ s ⊆ preimage t f hf :=
  sorry

theorem map_subset_iff_subset_preimage {α : Type u} {β : Type v} {f : α ↪ β} {s : finset α}
    {t : finset β} :
    map f s ⊆ t ↔
        s ⊆
          preimage t (⇑f)
            (function.injective.inj_on (function.embedding.injective f) (⇑f ⁻¹' ↑t)) :=
  sorry

theorem image_preimage {α : Type u} {β : Type v} [DecidableEq β] (f : α → β) (s : finset β)
    [(x : β) → Decidable (x ∈ set.range f)] (hf : set.inj_on f (f ⁻¹' ↑s)) :
    image f (preimage s f hf) = filter (fun (x : β) => x ∈ set.range f) s :=
  sorry

theorem image_preimage_of_bij {α : Type u} {β : Type v} [DecidableEq β] (f : α → β) (s : finset β)
    (hf : set.bij_on f (f ⁻¹' ↑s) ↑s) : image f (preimage s f (set.bij_on.inj_on hf)) = s :=
  sorry

theorem sigma_preimage_mk {α : Type u} {β : α → Type u_1} [DecidableEq α]
    (s : finset (sigma fun (a : α) => β a)) (t : finset α) :
    (finset.sigma t
          fun (a : α) =>
            preimage s (sigma.mk a)
              (function.injective.inj_on sigma_mk_injective (sigma.mk a ⁻¹' ↑s))) =
        filter (fun (a : sigma fun (a : α) => β a) => sigma.fst a ∈ t) s :=
  sorry

theorem sigma_preimage_mk_of_subset {α : Type u} {β : α → Type u_1} [DecidableEq α]
    (s : finset (sigma fun (a : α) => β a)) {t : finset α} (ht : image sigma.fst s ⊆ t) :
    (finset.sigma t
          fun (a : α) =>
            preimage s (sigma.mk a)
              (function.injective.inj_on sigma_mk_injective (sigma.mk a ⁻¹' ↑s))) =
        s :=
  sorry

theorem sigma_image_fst_preimage_mk {α : Type u} {β : α → Type u_1} [DecidableEq α]
    (s : finset (sigma fun (a : α) => β a)) :
    (finset.sigma (image sigma.fst s)
          fun (a : α) =>
            preimage s (sigma.mk a)
              (function.injective.inj_on sigma_mk_injective (sigma.mk a ⁻¹' ↑s))) =
        s :=
  sigma_preimage_mk_of_subset s (subset.refl (image sigma.fst s))

theorem prod_preimage' {α : Type u} {β : Type v} {γ : Type x} [comm_monoid β] (f : α → γ)
    [decidable_pred fun (x : γ) => x ∈ set.range f] (s : finset γ) (hf : set.inj_on f (f ⁻¹' ↑s))
    (g : γ → β) :
    (finset.prod (preimage s f hf) fun (x : α) => g (f x)) =
        finset.prod (filter (fun (x : γ) => x ∈ set.range f) s) fun (x : γ) => g x :=
  sorry

theorem prod_preimage {α : Type u} {β : Type v} {γ : Type x} [comm_monoid β] (f : α → γ)
    (s : finset γ) (hf : set.inj_on f (f ⁻¹' ↑s)) (g : γ → β)
    (hg : ∀ (x : γ), x ∈ s → ¬x ∈ set.range f → g x = 1) :
    (finset.prod (preimage s f hf) fun (x : α) => g (f x)) = finset.prod s fun (x : γ) => g x :=
  sorry

theorem sum_preimage_of_bij {α : Type u} {β : Type v} {γ : Type x} [add_comm_monoid β] (f : α → γ)
    (s : finset γ) (hf : set.bij_on f (f ⁻¹' ↑s) ↑s) (g : γ → β) :
    (finset.sum (preimage s f (set.bij_on.inj_on hf)) fun (x : α) => g (f x)) =
        finset.sum s fun (x : γ) => g x :=
  sum_preimage f s (set.bij_on.inj_on hf) g
    fun (x : γ) (hxs : x ∈ s) (hxf : ¬x ∈ set.range f) =>
      false.elim (hxf (set.bij_on.subset_range hf hxs))

end Mathlib