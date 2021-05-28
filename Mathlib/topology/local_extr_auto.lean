/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.order.filter.extr
import Mathlib.topology.continuous_on
import PostPort

universes u v w x 

namespace Mathlib

/-!
# Local extrema of functions on topological spaces

## Main definitions

This file defines special versions of `is_*_filter f a l`, `*=min/max/extr`,
from `order/filter/extr` for two kinds of filters: `nhds_within` and `nhds`.
These versions are called `is_local_*_on` and `is_local_*`, respectively.

## Main statements

Many lemmas in this file restate those from `order/filter/extr`, and you can find
a detailed documentation there. These convenience lemmas are provided only to make the dot notation
return propositions of expected types, not just `is_*_filter`.

Here is the list of statements specific to these two types of filters:

* `is_local_*.on`, `is_local_*_on.on_subset`: restrict to a subset;
* `is_local_*_on.inter` : intersect the set with another one;
* `is_*_on.localize` : a global extremum is a local extremum too.
* `is_[local_]*_on.is_local_*` : if we have `is_local_*_on f s a` and `s ∈ 𝓝 a`,
  then we have `is_local_* f a`.

-/

/-- `is_local_min_on f s a` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_min_on {α : Type u} {β : Type v} [topological_space α] [preorder β] (f : α → β) (s : set α) (a : α)  :=
  is_min_filter f (nhds_within a s) a

/-- `is_local_max_on f s a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_max_on {α : Type u} {β : Type v} [topological_space α] [preorder β] (f : α → β) (s : set α) (a : α)  :=
  is_max_filter f (nhds_within a s) a

/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def is_local_extr_on {α : Type u} {β : Type v} [topological_space α] [preorder β] (f : α → β) (s : set α) (a : α)  :=
  is_extr_filter f (nhds_within a s) a

/-- `is_local_min f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
def is_local_min {α : Type u} {β : Type v} [topological_space α] [preorder β] (f : α → β) (a : α)  :=
  is_min_filter f (nhds a) a

/-- `is_local_max f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_max {α : Type u} {β : Type v} [topological_space α] [preorder β] (f : α → β) (a : α)  :=
  is_max_filter f (nhds a) a

/-- `is_local_extr_on f s a` means `is_local_min_on f s a ∨ is_local_max_on f s a`. -/
def is_local_extr {α : Type u} {β : Type v} [topological_space α] [preorder β] (f : α → β) (a : α)  :=
  is_extr_filter f (nhds a) a

theorem is_local_extr_on.elim {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} {p : Prop} : is_local_extr_on f s a → (is_local_min_on f s a → p) → (is_local_max_on f s a → p) → p :=
  or.elim

theorem is_local_extr.elim {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {a : α} {p : Prop} : is_local_extr f a → (is_local_min f a → p) → (is_local_max f a → p) → p :=
  or.elim

/-! ### Restriction to (sub)sets -/

theorem is_local_min.on {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {a : α} (h : is_local_min f a) (s : set α) : is_local_min_on f s a :=
  is_min_filter.filter_inf h (filter.principal s)

theorem is_local_max.on {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {a : α} (h : is_local_max f a) (s : set α) : is_local_max_on f s a :=
  is_max_filter.filter_inf h (filter.principal s)

theorem is_local_extr.on {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {a : α} (h : is_local_extr f a) (s : set α) : is_local_extr_on f s a :=
  is_extr_filter.filter_inf h (filter.principal s)

theorem is_local_min_on.on_subset {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} {t : set α} (hf : is_local_min_on f t a) (h : s ⊆ t) : is_local_min_on f s a :=
  is_min_filter.filter_mono hf (nhds_within_mono a h)

theorem is_local_max_on.on_subset {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} {t : set α} (hf : is_local_max_on f t a) (h : s ⊆ t) : is_local_max_on f s a :=
  is_max_filter.filter_mono hf (nhds_within_mono a h)

theorem is_local_extr_on.on_subset {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} {t : set α} (hf : is_local_extr_on f t a) (h : s ⊆ t) : is_local_extr_on f s a :=
  is_extr_filter.filter_mono hf (nhds_within_mono a h)

theorem is_local_min_on.inter {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_local_min_on f s a) (t : set α) : is_local_min_on f (s ∩ t) a :=
  is_local_min_on.on_subset hf (set.inter_subset_left s t)

theorem is_local_max_on.inter {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_local_max_on f s a) (t : set α) : is_local_max_on f (s ∩ t) a :=
  is_local_max_on.on_subset hf (set.inter_subset_left s t)

theorem is_local_extr_on.inter {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_local_extr_on f s a) (t : set α) : is_local_extr_on f (s ∩ t) a :=
  is_local_extr_on.on_subset hf (set.inter_subset_left s t)

theorem is_min_on.localize {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_min_on f s a) : is_local_min_on f s a :=
  is_min_filter.filter_mono hf inf_le_right

theorem is_max_on.localize {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_max_on f s a) : is_local_max_on f s a :=
  is_max_filter.filter_mono hf inf_le_right

theorem is_extr_on.localize {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_extr_on f s a) : is_local_extr_on f s a :=
  is_extr_filter.filter_mono hf inf_le_right

theorem is_local_min_on.is_local_min {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_local_min_on f s a) (hs : s ∈ nhds a) : is_local_min f a :=
  (fun (this : nhds a ≤ filter.principal s) => is_min_filter.filter_mono hf (le_inf (le_refl (nhds a)) this))
    (iff.mpr filter.le_principal_iff hs)

theorem is_local_max_on.is_local_max {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_local_max_on f s a) (hs : s ∈ nhds a) : is_local_max f a :=
  (fun (this : nhds a ≤ filter.principal s) => is_max_filter.filter_mono hf (le_inf (le_refl (nhds a)) this))
    (iff.mpr filter.le_principal_iff hs)

theorem is_local_extr_on.is_local_extr {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_local_extr_on f s a) (hs : s ∈ nhds a) : is_local_extr f a :=
  is_local_extr_on.elim hf
    (fun (hf : is_local_min_on f s a) => is_min_filter.is_extr (is_local_min_on.is_local_min hf hs))
    fun (hf : is_local_max_on f s a) => is_max_filter.is_extr (is_local_max_on.is_local_max hf hs)

theorem is_min_on.is_local_min {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_min_on f s a) (hs : s ∈ nhds a) : is_local_min f a :=
  is_local_min_on.is_local_min (is_min_on.localize hf) hs

theorem is_max_on.is_local_max {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_max_on f s a) (hs : s ∈ nhds a) : is_local_max f a :=
  is_local_max_on.is_local_max (is_max_on.localize hf) hs

theorem is_extr_on.is_local_extr {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {s : set α} {a : α} (hf : is_extr_on f s a) (hs : s ∈ nhds a) : is_local_extr f a :=
  is_local_extr_on.is_local_extr (is_extr_on.localize hf) hs

/-! ### Constant -/

theorem is_local_min_on_const {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {a : α} {b : β} : is_local_min_on (fun (_x : α) => b) s a :=
  is_min_filter_const

theorem is_local_max_on_const {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {a : α} {b : β} : is_local_max_on (fun (_x : α) => b) s a :=
  is_max_filter_const

theorem is_local_extr_on_const {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {a : α} {b : β} : is_local_extr_on (fun (_x : α) => b) s a :=
  is_extr_filter_const

theorem is_local_min_const {α : Type u} {β : Type v} [topological_space α] [preorder β] {a : α} {b : β} : is_local_min (fun (_x : α) => b) a :=
  is_min_filter_const

theorem is_local_max_const {α : Type u} {β : Type v} [topological_space α] [preorder β] {a : α} {b : β} : is_local_max (fun (_x : α) => b) a :=
  is_max_filter_const

theorem is_local_extr_const {α : Type u} {β : Type v} [topological_space α] [preorder β] {a : α} {b : β} : is_local_extr (fun (_x : α) => b) a :=
  is_extr_filter_const

/-! ### Composition with (anti)monotone functions -/

theorem is_local_min.comp_mono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} (hf : is_local_min f a) {g : β → γ} (hg : monotone g) : is_local_min (g ∘ f) a :=
  is_min_filter.comp_mono hf hg

theorem is_local_max.comp_mono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} (hf : is_local_max f a) {g : β → γ} (hg : monotone g) : is_local_max (g ∘ f) a :=
  is_max_filter.comp_mono hf hg

theorem is_local_extr.comp_mono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} (hf : is_local_extr f a) {g : β → γ} (hg : monotone g) : is_local_extr (g ∘ f) a :=
  is_extr_filter.comp_mono hf hg

theorem is_local_min.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} (hf : is_local_min f a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_local_max (g ∘ f) a :=
  is_min_filter.comp_antimono hf hg

theorem is_local_max.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} (hf : is_local_max f a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_local_min (g ∘ f) a :=
  is_max_filter.comp_antimono hf hg

theorem is_local_extr.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} (hf : is_local_extr f a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_local_extr (g ∘ f) a :=
  is_extr_filter.comp_antimono hf hg

theorem is_local_min_on.comp_mono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_local_min_on f s a) {g : β → γ} (hg : monotone g) : is_local_min_on (g ∘ f) s a :=
  is_min_filter.comp_mono hf hg

theorem is_local_max_on.comp_mono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_local_max_on f s a) {g : β → γ} (hg : monotone g) : is_local_max_on (g ∘ f) s a :=
  is_max_filter.comp_mono hf hg

theorem is_local_extr_on.comp_mono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_local_extr_on f s a) {g : β → γ} (hg : monotone g) : is_local_extr_on (g ∘ f) s a :=
  is_extr_filter.comp_mono hf hg

theorem is_local_min_on.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_local_min_on f s a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_local_max_on (g ∘ f) s a :=
  is_min_filter.comp_antimono hf hg

theorem is_local_max_on.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_local_max_on f s a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_local_min_on (g ∘ f) s a :=
  is_max_filter.comp_antimono hf hg

theorem is_local_extr_on.comp_antimono {α : Type u} {β : Type v} {γ : Type w} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} (hf : is_local_extr_on f s a) {g : β → γ} (hg : ∀ {x y : β}, x ≤ y → g y ≤ g x) : is_local_extr_on (g ∘ f) s a :=
  is_extr_filter.comp_antimono hf hg

theorem is_local_min.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_local_min f a) {g : α → γ} (hg : is_local_min g a) : is_local_min (fun (x : α) => op (f x) (g x)) a :=
  is_min_filter.bicomp_mono hop hf hg

theorem is_local_max.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [preorder β] [preorder γ] {f : α → β} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_local_max f a) {g : α → γ} (hg : is_local_max g a) : is_local_max (fun (x : α) => op (f x) (g x)) a :=
  is_max_filter.bicomp_mono hop hf hg

-- No `extr` version because we need `hf` and `hg` to be of the same kind

theorem is_local_min_on.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_local_min_on f s a) {g : α → γ} (hg : is_local_min_on g s a) : is_local_min_on (fun (x : α) => op (f x) (g x)) s a :=
  is_min_filter.bicomp_mono hop hf hg

theorem is_local_max_on.bicomp_mono {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α] [preorder β] [preorder γ] {f : α → β} {s : set α} {a : α} [preorder δ] {op : β → γ → δ} (hop : relator.lift_fun LessEq (LessEq ⇒ LessEq) op op) (hf : is_local_max_on f s a) {g : α → γ} (hg : is_local_max_on g s a) : is_local_max_on (fun (x : α) => op (f x) (g x)) s a :=
  is_max_filter.bicomp_mono hop hf hg

/-! ### Composition with `continuous_at` -/

theorem is_local_min.comp_continuous {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {g : δ → α} {b : δ} (hf : is_local_min f (g b)) (hg : continuous_at g b) : is_local_min (f ∘ g) b :=
  hg hf

theorem is_local_max.comp_continuous {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {g : δ → α} {b : δ} (hf : is_local_max f (g b)) (hg : continuous_at g b) : is_local_max (f ∘ g) b :=
  hg hf

theorem is_local_extr.comp_continuous {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {g : δ → α} {b : δ} (hf : is_local_extr f (g b)) (hg : continuous_at g b) : is_local_extr (f ∘ g) b :=
  is_extr_filter.comp_tendsto hf hg

theorem is_local_min.comp_continuous_on {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {s : set δ} {g : δ → α} {b : δ} (hf : is_local_min f (g b)) (hg : continuous_on g s) (hb : b ∈ s) : is_local_min_on (f ∘ g) s b :=
  is_min_filter.comp_tendsto hf (hg b hb)

theorem is_local_max.comp_continuous_on {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {s : set δ} {g : δ → α} {b : δ} (hf : is_local_max f (g b)) (hg : continuous_on g s) (hb : b ∈ s) : is_local_max_on (f ∘ g) s b :=
  is_max_filter.comp_tendsto hf (hg b hb)

theorem is_local_extr.comp_continuous_on {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {s : set δ} (g : δ → α) {b : δ} (hf : is_local_extr f (g b)) (hg : continuous_on g s) (hb : b ∈ s) : is_local_extr_on (f ∘ g) s b :=
  is_local_extr.elim hf
    (fun (hf : is_local_min f (g b)) => is_min_filter.is_extr (is_local_min.comp_continuous_on hf hg hb))
    fun (hf : is_local_max f (g b)) => is_max_filter.is_extr (is_local_max.comp_continuous_on hf hg hb)

theorem is_local_min_on.comp_continuous_on {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {t : set α} {s : set δ} {g : δ → α} {b : δ} (hf : is_local_min_on f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : continuous_on g s) (hb : b ∈ s) : is_local_min_on (f ∘ g) s b :=
  is_min_filter.comp_tendsto hf
    (tendsto_nhds_within_mono_right (iff.mpr set.image_subset_iff hst)
      (continuous_within_at.tendsto_nhds_within_image (hg b hb)))

theorem is_local_max_on.comp_continuous_on {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {t : set α} {s : set δ} {g : δ → α} {b : δ} (hf : is_local_max_on f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : continuous_on g s) (hb : b ∈ s) : is_local_max_on (f ∘ g) s b :=
  is_max_filter.comp_tendsto hf
    (tendsto_nhds_within_mono_right (iff.mpr set.image_subset_iff hst)
      (continuous_within_at.tendsto_nhds_within_image (hg b hb)))

theorem is_local_extr_on.comp_continuous_on {α : Type u} {β : Type v} {δ : Type x} [topological_space α] [preorder β] {f : α → β} [topological_space δ] {t : set α} {s : set δ} (g : δ → α) {b : δ} (hf : is_local_extr_on f t (g b)) (hst : s ⊆ g ⁻¹' t) (hg : continuous_on g s) (hb : b ∈ s) : is_local_extr_on (f ∘ g) s b :=
  is_local_extr_on.elim hf
    (fun (hf : is_local_min_on f t (g b)) => is_min_filter.is_extr (is_local_min_on.comp_continuous_on hf hst hg hb))
    fun (hf : is_local_max_on f t (g b)) => is_max_filter.is_extr (is_local_max_on.comp_continuous_on hf hst hg hb)

/-! ### Pointwise addition -/

theorem is_local_min.add {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} (hf : is_local_min f a) (hg : is_local_min g a) : is_local_min (fun (x : α) => f x + g x) a :=
  is_min_filter.add hf hg

theorem is_local_max.add {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} (hf : is_local_max f a) (hg : is_local_max g a) : is_local_max (fun (x : α) => f x + g x) a :=
  is_max_filter.add hf hg

theorem is_local_min_on.add {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) : is_local_min_on (fun (x : α) => f x + g x) s a :=
  is_min_filter.add hf hg

theorem is_local_max_on.add {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_monoid β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) : is_local_max_on (fun (x : α) => f x + g x) s a :=
  is_max_filter.add hf hg

/-! ### Pointwise negation and subtraction -/

theorem is_local_min.neg {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {a : α} (hf : is_local_min f a) : is_local_max (fun (x : α) => -f x) a :=
  is_min_filter.neg hf

theorem is_local_max.neg {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {a : α} (hf : is_local_max f a) : is_local_min (fun (x : α) => -f x) a :=
  is_max_filter.neg hf

theorem is_local_extr.neg {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {a : α} (hf : is_local_extr f a) : is_local_extr (fun (x : α) => -f x) a :=
  is_extr_filter.neg hf

theorem is_local_min_on.neg {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) : is_local_max_on (fun (x : α) => -f x) s a :=
  is_min_filter.neg hf

theorem is_local_max_on.neg {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) : is_local_min_on (fun (x : α) => -f x) s a :=
  is_max_filter.neg hf

theorem is_local_extr_on.neg {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {a : α} {s : set α} (hf : is_local_extr_on f s a) : is_local_extr_on (fun (x : α) => -f x) s a :=
  is_extr_filter.neg hf

theorem is_local_min.sub {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} (hf : is_local_min f a) (hg : is_local_max g a) : is_local_min (fun (x : α) => f x - g x) a :=
  is_min_filter.sub hf hg

theorem is_local_max.sub {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} (hf : is_local_max f a) (hg : is_local_min g a) : is_local_max (fun (x : α) => f x - g x) a :=
  is_max_filter.sub hf hg

theorem is_local_min_on.sub {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) (hg : is_local_max_on g s a) : is_local_min_on (fun (x : α) => f x - g x) s a :=
  is_min_filter.sub hf hg

theorem is_local_max_on.sub {α : Type u} {β : Type v} [topological_space α] [ordered_add_comm_group β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) (hg : is_local_min_on g s a) : is_local_max_on (fun (x : α) => f x - g x) s a :=
  is_max_filter.sub hf hg

/-! ### Pointwise `sup`/`inf` -/

theorem is_local_min.sup {α : Type u} {β : Type v} [topological_space α] [semilattice_sup β] {f : α → β} {g : α → β} {a : α} (hf : is_local_min f a) (hg : is_local_min g a) : is_local_min (fun (x : α) => f x ⊔ g x) a :=
  is_min_filter.sup hf hg

theorem is_local_max.sup {α : Type u} {β : Type v} [topological_space α] [semilattice_sup β] {f : α → β} {g : α → β} {a : α} (hf : is_local_max f a) (hg : is_local_max g a) : is_local_max (fun (x : α) => f x ⊔ g x) a :=
  is_max_filter.sup hf hg

theorem is_local_min_on.sup {α : Type u} {β : Type v} [topological_space α] [semilattice_sup β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) : is_local_min_on (fun (x : α) => f x ⊔ g x) s a :=
  is_min_filter.sup hf hg

theorem is_local_max_on.sup {α : Type u} {β : Type v} [topological_space α] [semilattice_sup β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) : is_local_max_on (fun (x : α) => f x ⊔ g x) s a :=
  is_max_filter.sup hf hg

theorem is_local_min.inf {α : Type u} {β : Type v} [topological_space α] [semilattice_inf β] {f : α → β} {g : α → β} {a : α} (hf : is_local_min f a) (hg : is_local_min g a) : is_local_min (fun (x : α) => f x ⊓ g x) a :=
  is_min_filter.inf hf hg

theorem is_local_max.inf {α : Type u} {β : Type v} [topological_space α] [semilattice_inf β] {f : α → β} {g : α → β} {a : α} (hf : is_local_max f a) (hg : is_local_max g a) : is_local_max (fun (x : α) => f x ⊓ g x) a :=
  is_max_filter.inf hf hg

theorem is_local_min_on.inf {α : Type u} {β : Type v} [topological_space α] [semilattice_inf β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) : is_local_min_on (fun (x : α) => f x ⊓ g x) s a :=
  is_min_filter.inf hf hg

theorem is_local_max_on.inf {α : Type u} {β : Type v} [topological_space α] [semilattice_inf β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) : is_local_max_on (fun (x : α) => f x ⊓ g x) s a :=
  is_max_filter.inf hf hg

/-! ### Pointwise `min`/`max` -/

theorem is_local_min.min {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} (hf : is_local_min f a) (hg : is_local_min g a) : is_local_min (fun (x : α) => min (f x) (g x)) a :=
  is_min_filter.min hf hg

theorem is_local_max.min {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} (hf : is_local_max f a) (hg : is_local_max g a) : is_local_max (fun (x : α) => min (f x) (g x)) a :=
  is_max_filter.min hf hg

theorem is_local_min_on.min {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) : is_local_min_on (fun (x : α) => min (f x) (g x)) s a :=
  is_min_filter.min hf hg

theorem is_local_max_on.min {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) : is_local_max_on (fun (x : α) => min (f x) (g x)) s a :=
  is_max_filter.min hf hg

theorem is_local_min.max {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} (hf : is_local_min f a) (hg : is_local_min g a) : is_local_min (fun (x : α) => max (f x) (g x)) a :=
  is_min_filter.max hf hg

theorem is_local_max.max {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} (hf : is_local_max f a) (hg : is_local_max g a) : is_local_max (fun (x : α) => max (f x) (g x)) a :=
  is_max_filter.max hf hg

theorem is_local_min_on.max {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_min_on f s a) (hg : is_local_min_on g s a) : is_local_min_on (fun (x : α) => max (f x) (g x)) s a :=
  is_min_filter.max hf hg

theorem is_local_max_on.max {α : Type u} {β : Type v} [topological_space α] [linear_order β] {f : α → β} {g : α → β} {a : α} {s : set α} (hf : is_local_max_on f s a) (hg : is_local_max_on g s a) : is_local_max_on (fun (x : α) => max (f x) (g x)) s a :=
  is_max_filter.max hf hg

/-! ### Relation with `eventually` comparisons of two functions -/

theorem filter.eventually_le.is_local_max_on {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (hle : filter.eventually_le (nhds_within a s) g f) (hfga : f a = g a) (h : is_local_max_on f s a) : is_local_max_on g s a :=
  filter.eventually_le.is_max_filter hle hfga h

theorem is_local_max_on.congr {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (h : is_local_max_on f s a) (heq : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : is_local_max_on g s a :=
  is_max_filter.congr h heq (filter.eventually_eq.eq_of_nhds_within heq hmem)

theorem filter.eventually_eq.is_local_max_on_iff {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (heq : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : is_local_max_on f s a ↔ is_local_max_on g s a :=
  filter.eventually_eq.is_max_filter_iff heq (filter.eventually_eq.eq_of_nhds_within heq hmem)

theorem filter.eventually_le.is_local_min_on {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (hle : filter.eventually_le (nhds_within a s) f g) (hfga : f a = g a) (h : is_local_min_on f s a) : is_local_min_on g s a :=
  filter.eventually_le.is_min_filter hle hfga h

theorem is_local_min_on.congr {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (h : is_local_min_on f s a) (heq : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : is_local_min_on g s a :=
  is_min_filter.congr h heq (filter.eventually_eq.eq_of_nhds_within heq hmem)

theorem filter.eventually_eq.is_local_min_on_iff {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (heq : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : is_local_min_on f s a ↔ is_local_min_on g s a :=
  filter.eventually_eq.is_min_filter_iff heq (filter.eventually_eq.eq_of_nhds_within heq hmem)

theorem is_local_extr_on.congr {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (h : is_local_extr_on f s a) (heq : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : is_local_extr_on g s a :=
  is_extr_filter.congr h heq (filter.eventually_eq.eq_of_nhds_within heq hmem)

theorem filter.eventually_eq.is_local_extr_on_iff {α : Type u} {β : Type v} [topological_space α] [preorder β] {s : set α} {f : α → β} {g : α → β} {a : α} (heq : filter.eventually_eq (nhds_within a s) f g) (hmem : a ∈ s) : is_local_extr_on f s a ↔ is_local_extr_on g s a :=
  filter.eventually_eq.is_extr_filter_iff heq (filter.eventually_eq.eq_of_nhds_within heq hmem)

theorem filter.eventually_le.is_local_max {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (hle : filter.eventually_le (nhds a) g f) (hfga : f a = g a) (h : is_local_max f a) : is_local_max g a :=
  filter.eventually_le.is_max_filter hle hfga h

theorem is_local_max.congr {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (h : is_local_max f a) (heq : filter.eventually_eq (nhds a) f g) : is_local_max g a :=
  is_max_filter.congr h heq (filter.eventually_eq.eq_of_nhds heq)

theorem filter.eventually_eq.is_local_max_iff {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (heq : filter.eventually_eq (nhds a) f g) : is_local_max f a ↔ is_local_max g a :=
  filter.eventually_eq.is_max_filter_iff heq (filter.eventually_eq.eq_of_nhds heq)

theorem filter.eventually_le.is_local_min {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (hle : filter.eventually_le (nhds a) f g) (hfga : f a = g a) (h : is_local_min f a) : is_local_min g a :=
  filter.eventually_le.is_min_filter hle hfga h

theorem is_local_min.congr {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (h : is_local_min f a) (heq : filter.eventually_eq (nhds a) f g) : is_local_min g a :=
  is_min_filter.congr h heq (filter.eventually_eq.eq_of_nhds heq)

theorem filter.eventually_eq.is_local_min_iff {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (heq : filter.eventually_eq (nhds a) f g) : is_local_min f a ↔ is_local_min g a :=
  filter.eventually_eq.is_min_filter_iff heq (filter.eventually_eq.eq_of_nhds heq)

theorem is_local_extr.congr {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (h : is_local_extr f a) (heq : filter.eventually_eq (nhds a) f g) : is_local_extr g a :=
  is_extr_filter.congr h heq (filter.eventually_eq.eq_of_nhds heq)

theorem filter.eventually_eq.is_local_extr_iff {α : Type u} {β : Type v} [topological_space α] [preorder β] {f : α → β} {g : α → β} {a : α} (heq : filter.eventually_eq (nhds a) f g) : is_local_extr f a ↔ is_local_extr g a :=
  filter.eventually_eq.is_extr_filter_iff heq (filter.eventually_eq.eq_of_nhds heq)

