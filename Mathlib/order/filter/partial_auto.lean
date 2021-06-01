/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Extends `tendsto` to relations and partial functions.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.filter.basic
import Mathlib.PostPort

universes u v w 

namespace Mathlib

namespace filter


/-
Relations.
-/

def rmap {α : Type u} {β : Type v} (r : rel α β) (f : filter α) : filter β :=
  mk (set_of fun (s : set β) => rel.core r s ∈ f) sorry sorry sorry

theorem rmap_sets {α : Type u} {β : Type v} (r : rel α β) (f : filter α) :
    sets (rmap r f) = rel.core r ⁻¹' sets f :=
  rfl

@[simp] theorem mem_rmap {α : Type u} {β : Type v} (r : rel α β) (l : filter α) (s : set β) :
    s ∈ rmap r l ↔ rel.core r s ∈ l :=
  iff.rfl

@[simp] theorem rmap_rmap {α : Type u} {β : Type v} {γ : Type w} (r : rel α β) (s : rel β γ)
    (l : filter α) : rmap s (rmap r l) = rmap (rel.comp r s) l :=
  sorry

@[simp] theorem rmap_compose {α : Type u} {β : Type v} {γ : Type w} (r : rel α β) (s : rel β γ) :
    rmap s ∘ rmap r = rmap (rel.comp r s) :=
  funext (rmap_rmap r s)

def rtendsto {α : Type u} {β : Type v} (r : rel α β) (l₁ : filter α) (l₂ : filter β) :=
  rmap r l₁ ≤ l₂

theorem rtendsto_def {α : Type u} {β : Type v} (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
    rtendsto r l₁ l₂ ↔ ∀ (s : set β), s ∈ l₂ → rel.core r s ∈ l₁ :=
  iff.rfl

def rcomap {α : Type u} {β : Type v} (r : rel α β) (f : filter β) : filter α :=
  mk (rel.image (fun (s : set β) (t : set α) => rel.core r s ⊆ t) (sets f)) sorry sorry sorry

theorem rcomap_sets {α : Type u} {β : Type v} (r : rel α β) (f : filter β) :
    sets (rcomap r f) = rel.image (fun (s : set β) (t : set α) => rel.core r s ⊆ t) (sets f) :=
  rfl

@[simp] theorem rcomap_rcomap {α : Type u} {β : Type v} {γ : Type w} (r : rel α β) (s : rel β γ)
    (l : filter γ) : rcomap r (rcomap s l) = rcomap (rel.comp r s) l :=
  sorry

@[simp] theorem rcomap_compose {α : Type u} {β : Type v} {γ : Type w} (r : rel α β) (s : rel β γ) :
    rcomap r ∘ rcomap s = rcomap (rel.comp r s) :=
  funext (rcomap_rcomap r s)

theorem rtendsto_iff_le_comap {α : Type u} {β : Type v} (r : rel α β) (l₁ : filter α)
    (l₂ : filter β) : rtendsto r l₁ l₂ ↔ l₁ ≤ rcomap r l₂ :=
  sorry

-- Interestingly, there does not seem to be a way to express this relation using a forward map.

-- Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f` if

-- and only if `s ∈ f'`. But the intersection of two sets satsifying the lhs may be empty.

def rcomap' {α : Type u} {β : Type v} (r : rel α β) (f : filter β) : filter α :=
  mk (rel.image (fun (s : set β) (t : set α) => rel.preimage r s ⊆ t) (sets f)) sorry sorry sorry

@[simp] theorem mem_rcomap' {α : Type u} {β : Type v} (r : rel α β) (l : filter β) (s : set α) :
    s ∈ rcomap' r l ↔ ∃ (t : set β), ∃ (H : t ∈ l), rel.preimage r t ⊆ s :=
  iff.rfl

theorem rcomap'_sets {α : Type u} {β : Type v} (r : rel α β) (f : filter β) :
    sets (rcomap' r f) = rel.image (fun (s : set β) (t : set α) => rel.preimage r s ⊆ t) (sets f) :=
  rfl

@[simp] theorem rcomap'_rcomap' {α : Type u} {β : Type v} {γ : Type w} (r : rel α β) (s : rel β γ)
    (l : filter γ) : rcomap' r (rcomap' s l) = rcomap' (rel.comp r s) l :=
  sorry

@[simp] theorem rcomap'_compose {α : Type u} {β : Type v} {γ : Type w} (r : rel α β) (s : rel β γ) :
    rcomap' r ∘ rcomap' s = rcomap' (rel.comp r s) :=
  funext (rcomap'_rcomap' r s)

def rtendsto' {α : Type u} {β : Type v} (r : rel α β) (l₁ : filter α) (l₂ : filter β) :=
  l₁ ≤ rcomap' r l₂

theorem rtendsto'_def {α : Type u} {β : Type v} (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
    rtendsto' r l₁ l₂ ↔ ∀ (s : set β), s ∈ l₂ → rel.preimage r s ∈ l₁ :=
  sorry

theorem tendsto_iff_rtendsto {α : Type u} {β : Type v} (l₁ : filter α) (l₂ : filter β) (f : α → β) :
    tendsto f l₁ l₂ ↔ rtendsto (function.graph f) l₁ l₂ :=
  sorry

theorem tendsto_iff_rtendsto' {α : Type u} {β : Type v} (l₁ : filter α) (l₂ : filter β)
    (f : α → β) : tendsto f l₁ l₂ ↔ rtendsto' (function.graph f) l₁ l₂ :=
  sorry

/-
Partial functions.
-/

def pmap {α : Type u} {β : Type v} (f : α →. β) (l : filter α) : filter β := rmap (pfun.graph' f) l

@[simp] theorem mem_pmap {α : Type u} {β : Type v} (f : α →. β) (l : filter α) (s : set β) :
    s ∈ pmap f l ↔ pfun.core f s ∈ l :=
  iff.rfl

def ptendsto {α : Type u} {β : Type v} (f : α →. β) (l₁ : filter α) (l₂ : filter β) :=
  pmap f l₁ ≤ l₂

theorem ptendsto_def {α : Type u} {β : Type v} (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
    ptendsto f l₁ l₂ ↔ ∀ (s : set β), s ∈ l₂ → pfun.core f s ∈ l₁ :=
  iff.rfl

theorem ptendsto_iff_rtendsto {α : Type u} {β : Type v} (l₁ : filter α) (l₂ : filter β)
    (f : α →. β) : ptendsto f l₁ l₂ ↔ rtendsto (pfun.graph' f) l₁ l₂ :=
  iff.rfl

theorem pmap_res {α : Type u} {β : Type v} (l : filter α) (s : set α) (f : α → β) :
    pmap (pfun.res f s) l = map f (l ⊓ principal s) :=
  sorry

theorem tendsto_iff_ptendsto {α : Type u} {β : Type v} (l₁ : filter α) (l₂ : filter β) (s : set α)
    (f : α → β) : tendsto f (l₁ ⊓ principal s) l₂ ↔ ptendsto (pfun.res f s) l₁ l₂ :=
  sorry

theorem tendsto_iff_ptendsto_univ {α : Type u} {β : Type v} (l₁ : filter α) (l₂ : filter β)
    (f : α → β) : tendsto f l₁ l₂ ↔ ptendsto (pfun.res f set.univ) l₁ l₂ :=
  sorry

def pcomap' {α : Type u} {β : Type v} (f : α →. β) (l : filter β) : filter α :=
  rcomap' (pfun.graph' f) l

def ptendsto' {α : Type u} {β : Type v} (f : α →. β) (l₁ : filter α) (l₂ : filter β) :=
  l₁ ≤ rcomap' (pfun.graph' f) l₂

theorem ptendsto'_def {α : Type u} {β : Type v} (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
    ptendsto' f l₁ l₂ ↔ ∀ (s : set β), s ∈ l₂ → pfun.preimage f s ∈ l₁ :=
  rtendsto'_def (pfun.graph' f) l₁ l₂

theorem ptendsto_of_ptendsto' {α : Type u} {β : Type v} {f : α →. β} {l₁ : filter α}
    {l₂ : filter β} : ptendsto' f l₁ l₂ → ptendsto f l₁ l₂ :=
  sorry

theorem ptendsto'_of_ptendsto {α : Type u} {β : Type v} {f : α →. β} {l₁ : filter α} {l₂ : filter β}
    (h : pfun.dom f ∈ l₁) : ptendsto f l₁ l₂ → ptendsto' f l₁ l₂ :=
  sorry

end Mathlib