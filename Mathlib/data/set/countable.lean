/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.list
import Mathlib.data.set.finite
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

/-!
# Countable sets
-/

namespace set


/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
def countable {α : Type u} (s : set α) :=
  Nonempty (encodable ↥s)

theorem countable_iff_exists_injective {α : Type u} {s : set α} : countable s ↔ ∃ (f : ↥s → ℕ), function.injective f := sorry

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
theorem countable_iff_exists_inj_on {α : Type u} {s : set α} : countable s ↔ ∃ (f : α → ℕ), inj_on f s := sorry

theorem countable_iff_exists_surjective {α : Type u} [ne : Nonempty α] {s : set α} : countable s ↔ ∃ (f : ℕ → α), s ⊆ range f := sorry

/--
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
theorem countable_iff_exists_surjective_to_subtype {α : Type u} {s : set α} (hs : set.nonempty s) : countable s ↔ ∃ (f : ℕ → ↥s), function.surjective f := sorry

/-- Convert `countable s` to `encodable s` (noncomputable). -/
def countable.to_encodable {α : Type u} {s : set α} : countable s → encodable ↥s :=
  Classical.choice

theorem countable_encodable' {α : Type u} (s : set α) [H : encodable ↥s] : countable s :=
  Nonempty.intro H

theorem countable_encodable {α : Type u} [encodable α] (s : set α) : countable s :=
  Nonempty.intro encodable.subtype

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
theorem countable.exists_surjective {α : Type u} {s : set α} (hc : countable s) (hs : set.nonempty s) : ∃ (f : ℕ → α), s = range f := sorry

@[simp] theorem countable_empty {α : Type u} : countable ∅ :=
  Nonempty.intro
    (encodable.mk (fun (x : ↥∅) => false.elim (subtype.property x)) (fun (n : ℕ) => none)
      fun (x : ↥∅) => false.elim (subtype.property x))

@[simp] theorem countable_singleton {α : Type u} (a : α) : countable (singleton a) :=
  Nonempty.intro (encodable.of_equiv PUnit (equiv.set.singleton a))

theorem countable.mono {α : Type u} {s₁ : set α} {s₂ : set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁ := sorry

theorem countable.image {α : Type u} {β : Type v} {s : set α} (hs : countable s) (f : α → β) : countable (f '' s) := sorry

theorem countable_range {α : Type u} {β : Type v} [encodable α] (f : α → β) : countable (range f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable (range f))) (Eq.symm image_univ)))
    (countable.image (countable_encodable univ) f)

theorem exists_seq_supr_eq_top_iff_countable {α : Type u} [complete_lattice α] {p : α → Prop} (h : ∃ (x : α), p x) : (∃ (s : ℕ → α), (∀ (n : ℕ), p (s n)) ∧ (supr fun (n : ℕ) => s n) = ⊤) ↔
  ∃ (S : set α), countable S ∧ (∀ (s : α), s ∈ S → p s) ∧ Sup S = ⊤ := sorry

theorem exists_seq_cover_iff_countable {α : Type u} {p : set α → Prop} (h : ∃ (s : set α), p s) : (∃ (s : ℕ → set α), (∀ (n : ℕ), p (s n)) ∧ (Union fun (n : ℕ) => s n) = univ) ↔
  ∃ (S : set (set α)), countable S ∧ (∀ (s : set α), s ∈ S → p s) ∧ ⋃₀S = univ :=
  exists_seq_supr_eq_top_iff_countable h

theorem countable_of_injective_of_countable_image {α : Type u} {β : Type v} {s : set α} {f : α → β} (hf : inj_on f s) (hs : countable (f '' s)) : countable s := sorry

theorem countable_Union {α : Type u} {β : Type v} {t : α → set β} [encodable α] (ht : ∀ (a : α), countable (t a)) : countable (Union fun (a : α) => t a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable (Union fun (a : α) => t a))) (Union_eq_range_sigma fun (a : α) => t a)))
    (countable_range fun (a : sigma fun (i : α) => ↥(t i)) => ↑(sigma.snd a))

theorem countable.bUnion {α : Type u} {β : Type v} {s : set α} {t : (x : α) → x ∈ s → set β} (hs : countable s) (ht : ∀ (a : α) (H : a ∈ s), countable (t a H)) : countable (Union fun (a : α) => Union fun (H : a ∈ s) => t a H) := sorry

theorem countable.sUnion {α : Type u} {s : set (set α)} (hs : countable s) (h : ∀ (a : set α), a ∈ s → countable a) : countable (⋃₀s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable (⋃₀s))) sUnion_eq_bUnion)) (countable.bUnion hs h)

theorem countable_Union_Prop {β : Type v} {p : Prop} {t : p → set β} (ht : ∀ (h : p), countable (t h)) : countable (Union fun (h : p) => t h) := sorry

theorem countable.union {α : Type u} {s₁ : set α} {s₂ : set α} (h₁ : countable s₁) (h₂ : countable s₂) : countable (s₁ ∪ s₂) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable (s₁ ∪ s₂))) union_eq_Union))
    (countable_Union (iff.mpr bool.forall_bool { left := h₂, right := h₁ }))

theorem countable.insert {α : Type u} {s : set α} (a : α) (h : countable s) : countable (insert a s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countable (insert a s))) (insert_eq a s))) (countable.union (countable_singleton a) h)

theorem finite.countable {α : Type u} {s : set α} : finite s → countable s := sorry

/-- The set of finite subsets of a countable set is countable. -/
theorem countable_set_of_finite_subset {α : Type u} {s : set α} : countable s → countable (set_of fun (t : set α) => finite t ∧ t ⊆ s) := sorry

theorem countable_pi {α : Type u} {π : α → Type u_1} [fintype α] {s : (a : α) → set (π a)} (hs : ∀ (a : α), countable (s a)) : countable (set_of fun (f : (a : α) → π a) => ∀ (a : α), f a ∈ s a) := sorry

theorem countable_prod {α : Type u} {β : Type v} {s : set α} {t : set β} (hs : countable s) (ht : countable t) : countable (set.prod s t) := sorry

/-- Enumerate elements in a countable set.-/
def enumerate_countable {α : Type u} {s : set α} (h : countable s) (default : α) : ℕ → α :=
  fun (n : ℕ) => sorry

theorem subset_range_enumerate {α : Type u} {s : set α} (h : countable s) (default : α) : s ⊆ range (enumerate_countable h default) := sorry

end set


theorem finset.countable_to_set {α : Type u} (s : finset α) : set.countable ↑s :=
  set.finite.countable (finset.finite_to_set s)

