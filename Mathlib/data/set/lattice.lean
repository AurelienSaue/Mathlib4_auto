/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

-- QUESTION: can make the first argument in ∀ x ∈ a, ... implicit?
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.complete_boolean_algebra
import Mathlib.data.sigma.basic
import Mathlib.order.galois_connection
import Mathlib.order.directed
import Mathlib.PostPort

universes u v x y u_1 u_2 u_3 w 

namespace Mathlib

namespace set


protected instance lattice_set {α : Type u} : complete_lattice (set α) :=
  complete_lattice.mk boolean_algebra.sup boolean_algebra.le boolean_algebra.lt sorry sorry sorry sorry sorry sorry
    boolean_algebra.inf sorry sorry sorry boolean_algebra.top sorry boolean_algebra.bot sorry
    (fun (s : set (set α)) => set_of fun (a : α) => ∃ (t : set α), ∃ (H : t ∈ s), a ∈ t)
    (fun (s : set (set α)) => set_of fun (a : α) => ∀ (t : set α), t ∈ s → a ∈ t) sorry sorry sorry sorry

/-- Image is monotone. See `set.image_image` for the statement in terms of `⊆`. -/
theorem monotone_image {α : Type u} {β : Type v} {f : α → β} : monotone (image f) :=
  fun (s t : set α) (h : s ⊆ t) => image_subset f h

theorem monotone_inter {α : Type u} {β : Type v} [preorder β] {f : β → set α} {g : β → set α} (hf : monotone f) (hg : monotone g) : monotone fun (x : β) => f x ∩ g x :=
  fun (b₁ b₂ : β) (h : b₁ ≤ b₂) => inter_subset_inter (hf h) (hg h)

theorem monotone_union {α : Type u} {β : Type v} [preorder β] {f : β → set α} {g : β → set α} (hf : monotone f) (hg : monotone g) : monotone fun (x : β) => f x ∪ g x :=
  fun (b₁ b₂ : β) (h : b₁ ≤ b₂) => union_subset_union (hf h) (hg h)

theorem monotone_set_of {α : Type u} {β : Type v} [preorder α] {p : α → β → Prop} (hp : ∀ (b : β), monotone fun (a : α) => p a b) : monotone fun (a : α) => set_of fun (b : β) => p a b :=
  fun (a a' : α) (h : a ≤ a') (b : β) => hp b h

protected theorem image_preimage {α : Type u} {β : Type v} {f : α → β} : galois_connection (image f) (preimage f) :=
  fun (a : set α) (b : set β) => image_subset_iff

/-- `kern_image f s` is the set of `y` such that `f ⁻¹ y ⊆ s` -/
def kern_image {α : Type u} {β : Type v} (f : α → β) (s : set α) : set β :=
  set_of fun (y : β) => ∀ {x : α}, f x = y → x ∈ s

protected theorem preimage_kern_image {α : Type u} {β : Type v} {f : α → β} : galois_connection (preimage f) (kern_image f) := sorry

/- union and intersection over a family of sets indexed by a type -/

/-- Indexed union of a family of sets -/
def Union {β : Type v} {ι : Sort x} (s : ι → set β) : set β :=
  supr s

/-- Indexed intersection of a family of sets -/
def Inter {β : Type v} {ι : Sort x} (s : ι → set β) : set β :=
  infi s

@[simp] theorem mem_Union {β : Type v} {ι : Sort x} {x : β} {s : ι → set β} : x ∈ Union s ↔ ∃ (i : ι), x ∈ s i := sorry

/- alternative proof: dsimp [Union, supr, Sup]; simp -/

theorem set_of_exists {β : Type v} {ι : Sort x} (p : ι → β → Prop) : (set_of fun (x : β) => ∃ (i : ι), p i x) = Union fun (i : ι) => set_of fun (x : β) => p i x :=
  ext fun (i : β) => iff.symm mem_Union

@[simp] theorem mem_Inter {β : Type v} {ι : Sort x} {x : β} {s : ι → set β} : x ∈ Inter s ↔ ∀ (i : ι), x ∈ s i := sorry

theorem set_of_forall {β : Type v} {ι : Sort x} (p : ι → β → Prop) : (set_of fun (x : β) => ∀ (i : ι), p i x) = Inter fun (i : ι) => set_of fun (x : β) => p i x :=
  ext fun (i : β) => iff.symm mem_Inter

-- TODO: should be simpler when sets' order is based on lattices

theorem Union_subset {β : Type v} {ι : Sort x} {s : ι → set β} {t : set β} (h : ∀ (i : ι), s i ⊆ t) : (Union fun (i : ι) => s i) ⊆ t :=
  supr_le h

theorem Union_subset_iff {β : Type v} {ι : Sort x} {s : ι → set β} {t : set β} : (Union fun (i : ι) => s i) ⊆ t ↔ ∀ (i : ι), s i ⊆ t :=
  { mp := fun (h : (Union fun (i : ι) => s i) ⊆ t) (i : ι) => subset.trans (le_supr s i) h, mpr := Union_subset }

theorem mem_Inter_of_mem {β : Type v} {ι : Sort x} {x : β} {s : ι → set β} : (∀ (i : ι), x ∈ s i) → x ∈ Inter fun (i : ι) => s i :=
  iff.mpr mem_Inter

-- TODO: should be simpler when sets' order is based on lattices

theorem subset_Inter {β : Type v} {ι : Sort x} {t : set β} {s : ι → set β} (h : ∀ (i : ι), t ⊆ s i) : t ⊆ Inter fun (i : ι) => s i :=
  le_infi h

theorem subset_Inter_iff {β : Type v} {ι : Sort x} {t : set β} {s : ι → set β} : (t ⊆ Inter fun (i : ι) => s i) ↔ ∀ (i : ι), t ⊆ s i :=
  le_infi_iff

theorem subset_Union {β : Type v} {ι : Sort x} (s : ι → set β) (i : ι) : s i ⊆ Union fun (i : ι) => s i :=
  le_supr

-- This rather trivial consequence is convenient with `apply`,

-- and has `i` explicit for this use case.

theorem subset_subset_Union {β : Type v} {ι : Sort x} {A : set β} {s : ι → set β} (i : ι) (h : A ⊆ s i) : A ⊆ Union fun (i : ι) => s i :=
  subset.trans h (subset_Union s i)

theorem Inter_subset {β : Type v} {ι : Sort x} (s : ι → set β) (i : ι) : (Inter fun (i : ι) => s i) ⊆ s i :=
  infi_le

theorem Inter_subset_of_subset {α : Type u} {ι : Sort x} {s : ι → set α} {t : set α} (i : ι) (h : s i ⊆ t) : (Inter fun (i : ι) => s i) ⊆ t :=
  subset.trans (Inter_subset s i) h

theorem Inter_subset_Inter {α : Type u} {ι : Sort x} {s : ι → set α} {t : ι → set α} (h : ∀ (i : ι), s i ⊆ t i) : (Inter fun (i : ι) => s i) ⊆ Inter fun (i : ι) => t i :=
  subset_Inter fun (i : ι) => Inter_subset_of_subset i (h i)

theorem Inter_subset_Inter2 {α : Type u} {ι : Sort x} {ι' : Sort y} {s : ι → set α} {t : ι' → set α} (h : ∀ (j : ι'), ∃ (i : ι), s i ⊆ t j) : (Inter fun (i : ι) => s i) ⊆ Inter fun (j : ι') => t j := sorry

theorem Inter_set_of {α : Type u} {ι : Sort x} (P : ι → α → Prop) : (Inter fun (i : ι) => set_of fun (x : α) => P i x) = set_of fun (x : α) => ∀ (i : ι), P i x := sorry

theorem Union_const {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) : (Union fun (i : ι) => s) = s := sorry

theorem Inter_const {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) : (Inter fun (i : ι) => s) = s := sorry

@[simp] theorem compl_Union {β : Type v} {ι : Sort x} (s : ι → set β) : (Union fun (i : ι) => s i)ᶜ = Inter fun (i : ι) => s iᶜ := sorry

-- classical -- complete_boolean_algebra

theorem compl_Inter {β : Type v} {ι : Sort x} (s : ι → set β) : (Inter fun (i : ι) => s i)ᶜ = Union fun (i : ι) => s iᶜ := sorry

-- classical -- complete_boolean_algebra

theorem Union_eq_comp_Inter_comp {β : Type v} {ι : Sort x} (s : ι → set β) : (Union fun (i : ι) => s i) = ((Inter fun (i : ι) => s iᶜ)ᶜ) := sorry

-- classical -- complete_boolean_algebra

theorem Inter_eq_comp_Union_comp {β : Type v} {ι : Sort x} (s : ι → set β) : (Inter fun (i : ι) => s i) = ((Union fun (i : ι) => s iᶜ)ᶜ) := sorry

theorem inter_Union {β : Type v} {ι : Sort x} (s : set β) (t : ι → set β) : (s ∩ Union fun (i : ι) => t i) = Union fun (i : ι) => s ∩ t i := sorry

theorem Union_inter {β : Type v} {ι : Sort x} (s : set β) (t : ι → set β) : (Union fun (i : ι) => t i) ∩ s = Union fun (i : ι) => t i ∩ s := sorry

theorem Union_union_distrib {β : Type v} {ι : Sort x} (s : ι → set β) (t : ι → set β) : (Union fun (i : ι) => s i ∪ t i) = (Union fun (i : ι) => s i) ∪ Union fun (i : ι) => t i := sorry

theorem Inter_inter_distrib {β : Type v} {ι : Sort x} (s : ι → set β) (t : ι → set β) : (Inter fun (i : ι) => s i ∩ t i) = (Inter fun (i : ι) => s i) ∩ Inter fun (i : ι) => t i := sorry

theorem union_Union {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) (t : ι → set β) : (s ∪ Union fun (i : ι) => t i) = Union fun (i : ι) => s ∪ t i := sorry

theorem Union_union {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) (t : ι → set β) : (Union fun (i : ι) => t i) ∪ s = Union fun (i : ι) => t i ∪ s := sorry

theorem inter_Inter {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) (t : ι → set β) : (s ∩ Inter fun (i : ι) => t i) = Inter fun (i : ι) => s ∩ t i := sorry

theorem Inter_inter {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) (t : ι → set β) : (Inter fun (i : ι) => t i) ∩ s = Inter fun (i : ι) => t i ∩ s := sorry

-- classical

theorem union_Inter {β : Type v} {ι : Sort x} (s : set β) (t : ι → set β) : (s ∪ Inter fun (i : ι) => t i) = Inter fun (i : ι) => s ∪ t i := sorry

theorem Union_diff {β : Type v} {ι : Sort x} (s : set β) (t : ι → set β) : (Union fun (i : ι) => t i) \ s = Union fun (i : ι) => t i \ s :=
  Union_inter (fun (a : β) => a ∈ s → False) fun (i : ι) => t i

theorem diff_Union {β : Type v} {ι : Sort x} [Nonempty ι] (s : set β) (t : ι → set β) : (s \ Union fun (i : ι) => t i) = Inter fun (i : ι) => s \ t i := sorry

theorem diff_Inter {β : Type v} {ι : Sort x} (s : set β) (t : ι → set β) : (s \ Inter fun (i : ι) => t i) = Union fun (i : ι) => s \ t i := sorry

theorem directed_on_Union {α : Type u} {r : α → α → Prop} {ι : Sort v} {f : ι → set α} (hd : directed has_subset.subset f) (h : ∀ (x : ι), directed_on r (f x)) : directed_on r (Union fun (x : ι) => f x) := sorry

theorem Union_inter_subset {ι : Sort u_1} {α : Type u_2} {s : ι → set α} {t : ι → set α} : (Union fun (i : ι) => s i ∩ t i) ⊆ (Union fun (i : ι) => s i) ∩ Union fun (i : ι) => t i := sorry

theorem Union_inter_of_monotone {ι : Type u_1} {α : Type u_2} [semilattice_sup ι] {s : ι → set α} {t : ι → set α} (hs : monotone s) (ht : monotone t) : (Union fun (i : ι) => s i ∩ t i) = (Union fun (i : ι) => s i) ∩ Union fun (i : ι) => t i := sorry

/-- An equality version of this lemma is `Union_Inter_of_monotone` in `data.set.finite`. -/
theorem Union_Inter_subset {ι : Sort u_1} {ι' : Sort u_2} {α : Type u_3} {s : ι → ι' → set α} : (Union fun (j : ι') => Inter fun (i : ι) => s i j) ⊆ Inter fun (i : ι) => Union fun (j : ι') => s i j := sorry

/- bounded unions and intersections -/

theorem mem_bUnion_iff {α : Type u} {β : Type v} {s : set α} {t : α → set β} {y : β} : (y ∈ Union fun (x : α) => Union fun (H : x ∈ s) => t x) ↔ ∃ (x : α), ∃ (H : x ∈ s), y ∈ t x := sorry

theorem mem_bInter_iff {α : Type u} {β : Type v} {s : set α} {t : α → set β} {y : β} : (y ∈ Inter fun (x : α) => Inter fun (H : x ∈ s) => t x) ↔ ∀ (x : α), x ∈ s → y ∈ t x := sorry

theorem mem_bUnion {α : Type u} {β : Type v} {s : set α} {t : α → set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) : y ∈ Union fun (x : α) => Union fun (H : x ∈ s) => t x := sorry

theorem mem_bInter {α : Type u} {β : Type v} {s : set α} {t : α → set β} {y : β} (h : ∀ (x : α), x ∈ s → y ∈ t x) : y ∈ Inter fun (x : α) => Inter fun (H : x ∈ s) => t x :=
  eq.mpr (id (Eq.trans (propext mem_Inter) (forall_congr_eq fun (i : α) => propext mem_Inter))) h

theorem bUnion_subset {α : Type u} {β : Type v} {s : set α} {t : set β} {u : α → set β} (h : ∀ (x : α), x ∈ s → u x ⊆ t) : (Union fun (x : α) => Union fun (H : x ∈ s) => u x) ⊆ t :=
  (fun (this : (supr fun (x : α) => supr fun (H : x ∈ s) => u x) ≤ t) => this) (supr_le fun (x : α) => supr_le (h x))

theorem subset_bInter {α : Type u} {β : Type v} {s : set α} {t : set β} {u : α → set β} (h : ∀ (x : α), x ∈ s → t ⊆ u x) : t ⊆ Inter fun (x : α) => Inter fun (H : x ∈ s) => u x :=
  subset_Inter fun (x : α) => subset_Inter (h x)

theorem subset_bUnion_of_mem {α : Type u} {β : Type v} {s : set α} {u : α → set β} {x : α} (xs : x ∈ s) : u x ⊆ Union fun (x : α) => Union fun (H : x ∈ s) => u x :=
  (fun (this : u x ≤ supr fun (x : α) => supr fun (H : x ∈ s) => u x) => this)
    (le_supr_of_le x (le_supr (fun (xs : x ∈ s) => u x) xs))

theorem bInter_subset_of_mem {α : Type u} {β : Type v} {s : set α} {t : α → set β} {x : α} (xs : x ∈ s) : (Inter fun (x : α) => Inter fun (H : x ∈ s) => t x) ⊆ t x :=
  (fun (this : (infi fun (x : α) => infi fun (H : x ∈ s) => t x) ≤ t x) => this)
    (infi_le_of_le x (infi_le (fun (H : x ∈ s) => t x) xs))

theorem bUnion_subset_bUnion_left {α : Type u} {β : Type v} {s : set α} {s' : set α} {t : α → set β} (h : s ⊆ s') : (Union fun (x : α) => Union fun (H : x ∈ s) => t x) ⊆ Union fun (x : α) => Union fun (H : x ∈ s') => t x :=
  bUnion_subset fun (x : α) (xs : x ∈ s) => subset_bUnion_of_mem (h xs)

theorem bInter_subset_bInter_left {α : Type u} {β : Type v} {s : set α} {s' : set α} {t : α → set β} (h : s' ⊆ s) : (Inter fun (x : α) => Inter fun (H : x ∈ s) => t x) ⊆ Inter fun (x : α) => Inter fun (H : x ∈ s') => t x :=
  subset_bInter fun (x : α) (xs : x ∈ s') => bInter_subset_of_mem (h xs)

theorem bUnion_subset_bUnion_right {α : Type u} {β : Type v} {s : set α} {t1 : α → set β} {t2 : α → set β} (h : ∀ (x : α), x ∈ s → t1 x ⊆ t2 x) : (Union fun (x : α) => Union fun (H : x ∈ s) => t1 x) ⊆ Union fun (x : α) => Union fun (H : x ∈ s) => t2 x :=
  bUnion_subset fun (x : α) (xs : x ∈ s) => subset.trans (h x xs) (subset_bUnion_of_mem xs)

theorem bInter_subset_bInter_right {α : Type u} {β : Type v} {s : set α} {t1 : α → set β} {t2 : α → set β} (h : ∀ (x : α), x ∈ s → t1 x ⊆ t2 x) : (Inter fun (x : α) => Inter fun (H : x ∈ s) => t1 x) ⊆ Inter fun (x : α) => Inter fun (H : x ∈ s) => t2 x :=
  subset_bInter fun (x : α) (xs : x ∈ s) => subset.trans (bInter_subset_of_mem xs) (h x xs)

theorem bUnion_subset_bUnion {α : Type u} {β : Type v} {γ : Type u_1} {s : set α} {t : α → set β} {s' : set γ} {t' : γ → set β} (h : ∀ (x : α) (H : x ∈ s), ∃ (y : γ), ∃ (H : y ∈ s'), t x ⊆ t' y) : (Union fun (x : α) => Union fun (H : x ∈ s) => t x) ⊆ Union fun (y : γ) => Union fun (H : y ∈ s') => t' y := sorry

theorem bInter_mono' {α : Type u} {β : Type v} {s : set α} {s' : set α} {t : α → set β} {t' : α → set β} (hs : s ⊆ s') (h : ∀ (x : α), x ∈ s → t x ⊆ t' x) : (Inter fun (x : α) => Inter fun (H : x ∈ s') => t x) ⊆ Inter fun (x : α) => Inter fun (H : x ∈ s) => t' x := sorry

theorem bInter_mono {α : Type u} {β : Type v} {s : set α} {t : α → set β} {t' : α → set β} (h : ∀ (x : α), x ∈ s → t x ⊆ t' x) : (Inter fun (x : α) => Inter fun (H : x ∈ s) => t x) ⊆ Inter fun (x : α) => Inter fun (H : x ∈ s) => t' x :=
  bInter_mono' (subset.refl s) h

theorem bUnion_mono {α : Type u} {β : Type v} {s : set α} {t : α → set β} {t' : α → set β} (h : ∀ (x : α), x ∈ s → t x ⊆ t' x) : (Union fun (x : α) => Union fun (H : x ∈ s) => t x) ⊆ Union fun (x : α) => Union fun (H : x ∈ s) => t' x :=
  bUnion_subset_bUnion fun (x : α) (x_in : x ∈ s) => Exists.intro x (Exists.intro x_in (h x x_in))

theorem bUnion_eq_Union {α : Type u} {β : Type v} (s : set α) (t : (x : α) → x ∈ s → set β) : (Union fun (x : α) => Union fun (H : x ∈ s) => t x H) = Union fun (x : ↥s) => t (↑x) (subtype.property x) :=
  supr_subtype'

theorem bInter_eq_Inter {α : Type u} {β : Type v} (s : set α) (t : (x : α) → x ∈ s → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ s) => t x H) = Inter fun (x : ↥s) => t (↑x) (subtype.property x) :=
  infi_subtype'

theorem bInter_empty {α : Type u} {β : Type v} (u : α → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ ∅) => u x) = univ :=
  (fun (this : (infi fun (x : α) => infi fun (H : x ∈ ∅) => u x) = ⊤) => this) infi_emptyset

theorem bInter_univ {α : Type u} {β : Type v} (u : α → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ univ) => u x) = Inter fun (x : α) => u x :=
  infi_univ

-- TODO(Jeremy): here is an artifact of the the encoding of bounded intersection:

-- without dsimp, the next theorem fails to type check, because there is a lambda

-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.

@[simp] theorem bInter_singleton {α : Type u} {β : Type v} (a : α) (s : α → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ singleton a) => s x) = s a := sorry

theorem bInter_union {α : Type u} {β : Type v} (s : set α) (t : set α) (u : α → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ s ∪ t) => u x) =
  (Inter fun (x : α) => Inter fun (H : x ∈ s) => u x) ∩ Inter fun (x : α) => Inter fun (H : x ∈ t) => u x := sorry

-- TODO(Jeremy): simp [insert_eq, bInter_union] doesn't work

@[simp] theorem bInter_insert {α : Type u} {β : Type v} (a : α) (s : set α) (t : α → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ insert a s) => t x) = t a ∩ Inter fun (x : α) => Inter fun (H : x ∈ s) => t x := sorry

-- TODO(Jeremy): another example of where an annotation is needed

theorem bInter_pair {α : Type u} {β : Type v} (a : α) (b : α) (s : α → set β) : (Inter fun (x : α) => Inter fun (H : x ∈ insert a (singleton b)) => s x) = s a ∩ s b := sorry

theorem bUnion_empty {α : Type u} {β : Type v} (s : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ ∅) => s x) = ∅ :=
  supr_emptyset

theorem bUnion_univ {α : Type u} {β : Type v} (s : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ univ) => s x) = Union fun (x : α) => s x :=
  supr_univ

@[simp] theorem bUnion_singleton {α : Type u} {β : Type v} (a : α) (s : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ singleton a) => s x) = s a :=
  supr_singleton

@[simp] theorem bUnion_of_singleton {α : Type u} (s : set α) : (Union fun (x : α) => Union fun (H : x ∈ s) => singleton x) = s := sorry

theorem bUnion_union {α : Type u} {β : Type v} (s : set α) (t : set α) (u : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ s ∪ t) => u x) =
  (Union fun (x : α) => Union fun (H : x ∈ s) => u x) ∪ Union fun (x : α) => Union fun (H : x ∈ t) => u x :=
  supr_union

@[simp] theorem Union_subtype {α : Type u_1} {β : Type u_2} (s : set α) (f : α → set β) : (Union fun (i : ↥s) => f ↑i) = Union fun (i : α) => Union fun (H : i ∈ s) => f i :=
  Eq.symm (bUnion_eq_Union s fun (x : α) (_x : x ∈ s) => f x)

-- TODO(Jeremy): once again, simp doesn't do it alone.

@[simp] theorem bUnion_insert {α : Type u} {β : Type v} (a : α) (s : set α) (t : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ insert a s) => t x) = t a ∪ Union fun (x : α) => Union fun (H : x ∈ s) => t x := sorry

theorem bUnion_pair {α : Type u} {β : Type v} (a : α) (b : α) (s : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ insert a (singleton b)) => s x) = s a ∪ s b := sorry

@[simp] theorem compl_bUnion {α : Type u} {β : Type v} (s : set α) (t : α → set β) : (Union fun (i : α) => Union fun (H : i ∈ s) => t i)ᶜ = Inter fun (i : α) => Inter fun (H : i ∈ s) => t iᶜ := sorry

-- classical -- complete_boolean_algebra

theorem compl_bInter {α : Type u} {β : Type v} (s : set α) (t : α → set β) : (Inter fun (i : α) => Inter fun (H : i ∈ s) => t i)ᶜ = Union fun (i : α) => Union fun (H : i ∈ s) => t iᶜ := sorry

theorem inter_bUnion {α : Type u} {β : Type v} (s : set α) (t : α → set β) (u : set β) : (u ∩ Union fun (i : α) => Union fun (H : i ∈ s) => t i) = Union fun (i : α) => Union fun (H : i ∈ s) => u ∩ t i := sorry

theorem bUnion_inter {α : Type u} {β : Type v} (s : set α) (t : α → set β) (u : set β) : (Union fun (i : α) => Union fun (H : i ∈ s) => t i) ∩ u = Union fun (i : α) => Union fun (H : i ∈ s) => t i ∩ u := sorry

/-- Intersection of a set of sets. -/
def sInter {α : Type u} (S : set (set α)) : set α :=
  Inf S

prefix:110 "⋂₀" => Mathlib.set.sInter

theorem mem_sUnion_of_mem {α : Type u} {x : α} {t : set α} {S : set (set α)} (hx : x ∈ t) (ht : t ∈ S) : x ∈ ⋃₀S :=
  Exists.intro t (Exists.intro ht hx)

theorem mem_sUnion {α : Type u} {x : α} {S : set (set α)} : x ∈ ⋃₀S ↔ ∃ (t : set α), ∃ (H : t ∈ S), x ∈ t :=
  iff.rfl

-- is this theorem really necessary?

theorem not_mem_of_not_mem_sUnion {α : Type u} {x : α} {t : set α} {S : set (set α)} (hx : ¬x ∈ ⋃₀S) (ht : t ∈ S) : ¬x ∈ t :=
  fun (h : x ∈ t) => hx (Exists.intro t (Exists.intro ht h))

@[simp] theorem mem_sInter {α : Type u} {x : α} {S : set (set α)} : x ∈ ⋂₀S ↔ ∀ (t : set α), t ∈ S → x ∈ t :=
  iff.rfl

theorem sInter_subset_of_mem {α : Type u} {S : set (set α)} {t : set α} (tS : t ∈ S) : ⋂₀S ⊆ t :=
  Inf_le tS

theorem subset_sUnion_of_mem {α : Type u} {S : set (set α)} {t : set α} (tS : t ∈ S) : t ⊆ ⋃₀S :=
  le_Sup tS

theorem subset_sUnion_of_subset {α : Type u} {s : set α} (t : set (set α)) (u : set α) (h₁ : s ⊆ u) (h₂ : u ∈ t) : s ⊆ ⋃₀t :=
  subset.trans h₁ (subset_sUnion_of_mem h₂)

theorem sUnion_subset {α : Type u} {S : set (set α)} {t : set α} (h : ∀ (t' : set α), t' ∈ S → t' ⊆ t) : ⋃₀S ⊆ t :=
  Sup_le h

theorem sUnion_subset_iff {α : Type u} {s : set (set α)} {t : set α} : ⋃₀s ⊆ t ↔ ∀ (t' : set α), t' ∈ s → t' ⊆ t :=
  { mp := fun (h : ⋃₀s ⊆ t) (t' : set α) (ht' : t' ∈ s) => subset.trans (subset_sUnion_of_mem ht') h,
    mpr := sUnion_subset }

theorem subset_sInter {α : Type u} {S : set (set α)} {t : set α} (h : ∀ (t' : set α), t' ∈ S → t ⊆ t') : t ⊆ ⋂₀S :=
  le_Inf h

theorem sUnion_subset_sUnion {α : Type u} {S : set (set α)} {T : set (set α)} (h : S ⊆ T) : ⋃₀S ⊆ ⋃₀T :=
  sUnion_subset fun (s : set α) (hs : s ∈ S) => subset_sUnion_of_mem (h hs)

theorem sInter_subset_sInter {α : Type u} {S : set (set α)} {T : set (set α)} (h : S ⊆ T) : ⋂₀T ⊆ ⋂₀S :=
  subset_sInter fun (s : set α) (hs : s ∈ S) => sInter_subset_of_mem (h hs)

@[simp] theorem sUnion_empty {α : Type u} : ⋃₀∅ = ∅ :=
  Sup_empty

@[simp] theorem sInter_empty {α : Type u} : ⋂₀∅ = univ :=
  Inf_empty

@[simp] theorem sUnion_singleton {α : Type u} (s : set α) : ⋃₀singleton s = s :=
  Sup_singleton

@[simp] theorem sInter_singleton {α : Type u} (s : set α) : ⋂₀singleton s = s :=
  Inf_singleton

@[simp] theorem sUnion_eq_empty {α : Type u} {S : set (set α)} : ⋃₀S = ∅ ↔ ∀ (s : set α), s ∈ S → s = ∅ :=
  Sup_eq_bot

@[simp] theorem sInter_eq_univ {α : Type u} {S : set (set α)} : ⋂₀S = univ ↔ ∀ (s : set α), s ∈ S → s = univ :=
  Inf_eq_top

@[simp] theorem nonempty_sUnion {α : Type u} {S : set (set α)} : set.nonempty (⋃₀S) ↔ ∃ (s : set α), ∃ (H : s ∈ S), set.nonempty s := sorry

theorem nonempty.of_sUnion {α : Type u} {s : set (set α)} (h : set.nonempty (⋃₀s)) : set.nonempty s := sorry

theorem nonempty.of_sUnion_eq_univ {α : Type u} [Nonempty α] {s : set (set α)} (h : ⋃₀s = univ) : set.nonempty s :=
  nonempty.of_sUnion (Eq.symm h ▸ univ_nonempty)

theorem sUnion_union {α : Type u} (S : set (set α)) (T : set (set α)) : ⋃₀(S ∪ T) = ⋃₀S ∪ ⋃₀T :=
  Sup_union

theorem sInter_union {α : Type u} (S : set (set α)) (T : set (set α)) : ⋂₀(S ∪ T) = ⋂₀S ∩ ⋂₀T :=
  Inf_union

theorem sInter_Union {α : Type u} {ι : Sort x} (s : ι → set (set α)) : (⋂₀Union fun (i : ι) => s i) = Inter fun (i : ι) => ⋂₀s i := sorry

@[simp] theorem sUnion_insert {α : Type u} (s : set α) (T : set (set α)) : ⋃₀insert s T = s ∪ ⋃₀T :=
  Sup_insert

@[simp] theorem sInter_insert {α : Type u} (s : set α) (T : set (set α)) : ⋂₀insert s T = s ∩ ⋂₀T :=
  Inf_insert

theorem sUnion_pair {α : Type u} (s : set α) (t : set α) : ⋃₀insert s (singleton t) = s ∪ t :=
  Sup_pair

theorem sInter_pair {α : Type u} (s : set α) (t : set α) : ⋂₀insert s (singleton t) = s ∩ t :=
  Inf_pair

@[simp] theorem sUnion_image {α : Type u} {β : Type v} (f : α → set β) (s : set α) : ⋃₀(f '' s) = Union fun (x : α) => Union fun (H : x ∈ s) => f x :=
  Sup_image

@[simp] theorem sInter_image {α : Type u} {β : Type v} (f : α → set β) (s : set α) : ⋂₀(f '' s) = Inter fun (x : α) => Inter fun (H : x ∈ s) => f x :=
  Inf_image

@[simp] theorem sUnion_range {β : Type v} {ι : Sort x} (f : ι → set β) : ⋃₀range f = Union fun (x : ι) => f x :=
  rfl

@[simp] theorem sInter_range {β : Type v} {ι : Sort x} (f : ι → set β) : ⋂₀range f = Inter fun (x : ι) => f x :=
  rfl

theorem Union_eq_univ_iff {α : Type u} {ι : Sort x} {f : ι → set α} : (Union fun (i : ι) => f i) = univ ↔ ∀ (x : α), ∃ (i : ι), x ∈ f i := sorry

theorem bUnion_eq_univ_iff {α : Type u} {β : Type v} {f : α → set β} {s : set α} : (Union fun (x : α) => Union fun (H : x ∈ s) => f x) = univ ↔ ∀ (y : β), ∃ (x : α), ∃ (H : x ∈ s), y ∈ f x := sorry

theorem sUnion_eq_univ_iff {α : Type u} {c : set (set α)} : ⋃₀c = univ ↔ ∀ (a : α), ∃ (b : set α), ∃ (H : b ∈ c), a ∈ b := sorry

theorem compl_sUnion {α : Type u} (S : set (set α)) : ⋃₀Sᶜ = ⋂₀(compl '' S) := sorry

-- classical

theorem sUnion_eq_compl_sInter_compl {α : Type u} (S : set (set α)) : ⋃₀S = (⋂₀(compl '' S)ᶜ) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⋃₀S = (⋂₀(compl '' S)ᶜ))) (Eq.symm (compl_compl (⋃₀S)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⋃₀Sᶜᶜ = (⋂₀(compl '' S)ᶜ))) (compl_sUnion S))) (Eq.refl (⋂₀(compl '' S)ᶜ)))

-- classical

theorem compl_sInter {α : Type u} (S : set (set α)) : ⋂₀Sᶜ = ⋃₀(compl '' S) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⋂₀Sᶜ = ⋃₀(compl '' S))) (sUnion_eq_compl_sInter_compl (compl '' S))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⋂₀Sᶜ = (⋂₀(compl '' (compl '' S))ᶜ))) (compl_compl_image S))) (Eq.refl (⋂₀Sᶜ)))

-- classical

theorem sInter_eq_comp_sUnion_compl {α : Type u} (S : set (set α)) : ⋂₀S = (⋃₀(compl '' S)ᶜ) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (⋂₀S = (⋃₀(compl '' S)ᶜ))) (Eq.symm (compl_compl (⋂₀S)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⋂₀Sᶜᶜ = (⋃₀(compl '' S)ᶜ))) (compl_sInter S))) (Eq.refl (⋃₀(compl '' S)ᶜ)))

theorem inter_empty_of_inter_sUnion_empty {α : Type u} {s : set α} {t : set α} {S : set (set α)} (hs : t ∈ S) (h : s ∩ ⋃₀S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ t ⊆ ∅)) (Eq.symm h))) (inter_subset_inter_right s (subset_sUnion_of_mem hs)))

theorem range_sigma_eq_Union_range {α : Type u} {β : Type v} {γ : α → Type u_1} (f : sigma γ → β) : range f = Union fun (a : α) => range fun (b : γ a) => f (sigma.mk a b) := sorry

theorem Union_eq_range_sigma {α : Type u} {β : Type v} (s : α → set β) : (Union fun (i : α) => s i) = range fun (a : sigma fun (i : α) => ↥(s i)) => ↑(sigma.snd a) := sorry

theorem Union_image_preimage_sigma_mk_eq_self {ι : Type u_1} {σ : ι → Type u_2} (s : set (sigma σ)) : (Union fun (i : ι) => sigma.mk i '' (sigma.mk i ⁻¹' s)) = s := sorry

theorem sUnion_mono {α : Type u} {s : set (set α)} {t : set (set α)} (h : s ⊆ t) : ⋃₀s ⊆ ⋃₀t :=
  sUnion_subset fun (t' : set α) (ht' : t' ∈ s) => subset_sUnion_of_mem (h ht')

theorem Union_subset_Union {α : Type u} {ι : Sort x} {s : ι → set α} {t : ι → set α} (h : ∀ (i : ι), s i ⊆ t i) : (Union fun (i : ι) => s i) ⊆ Union fun (i : ι) => t i :=
  supr_le_supr h

theorem Union_subset_Union2 {α : Type u} {ι : Sort x} {ι₂ : Sort u_1} {s : ι → set α} {t : ι₂ → set α} (h : ∀ (i : ι), ∃ (j : ι₂), s i ⊆ t j) : (Union fun (i : ι) => s i) ⊆ Union fun (i : ι₂) => t i :=
  supr_le_supr2 h

theorem Union_subset_Union_const {α : Type u} {ι : Sort x} {ι₂ : Sort x} {s : set α} (h : ι → ι₂) : (Union fun (i : ι) => s) ⊆ Union fun (j : ι₂) => s :=
  supr_le_supr_const h

@[simp] theorem Union_of_singleton (α : Type u) : (Union fun (x : α) => singleton x) = univ := sorry

@[simp] theorem Union_of_singleton_coe {α : Type u} (s : set α) : (Union fun (i : ↥s) => singleton ↑i) = s := sorry

theorem bUnion_subset_Union {α : Type u} {β : Type v} (s : set α) (t : α → set β) : (Union fun (x : α) => Union fun (H : x ∈ s) => t x) ⊆ Union fun (x : α) => t x :=
  Union_subset_Union fun (i : α) => Union_subset fun (h : i ∈ s) => subset.refl (t i)

theorem sUnion_eq_bUnion {α : Type u} {s : set (set α)} : ⋃₀s = Union fun (i : set α) => Union fun (h : i ∈ s) => i := sorry

theorem sInter_eq_bInter {α : Type u} {s : set (set α)} : ⋂₀s = Inter fun (i : set α) => Inter fun (h : i ∈ s) => i := sorry

theorem sUnion_eq_Union {α : Type u} {s : set (set α)} : ⋃₀s = Union fun (i : ↥s) => ↑i := sorry

theorem sInter_eq_Inter {α : Type u} {s : set (set α)} : ⋂₀s = Inter fun (i : ↥s) => ↑i := sorry

theorem union_eq_Union {α : Type u} {s₁ : set α} {s₂ : set α} : s₁ ∪ s₂ = Union fun (b : Bool) => cond b s₁ s₂ := sorry

theorem inter_eq_Inter {α : Type u} {s₁ : set α} {s₂ : set α} : s₁ ∩ s₂ = Inter fun (b : Bool) => cond b s₁ s₂ := sorry

protected instance complete_boolean_algebra {α : Type u} : complete_boolean_algebra (set α) :=
  complete_boolean_algebra.mk boolean_algebra.sup boolean_algebra.le boolean_algebra.lt sorry sorry sorry sorry sorry
    sorry boolean_algebra.inf sorry sorry sorry sorry boolean_algebra.top sorry boolean_algebra.bot sorry compl
    has_sdiff.sdiff sorry sorry sorry complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry sorry sorry

theorem sInter_union_sInter {α : Type u} {S : set (set α)} {T : set (set α)} : ⋂₀S ∪ ⋂₀T = Inter fun (p : set α × set α) => Inter fun (H : p ∈ set.prod S T) => prod.fst p ∪ prod.snd p :=
  Inf_sup_Inf

theorem sUnion_inter_sUnion {α : Type u} {s : set (set α)} {t : set (set α)} : ⋃₀s ∩ ⋃₀t = Union fun (p : set α × set α) => Union fun (H : p ∈ set.prod s t) => prod.fst p ∩ prod.snd p :=
  Sup_inf_Sup

/-- If `S` is a set of sets, and each `s ∈ S` can be represented as an intersection
of sets `T s hs`, then `⋂₀ S` is the intersection of the union of all `T s hs`. -/
theorem sInter_bUnion {α : Type u} {S : set (set α)} {T : (s : set α) → s ∈ S → set (set α)} (hT : ∀ (s : set α) (H : s ∈ S), s = ⋂₀T s H) : (⋂₀Union fun (s : set α) => Union fun (H : s ∈ S) => T s H) = ⋂₀S := sorry

/-- If `S` is a set of sets, and each `s ∈ S` can be represented as an union
of sets `T s hs`, then `⋃₀ S` is the union of the union of all `T s hs`. -/
theorem sUnion_bUnion {α : Type u} {S : set (set α)} {T : (s : set α) → s ∈ S → set (set α)} (hT : ∀ (s : set α) (H : s ∈ S), s = ⋃₀T s H) : (⋃₀Union fun (s : set α) => Union fun (H : s ∈ S) => T s H) = ⋃₀S := sorry

theorem Union_range_eq_sUnion {α : Type u_1} {β : Type u_2} (C : set (set α)) {f : (s : ↥C) → β → ↥s} (hf : ∀ (s : ↥C), function.surjective (f s)) : (Union fun (y : β) => range fun (s : ↥C) => subtype.val (f s y)) = ⋃₀C := sorry

theorem Union_range_eq_Union {ι : Type u_1} {α : Type u_2} {β : Type u_3} (C : ι → set α) {f : (x : ι) → β → ↥(C x)} (hf : ∀ (x : ι), function.surjective (f x)) : (Union fun (y : β) => range fun (x : ι) => subtype.val (f x y)) = Union fun (x : ι) => C x := sorry

theorem union_distrib_Inter_right {α : Type u} {ι : Type u_1} (s : ι → set α) (t : set α) : (Inter fun (i : ι) => s i) ∪ t = Inter fun (i : ι) => s i ∪ t := sorry

theorem union_distrib_Inter_left {α : Type u} {ι : Type u_1} (s : ι → set α) (t : set α) : (t ∪ Inter fun (i : ι) => s i) = Inter fun (i : ι) => t ∪ s i := sorry

/-!
### `maps_to`
-/

theorem maps_to_sUnion {α : Type u} {β : Type v} {S : set (set α)} {t : set β} {f : α → β} (H : ∀ (s : set α), s ∈ S → maps_to f s t) : maps_to f (⋃₀S) t := sorry

theorem maps_to_Union {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} {t : set β} {f : α → β} (H : ∀ (i : ι), maps_to f (s i) t) : maps_to f (Union fun (i : ι) => s i) t :=
  maps_to_sUnion (iff.mpr forall_range_iff H)

theorem maps_to_bUnion {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : (i : ι) → p i → set α} {t : set β} {f : α → β} (H : ∀ (i : ι) (hi : p i), maps_to f (s i hi) t) : maps_to f (Union fun (i : ι) => Union fun (hi : p i) => s i hi) t :=
  maps_to_Union fun (i : ι) => maps_to_Union (H i)

theorem maps_to_Union_Union {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), maps_to f (s i) (t i)) : maps_to f (Union fun (i : ι) => s i) (Union fun (i : ι) => t i) :=
  maps_to_Union fun (i : ι) => maps_to.mono (subset.refl (s i)) (subset_Union t i) (H i)

theorem maps_to_bUnion_bUnion {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : (i : ι) → p i → set α} {t : (i : ι) → p i → set β} {f : α → β} (H : ∀ (i : ι) (hi : p i), maps_to f (s i hi) (t i hi)) : maps_to f (Union fun (i : ι) => Union fun (hi : p i) => s i hi) (Union fun (i : ι) => Union fun (hi : p i) => t i hi) :=
  maps_to_Union_Union fun (i : ι) => maps_to_Union_Union (H i)

theorem maps_to_sInter {α : Type u} {β : Type v} {s : set α} {T : set (set β)} {f : α → β} (H : ∀ (t : set β), t ∈ T → maps_to f s t) : maps_to f s (⋂₀T) :=
  fun (x : α) (hx : x ∈ s) (t : set β) (ht : t ∈ T) => H t ht hx

theorem maps_to_Inter {α : Type u} {β : Type v} {ι : Sort x} {s : set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), maps_to f s (t i)) : maps_to f s (Inter fun (i : ι) => t i) :=
  fun (x : α) (hx : x ∈ s) => iff.mpr mem_Inter fun (i : ι) => H i hx

theorem maps_to_bInter {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : set α} {t : (i : ι) → p i → set β} {f : α → β} (H : ∀ (i : ι) (hi : p i), maps_to f s (t i hi)) : maps_to f s (Inter fun (i : ι) => Inter fun (hi : p i) => t i hi) :=
  maps_to_Inter fun (i : ι) => maps_to_Inter (H i)

theorem maps_to_Inter_Inter {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), maps_to f (s i) (t i)) : maps_to f (Inter fun (i : ι) => s i) (Inter fun (i : ι) => t i) :=
  maps_to_Inter fun (i : ι) => maps_to.mono (Inter_subset s i) (subset.refl (t i)) (H i)

theorem maps_to_bInter_bInter {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : (i : ι) → p i → set α} {t : (i : ι) → p i → set β} {f : α → β} (H : ∀ (i : ι) (hi : p i), maps_to f (s i hi) (t i hi)) : maps_to f (Inter fun (i : ι) => Inter fun (hi : p i) => s i hi) (Inter fun (i : ι) => Inter fun (hi : p i) => t i hi) :=
  maps_to_Inter_Inter fun (i : ι) => maps_to_Inter_Inter (H i)

theorem image_Inter_subset {α : Type u} {β : Type v} {ι : Sort x} (s : ι → set α) (f : α → β) : (f '' Inter fun (i : ι) => s i) ⊆ Inter fun (i : ι) => f '' s i :=
  maps_to.image_subset (maps_to_Inter_Inter fun (i : ι) => maps_to_image f (s i))

theorem image_bInter_subset {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} (s : (i : ι) → p i → set α) (f : α → β) : (f '' Inter fun (i : ι) => Inter fun (hi : p i) => s i hi) ⊆ Inter fun (i : ι) => Inter fun (hi : p i) => f '' s i hi :=
  maps_to.image_subset (maps_to_bInter_bInter fun (i : ι) (hi : p i) => maps_to_image f (s i hi))

theorem image_sInter_subset {α : Type u} {β : Type v} (S : set (set α)) (f : α → β) : f '' ⋂₀S ⊆ Inter fun (s : set α) => Inter fun (H : s ∈ S) => f '' s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (f '' ⋂₀S ⊆ Inter fun (s : set α) => Inter fun (H : s ∈ S) => f '' s)) sInter_eq_bInter))
    (image_bInter_subset (fun (i : set α) (hi : i ∈ S) => i) f)

/-!
### `inj_on`
-/

theorem inj_on.image_Inter_eq {α : Type u} {β : Type v} {ι : Sort x} [Nonempty ι] {s : ι → set α} {f : α → β} (h : inj_on f (Union fun (i : ι) => s i)) : (f '' Inter fun (i : ι) => s i) = Inter fun (i : ι) => f '' s i := sorry

theorem inj_on.image_bInter_eq {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : (i : ι) → p i → set α} (hp : ∃ (i : ι), p i) {f : α → β} (h : inj_on f (Union fun (i : ι) => Union fun (hi : p i) => s i hi)) : (f '' Inter fun (i : ι) => Inter fun (hi : p i) => s i hi) = Inter fun (i : ι) => Inter fun (hi : p i) => f '' s i hi := sorry

theorem inj_on_Union_of_directed {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} (hs : directed has_subset.subset s) {f : α → β} (hf : ∀ (i : ι), inj_on f (s i)) : inj_on f (Union fun (i : ι) => s i) := sorry

/-!
### `surj_on`
-/

theorem surj_on_sUnion {α : Type u} {β : Type v} {s : set α} {T : set (set β)} {f : α → β} (H : ∀ (t : set β), t ∈ T → surj_on f s t) : surj_on f s (⋃₀T) := sorry

theorem surj_on_Union {α : Type u} {β : Type v} {ι : Sort x} {s : set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), surj_on f s (t i)) : surj_on f s (Union fun (i : ι) => t i) :=
  surj_on_sUnion (iff.mpr forall_range_iff H)

theorem surj_on_Union_Union {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), surj_on f (s i) (t i)) : surj_on f (Union fun (i : ι) => s i) (Union fun (i : ι) => t i) :=
  surj_on_Union fun (i : ι) => surj_on.mono (subset_Union s i) (subset.refl (t i)) (H i)

theorem surj_on_bUnion {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : set α} {t : (i : ι) → p i → set β} {f : α → β} (H : ∀ (i : ι) (hi : p i), surj_on f s (t i hi)) : surj_on f s (Union fun (i : ι) => Union fun (hi : p i) => t i hi) :=
  surj_on_Union fun (i : ι) => surj_on_Union (H i)

theorem surj_on_bUnion_bUnion {α : Type u} {β : Type v} {ι : Sort x} {p : ι → Prop} {s : (i : ι) → p i → set α} {t : (i : ι) → p i → set β} {f : α → β} (H : ∀ (i : ι) (hi : p i), surj_on f (s i hi) (t i hi)) : surj_on f (Union fun (i : ι) => Union fun (hi : p i) => s i hi) (Union fun (i : ι) => Union fun (hi : p i) => t i hi) :=
  surj_on_Union_Union fun (i : ι) => surj_on_Union_Union (H i)

theorem surj_on_Inter {α : Type u} {β : Type v} {ι : Sort x} [hi : Nonempty ι] {s : ι → set α} {t : set β} {f : α → β} (H : ∀ (i : ι), surj_on f (s i) t) (Hinj : inj_on f (Union fun (i : ι) => s i)) : surj_on f (Inter fun (i : ι) => s i) t := sorry

theorem surj_on_Inter_Inter {α : Type u} {β : Type v} {ι : Sort x} [hi : Nonempty ι] {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), surj_on f (s i) (t i)) (Hinj : inj_on f (Union fun (i : ι) => s i)) : surj_on f (Inter fun (i : ι) => s i) (Inter fun (i : ι) => t i) :=
  surj_on_Inter (fun (i : ι) => surj_on.mono (subset.refl (s i)) (Inter_subset (fun (i : ι) => t i) i) (H i)) Hinj

/-!
### `bij_on`
-/

theorem bij_on_Union {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), bij_on f (s i) (t i)) (Hinj : inj_on f (Union fun (i : ι) => s i)) : bij_on f (Union fun (i : ι) => s i) (Union fun (i : ι) => t i) :=
  { left := maps_to_Union_Union fun (i : ι) => bij_on.maps_to (H i),
    right := { left := Hinj, right := surj_on_Union_Union fun (i : ι) => bij_on.surj_on (H i) } }

theorem bij_on_Inter {α : Type u} {β : Type v} {ι : Sort x} [hi : Nonempty ι] {s : ι → set α} {t : ι → set β} {f : α → β} (H : ∀ (i : ι), bij_on f (s i) (t i)) (Hinj : inj_on f (Union fun (i : ι) => s i)) : bij_on f (Inter fun (i : ι) => s i) (Inter fun (i : ι) => t i) := sorry

theorem bij_on_Union_of_directed {α : Type u} {β : Type v} {ι : Sort x} {s : ι → set α} (hs : directed has_subset.subset s) {t : ι → set β} {f : α → β} (H : ∀ (i : ι), bij_on f (s i) (t i)) : bij_on f (Union fun (i : ι) => s i) (Union fun (i : ι) => t i) :=
  bij_on_Union H (inj_on_Union_of_directed hs fun (i : ι) => bij_on.inj_on (H i))

theorem bij_on_Inter_of_directed {α : Type u} {β : Type v} {ι : Sort x} [Nonempty ι] {s : ι → set α} (hs : directed has_subset.subset s) {t : ι → set β} {f : α → β} (H : ∀ (i : ι), bij_on f (s i) (t i)) : bij_on f (Inter fun (i : ι) => s i) (Inter fun (i : ι) => t i) :=
  bij_on_Inter H (inj_on_Union_of_directed hs fun (i : ι) => bij_on.inj_on (H i))

@[simp] theorem Inter_pos {α : Type u} {p : Prop} {μ : p → set α} (hp : p) : (Inter fun (h : p) => μ h) = μ hp :=
  infi_pos hp

@[simp] theorem Inter_neg {α : Type u} {p : Prop} {μ : p → set α} (hp : ¬p) : (Inter fun (h : p) => μ h) = univ :=
  infi_neg hp

@[simp] theorem Union_pos {α : Type u} {p : Prop} {μ : p → set α} (hp : p) : (Union fun (h : p) => μ h) = μ hp :=
  supr_pos hp

@[simp] theorem Union_neg {α : Type u} {p : Prop} {μ : p → set α} (hp : ¬p) : (Union fun (h : p) => μ h) = ∅ :=
  supr_neg hp

@[simp] theorem Union_empty {α : Type u} {ι : Sort x} : (Union fun (i : ι) => ∅) = ∅ :=
  supr_bot

@[simp] theorem Inter_univ {α : Type u} {ι : Sort x} : (Inter fun (i : ι) => univ) = univ :=
  infi_top

@[simp] theorem Union_eq_empty {α : Type u} {ι : Sort x} {s : ι → set α} : (Union fun (i : ι) => s i) = ∅ ↔ ∀ (i : ι), s i = ∅ :=
  supr_eq_bot

@[simp] theorem Inter_eq_univ {α : Type u} {ι : Sort x} {s : ι → set α} : (Inter fun (i : ι) => s i) = univ ↔ ∀ (i : ι), s i = univ :=
  infi_eq_top

@[simp] theorem nonempty_Union {α : Type u} {ι : Sort x} {s : ι → set α} : set.nonempty (Union fun (i : ι) => s i) ↔ ∃ (i : ι), set.nonempty (s i) := sorry

theorem image_Union {α : Type u} {β : Type v} {ι : Sort x} {f : α → β} {s : ι → set α} : (f '' Union fun (i : ι) => s i) = Union fun (i : ι) => f '' s i := sorry

theorem univ_subtype {α : Type u} {p : α → Prop} : univ = Union fun (x : α) => Union fun (h : p x) => singleton { val := x, property := h } := sorry

theorem range_eq_Union {α : Type u} {ι : Sort u_1} (f : ι → α) : range f = Union fun (i : ι) => singleton (f i) := sorry

theorem image_eq_Union {α : Type u} {β : Type v} (f : α → β) (s : set α) : f '' s = Union fun (i : α) => Union fun (H : i ∈ s) => singleton (f i) := sorry

@[simp] theorem bUnion_range {α : Type u} {β : Type v} {ι : Sort x} {f : ι → α} {g : α → set β} : (Union fun (x : α) => Union fun (H : x ∈ range f) => g x) = Union fun (y : ι) => g (f y) :=
  supr_range

@[simp] theorem bInter_range {α : Type u} {β : Type v} {ι : Sort x} {f : ι → α} {g : α → set β} : (Inter fun (x : α) => Inter fun (H : x ∈ range f) => g x) = Inter fun (y : ι) => g (f y) :=
  infi_range

@[simp] theorem bUnion_image {α : Type u} {β : Type v} {γ : Type w} {s : set γ} {f : γ → α} {g : α → set β} : (Union fun (x : α) => Union fun (H : x ∈ f '' s) => g x) = Union fun (y : γ) => Union fun (H : y ∈ s) => g (f y) :=
  supr_image

@[simp] theorem bInter_image {α : Type u} {β : Type v} {γ : Type w} {s : set γ} {f : γ → α} {g : α → set β} : (Inter fun (x : α) => Inter fun (H : x ∈ f '' s) => g x) = Inter fun (y : γ) => Inter fun (H : y ∈ s) => g (f y) :=
  infi_image

theorem Union_image_left {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) {s : set α} {t : set β} : (Union fun (a : α) => Union fun (H : a ∈ s) => f a '' t) = image2 f s t := sorry

theorem Union_image_right {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) {s : set α} {t : set β} : (Union fun (b : β) => Union fun (H : b ∈ t) => (fun (a : α) => f a b) '' s) = image2 f s t := sorry

theorem monotone_preimage {α : Type u} {β : Type v} {f : α → β} : monotone (preimage f) :=
  fun (a b : set β) (h : a ≤ b) => preimage_mono h

@[simp] theorem preimage_Union {α : Type u} {β : Type v} {ι : Sort w} {f : α → β} {s : ι → set β} : (f ⁻¹' Union fun (i : ι) => s i) = Union fun (i : ι) => f ⁻¹' s i := sorry

theorem preimage_bUnion {α : Type u} {β : Type v} {ι : Type u_1} {f : α → β} {s : set ι} {t : ι → set β} : (f ⁻¹' Union fun (i : ι) => Union fun (H : i ∈ s) => t i) = Union fun (i : ι) => Union fun (H : i ∈ s) => f ⁻¹' t i := sorry

@[simp] theorem preimage_sUnion {α : Type u} {β : Type v} {f : α → β} {s : set (set β)} : f ⁻¹' ⋃₀s = Union fun (t : set β) => Union fun (H : t ∈ s) => f ⁻¹' t := sorry

theorem preimage_Inter {α : Type u} {β : Type v} {ι : Sort u_1} {s : ι → set β} {f : α → β} : (f ⁻¹' Inter fun (i : ι) => s i) = Inter fun (i : ι) => f ⁻¹' s i := sorry

theorem preimage_bInter {α : Type u} {β : Type v} {γ : Type w} {s : γ → set β} {t : set γ} {f : α → β} : (f ⁻¹' Inter fun (i : γ) => Inter fun (H : i ∈ t) => s i) = Inter fun (i : γ) => Inter fun (H : i ∈ t) => f ⁻¹' s i := sorry

@[simp] theorem bUnion_preimage_singleton {α : Type u} {β : Type v} (f : α → β) (s : set β) : (Union fun (y : β) => Union fun (H : y ∈ s) => f ⁻¹' singleton y) = f ⁻¹' s := sorry

theorem bUnion_range_preimage_singleton {α : Type u} {β : Type v} (f : α → β) : (Union fun (y : β) => Union fun (H : y ∈ range f) => f ⁻¹' singleton y) = univ := sorry

theorem monotone_prod {α : Type u} {β : Type v} {γ : Type w} [preorder α] {f : α → set β} {g : α → set γ} (hf : monotone f) (hg : monotone g) : monotone fun (x : α) => set.prod (f x) (g x) :=
  fun (a b : α) (h : a ≤ b) => prod_mono (hf h) (hg h)

theorem Mathlib.monotone.set_prod {α : Type u} {β : Type v} {γ : Type w} [preorder α] {f : α → set β} {g : α → set γ} (hf : monotone f) (hg : monotone g) : monotone fun (x : α) => set.prod (f x) (g x) :=
  monotone_prod

theorem prod_Union {α : Type u} {β : Type v} {ι : Sort u_1} {s : set α} {t : ι → set β} : set.prod s (Union fun (i : ι) => t i) = Union fun (i : ι) => set.prod s (t i) := sorry

theorem prod_bUnion {α : Type u} {β : Type v} {ι : Type u_1} {u : set ι} {s : set α} {t : ι → set β} : set.prod s (Union fun (i : ι) => Union fun (H : i ∈ u) => t i) =
  Union fun (i : ι) => Union fun (H : i ∈ u) => set.prod s (t i) := sorry

theorem prod_sUnion {α : Type u} {β : Type v} {s : set α} {C : set (set β)} : set.prod s (⋃₀C) = ⋃₀((fun (t : set β) => set.prod s t) '' C) := sorry

theorem Union_prod {α : Type u} {β : Type v} {ι : Sort u_1} {s : ι → set α} {t : set β} : set.prod (Union fun (i : ι) => s i) t = Union fun (i : ι) => set.prod (s i) t := sorry

theorem bUnion_prod {α : Type u} {β : Type v} {ι : Type u_1} {u : set ι} {s : ι → set α} {t : set β} : set.prod (Union fun (i : ι) => Union fun (H : i ∈ u) => s i) t =
  Union fun (i : ι) => Union fun (H : i ∈ u) => set.prod (s i) t := sorry

theorem sUnion_prod {α : Type u} {β : Type v} {C : set (set α)} {t : set β} : set.prod (⋃₀C) t = ⋃₀((fun (s : set α) => set.prod s t) '' C) := sorry

theorem Union_prod_of_monotone {α : Type u} {β : Type v} {γ : Type w} [semilattice_sup α] {s : α → set β} {t : α → set γ} (hs : monotone s) (ht : monotone t) : (Union fun (x : α) => set.prod (s x) (t x)) = set.prod (Union fun (x : α) => s x) (Union fun (x : α) => t x) := sorry

/-- Given a set `s` of functions `α → β` and `t : set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq {α : Type u} {β : Type v} (s : set (α → β)) (t : set α) : set β :=
  set_of fun (b : β) => ∃ (f : α → β), ∃ (H : f ∈ s), ∃ (a : α), ∃ (H : a ∈ t), f a = b

theorem seq_def {α : Type u} {β : Type v} {s : set (α → β)} {t : set α} : seq s t = Union fun (f : α → β) => Union fun (H : f ∈ s) => f '' t := sorry

@[simp] theorem mem_seq_iff {α : Type u} {β : Type v} {s : set (α → β)} {t : set α} {b : β} : b ∈ seq s t ↔ ∃ (f : α → β), ∃ (H : f ∈ s), ∃ (a : α), ∃ (H : a ∈ t), f a = b :=
  iff.rfl

theorem seq_subset {α : Type u} {β : Type v} {s : set (α → β)} {t : set α} {u : set β} : seq s t ⊆ u ↔ ∀ (f : α → β), f ∈ s → ∀ (a : α), a ∈ t → f a ∈ u := sorry

theorem seq_mono {α : Type u} {β : Type v} {s₀ : set (α → β)} {s₁ : set (α → β)} {t₀ : set α} {t₁ : set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) : seq s₀ t₀ ⊆ seq s₁ t₁ := sorry

theorem singleton_seq {α : Type u} {β : Type v} {f : α → β} {t : set α} : seq (singleton f) t = f '' t := sorry

theorem seq_singleton {α : Type u} {β : Type v} {s : set (α → β)} {a : α} : seq s (singleton a) = (fun (f : α → β) => f a) '' s := sorry

theorem seq_seq {α : Type u} {β : Type v} {γ : Type w} {s : set (β → γ)} {t : set (α → β)} {u : set α} : seq s (seq t u) = seq (seq (function.comp '' s) t) u := sorry

theorem image_seq {α : Type u} {β : Type v} {γ : Type w} {f : β → γ} {s : set (α → β)} {t : set α} : f '' seq s t = seq (function.comp f '' s) t := sorry

theorem prod_eq_seq {α : Type u} {β : Type v} {s : set α} {t : set β} : set.prod s t = seq (Prod.mk '' s) t := sorry

theorem prod_image_seq_comm {α : Type u} {β : Type v} (s : set α) (t : set β) : seq (Prod.mk '' s) t = seq ((fun (b : β) (a : α) => (a, b)) '' t) s := sorry

theorem image2_eq_seq {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (s : set α) (t : set β) : image2 f s t = seq (f '' s) t := sorry

protected instance monad : Monad set :=
  { toApplicative :=
      { toFunctor := { map := fun (α β : Type u) => image, mapConst := fun (α β : Type u) => image ∘ function.const β },
        toPure := { pure := fun (α : Type u) (a : α) => singleton a }, toSeq := { seq := fun (α β : Type u) => seq },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u) (a : set α) (b : set β) =>
                (fun (α β : Type u) => seq) β α ((fun (α β : Type u) => image) α (β → α) (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u) (a : set α) (b : set β) =>
                (fun (α β : Type u) => seq) β β ((fun (α β : Type u) => image) α (β → β) (function.const α id) a) b } },
    toBind :=
      { bind := fun (α β : Type u) (s : set α) (f : α → set β) => Union fun (i : α) => Union fun (H : i ∈ s) => f i } }

@[simp] theorem bind_def {α' : Type u} {β' : Type u} {s : set α'} {f : α' → set β'} : s >>= f = Union fun (i : α') => Union fun (H : i ∈ s) => f i :=
  rfl

@[simp] theorem fmap_eq_image {α' : Type u} {β' : Type u} {s : set α'} (f : α' → β') : f <$> s = f '' s :=
  rfl

@[simp] theorem seq_eq_set_seq {α : Type u_1} {β : Type u_1} (s : set (α → β)) (t : set α) : s <*> t = seq s t :=
  rfl

@[simp] theorem pure_def {α : Type u} (a : α) : pure a = singleton a :=
  rfl

protected instance is_lawful_monad : is_lawful_monad set := sorry

protected instance is_comm_applicative : is_comm_applicative set :=
  is_comm_applicative.mk fun (α β : Type u) (s : set α) (t : set β) => prod_image_seq_comm s t

theorem pi_def {α : Type u} {π : α → Type u_1} (i : set α) (s : (a : α) → set (π a)) : pi i s = Inter fun (a : α) => Inter fun (H : a ∈ i) => function.eval a ⁻¹' s a := sorry

theorem pi_diff_pi_subset {α : Type u} {π : α → Type u_1} (i : set α) (s : (a : α) → set (π a)) (t : (a : α) → set (π a)) : pi i s \ pi i t ⊆ Union fun (a : α) => Union fun (H : a ∈ i) => function.eval a ⁻¹' (s a \ t a) := sorry

end set


/-! ### Disjoint sets -/

namespace disjoint


/-! We define some lemmas in the `disjoint` namespace to be able to use projection notation. -/

theorem union_left {α : Type u} {s : set α} {t : set α} {u : set α} (hs : disjoint s u) (ht : disjoint t u) : disjoint (s ∪ t) u :=
  sup_left hs ht

theorem union_right {α : Type u} {s : set α} {t : set α} {u : set α} (ht : disjoint s t) (hu : disjoint s u) : disjoint s (t ∪ u) :=
  sup_right ht hu

theorem preimage {α : Type u_1} {β : Type u_2} (f : α → β) {s : set β} {t : set β} (h : disjoint s t) : disjoint (f ⁻¹' s) (f ⁻¹' t) :=
  fun (x : α) (hx : x ∈ f ⁻¹' s ⊓ f ⁻¹' t) => h hx

end disjoint


namespace set


protected theorem disjoint_iff {α : Type u} {s : set α} {t : set α} : disjoint s t ↔ s ∩ t ⊆ ∅ :=
  iff.rfl

theorem disjoint_iff_inter_eq_empty {α : Type u} {s : set α} {t : set α} : disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem not_disjoint_iff {α : Type u} {s : set α} {t : set α} : ¬disjoint s t ↔ ∃ (x : α), x ∈ s ∧ x ∈ t :=
  iff.trans not_forall (exists_congr fun (x : α) => not_not)

theorem disjoint_left {α : Type u} {s : set α} {t : set α} : disjoint s t ↔ ∀ {a : α}, a ∈ s → ¬a ∈ t :=
  (fun (this : (∀ (x : α), ¬x ∈ s ∩ t) ↔ ∀ (a : α), a ∈ s → ¬a ∈ t) => this)
    { mp := fun (h : ∀ (x : α), ¬x ∈ s ∩ t) (a : α) => iff.mp not_and (h a),
      mpr := fun (h : ∀ (a : α), a ∈ s → ¬a ∈ t) (a : α) => iff.mpr not_and (h a) }

theorem disjoint_right {α : Type u} {s : set α} {t : set α} : disjoint s t ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (disjoint s t ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s)) (propext disjoint.comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (disjoint t s ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s)) (propext disjoint_left)))
      (iff.refl (∀ {a : α}, a ∈ t → ¬a ∈ s)))

theorem disjoint_of_subset_left {α : Type u} {s : set α} {t : set α} {u : set α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
  disjoint.mono_left h d

theorem disjoint_of_subset_right {α : Type u} {s : set α} {t : set α} {u : set α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
  disjoint.mono_right h d

theorem disjoint_of_subset {α : Type u} {s : set α} {t : set α} {u : set α} {v : set α} (h1 : s ⊆ u) (h2 : t ⊆ v) (d : disjoint u v) : disjoint s t :=
  disjoint.mono h1 h2 d

@[simp] theorem disjoint_union_left {α : Type u} {s : set α} {t : set α} {u : set α} : disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
  disjoint_sup_left

@[simp] theorem disjoint_union_right {α : Type u} {s : set α} {t : set α} {u : set α} : disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
  disjoint_sup_right

theorem disjoint_diff {α : Type u} {a : set α} {b : set α} : disjoint a (b \ a) :=
  iff.mpr disjoint_iff (inter_diff_self a b)

@[simp] theorem disjoint_empty {α : Type u} (s : set α) : disjoint s ∅ :=
  disjoint_bot_right

@[simp] theorem empty_disjoint {α : Type u} (s : set α) : disjoint ∅ s :=
  disjoint_bot_left

@[simp] theorem univ_disjoint {α : Type u} {s : set α} : disjoint univ s ↔ s = ∅ :=
  top_disjoint

@[simp] theorem disjoint_univ {α : Type u} {s : set α} : disjoint s univ ↔ s = ∅ :=
  disjoint_top

@[simp] theorem disjoint_singleton_left {α : Type u} {a : α} {s : set α} : disjoint (singleton a) s ↔ ¬a ∈ s := sorry

@[simp] theorem disjoint_singleton_right {α : Type u} {a : α} {s : set α} : disjoint s (singleton a) ↔ ¬a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (disjoint s (singleton a) ↔ ¬a ∈ s)) (propext disjoint.comm))) disjoint_singleton_left

theorem disjoint_image_image {α : Type u} {β : Type v} {γ : Type w} {f : β → α} {g : γ → α} {s : set β} {t : set γ} (h : ∀ (b : β), b ∈ s → ∀ (c : γ), c ∈ t → f b ≠ g c) : disjoint (f '' s) (g '' t) := sorry

theorem pairwise_on_disjoint_fiber {α : Type u} {β : Type v} (f : α → β) (s : set β) : pairwise_on s (disjoint on fun (y : β) => f ⁻¹' singleton y) := sorry

theorem preimage_eq_empty {α : Type u} {β : Type v} {f : α → β} {s : set β} (h : disjoint s (range f)) : f ⁻¹' s = ∅ := sorry

theorem preimage_eq_empty_iff {α : Type u} {β : Type v} {f : α → β} {s : set β} : disjoint s (range f) ↔ f ⁻¹' s = ∅ := sorry

end set


namespace set


/-- A collection of sets is `pairwise_disjoint`, if any two different sets in this collection
are disjoint.  -/
def pairwise_disjoint {α : Type u} (s : set (set α))  :=
  pairwise_on s disjoint

theorem pairwise_disjoint.subset {α : Type u} {s : set (set α)} {t : set (set α)} (h : s ⊆ t) (ht : pairwise_disjoint t) : pairwise_disjoint s :=
  pairwise_on.mono h ht

theorem pairwise_disjoint.range {α : Type u} {s : set (set α)} (f : ↥s → set α) (hf : ∀ (x : ↥s), f x ⊆ subtype.val x) (ht : pairwise_disjoint s) : pairwise_disjoint (range f) := sorry

/- classical -/

theorem pairwise_disjoint.elim {α : Type u} {s : set (set α)} (h : pairwise_disjoint s) {x : set α} {y : set α} (hx : x ∈ s) (hy : y ∈ s) (z : α) (hzx : z ∈ x) (hzy : z ∈ y) : x = y :=
  iff.mp not_not fun (h' : ¬x = y) => h x hx y hy h' { left := hzx, right := hzy }

end set


namespace set


theorem subset_diff {α : Type u} {s : set α} {t : set α} {u : set α} : s ⊆ t \ u ↔ s ⊆ t ∧ disjoint s u := sorry

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigma_to_Union {α : Type u} {β : Type v} (t : α → set β) (x : sigma fun (i : α) => ↥(t i)) : ↥(Union fun (i : α) => t i) :=
  { val := ↑(sigma.snd x), property := sorry }

theorem sigma_to_Union_surjective {α : Type u} {β : Type v} (t : α → set β) : function.surjective (sigma_to_Union t) := sorry

theorem sigma_to_Union_injective {α : Type u} {β : Type v} (t : α → set β) (h : ∀ (i j : α), i ≠ j → disjoint (t i) (t j)) : function.injective (sigma_to_Union t) := sorry

theorem sigma_to_Union_bijective {α : Type u} {β : Type v} (t : α → set β) (h : ∀ (i j : α), i ≠ j → disjoint (t i) (t j)) : function.bijective (sigma_to_Union t) :=
  { left := sigma_to_Union_injective t h, right := sigma_to_Union_surjective t }

/-- Equivalence between a disjoint union and a dependent sum. -/
def Union_eq_sigma_of_disjoint {α : Type u} {β : Type v} {t : α → set β} (h : ∀ (i j : α), i ≠ j → disjoint (t i) (t j)) : ↥(Union fun (i : α) => t i) ≃ sigma fun (i : α) => ↥(t i) :=
  equiv.symm (equiv.of_bijective (sigma_to_Union t) (sigma_to_Union_bijective t h))

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
def bUnion_eq_sigma_of_disjoint {α : Type u} {β : Type v} {s : set α} {t : α → set β} (h : pairwise_on s (disjoint on t)) : ↥(Union fun (i : α) => Union fun (H : i ∈ s) => t i) ≃ sigma fun (i : ↥s) => ↥(t (subtype.val i)) :=
  equiv.trans (equiv.set_congr sorry) (Union_eq_sigma_of_disjoint sorry)

