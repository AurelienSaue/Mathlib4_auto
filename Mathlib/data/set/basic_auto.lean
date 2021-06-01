/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.unique
import Mathlib.order.boolean_algebra
import Mathlib.PostPort

universes u_1 u v w u_2 x u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coersion from `set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the file `set_theory/zfc.lean`, which contains an encoding of ZFC set theory in Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : set α` and `s₁ s₂ : set α` are subsets of `α`

-  `t : set β` is a subset of `β`.

Definitions in the file:

* `strict_subset s₁ s₂ : Prop` : the predicate `s₁ ⊆ s₂` but `s₁ ≠ s₂`.

* `nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

* `s.prod t : set (α × β)` : the subset `s × t`.

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `f ⁻¹' t` for `preimage f t`

* `f '' s` for `image f s`

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.nonempty` dot notation can be used.

* For `s : set α`, do not use `subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, image, preimage, pre-image, range, union, intersection, insert,
singleton, complement, powerset

-/

/-! ### Set coercion to a type -/

namespace set


protected instance has_le {α : Type u_1} : HasLessEq (set α) := { LessEq := has_subset.subset }

protected instance has_lt {α : Type u_1} : HasLess (set α) :=
  { Less := fun (s t : set α) => s ≤ t ∧ ¬t ≤ s }

protected instance boolean_algebra {α : Type u_1} : boolean_algebra (set α) :=
  boolean_algebra.mk has_union.union LessEq Less sorry sorry sorry sorry sorry sorry has_inter.inter
    sorry sorry sorry sorry univ sorry ∅ sorry compl has_sdiff.sdiff sorry sorry sorry

@[simp] theorem top_eq_univ {α : Type u_1} : ⊤ = univ := rfl

@[simp] theorem bot_eq_empty {α : Type u_1} : ⊥ = ∅ := rfl

@[simp] theorem sup_eq_union {α : Type u_1} (s : set α) (t : set α) : s ⊔ t = s ∪ t := rfl

@[simp] theorem inf_eq_inter {α : Type u_1} (s : set α) (t : set α) : s ⊓ t = s ∩ t := rfl

/-! `set.lt_eq_ssubset` is defined further down -/

@[simp] theorem le_eq_subset {α : Type u_1} (s : set α) (t : set α) : s ≤ t = (s ⊆ t) := rfl

/-- Coercion from a set to the corresponding subtype. -/
protected instance has_coe_to_sort {α : Type u_1} : has_coe_to_sort (set α) :=
  has_coe_to_sort.mk (Type (max 0 u_1)) fun (s : set α) => Subtype fun (x : α) => x ∈ s

end set


theorem set.set_coe_eq_subtype {α : Type u} (s : set α) : ↥s = Subtype fun (x : α) => x ∈ s := rfl

@[simp] theorem set_coe.forall {α : Type u} {s : set α} {p : ↥s → Prop} :
    (∀ (x : ↥s), p x) ↔ ∀ (x : α) (h : x ∈ s), p { val := x, property := h } :=
  subtype.forall

@[simp] theorem set_coe.exists {α : Type u} {s : set α} {p : ↥s → Prop} :
    (∃ (x : ↥s), p x) ↔ ∃ (x : α), ∃ (h : x ∈ s), p { val := x, property := h } :=
  subtype.exists

theorem set_coe.exists' {α : Type u} {s : set α} {p : (x : α) → x ∈ s → Prop} :
    (∃ (x : α), ∃ (h : x ∈ s), p x h) ↔ ∃ (x : ↥s), p (↑x) (subtype.property x) :=
  iff.symm set_coe.exists

theorem set_coe.forall' {α : Type u} {s : set α} {p : (x : α) → x ∈ s → Prop} :
    (∀ (x : α) (h : x ∈ s), p x h) ↔ ∀ (x : ↥s), p (↑x) (subtype.property x) :=
  iff.symm set_coe.forall

@[simp] theorem set_coe_cast {α : Type u} {s : set α} {t : set α} (H' : s = t) (H : ↥s = ↥t)
    (x : ↥s) : cast H x = { val := subtype.val x, property := H' ▸ subtype.property x } :=
  sorry

theorem set_coe.ext {α : Type u} {s : set α} {a : ↥s} {b : ↥s} : ↑a = ↑b → a = b := subtype.eq

theorem set_coe.ext_iff {α : Type u} {s : set α} {a : ↥s} {b : ↥s} : ↑a = ↑b ↔ a = b :=
  { mp := set_coe.ext, mpr := fun (h : a = b) => h ▸ rfl }

/-- See also `subtype.prop` -/
theorem subtype.mem {α : Type u_1} {s : set α} (p : ↥s) : ↑p ∈ s := subtype.prop p

theorem eq.subset {α : Type u_1} {s : set α} {t : set α} : s = t → s ⊆ t :=
  fun (ᾰ : s = t) => id fun (x : α) (hx : x ∈ s) => Eq._oldrec hx ᾰ

namespace set


protected instance inhabited {α : Type u} : Inhabited (set α) := { default := ∅ }

theorem ext {α : Type u} {a : set α} {b : set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext fun (x : α) => propext (h x)

theorem ext_iff {α : Type u} {s : set α} {t : set α} : s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t :=
  { mp :=
      fun (h : s = t) (x : α) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (x ∈ s ↔ x ∈ t)) h)) (iff.refl (x ∈ t)),
    mpr := ext }

theorem mem_of_mem_of_subset {α : Type u} {x : α} {s : set α} {t : set α} (hx : x ∈ s) (h : s ⊆ t) :
    x ∈ t :=
  h hx

/-! ### Lemmas about `mem` and `set_of` -/

@[simp] theorem mem_set_of_eq {α : Type u} {a : α} {p : α → Prop} :
    (a ∈ set_of fun (a : α) => p a) = p a :=
  rfl

theorem nmem_set_of_eq {α : Type u} {a : α} {P : α → Prop} :
    (¬a ∈ set_of fun (a : α) => P a) = (¬P a) :=
  rfl

@[simp] theorem set_of_mem_eq {α : Type u} {s : set α} : (set_of fun (x : α) => x ∈ s) = s := rfl

theorem set_of_set {α : Type u} {s : set α} : set_of s = s := rfl

theorem set_of_app_iff {α : Type u} {p : α → Prop} {x : α} : set_of (fun (x : α) => p x) x ↔ p x :=
  iff.rfl

theorem mem_def {α : Type u} {a : α} {s : set α} : a ∈ s ↔ s a := iff.rfl

protected instance decidable_mem {α : Type u} (s : set α) [H : decidable_pred s] (a : α) :
    Decidable (a ∈ s) :=
  H

protected instance decidable_set_of {α : Type u} (p : α → Prop) [H : decidable_pred p] :
    decidable_pred (set_of fun (a : α) => p a) :=
  H

@[simp] theorem set_of_subset_set_of {α : Type u} {p : α → Prop} {q : α → Prop} :
    ((set_of fun (a : α) => p a) ⊆ set_of fun (a : α) => q a) ↔ ∀ (a : α), p a → q a :=
  iff.rfl

@[simp] theorem sep_set_of {α : Type u} {p : α → Prop} {q : α → Prop} :
    has_sep.sep (fun (a : α) => q a) (set_of fun (a : α) => p a) =
        set_of fun (a : α) => p a ∧ q a :=
  rfl

theorem set_of_and {α : Type u} {p : α → Prop} {q : α → Prop} :
    (set_of fun (a : α) => p a ∧ q a) = (set_of fun (a : α) => p a) ∩ set_of fun (a : α) => q a :=
  rfl

theorem set_of_or {α : Type u} {p : α → Prop} {q : α → Prop} :
    (set_of fun (a : α) => p a ∨ q a) = (set_of fun (a : α) => p a) ∪ set_of fun (a : α) => q a :=
  rfl

/-! ### Lemmas about subsets -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?

theorem subset_def {α : Type u} {s : set α} {t : set α} : s ⊆ t = ∀ (x : α), x ∈ s → x ∈ t := rfl

theorem subset.refl {α : Type u} (a : set α) : a ⊆ a := fun (x : α) => id

theorem subset.rfl {α : Type u} {s : set α} : s ⊆ s := subset.refl s

theorem subset.trans {α : Type u} {a : set α} {b : set α} {c : set α} (ab : a ⊆ b) (bc : b ⊆ c) :
    a ⊆ c :=
  fun (x : α) (h : x ∈ a) => bc (ab h)

theorem mem_of_eq_of_mem {α : Type u} {x : α} {y : α} {s : set α} (hx : x = y) (h : y ∈ s) :
    x ∈ s :=
  Eq.symm hx ▸ h

theorem subset.antisymm {α : Type u} {a : set α} {b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  ext fun (x : α) => { mp := h₁, mpr := h₂ }

theorem subset.antisymm_iff {α : Type u} {a : set α} {b : set α} : a = b ↔ a ⊆ b ∧ b ⊆ a := sorry

-- an alternative name

theorem eq_of_subset_of_subset {α : Type u} {a : set α} {b : set α} : a ⊆ b → b ⊆ a → a = b :=
  subset.antisymm

theorem mem_of_subset_of_mem {α : Type u} {s₁ : set α} {s₂ : set α} {a : α} (h : s₁ ⊆ s₂) :
    a ∈ s₁ → a ∈ s₂ :=
  h

theorem not_subset {α : Type u} {s : set α} {t : set α} :
    ¬s ⊆ t ↔ ∃ (a : α), ∃ (H : a ∈ s), ¬a ∈ t :=
  sorry

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/

protected instance has_ssubset {α : Type u} : has_ssubset (set α) := has_ssubset.mk Less

@[simp] theorem lt_eq_ssubset {α : Type u} (s : set α) (t : set α) : s < t = (s ⊂ t) := rfl

theorem ssubset_def {α : Type u} {s : set α} {t : set α} : s ⊂ t = (s ⊆ t ∧ ¬t ⊆ s) := rfl

theorem exists_of_ssubset {α : Type u} {s : set α} {t : set α} (h : s ⊂ t) :
    ∃ (x : α), ∃ (H : x ∈ t), ¬x ∈ s :=
  iff.mp not_subset (and.right h)

theorem ssubset_iff_subset_ne {α : Type u} {s : set α} {t : set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  and_congr_right
    fun (h : s ≤ t) => not_congr (iff.symm (iff.trans subset.antisymm_iff (and_iff_right h)))

theorem eq_or_ssubset_of_subset {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  iff.mpr or_iff_not_imp_left
    fun (h' : ¬s = t) => iff.mpr ssubset_iff_subset_ne { left := h, right := h' }

theorem ssubset_iff_of_subset {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) :
    s ⊂ t ↔ ∃ (x : α), ∃ (H : x ∈ t), ¬x ∈ s :=
  sorry

theorem not_mem_empty {α : Type u} (x : α) : ¬x ∈ ∅ := id

@[simp] theorem not_not_mem {α : Type u} {a : α} {s : set α} : ¬¬a ∈ s ↔ a ∈ s := not_not

/-! ### Non-empty sets -/

/-- The property `s.nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty {α : Type u} (s : set α) := ∃ (x : α), x ∈ s

theorem nonempty_def {α : Type u} {s : set α} : set.nonempty s ↔ ∃ (x : α), x ∈ s := iff.rfl

theorem nonempty_of_mem {α : Type u} {s : set α} {x : α} (h : x ∈ s) : set.nonempty s :=
  Exists.intro x h

theorem nonempty.not_subset_empty {α : Type u} {s : set α} : set.nonempty s → ¬s ⊆ ∅ :=
  fun (ᾰ : set.nonempty s) (ᾰ_1 : s ⊆ ∅) =>
    Exists.dcases_on ᾰ fun (ᾰ_w : α) (ᾰ_h : ᾰ_w ∈ s) => idRhs (ᾰ_w ∈ ∅) (ᾰ_1 ᾰ_h)

theorem nonempty.ne_empty {α : Type u} {s : set α} : set.nonempty s → s ≠ ∅ := sorry

/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected def nonempty.some {α : Type u} {s : set α} (h : set.nonempty s) : α := classical.some h

protected theorem nonempty.some_mem {α : Type u} {s : set α} (h : set.nonempty s) :
    nonempty.some h ∈ s :=
  classical.some_spec h

theorem nonempty.mono {α : Type u} {s : set α} {t : set α} (ht : s ⊆ t) (hs : set.nonempty s) :
    set.nonempty t :=
  Exists.imp ht hs

theorem nonempty_of_not_subset {α : Type u} {s : set α} {t : set α} (h : ¬s ⊆ t) :
    set.nonempty (s \ t) :=
  sorry

theorem nonempty_of_ssubset {α : Type u} {s : set α} {t : set α} (ht : s ⊂ t) :
    set.nonempty (t \ s) :=
  nonempty_of_not_subset (and.right ht)

theorem nonempty.of_diff {α : Type u} {s : set α} {t : set α} (h : set.nonempty (s \ t)) :
    set.nonempty s :=
  Exists.imp (fun (_x : α) => and.left) h

theorem nonempty_of_ssubset' {α : Type u} {s : set α} {t : set α} (ht : s ⊂ t) : set.nonempty t :=
  nonempty.of_diff (nonempty_of_ssubset ht)

theorem nonempty.inl {α : Type u} {s : set α} {t : set α} (hs : set.nonempty s) :
    set.nonempty (s ∪ t) :=
  Exists.imp (fun (_x : α) => Or.inl) hs

theorem nonempty.inr {α : Type u} {s : set α} {t : set α} (ht : set.nonempty t) :
    set.nonempty (s ∪ t) :=
  Exists.imp (fun (_x : α) => Or.inr) ht

@[simp] theorem union_nonempty {α : Type u} {s : set α} {t : set α} :
    set.nonempty (s ∪ t) ↔ set.nonempty s ∨ set.nonempty t :=
  exists_or_distrib

theorem nonempty.left {α : Type u} {s : set α} {t : set α} (h : set.nonempty (s ∩ t)) :
    set.nonempty s :=
  Exists.imp (fun (_x : α) => and.left) h

theorem nonempty.right {α : Type u} {s : set α} {t : set α} (h : set.nonempty (s ∩ t)) :
    set.nonempty t :=
  Exists.imp (fun (_x : α) => and.right) h

theorem nonempty_inter_iff_exists_right {α : Type u} {s : set α} {t : set α} :
    set.nonempty (s ∩ t) ↔ ∃ (x : ↥t), ↑x ∈ s :=
  sorry

theorem nonempty_inter_iff_exists_left {α : Type u} {s : set α} {t : set α} :
    set.nonempty (s ∩ t) ↔ ∃ (x : ↥s), ↑x ∈ t :=
  sorry

theorem nonempty_iff_univ_nonempty {α : Type u} : Nonempty α ↔ set.nonempty univ := sorry

@[simp] theorem univ_nonempty {α : Type u} [h : Nonempty α] : set.nonempty univ :=
  nonempty.dcases_on h fun (h : α) => idRhs (∃ (x : α), x ∈ univ) (Exists.intro h trivial)

theorem nonempty.to_subtype {α : Type u} {s : set α} (h : set.nonempty s) : Nonempty ↥s :=
  iff.mpr nonempty_subtype h

protected instance univ.nonempty {α : Type u} [Nonempty α] : Nonempty ↥univ :=
  nonempty.to_subtype univ_nonempty

@[simp] theorem nonempty_insert {α : Type u} (a : α) (s : set α) : set.nonempty (insert a s) :=
  Exists.intro a (Or.inl rfl)

theorem nonempty_of_nonempty_subtype {α : Type u} {s : set α} [Nonempty ↥s] : set.nonempty s :=
  iff.mp nonempty_subtype _inst_1

/-! ### Lemmas about the empty set -/

theorem empty_def {α : Type u} : ∅ = set_of fun (x : α) => False := rfl

@[simp] theorem mem_empty_eq {α : Type u} (x : α) : x ∈ ∅ = False := rfl

@[simp] theorem set_of_false {α : Type u} : (set_of fun (a : α) => False) = ∅ := rfl

@[simp] theorem empty_subset {α : Type u} (s : set α) : ∅ ⊆ s :=
  fun {a : α} (ᾰ : a ∈ ∅) => false.dcases_on (fun (ᾰ : a ∈ ∅) => a ∈ s) ᾰ

theorem subset_empty_iff {α : Type u} {s : set α} : s ⊆ ∅ ↔ s = ∅ :=
  iff.symm (iff.trans subset.antisymm_iff (and_iff_left (empty_subset s)))

theorem eq_empty_iff_forall_not_mem {α : Type u} {s : set α} : s = ∅ ↔ ∀ (x : α), ¬x ∈ s :=
  iff.symm subset_empty_iff

theorem eq_empty_of_subset_empty {α : Type u} {s : set α} : s ⊆ ∅ → s = ∅ := iff.mp subset_empty_iff

theorem eq_empty_of_not_nonempty {α : Type u} (h : ¬Nonempty α) (s : set α) : s = ∅ :=
  eq_empty_of_subset_empty fun (x : α) (hx : x ∈ s) => h (Nonempty.intro x)

theorem not_nonempty_iff_eq_empty {α : Type u} {s : set α} : ¬set.nonempty s ↔ s = ∅ := sorry

theorem empty_not_nonempty {α : Type u} : ¬set.nonempty ∅ :=
  fun (h : set.nonempty ∅) => nonempty.ne_empty h rfl

theorem ne_empty_iff_nonempty {α : Type u} {s : set α} : s ≠ ∅ ↔ set.nonempty s :=
  iff.mp not_iff_comm not_nonempty_iff_eq_empty

theorem eq_empty_or_nonempty {α : Type u} (s : set α) : s = ∅ ∨ set.nonempty s :=
  iff.mpr or_iff_not_imp_left (iff.mp ne_empty_iff_nonempty)

theorem subset_eq_empty {α : Type u} {s : set α} {t : set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  iff.mp subset_empty_iff (e ▸ h)

theorem ball_empty_iff {α : Type u} {p : α → Prop} : (∀ (x : α), x ∈ ∅ → p x) ↔ True :=
  iff_true_intro fun (x : α) => false.elim

/-!

### Universal set.

In Lean `@univ α` (or `univ : set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/

@[simp] theorem set_of_true {α : Type u} : (set_of fun (x : α) => True) = univ := rfl

@[simp] theorem mem_univ {α : Type u} (x : α) : x ∈ univ := trivial

@[simp] theorem univ_eq_empty_iff {α : Type u} : univ = ∅ ↔ ¬Nonempty α := sorry

theorem empty_ne_univ {α : Type u} [h : Nonempty α] : ∅ ≠ univ :=
  fun (e : ∅ = univ) => iff.mp univ_eq_empty_iff (Eq.symm e) h

@[simp] theorem subset_univ {α : Type u} (s : set α) : s ⊆ univ :=
  fun (x : α) (H : x ∈ s) => trivial

theorem univ_subset_iff {α : Type u} {s : set α} : univ ⊆ s ↔ s = univ :=
  iff.symm (iff.trans subset.antisymm_iff (and_iff_right (subset_univ s)))

theorem eq_univ_of_univ_subset {α : Type u} {s : set α} : univ ⊆ s → s = univ :=
  iff.mp univ_subset_iff

theorem eq_univ_iff_forall {α : Type u} {s : set α} : s = univ ↔ ∀ (x : α), x ∈ s :=
  iff.trans (iff.symm univ_subset_iff) (forall_congr fun (x : α) => imp_iff_right True.intro)

theorem eq_univ_of_forall {α : Type u} {s : set α} : (∀ (x : α), x ∈ s) → s = univ :=
  iff.mpr eq_univ_iff_forall

theorem eq_univ_of_subset {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) (hs : s = univ) :
    t = univ :=
  eq_univ_of_univ_subset (hs ▸ h)

theorem exists_mem_of_nonempty (α : Type u_1) [Nonempty α] : ∃ (x : α), x ∈ univ :=
  nonempty.dcases_on _inst_1 fun (val : α) => idRhs (∃ (x : α), x ∈ univ) (Exists.intro val trivial)

protected instance univ_decidable {α : Type u} : decidable_pred univ :=
  fun (x : α) => is_true trivial

/-- `diagonal α` is the subset of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type u_1) : set (α × α) := set_of fun (p : α × α) => prod.fst p = prod.snd p

@[simp] theorem mem_diagonal {α : Type u_1} (x : α) : (x, x) ∈ diagonal α := sorry

/-! ### Lemmas about union -/

theorem union_def {α : Type u} {s₁ : set α} {s₂ : set α} :
    s₁ ∪ s₂ = set_of fun (a : α) => a ∈ s₁ ∨ a ∈ s₂ :=
  rfl

theorem mem_union_left {α : Type u} {x : α} {a : set α} (b : set α) : x ∈ a → x ∈ a ∪ b := Or.inl

theorem mem_union_right {α : Type u} {x : α} {b : set α} (a : set α) : x ∈ b → x ∈ a ∪ b := Or.inr

theorem mem_or_mem_of_mem_union {α : Type u} {x : α} {a : set α} {b : set α} (H : x ∈ a ∪ b) :
    x ∈ a ∨ x ∈ b :=
  H

theorem mem_union.elim {α : Type u} {x : α} {a : set α} {b : set α} {P : Prop} (H₁ : x ∈ a ∪ b)
    (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
  or.elim H₁ H₂ H₃

theorem mem_union {α : Type u} (x : α) (a : set α) (b : set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  iff.rfl

@[simp] theorem mem_union_eq {α : Type u} (x : α) (a : set α) (b : set α) :
    x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) :=
  rfl

@[simp] theorem union_self {α : Type u} (a : set α) : a ∪ a = a :=
  ext fun (x : α) => or_self (x ∈ a)

@[simp] theorem union_empty {α : Type u} (a : set α) : a ∪ ∅ = a :=
  ext fun (x : α) => or_false (x ∈ a)

@[simp] theorem empty_union {α : Type u} (a : set α) : ∅ ∪ a = a :=
  ext fun (x : α) => false_or (x ∈ a)

theorem union_comm {α : Type u} (a : set α) (b : set α) : a ∪ b = b ∪ a :=
  ext fun (x : α) => or.comm

theorem union_assoc {α : Type u} (a : set α) (b : set α) (c : set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext fun (x : α) => or.assoc

protected instance union_is_assoc {α : Type u} : is_associative (set α) has_union.union :=
  is_associative.mk union_assoc

protected instance union_is_comm {α : Type u} : is_commutative (set α) has_union.union :=
  is_commutative.mk union_comm

theorem union_left_comm {α : Type u} (s₁ : set α) (s₂ : set α) (s₃ : set α) :
    s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext fun (x : α) => or.left_comm

theorem union_right_comm {α : Type u} (s₁ : set α) (s₂ : set α) (s₃ : set α) :
    s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext fun (x : α) => or.right_comm

theorem union_eq_self_of_subset_left {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) : s ∪ t = t :=
  ext fun (x : α) => or_iff_right_of_imp h

theorem union_eq_self_of_subset_right {α : Type u} {s : set α} {t : set α} (h : t ⊆ s) :
    s ∪ t = s :=
  ext fun (x : α) => or_iff_left_of_imp h

@[simp] theorem subset_union_left {α : Type u} (s : set α) (t : set α) : s ⊆ s ∪ t :=
  fun (x : α) => Or.inl

@[simp] theorem subset_union_right {α : Type u} (s : set α) (t : set α) : t ⊆ s ∪ t :=
  fun (x : α) => Or.inr

theorem union_subset {α : Type u} {s : set α} {t : set α} {r : set α} (sr : s ⊆ r) (tr : t ⊆ r) :
    s ∪ t ⊆ r :=
  fun (x : α) => Or._oldrec sr tr

@[simp] theorem union_subset_iff {α : Type u} {s : set α} {t : set α} {u : set α} :
    s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  iff.trans (forall_congr fun (x : α) => or_imp_distrib) forall_and_distrib

theorem union_subset_union {α : Type u} {s₁ : set α} {s₂ : set α} {t₁ : set α} {t₂ : set α}
    (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∪ t₁ ⊆ s₂ ∪ t₂ :=
  fun (x : α) => or.imp h₁ h₂

theorem union_subset_union_left {α : Type u} {s₁ : set α} {s₂ : set α} (t : set α) (h : s₁ ⊆ s₂) :
    s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h subset.rfl

theorem union_subset_union_right {α : Type u} (s : set α) {t₁ : set α} {t₂ : set α} (h : t₁ ⊆ t₂) :
    s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union subset.rfl h

theorem subset_union_of_subset_left {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) (u : set α) :
    s ⊆ t ∪ u :=
  subset.trans h (subset_union_left t u)

theorem subset_union_of_subset_right {α : Type u} {s : set α} {u : set α} (h : s ⊆ u) (t : set α) :
    s ⊆ t ∪ u :=
  subset.trans h (subset_union_right t u)

@[simp] theorem union_empty_iff {α : Type u} {s : set α} {t : set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ :=
  sorry

/-! ### Lemmas about intersection -/

theorem inter_def {α : Type u} {s₁ : set α} {s₂ : set α} :
    s₁ ∩ s₂ = set_of fun (a : α) => a ∈ s₁ ∧ a ∈ s₂ :=
  rfl

theorem mem_inter_iff {α : Type u} (x : α) (a : set α) (b : set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  iff.rfl

@[simp] theorem mem_inter_eq {α : Type u} (x : α) (a : set α) (b : set α) :
    x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) :=
  rfl

theorem mem_inter {α : Type u} {x : α} {a : set α} {b : set α} (ha : x ∈ a) (hb : x ∈ b) :
    x ∈ a ∩ b :=
  { left := ha, right := hb }

theorem mem_of_mem_inter_left {α : Type u} {x : α} {a : set α} {b : set α} (h : x ∈ a ∩ b) :
    x ∈ a :=
  and.left h

theorem mem_of_mem_inter_right {α : Type u} {x : α} {a : set α} {b : set α} (h : x ∈ a ∩ b) :
    x ∈ b :=
  and.right h

@[simp] theorem inter_self {α : Type u} (a : set α) : a ∩ a = a :=
  ext fun (x : α) => and_self (x ∈ a)

@[simp] theorem inter_empty {α : Type u} (a : set α) : a ∩ ∅ = ∅ :=
  ext fun (x : α) => and_false (x ∈ a)

@[simp] theorem empty_inter {α : Type u} (a : set α) : ∅ ∩ a = ∅ :=
  ext fun (x : α) => false_and (x ∈ a)

theorem inter_comm {α : Type u} (a : set α) (b : set α) : a ∩ b = b ∩ a :=
  ext fun (x : α) => and.comm

theorem inter_assoc {α : Type u} (a : set α) (b : set α) (c : set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext fun (x : α) => and.assoc

protected instance inter_is_assoc {α : Type u} : is_associative (set α) has_inter.inter :=
  is_associative.mk inter_assoc

protected instance inter_is_comm {α : Type u} : is_commutative (set α) has_inter.inter :=
  is_commutative.mk inter_comm

theorem inter_left_comm {α : Type u} (s₁ : set α) (s₂ : set α) (s₃ : set α) :
    s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun (x : α) => and.left_comm

theorem inter_right_comm {α : Type u} (s₁ : set α) (s₂ : set α) (s₃ : set α) :
    s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun (x : α) => and.right_comm

@[simp] theorem inter_subset_left {α : Type u} (s : set α) (t : set α) : s ∩ t ⊆ s :=
  fun (x : α) => and.left

@[simp] theorem inter_subset_right {α : Type u} (s : set α) (t : set α) : s ∩ t ⊆ t :=
  fun (x : α) => and.right

theorem subset_inter {α : Type u} {s : set α} {t : set α} {r : set α} (rs : r ⊆ s) (rt : r ⊆ t) :
    r ⊆ s ∩ t :=
  fun (x : α) (h : x ∈ r) => { left := rs h, right := rt h }

@[simp] theorem subset_inter_iff {α : Type u} {s : set α} {t : set α} {r : set α} :
    r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  iff.trans (forall_congr fun (x : α) => imp_and_distrib) forall_and_distrib

theorem subset_iff_inter_eq_left {α : Type u} {s : set α} {t : set α} : s ⊆ t ↔ s ∩ t = s :=
  iff.symm (iff.trans ext_iff (forall_congr fun (x : α) => and_iff_left_iff_imp))

theorem subset_iff_inter_eq_right {α : Type u} {s : set α} {t : set α} : t ⊆ s ↔ s ∩ t = t :=
  iff.symm (iff.trans ext_iff (forall_congr fun (x : α) => and_iff_right_iff_imp))

theorem inter_eq_self_of_subset_left {α : Type u} {s : set α} {t : set α} : s ⊆ t → s ∩ t = s :=
  iff.mp subset_iff_inter_eq_left

theorem inter_eq_self_of_subset_right {α : Type u} {s : set α} {t : set α} : t ⊆ s → s ∩ t = t :=
  iff.mp subset_iff_inter_eq_right

@[simp] theorem inter_univ {α : Type u} (a : set α) : a ∩ univ = a :=
  inter_eq_self_of_subset_left (subset_univ a)

@[simp] theorem univ_inter {α : Type u} (a : set α) : univ ∩ a = a :=
  inter_eq_self_of_subset_right (subset_univ a)

theorem inter_subset_inter {α : Type u} {s₁ : set α} {s₂ : set α} {t₁ : set α} {t₂ : set α}
    (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
  fun (x : α) => and.imp h₁ h₂

theorem inter_subset_inter_left {α : Type u} {s : set α} {t : set α} (u : set α) (H : s ⊆ t) :
    s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H subset.rfl

theorem inter_subset_inter_right {α : Type u} {s : set α} {t : set α} (u : set α) (H : s ⊆ t) :
    u ∩ s ⊆ u ∩ t :=
  inter_subset_inter subset.rfl H

theorem union_inter_cancel_left {α : Type u} {s : set α} {t : set α} : (s ∪ t) ∩ s = s :=
  iff.mp subset_iff_inter_eq_right (subset_union_left s t)

theorem union_inter_cancel_right {α : Type u} {s : set α} {t : set α} : (s ∪ t) ∩ t = t :=
  iff.mp subset_iff_inter_eq_right (subset_union_right s t)

/-! ### Distributivity laws -/

theorem inter_distrib_left {α : Type u} (s : set α) (t : set α) (u : set α) :
    s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  ext fun (x : α) => and_or_distrib_left

theorem inter_distrib_right {α : Type u} (s : set α) (t : set α) (u : set α) :
    (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  ext fun (x : α) => or_and_distrib_right

theorem union_distrib_left {α : Type u} (s : set α) (t : set α) (u : set α) :
    s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  ext fun (x : α) => or_and_distrib_left

theorem union_distrib_right {α : Type u} (s : set α) (t : set α) (u : set α) :
    s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  ext fun (x : α) => and_or_distrib_right

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/

theorem insert_def {α : Type u} (x : α) (s : set α) :
    insert x s = set_of fun (y : α) => y = x ∨ y ∈ s :=
  rfl

@[simp] theorem subset_insert {α : Type u} (x : α) (s : set α) : s ⊆ insert x s :=
  fun (y : α) => Or.inr

theorem mem_insert {α : Type u} (x : α) (s : set α) : x ∈ insert x s := Or.inl rfl

theorem mem_insert_of_mem {α : Type u} {x : α} {s : set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr

theorem eq_or_mem_of_mem_insert {α : Type u} {x : α} {a : α} {s : set α} :
    x ∈ insert a s → x = a ∨ x ∈ s :=
  id

theorem mem_of_mem_insert_of_ne {α : Type u} {x : α} {a : α} {s : set α} :
    x ∈ insert a s → x ≠ a → x ∈ s :=
  or.resolve_left

@[simp] theorem mem_insert_iff {α : Type u} {x : α} {a : α} {s : set α} :
    x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  iff.rfl

@[simp] theorem insert_eq_of_mem {α : Type u} {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
  ext fun (x : α) => or_iff_right_of_imp fun (e : x = a) => Eq.symm e ▸ h

theorem ne_insert_of_not_mem {α : Type u} {s : set α} (t : set α) {a : α} :
    ¬a ∈ s → s ≠ insert a t :=
  mt fun (e : s = insert a t) => Eq.symm e ▸ mem_insert a t

theorem insert_subset {α : Type u} {a : α} {s : set α} {t : set α} :
    insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  sorry

theorem insert_subset_insert {α : Type u} {a : α} {s : set α} {t : set α} (h : s ⊆ t) :
    insert a s ⊆ insert a t :=
  fun (x : α) => or.imp_right h

theorem ssubset_iff_insert {α : Type u} {s : set α} {t : set α} :
    s ⊂ t ↔ ∃ (a : α), ∃ (H : ¬a ∈ s), insert a s ⊆ t :=
  sorry

theorem ssubset_insert {α : Type u} {s : set α} {a : α} (h : ¬a ∈ s) : s ⊂ insert a s :=
  iff.mpr ssubset_iff_insert (Exists.intro a (Exists.intro h (subset.refl (insert a s))))

theorem insert_comm {α : Type u} (a : α) (b : α) (s : set α) :
    insert a (insert b s) = insert b (insert a s) :=
  ext fun (x : α) => or.left_comm

theorem insert_union {α : Type u} {a : α} {s : set α} {t : set α} :
    insert a s ∪ t = insert a (s ∪ t) :=
  ext fun (x : α) => or.assoc

@[simp] theorem union_insert {α : Type u} {a : α} {s : set α} {t : set α} :
    s ∪ insert a t = insert a (s ∪ t) :=
  ext fun (x : α) => or.left_comm

theorem insert_nonempty {α : Type u} (a : α) (s : set α) : set.nonempty (insert a s) :=
  Exists.intro a (mem_insert a s)

protected instance has_insert.insert.nonempty {α : Type u} (a : α) (s : set α) :
    Nonempty ↥(insert a s) :=
  nonempty.to_subtype (insert_nonempty a s)

theorem insert_inter {α : Type u} (x : α) (s : set α) (t : set α) :
    insert x (s ∩ t) = insert x s ∩ insert x t :=
  ext fun (y : α) => or_and_distrib_left

-- useful in proofs by induction

theorem forall_of_forall_insert {α : Type u} {P : α → Prop} {a : α} {s : set α}
    (H : ∀ (x : α), x ∈ insert a s → P x) (x : α) (h : x ∈ s) : P x :=
  H x (Or.inr h)

theorem forall_insert_of_forall {α : Type u} {P : α → Prop} {a : α} {s : set α}
    (H : ∀ (x : α), x ∈ s → P x) (ha : P a) (x : α) (h : x ∈ insert a s) : P x :=
  or.elim h (fun (e : x = a) => Eq.symm e ▸ ha) (H x)

theorem bex_insert_iff {α : Type u} {P : α → Prop} {a : α} {s : set α} :
    (∃ (x : α), ∃ (H : x ∈ insert a s), P x) ↔ P a ∨ ∃ (x : α), ∃ (H : x ∈ s), P x :=
  iff.trans bex_or_left_distrib (or_congr_left bex_eq_left)

theorem ball_insert_iff {α : Type u} {P : α → Prop} {a : α} {s : set α} :
    (∀ (x : α), x ∈ insert a s → P x) ↔ P a ∧ ∀ (x : α), x ∈ s → P x :=
  iff.trans ball_or_left_distrib (and_congr_left' forall_eq)

/-! ### Lemmas about singletons -/

theorem singleton_def {α : Type u} (a : α) : singleton a = insert a ∅ :=
  Eq.symm (insert_emptyc_eq a)

@[simp] theorem mem_singleton_iff {α : Type u} {a : α} {b : α} : a ∈ singleton b ↔ a = b := iff.rfl

@[simp] theorem set_of_eq_eq_singleton {α : Type u} {a : α} :
    (set_of fun (n : α) => n = a) = singleton a :=
  ext fun (n : α) => iff.symm mem_singleton_iff

-- TODO: again, annotation needed

@[simp] theorem mem_singleton {α : Type u} (a : α) : a ∈ singleton a := rfl

theorem eq_of_mem_singleton {α : Type u} {x : α} {y : α} (h : x ∈ singleton y) : x = y := h

@[simp] theorem singleton_eq_singleton_iff {α : Type u} {x : α} {y : α} :
    singleton x = singleton y ↔ x = y :=
  iff.trans ext_iff eq_iff_eq_cancel_left

theorem mem_singleton_of_eq {α : Type u} {x : α} {y : α} (H : x = y) : x ∈ singleton y := H

theorem insert_eq {α : Type u} (x : α) (s : set α) : insert x s = singleton x ∪ s := rfl

@[simp] theorem pair_eq_singleton {α : Type u} (a : α) : insert a (singleton a) = singleton a :=
  union_self fun (b : α) => b = a

theorem pair_comm {α : Type u} (a : α) (b : α) : insert a (singleton b) = insert b (singleton a) :=
  union_comm (fun (b : α) => b = a) (singleton b)

@[simp] theorem singleton_nonempty {α : Type u} (a : α) : set.nonempty (singleton a) :=
  Exists.intro a rfl

@[simp] theorem singleton_subset_iff {α : Type u} {a : α} {s : set α} : singleton a ⊆ s ↔ a ∈ s :=
  forall_eq

theorem set_compr_eq_eq_singleton {α : Type u} {a : α} :
    (set_of fun (b : α) => b = a) = singleton a :=
  rfl

@[simp] theorem singleton_union {α : Type u} {a : α} {s : set α} : singleton a ∪ s = insert a s :=
  rfl

@[simp] theorem union_singleton {α : Type u} {a : α} {s : set α} : s ∪ singleton a = insert a s :=
  union_comm s (singleton a)

@[simp] theorem singleton_inter_nonempty {α : Type u} {a : α} {s : set α} :
    set.nonempty (singleton a ∩ s) ↔ a ∈ s :=
  sorry

@[simp] theorem inter_singleton_nonempty {α : Type u} {a : α} {s : set α} :
    set.nonempty (s ∩ singleton a) ↔ a ∈ s :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (set.nonempty (s ∩ singleton a) ↔ a ∈ s)) (inter_comm s (singleton a))))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (set.nonempty (singleton a ∩ s) ↔ a ∈ s))
          (propext singleton_inter_nonempty)))
      (iff.refl (a ∈ s)))

@[simp] theorem singleton_inter_eq_empty {α : Type u} {a : α} {s : set α} :
    singleton a ∩ s = ∅ ↔ ¬a ∈ s :=
  iff.trans (iff.symm not_nonempty_iff_eq_empty) (not_congr singleton_inter_nonempty)

@[simp] theorem inter_singleton_eq_empty {α : Type u} {a : α} {s : set α} :
    s ∩ singleton a = ∅ ↔ ¬a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ singleton a = ∅ ↔ ¬a ∈ s)) (inter_comm s (singleton a))))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (singleton a ∩ s = ∅ ↔ ¬a ∈ s)) (propext singleton_inter_eq_empty)))
      (iff.refl (¬a ∈ s)))

theorem nmem_singleton_empty {α : Type u} {s : set α} : ¬s ∈ singleton ∅ ↔ set.nonempty s :=
  ne_empty_iff_nonempty

protected instance unique_singleton {α : Type u} (a : α) : unique ↥(singleton a) :=
  unique.mk { default := { val := a, property := mem_singleton a } } sorry

theorem eq_singleton_iff_unique_mem {α : Type u} {s : set α} {a : α} :
    s = singleton a ↔ a ∈ s ∧ ∀ (x : α), x ∈ s → x = a :=
  iff.trans subset.antisymm_iff (iff.trans and.comm (and_congr_left' singleton_subset_iff))

theorem eq_singleton_iff_nonempty_unique_mem {α : Type u} {s : set α} {a : α} :
    s = singleton a ↔ set.nonempty s ∧ ∀ (x : α), x ∈ s → x = a :=
  sorry

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

theorem mem_sep {α : Type u} {s : set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) :
    x ∈ has_sep.sep (fun (x : α) => p x) s :=
  { left := xs, right := px }

@[simp] theorem sep_mem_eq {α : Type u} {s : set α} {t : set α} :
    has_sep.sep (fun (x : α) => x ∈ t) s = s ∩ t :=
  rfl

@[simp] theorem mem_sep_eq {α : Type u} {s : set α} {p : α → Prop} {x : α} :
    x ∈ has_sep.sep (fun (x : α) => p x) s = (x ∈ s ∧ p x) :=
  rfl

theorem mem_sep_iff {α : Type u} {s : set α} {p : α → Prop} {x : α} :
    x ∈ has_sep.sep (fun (x : α) => p x) s ↔ x ∈ s ∧ p x :=
  iff.rfl

theorem eq_sep_of_subset {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) :
    s = has_sep.sep (fun (x : α) => x ∈ s) t :=
  Eq.symm (iff.mp subset_iff_inter_eq_right h)

theorem sep_subset {α : Type u} (s : set α) (p : α → Prop) :
    has_sep.sep (fun (x : α) => p x) s ⊆ s :=
  fun (x : α) => and.left

theorem forall_not_of_sep_empty {α : Type u} {s : set α} {p : α → Prop}
    (H : has_sep.sep (fun (x : α) => p x) s = ∅) (x : α) : x ∈ s → ¬p x :=
  iff.mp not_and (iff.mp eq_empty_iff_forall_not_mem H x)

@[simp] theorem sep_univ {α : Type u_1} {p : α → Prop} :
    has_sep.sep (fun (a : α) => p a) univ = set_of fun (a : α) => p a :=
  univ_inter fun (a : α) => p a

@[simp] theorem subset_singleton_iff {α : Type u_1} {s : set α} {x : α} :
    s ⊆ singleton x ↔ ∀ (y : α), y ∈ s → y = x :=
  iff.rfl

/-! ### Lemmas about complement -/

theorem mem_compl {α : Type u} {s : set α} {x : α} (h : ¬x ∈ s) : x ∈ (sᶜ) := h

theorem compl_set_of {α : Type u_1} (p : α → Prop) :
    (set_of fun (a : α) => p a)ᶜ = set_of fun (a : α) => ¬p a :=
  rfl

theorem not_mem_of_mem_compl {α : Type u} {s : set α} {x : α} (h : x ∈ (sᶜ)) : ¬x ∈ s := h

@[simp] theorem mem_compl_eq {α : Type u} (s : set α) (x : α) : x ∈ (sᶜ) = (¬x ∈ s) := rfl

theorem mem_compl_iff {α : Type u} (s : set α) (x : α) : x ∈ (sᶜ) ↔ ¬x ∈ s := iff.rfl

@[simp] theorem inter_compl_self {α : Type u} (s : set α) : s ∩ (sᶜ) = ∅ := inf_compl_eq_bot

@[simp] theorem compl_inter_self {α : Type u} (s : set α) : sᶜ ∩ s = ∅ := compl_inf_eq_bot

@[simp] theorem compl_empty {α : Type u} : ∅ᶜ = univ := compl_bot

@[simp] theorem compl_union {α : Type u} (s : set α) (t : set α) : s ∪ tᶜ = sᶜ ∩ (tᶜ) := compl_sup

theorem compl_inter {α : Type u} (s : set α) (t : set α) : s ∩ tᶜ = sᶜ ∪ (tᶜ) := compl_inf

@[simp] theorem compl_univ {α : Type u} : univᶜ = ∅ := compl_top

@[simp] theorem compl_empty_iff {α : Type u} {s : set α} : sᶜ = ∅ ↔ s = univ := compl_eq_bot

@[simp] theorem compl_univ_iff {α : Type u} {s : set α} : sᶜ = univ ↔ s = ∅ := compl_eq_top

theorem nonempty_compl {α : Type u} {s : set α} : set.nonempty (sᶜ) ↔ s ≠ univ :=
  iff.trans (iff.symm ne_empty_iff_nonempty) (not_congr compl_empty_iff)

theorem mem_compl_singleton_iff {α : Type u} {a : α} {x : α} : x ∈ (singleton aᶜ) ↔ x ≠ a :=
  not_congr mem_singleton_iff

theorem compl_singleton_eq {α : Type u} (a : α) : singleton aᶜ = set_of fun (x : α) => x ≠ a :=
  ext fun (x : α) => mem_compl_singleton_iff

theorem union_eq_compl_compl_inter_compl {α : Type u} (s : set α) (t : set α) :
    s ∪ t = (sᶜ ∩ (tᶜ)ᶜ) :=
  ext fun (x : α) => or_iff_not_and_not

theorem inter_eq_compl_compl_union_compl {α : Type u} (s : set α) (t : set α) :
    s ∩ t = (sᶜ ∪ (tᶜ)ᶜ) :=
  ext fun (x : α) => and_iff_not_or_not

@[simp] theorem union_compl_self {α : Type u} (s : set α) : s ∪ (sᶜ) = univ :=
  iff.mpr eq_univ_iff_forall fun (x : α) => em (x ∈ s)

@[simp] theorem compl_union_self {α : Type u} (s : set α) : sᶜ ∪ s = univ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (sᶜ ∪ s = univ)) (union_comm (sᶜ) s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ (sᶜ) = univ)) (union_compl_self s))) (Eq.refl univ))

theorem compl_comp_compl {α : Type u} : compl ∘ compl = id := funext compl_compl

theorem compl_subset_comm {α : Type u} {s : set α} {t : set α} : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
  compl_le_iff_compl_le

theorem compl_subset_compl {α : Type u} {s : set α} {t : set α} : sᶜ ⊆ (tᶜ) ↔ t ⊆ s :=
  compl_le_compl_iff_le

theorem compl_subset_iff_union {α : Type u} {s : set α} {t : set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
  iff.symm (iff.trans eq_univ_iff_forall (forall_congr fun (a : α) => or_iff_not_imp_left))

theorem subset_compl_comm {α : Type u} {s : set α} {t : set α} : s ⊆ (tᶜ) ↔ t ⊆ (sᶜ) :=
  forall_congr fun (a : α) => imp_not_comm

theorem subset_compl_iff_disjoint {α : Type u} {s : set α} {t : set α} : s ⊆ (tᶜ) ↔ s ∩ t = ∅ :=
  iff.trans (forall_congr fun (a : α) => iff.symm and_imp) subset_empty_iff

theorem subset_compl_singleton_iff {α : Type u} {a : α} {s : set α} : s ⊆ (singleton aᶜ) ↔ ¬a ∈ s :=
  iff.trans subset_compl_comm singleton_subset_iff

theorem inter_subset {α : Type u} (a : set α) (b : set α) (c : set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
  forall_congr fun (x : α) => iff.trans and_imp (imp_congr_right fun (_x : x ∈ a) => imp_iff_not_or)

theorem inter_compl_nonempty_iff {α : Type u} {s : set α} {t : set α} :
    set.nonempty (s ∩ (tᶜ)) ↔ ¬s ⊆ t :=
  sorry

/-! ### Lemmas about set difference -/

theorem diff_eq {α : Type u} (s : set α) (t : set α) : s \ t = s ∩ (tᶜ) := rfl

@[simp] theorem mem_diff {α : Type u} {s : set α} {t : set α} (x : α) :
    x ∈ s \ t ↔ x ∈ s ∧ ¬x ∈ t :=
  iff.rfl

theorem mem_diff_of_mem {α : Type u} {s : set α} {t : set α} {x : α} (h1 : x ∈ s) (h2 : ¬x ∈ t) :
    x ∈ s \ t :=
  { left := h1, right := h2 }

theorem mem_of_mem_diff {α : Type u} {s : set α} {t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  and.left h

theorem not_mem_of_mem_diff {α : Type u} {s : set α} {t : set α} {x : α} (h : x ∈ s \ t) : ¬x ∈ t :=
  and.right h

theorem diff_eq_compl_inter {α : Type u} {s : set α} {t : set α} : s \ t = tᶜ ∩ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ t = tᶜ ∩ s)) (diff_eq s t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ (tᶜ) = tᶜ ∩ s)) (inter_comm s (tᶜ)))) (Eq.refl (tᶜ ∩ s)))

theorem nonempty_diff {α : Type u} {s : set α} {t : set α} : set.nonempty (s \ t) ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff

theorem diff_subset {α : Type u} (s : set α) (t : set α) : s \ t ⊆ s :=
  inter_subset_left s fun (a : α) => a ∈ t → False

theorem union_diff_cancel' {α : Type u} {s : set α} {t : set α} {u : set α} (h₁ : s ⊆ t)
    (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sorry

theorem union_diff_cancel {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  union_diff_cancel' (subset.refl s) h

theorem union_diff_cancel_left {α : Type u} {s : set α} {t : set α} (h : s ∩ t ⊆ ∅) :
    (s ∪ t) \ s = t :=
  sorry

theorem union_diff_cancel_right {α : Type u} {s : set α} {t : set α} (h : s ∩ t ⊆ ∅) :
    (s ∪ t) \ t = s :=
  sorry

@[simp] theorem union_diff_left {α : Type u} {s : set α} {t : set α} : (s ∪ t) \ s = t \ s := sorry

@[simp] theorem union_diff_right {α : Type u} {s : set α} {t : set α} : (s ∪ t) \ t = s \ t := sorry

theorem union_diff_distrib {α : Type u} {s : set α} {t : set α} {u : set α} :
    (s ∪ t) \ u = s \ u ∪ t \ u :=
  inter_distrib_right s t fun (a : α) => a ∈ u → False

theorem inter_union_distrib_left {α : Type u} {s : set α} {t : set α} {u : set α} :
    s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  ext fun (_x : α) => and_or_distrib_left

theorem inter_union_distrib_right {α : Type u} {s : set α} {t : set α} {u : set α} :
    s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  ext fun (_x : α) => and_or_distrib_right

theorem union_inter_distrib_left {α : Type u} {s : set α} {t : set α} {u : set α} :
    s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  ext fun (_x : α) => or_and_distrib_left

theorem union_inter_distrib_right {α : Type u} {s : set α} {t : set α} {u : set α} :
    (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  ext fun (_x : α) => or_and_distrib_right

theorem inter_diff_assoc {α : Type u} (a : set α) (b : set α) (c : set α) :
    a ∩ b \ c = a ∩ (b \ c) :=
  inter_assoc a b fun (a : α) => a ∈ c → False

@[simp] theorem inter_diff_self {α : Type u} (a : set α) (b : set α) : a ∩ (b \ a) = ∅ := sorry

@[simp] theorem inter_union_diff {α : Type u} (s : set α) (t : set α) : s ∩ t ∪ s \ t = s := sorry

@[simp] theorem inter_union_compl {α : Type u} (s : set α) (t : set α) : s ∩ t ∪ s ∩ (tᶜ) = s :=
  inter_union_diff s t

theorem diff_subset_diff {α : Type u} {s₁ : set α} {s₂ : set α} {t₁ : set α} {t₂ : set α} :
    s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  sorry

theorem diff_subset_diff_left {α : Type u} {s₁ : set α} {s₂ : set α} {t : set α} (h : s₁ ⊆ s₂) :
    s₁ \ t ⊆ s₂ \ t :=
  diff_subset_diff h (subset.refl t)

theorem diff_subset_diff_right {α : Type u} {s : set α} {t : set α} {u : set α} (h : t ⊆ u) :
    s \ u ⊆ s \ t :=
  diff_subset_diff (subset.refl s) h

theorem compl_eq_univ_diff {α : Type u} (s : set α) : sᶜ = univ \ s := sorry

@[simp] theorem empty_diff {α : Type u} (s : set α) : ∅ \ s = ∅ :=
  eq_empty_of_subset_empty
    fun (x : α) (_x : x ∈ ∅ \ s) =>
      (fun (_a : x ∈ ∅ \ s) =>
          and.dcases_on _a fun (left : x ∈ ∅) (right : ¬x ∈ s) => idRhs (x ∈ ∅) left)
        _x

theorem diff_eq_empty {α : Type u} {s : set α} {t : set α} : s \ t = ∅ ↔ s ⊆ t := sorry

@[simp] theorem diff_empty {α : Type u} {s : set α} : s \ ∅ = s := sorry

theorem diff_diff {α : Type u} {s : set α} {t : set α} {u : set α} : s \ t \ u = s \ (t ∪ u) :=
  sorry

-- the following statement contains parentheses to help the reader

theorem diff_diff_comm {α : Type u} {s : set α} {t : set α} {u : set α} : s \ t \ u = s \ u \ t :=
  sorry

theorem diff_subset_iff {α : Type u} {s : set α} {t : set α} {u : set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  sorry

theorem subset_diff_union {α : Type u} (s : set α) (t : set α) : s ⊆ s \ t ∪ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ⊆ s \ t ∪ t)) (union_comm (s \ t) t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ⊆ t ∪ s \ t)) (Eq.symm (propext diff_subset_iff))))
      (subset.refl (s \ t)))

@[simp] theorem diff_singleton_subset_iff {α : Type u} {x : α} {s : set α} {t : set α} :
    s \ singleton x ⊆ t ↔ s ⊆ insert x t :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (s \ singleton x ⊆ t ↔ s ⊆ insert x t)) (Eq.symm union_singleton)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (s \ singleton x ⊆ t ↔ s ⊆ t ∪ singleton x))
          (union_comm t (singleton x))))
      diff_subset_iff)

theorem subset_diff_singleton {α : Type u} {x : α} {s : set α} {t : set α} (h : s ⊆ t)
    (hx : ¬x ∈ s) : s ⊆ t \ singleton x :=
  subset_inter h (iff.mp subset_compl_comm (iff.mpr singleton_subset_iff hx))

theorem subset_insert_diff_singleton {α : Type u} (x : α) (s : set α) :
    s ⊆ insert x (s \ singleton x) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (s ⊆ insert x (s \ singleton x)))
        (Eq.symm (propext diff_singleton_subset_iff))))
    (subset.refl (s \ singleton x))

theorem diff_subset_comm {α : Type u} {s : set α} {t : set α} {u : set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ⊆ u ↔ s \ u ⊆ t)) (propext diff_subset_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ⊆ t ∪ u ↔ s \ u ⊆ t)) (propext diff_subset_iff)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (s ⊆ t ∪ u ↔ s ⊆ u ∪ t)) (union_comm t u)))
        (iff.refl (s ⊆ u ∪ t))))

theorem diff_inter {α : Type u} {s : set α} {t : set α} {u : set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sorry

theorem diff_inter_diff {α : Type u} {s : set α} {t : set α} {u : set α} :
    s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sorry

theorem diff_compl {α : Type u} {s : set α} {t : set α} : s \ (tᶜ) = s ∩ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ (tᶜ) = s ∩ t)) (diff_eq s (tᶜ))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ (tᶜᶜ) = s ∩ t)) (compl_compl t))) (Eq.refl (s ∩ t)))

theorem diff_diff_right {α : Type u} {s : set α} {t : set α} {u : set α} :
    s \ (t \ u) = s \ t ∪ s ∩ u :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ (t \ u) = s \ t ∪ s ∩ u)) (diff_eq t u)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s \ (t ∩ (uᶜ)) = s \ t ∪ s ∩ u)) diff_inter))
      (eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ∪ s \ (uᶜ) = s \ t ∪ s ∩ u)) diff_compl))
        (Eq.refl (s \ t ∪ s ∩ u))))

@[simp] theorem insert_diff_of_mem {α : Type u} {a : α} {t : set α} (s : set α) (h : a ∈ t) :
    insert a s \ t = s \ t :=
  sorry

theorem insert_diff_of_not_mem {α : Type u} {a : α} {t : set α} (s : set α) (h : ¬a ∈ t) :
    insert a s \ t = insert a (s \ t) :=
  sorry

theorem insert_diff_self_of_not_mem {α : Type u} {a : α} {s : set α} (h : ¬a ∈ s) :
    insert a s \ singleton a = s :=
  sorry

theorem union_diff_self {α : Type u} {s : set α} {t : set α} : s ∪ t \ s = s ∪ t := sorry

theorem diff_union_self {α : Type u} {s : set α} {t : set α} : s \ t ∪ t = s ∪ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ∪ t = s ∪ t)) (union_comm (s \ t) t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t ∪ s \ t = s ∪ t)) union_diff_self))
      (eq.mpr (id (Eq._oldrec (Eq.refl (t ∪ s = s ∪ t)) (union_comm t s))) (Eq.refl (s ∪ t))))

theorem diff_inter_self {α : Type u} {a : set α} {b : set α} : b \ a ∩ a = ∅ := sorry

theorem diff_inter_self_eq_diff {α : Type u} {s : set α} {t : set α} : s \ (t ∩ s) = s \ t := sorry

theorem diff_self_inter {α : Type u} {s : set α} {t : set α} : s \ (s ∩ t) = s \ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ (s ∩ t) = s \ t)) (inter_comm s t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s \ (t ∩ s) = s \ t)) diff_inter_self_eq_diff))
      (Eq.refl (s \ t)))

theorem diff_eq_self {α : Type u} {s : set α} {t : set α} : s \ t = s ↔ t ∩ s ⊆ ∅ := sorry

@[simp] theorem diff_singleton_eq_self {α : Type u} {a : α} {s : set α} (h : ¬a ∈ s) :
    s \ singleton a = s :=
  sorry

@[simp] theorem insert_diff_singleton {α : Type u} {a : α} {s : set α} :
    insert a (s \ singleton a) = insert a s :=
  sorry

@[simp] theorem diff_self {α : Type u} {s : set α} : s \ s = ∅ := sorry

theorem diff_diff_cancel_left {α : Type u} {s : set α} {t : set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sorry

theorem mem_diff_singleton {α : Type u} {x : α} {y : α} {s : set α} :
    x ∈ s \ singleton y ↔ x ∈ s ∧ x ≠ y :=
  iff.rfl

theorem mem_diff_singleton_empty {α : Type u} {s : set α} {t : set (set α)} :
    s ∈ t \ singleton ∅ ↔ s ∈ t ∧ set.nonempty s :=
  iff.trans mem_diff_singleton (and_congr iff.rfl ne_empty_iff_nonempty)

/-! ### Powerset -/

theorem mem_powerset {α : Type u} {x : set α} {s : set α} (h : x ⊆ s) : x ∈ 𝒫 s := h

theorem subset_of_mem_powerset {α : Type u} {x : set α} {s : set α} (h : x ∈ 𝒫 s) : x ⊆ s := h

@[simp] theorem mem_powerset_iff {α : Type u} (x : set α) (s : set α) : x ∈ 𝒫 s ↔ x ⊆ s := iff.rfl

theorem powerset_inter {α : Type u} (s : set α) (t : set α) : 𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext fun (u : set α) => subset_inter_iff

@[simp] theorem powerset_mono {α : Type u} {s : set α} {t : set α} : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  { mp := fun (h : 𝒫 s ⊆ 𝒫 t) => h (subset.refl s),
    mpr := fun (h : s ⊆ t) (u : set α) (hu : u ∈ 𝒫 s) => subset.trans hu h }

theorem monotone_powerset {α : Type u} : monotone powerset :=
  fun (s t : set α) => iff.mpr powerset_mono

@[simp] theorem powerset_nonempty {α : Type u} {s : set α} : set.nonempty (𝒫 s) :=
  Exists.intro ∅ (empty_subset s)

@[simp] theorem powerset_empty {α : Type u} : 𝒫∅ = singleton ∅ :=
  ext fun (s : set α) => subset_empty_iff

/-! ### Inverse image -/

/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α :=
  set_of fun (x : α) => f x ∈ s

infixl:80 " ⁻¹' " => Mathlib.set.preimage

@[simp] theorem preimage_empty {α : Type u} {β : Type v} {f : α → β} : f ⁻¹' ∅ = ∅ := rfl

@[simp] theorem mem_preimage {α : Type u} {β : Type v} {f : α → β} {s : set β} {a : α} :
    a ∈ f ⁻¹' s ↔ f a ∈ s :=
  iff.rfl

theorem preimage_congr {α : Type u} {β : Type v} {f : α → β} {g : α → β} {s : set β}
    (h : ∀ (x : α), f x = g x) : f ⁻¹' s = g ⁻¹' s :=
  (fun (f f_1 : α → β) (e_1 : f = f_1) (s s_1 : set β) (e_2 : s = s_1) =>
      congr (congr_arg preimage e_1) e_2)
    f g (funext fun (x : α) => h x) s s (Eq.refl s)

theorem preimage_mono {α : Type u} {β : Type v} {f : α → β} {s : set β} {t : set β} (h : s ⊆ t) :
    f ⁻¹' s ⊆ f ⁻¹' t :=
  fun (x : α) (hx : x ∈ f ⁻¹' s) => h hx

@[simp] theorem preimage_univ {α : Type u} {β : Type v} {f : α → β} : f ⁻¹' univ = univ := rfl

theorem subset_preimage_univ {α : Type u} {β : Type v} {f : α → β} {s : set α} : s ⊆ f ⁻¹' univ :=
  subset_univ s

@[simp] theorem preimage_inter {α : Type u} {β : Type v} {f : α → β} {s : set β} {t : set β} :
    f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl

@[simp] theorem preimage_union {α : Type u} {β : Type v} {f : α → β} {s : set β} {t : set β} :
    f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl

@[simp] theorem preimage_compl {α : Type u} {β : Type v} {f : α → β} {s : set β} :
    f ⁻¹' (sᶜ) = (f ⁻¹' sᶜ) :=
  rfl

@[simp] theorem preimage_diff {α : Type u} {β : Type v} (f : α → β) (s : set β) (t : set β) :
    f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl

@[simp] theorem preimage_set_of_eq {α : Type u} {β : Type v} {p : α → Prop} {f : β → α} :
    (f ⁻¹' set_of fun (a : α) => p a) = set_of fun (a : β) => p (f a) :=
  rfl

@[simp] theorem preimage_id {α : Type u} {s : set α} : id ⁻¹' s = s := rfl

@[simp] theorem preimage_id' {α : Type u} {s : set α} : (fun (x : α) => x) ⁻¹' s = s := rfl

theorem preimage_const_of_mem {α : Type u} {β : Type v} {b : β} {s : set β} (h : b ∈ s) :
    (fun (x : α) => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun (x : α) => h

theorem preimage_const_of_not_mem {α : Type u} {β : Type v} {b : β} {s : set β} (h : ¬b ∈ s) :
    (fun (x : α) => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun (x : α) (hx : x ∈ (fun (x : α) => b) ⁻¹' s) => h hx

theorem preimage_const {α : Type u} {β : Type v} (b : β) (s : set β) [Decidable (b ∈ s)] :
    (fun (x : α) => b) ⁻¹' s = ite (b ∈ s) univ ∅ :=
  sorry

theorem preimage_comp {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ} {s : set γ} :
    g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl

theorem preimage_preimage {α : Type u} {β : Type v} {γ : Type w} {g : β → γ} {f : α → β}
    {s : set γ} : f ⁻¹' (g ⁻¹' s) = (fun (x : α) => g (f x)) ⁻¹' s :=
  Eq.symm preimage_comp

theorem eq_preimage_subtype_val_iff {α : Type u} {p : α → Prop} {s : set (Subtype p)} {t : set α} :
    s = subtype.val ⁻¹' t ↔ ∀ (x : α) (h : p x), { val := x, property := h } ∈ s ↔ x ∈ t :=
  sorry

theorem preimage_coe_coe_diagonal {α : Type u_1} (s : set α) :
    prod.map coe coe ⁻¹' diagonal α = diagonal ↥s :=
  sorry

infixl:80 " '' " => Mathlib.set.image

/-! ### Image of a set under a function -/

theorem mem_image_iff_bex {α : Type u} {β : Type v} {f : α → β} {s : set α} {y : β} :
    y ∈ f '' s ↔ ∃ (x : α), ∃ (_x : x ∈ s), f x = y :=
  iff.symm bex_def

theorem mem_image_eq {α : Type u} {β : Type v} (f : α → β) (s : set α) (y : β) :
    y ∈ f '' s = ∃ (x : α), x ∈ s ∧ f x = y :=
  rfl

@[simp] theorem mem_image {α : Type u} {β : Type v} (f : α → β) (s : set α) (y : β) :
    y ∈ f '' s ↔ ∃ (x : α), x ∈ s ∧ f x = y :=
  iff.rfl

theorem image_eta {α : Type u} {β : Type v} {s : set α} (f : α → β) :
    f '' s = (fun (x : α) => f x) '' s :=
  rfl

theorem mem_image_of_mem {α : Type u} {β : Type v} (f : α → β) {x : α} {a : set α} (h : x ∈ a) :
    f x ∈ f '' a :=
  Exists.intro x { left := h, right := rfl }

theorem mem_image_of_injective {α : Type u} {β : Type v} {f : α → β} {a : α} {s : set α}
    (hf : function.injective f) : f a ∈ f '' s ↔ a ∈ s :=
  sorry

theorem ball_image_iff {α : Type u} {β : Type v} {f : α → β} {s : set α} {p : β → Prop} :
    (∀ (y : β), y ∈ f '' s → p y) ↔ ∀ (x : α), x ∈ s → p (f x) :=
  sorry

theorem ball_image_of_ball {α : Type u} {β : Type v} {f : α → β} {s : set α} {p : β → Prop}
    (h : ∀ (x : α), x ∈ s → p (f x)) (y : β) (H : y ∈ f '' s) : p y :=
  iff.mpr ball_image_iff h

theorem bex_image_iff {α : Type u} {β : Type v} {f : α → β} {s : set α} {p : β → Prop} :
    (∃ (y : β), ∃ (H : y ∈ f '' s), p y) ↔ ∃ (x : α), ∃ (H : x ∈ s), p (f x) :=
  sorry

theorem mem_image_elim {α : Type u} {β : Type v} {f : α → β} {s : set α} {C : β → Prop}
    (h : ∀ (x : α), x ∈ s → C (f x)) {y : β} : y ∈ f '' s → C y :=
  sorry

theorem mem_image_elim_on {α : Type u} {β : Type v} {f : α → β} {s : set α} {C : β → Prop} {y : β}
    (h_y : y ∈ f '' s) (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
  mem_image_elim h h_y

theorem image_congr {α : Type u} {β : Type v} {f : α → β} {g : α → β} {s : set α}
    (h : ∀ (a : α), a ∈ s → f a = g a) : f '' s = g '' s :=
  sorry

/-- A common special case of `image_congr` -/
theorem image_congr' {α : Type u} {β : Type v} {f : α → β} {g : α → β} {s : set α}
    (h : ∀ (x : α), f x = g x) : f '' s = g '' s :=
  image_congr fun (x : α) (_x : x ∈ s) => h x

theorem image_comp {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) (g : α → β) (a : set α) :
    f ∘ g '' a = f '' (g '' a) :=
  subset.antisymm
    (ball_image_of_ball fun (a_1 : α) (ha : a_1 ∈ a) => mem_image_of_mem f (mem_image_of_mem g ha))
    (ball_image_of_ball
      (ball_image_of_ball fun (a_1 : α) (ha : a_1 ∈ a) => mem_image_of_mem (f ∘ g) ha))

/-- A variant of `image_comp`, useful for rewriting -/
theorem image_image {α : Type u} {β : Type v} {γ : Type w} (g : β → γ) (f : α → β) (s : set α) :
    g '' (f '' s) = (fun (x : α) => g (f x)) '' s :=
  Eq.symm (image_comp g f s)

/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {α : Type u} {β : Type v} {a : set α} {b : set α} (f : α → β) (h : a ⊆ b) :
    f '' a ⊆ f '' b :=
  sorry

theorem image_union {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set α) :
    f '' (s ∪ t) = f '' s ∪ f '' t :=
  sorry

@[simp] theorem image_empty {α : Type u} {β : Type v} (f : α → β) : f '' ∅ = ∅ := sorry

theorem image_inter_subset {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set α) :
    f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  subset_inter (image_subset f (inter_subset_left s t)) (image_subset f (inter_subset_right s t))

theorem image_inter_on {α : Type u} {β : Type v} {f : α → β} {s : set α} {t : set α}
    (h : ∀ (x : α), x ∈ t → ∀ (y : α), y ∈ s → f x = f y → x = y) :
    f '' s ∩ f '' t = f '' (s ∩ t) :=
  sorry

theorem image_inter {α : Type u} {β : Type v} {f : α → β} {s : set α} {t : set α}
    (H : function.injective f) : f '' s ∩ f '' t = f '' (s ∩ t) :=
  image_inter_on fun (x : α) (_x : x ∈ t) (y : α) (_x : y ∈ s) (h : f x = f y) => H h

theorem image_univ_of_surjective {β : Type v} {ι : Type u_1} {f : ι → β}
    (H : function.surjective f) : f '' univ = univ :=
  sorry

@[simp] theorem image_singleton {α : Type u} {β : Type v} {f : α → β} {a : α} :
    f '' singleton a = singleton (f a) :=
  sorry

@[simp] theorem nonempty.image_const {α : Type u} {β : Type v} {s : set α} (hs : set.nonempty s)
    (a : β) : (fun (_x : α) => a) '' s = singleton a :=
  sorry

@[simp] theorem image_eq_empty {α : Type u_1} {β : Type u_2} {f : α → β} {s : set α} :
    f '' s = ∅ ↔ s = ∅ :=
  sorry

-- TODO(Jeremy): there is an issue with - t unfolding to compl t

theorem mem_compl_image {α : Type u} (t : set α) (S : set (set α)) : t ∈ compl '' S ↔ tᶜ ∈ S :=
  sorry

/-- A variant of `image_id` -/
@[simp] theorem image_id' {α : Type u} (s : set α) : (fun (x : α) => x) '' s = s := sorry

theorem image_id {α : Type u} (s : set α) : id '' s = s := sorry

theorem compl_compl_image {α : Type u} (S : set (set α)) : compl '' (compl '' S) = S :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (compl '' (compl '' S) = S)) (Eq.symm (image_comp compl compl S))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (compl ∘ compl '' S = S)) compl_comp_compl))
      (eq.mpr (id (Eq._oldrec (Eq.refl (id '' S = S)) (image_id S))) (Eq.refl S)))

theorem image_insert_eq {α : Type u} {β : Type v} {f : α → β} {a : α} {s : set α} :
    f '' insert a s = insert (f a) (f '' s) :=
  sorry

theorem image_pair {α : Type u} {β : Type v} (f : α → β) (a : α) (b : α) :
    f '' insert a (singleton b) = insert (f a) (singleton (f b)) :=
  sorry

theorem image_subset_preimage_of_inverse {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (I : function.left_inverse g f) (s : set α) : f '' s ⊆ g ⁻¹' s :=
  sorry

theorem preimage_subset_image_of_inverse {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (I : function.left_inverse g f) (s : set β) : f ⁻¹' s ⊆ g '' s :=
  fun (b : α) (h : b ∈ f ⁻¹' s) => Exists.intro (f b) { left := h, right := I b }

theorem image_eq_preimage_of_inverse {α : Type u} {β : Type v} {f : α → β} {g : β → α}
    (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : image f = preimage g :=
  funext
    fun (s : set α) =>
      subset.antisymm (image_subset_preimage_of_inverse h₁ s)
        (preimage_subset_image_of_inverse h₂ s)

theorem mem_image_iff_of_inverse {α : Type u} {β : Type v} {f : α → β} {g : β → α} {b : β}
    {s : set α} (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
    b ∈ f '' s ↔ g b ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b ∈ f '' s ↔ g b ∈ s)) (image_eq_preimage_of_inverse h₁ h₂)))
    (iff.refl (b ∈ g ⁻¹' s))

theorem image_compl_subset {α : Type u} {β : Type v} {f : α → β} {s : set α}
    (H : function.injective f) : f '' (sᶜ) ⊆ (f '' sᶜ) :=
  sorry

theorem subset_image_compl {α : Type u} {β : Type v} {f : α → β} {s : set α}
    (H : function.surjective f) : f '' sᶜ ⊆ f '' (sᶜ) :=
  sorry

theorem image_compl_eq {α : Type u} {β : Type v} {f : α → β} {s : set α}
    (H : function.bijective f) : f '' (sᶜ) = (f '' sᶜ) :=
  subset.antisymm (image_compl_subset (and.left H)) (subset_image_compl (and.right H))

theorem subset_image_diff {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set α) :
    f '' s \ f '' t ⊆ f '' (s \ t) :=
  sorry

theorem image_diff {α : Type u} {β : Type v} {f : α → β} (hf : function.injective f) (s : set α)
    (t : set α) : f '' (s \ t) = f '' s \ f '' t :=
  sorry

theorem nonempty.image {α : Type u} {β : Type v} (f : α → β) {s : set α} :
    set.nonempty s → set.nonempty (f '' s) :=
  fun (ᾰ : set.nonempty s) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : α) (ᾰ_h : ᾰ_w ∈ s) =>
        idRhs (∃ (x : β), x ∈ f '' s) (Exists.intro (f ᾰ_w) (mem_image_of_mem f ᾰ_h))

theorem nonempty.of_image {α : Type u} {β : Type v} {f : α → β} {s : set α} :
    set.nonempty (f '' s) → set.nonempty s :=
  sorry

@[simp] theorem nonempty_image_iff {α : Type u} {β : Type v} {f : α → β} {s : set α} :
    set.nonempty (f '' s) ↔ set.nonempty s :=
  { mp := nonempty.of_image, mpr := fun (h : set.nonempty s) => nonempty.image f h }

protected instance image.nonempty {α : Type u} {β : Type v} (f : α → β) (s : set α) [Nonempty ↥s] :
    Nonempty ↥(f '' s) :=
  nonempty.to_subtype (nonempty.image f nonempty_of_nonempty_subtype)

/-- image and preimage are a Galois connection -/
@[simp] theorem image_subset_iff {α : Type u} {β : Type v} {s : set α} {t : set β} {f : α → β} :
    f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  ball_image_iff

theorem image_preimage_subset {α : Type u} {β : Type v} (f : α → β) (s : set β) :
    f '' (f ⁻¹' s) ⊆ s :=
  iff.mpr image_subset_iff (subset.refl (f ⁻¹' s))

theorem subset_preimage_image {α : Type u} {β : Type v} (f : α → β) (s : set α) :
    s ⊆ f ⁻¹' (f '' s) :=
  fun (x : α) => mem_image_of_mem f

theorem preimage_image_eq {α : Type u} {β : Type v} {f : α → β} (s : set α)
    (h : function.injective f) : f ⁻¹' (f '' s) = s :=
  sorry

theorem image_preimage_eq {α : Type u} {β : Type v} {f : α → β} (s : set β)
    (h : function.surjective f) : f '' (f ⁻¹' s) = s :=
  sorry

theorem preimage_eq_preimage {α : Type u} {β : Type v} {s : set α} {t : set α} {f : β → α}
    (hf : function.surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  sorry

theorem image_inter_preimage {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β) :
    f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
  sorry

theorem image_preimage_inter {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β) :
    f '' (f ⁻¹' t ∩ s) = t ∩ f '' s :=
  sorry

@[simp] theorem image_inter_nonempty_iff {α : Type u} {β : Type v} {f : α → β} {s : set α}
    {t : set β} : set.nonempty (f '' s ∩ t) ↔ set.nonempty (s ∩ f ⁻¹' t) :=
  sorry

theorem image_diff_preimage {α : Type u} {β : Type v} {f : α → β} {s : set α} {t : set β} :
    f '' (s \ f ⁻¹' t) = f '' s \ t :=
  sorry

theorem compl_image {α : Type u} : image compl = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {α : Type u} {p : set α → Prop} :
    (compl '' set_of fun (s : set α) => p s) = set_of fun (s : set α) => p (sᶜ) :=
  congr_fun compl_image p

theorem inter_preimage_subset {α : Type u} {β : Type v} (s : set α) (t : set β) (f : α → β) :
    s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) :=
  fun (x : α) (h : x ∈ s ∩ f ⁻¹' t) =>
    { left := mem_image_of_mem f (and.left h), right := and.right h }

theorem union_preimage_subset {α : Type u} {β : Type v} (s : set α) (t : set β) (f : α → β) :
    s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) :=
  fun (x : α) (h : x ∈ s ∪ f ⁻¹' t) =>
    or.elim h (fun (l : x ∈ s) => Or.inl (mem_image_of_mem f l)) fun (r : x ∈ f ⁻¹' t) => Or.inr r

theorem subset_image_union {α : Type u} {β : Type v} (f : α → β) (s : set α) (t : set β) :
    f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
  iff.mpr image_subset_iff (union_preimage_subset s t f)

theorem preimage_subset_iff {α : Type u} {β : Type v} {A : set α} {B : set β} {f : α → β} :
    f ⁻¹' B ⊆ A ↔ ∀ (a : α), f a ∈ B → a ∈ A :=
  iff.rfl

theorem image_eq_image {α : Type u} {β : Type v} {s : set α} {t : set α} {f : α → β}
    (hf : function.injective f) : f '' s = f '' t ↔ s = t :=
  sorry

theorem image_subset_image_iff {α : Type u} {β : Type v} {s : set α} {t : set α} {f : α → β}
    (hf : function.injective f) : f '' s ⊆ f '' t ↔ s ⊆ t :=
  sorry

theorem prod_quotient_preimage_eq_image {α : Type u} {β : Type v} [s : setoid α]
    (g : quotient s → β) {h : α → β} (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
    (set_of fun (x : quotient s × quotient s) => (g (prod.fst x), g (prod.snd x)) ∈ r) =
        (fun (a : α × α) => (quotient.mk (prod.fst a), quotient.mk (prod.snd a))) ''
          ((fun (a : α × α) => (h (prod.fst a), h (prod.snd a))) ⁻¹' r) :=
  sorry

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def image_factorization {α : Type u} {β : Type v} (f : α → β) (s : set α) : ↥s → ↥(f '' s) :=
  fun (p : ↥s) => { val := f (subtype.val p), property := sorry }

theorem image_factorization_eq {α : Type u} {β : Type v} {f : α → β} {s : set α} :
    subtype.val ∘ image_factorization f s = f ∘ subtype.val :=
  funext fun (p : ↥s) => rfl

theorem surjective_onto_image {α : Type u} {β : Type v} {f : α → β} {s : set α} :
    function.surjective (image_factorization f s) :=
  sorry

/-! ### Subsingleton -/

/-- A set `s` is a `subsingleton`, if it has at most one element. -/
protected def subsingleton {α : Type u} (s : set α) := ∀ {x : α}, x ∈ s → ∀ {y : α}, y ∈ s → x = y

theorem subsingleton.mono {α : Type u} {s : set α} {t : set α} (ht : set.subsingleton t)
    (hst : s ⊆ t) : set.subsingleton s :=
  fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) => ht (hst hx) (hst hy)

theorem subsingleton.image {α : Type u} {β : Type v} {s : set α} (hs : set.subsingleton s)
    (f : α → β) : set.subsingleton (f '' s) :=
  sorry

theorem subsingleton.eq_singleton_of_mem {α : Type u} {s : set α} (hs : set.subsingleton s) {x : α}
    (hx : x ∈ s) : s = singleton x :=
  sorry

theorem subsingleton_empty {α : Type u} : set.subsingleton ∅ := fun (x : α) => false.elim

theorem subsingleton_singleton {α : Type u} {a : α} : set.subsingleton (singleton a) :=
  fun (x : α) (hx : x ∈ singleton a) (y : α) (hy : y ∈ singleton a) =>
    Eq.symm (eq_of_mem_singleton hx) ▸ Eq.symm (eq_of_mem_singleton hy) ▸ rfl

theorem subsingleton.eq_empty_or_singleton {α : Type u} {s : set α} (hs : set.subsingleton s) :
    s = ∅ ∨ ∃ (x : α), s = singleton x :=
  sorry

theorem subsingleton.induction_on {α : Type u} {s : set α} {p : set α → Prop}
    (hs : set.subsingleton s) (he : p ∅) (h₁ : ∀ (x : α), p (singleton x)) : p s :=
  sorry

theorem subsingleton_univ {α : Type u} [subsingleton α] : set.subsingleton univ :=
  fun (x : α) (hx : x ∈ univ) (y : α) (hy : y ∈ univ) => subsingleton.elim x y

/-- `s`, coerced to a type, is a subsingleton type if and only if `s`
is a subsingleton set. -/
@[simp] theorem subsingleton_coe {α : Type u} (s : set α) : subsingleton ↥s ↔ set.subsingleton s :=
  sorry

/-- `s` is a subsingleton, if its image of an injective function is. -/
theorem subsingleton_of_image {α : Type u_1} {β : Type u_2} {f : α → β} (hf : function.injective f)
    (s : set α) (hs : subsingleton ↥(f '' s)) : subsingleton ↥s :=
  sorry

theorem univ_eq_true_false : univ = insert True (singleton False) := sorry

/-! ### Lemmas about range of a function. -/

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range {α : Type u} {ι : Sort x} (f : ι → α) : set α := set_of fun (x : α) => ∃ (y : ι), f y = x

@[simp] theorem mem_range {α : Type u} {ι : Sort x} {f : ι → α} {x : α} :
    x ∈ range f ↔ ∃ (y : ι), f y = x :=
  iff.rfl

@[simp] theorem mem_range_self {α : Type u} {ι : Sort x} {f : ι → α} (i : ι) : f i ∈ range f :=
  Exists.intro i rfl

theorem forall_range_iff {α : Type u} {ι : Sort x} {f : ι → α} {p : α → Prop} :
    (∀ (a : α), a ∈ range f → p a) ↔ ∀ (i : ι), p (f i) :=
  sorry

theorem exists_range_iff {α : Type u} {ι : Sort x} {f : ι → α} {p : α → Prop} :
    (∃ (a : α), ∃ (H : a ∈ range f), p a) ↔ ∃ (i : ι), p (f i) :=
  sorry

theorem exists_range_iff' {α : Type u} {ι : Sort x} {f : ι → α} {p : α → Prop} :
    (∃ (a : α), a ∈ range f ∧ p a) ↔ ∃ (i : ι), p (f i) :=
  sorry

theorem range_iff_surjective {α : Type u} {ι : Sort x} {f : ι → α} :
    range f = univ ↔ function.surjective f :=
  eq_univ_iff_forall

theorem Mathlib.function.surjective.range_eq {α : Type u} {ι : Sort x} {f : ι → α} :
    function.surjective f → range f = univ :=
  iff.mpr range_iff_surjective

@[simp] theorem range_id {α : Type u} : range id = univ :=
  iff.mpr range_iff_surjective function.surjective_id

theorem is_compl_range_inl_range_inr {α : Type u} {β : Type v} :
    is_compl (range sum.inl) (range sum.inr) :=
  sorry

@[simp] theorem range_inl_union_range_inr {α : Type u} {β : Type v} :
    range sum.inl ∪ range sum.inr = univ :=
  is_compl.sup_eq_top is_compl_range_inl_range_inr

@[simp] theorem range_inl_inter_range_inr {α : Type u} {β : Type v} :
    range sum.inl ∩ range sum.inr = ∅ :=
  is_compl.inf_eq_bot is_compl_range_inl_range_inr

@[simp] theorem range_inr_union_range_inl {α : Type u} {β : Type v} :
    range sum.inr ∪ range sum.inl = univ :=
  is_compl.sup_eq_top (is_compl.symm is_compl_range_inl_range_inr)

@[simp] theorem range_inr_inter_range_inl {α : Type u} {β : Type v} :
    range sum.inr ∩ range sum.inl = ∅ :=
  is_compl.inf_eq_bot (is_compl.symm is_compl_range_inl_range_inr)

@[simp] theorem preimage_inl_range_inr {α : Type u} {β : Type v} : sum.inl ⁻¹' range sum.inr = ∅ :=
  sorry

@[simp] theorem preimage_inr_range_inl {α : Type u} {β : Type v} : sum.inr ⁻¹' range sum.inl = ∅ :=
  sorry

@[simp] theorem range_quot_mk {α : Type u} (r : α → α → Prop) : range (Quot.mk r) = univ :=
  function.surjective.range_eq (surjective_quot_mk r)

@[simp] theorem image_univ {β : Type v} {ι : Type u_1} {f : ι → β} : f '' univ = range f := sorry

theorem image_subset_range {β : Type v} {ι : Type u_1} (f : ι → β) (s : set ι) : f '' s ⊆ range f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f '' s ⊆ range f)) (Eq.symm image_univ)))
    (image_subset f (subset_univ s))

theorem range_comp {α : Type u} {β : Type v} {ι : Sort x} (g : α → β) (f : ι → α) :
    range (g ∘ f) = g '' range f :=
  subset.antisymm (iff.mpr forall_range_iff fun (i : ι) => mem_image_of_mem g (mem_range_self i))
    (iff.mpr ball_image_iff (iff.mpr forall_range_iff mem_range_self))

theorem range_subset_iff {α : Type u} {ι : Sort x} {f : ι → α} {s : set α} :
    range f ⊆ s ↔ ∀ (y : ι), f y ∈ s :=
  forall_range_iff

theorem range_comp_subset_range {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) :
    range (g ∘ f) ⊆ range g :=
  eq.mpr (id (Eq._oldrec (Eq.refl (range (g ∘ f) ⊆ range g)) (range_comp g f)))
    (image_subset_range g (range f))

theorem range_nonempty_iff_nonempty {α : Type u} {ι : Sort x} {f : ι → α} :
    set.nonempty (range f) ↔ Nonempty ι :=
  sorry

theorem range_nonempty {α : Type u} {ι : Sort x} [h : Nonempty ι] (f : ι → α) :
    set.nonempty (range f) :=
  iff.mpr range_nonempty_iff_nonempty h

@[simp] theorem range_eq_empty {α : Type u} {ι : Sort x} {f : ι → α} : range f = ∅ ↔ ¬Nonempty ι :=
  iff.trans (iff.symm not_nonempty_iff_eq_empty) (not_congr range_nonempty_iff_nonempty)

protected instance range.nonempty {α : Type u} {ι : Sort x} [Nonempty ι] (f : ι → α) :
    Nonempty ↥(range f) :=
  nonempty.to_subtype (range_nonempty f)

@[simp] theorem image_union_image_compl_eq_range {α : Type u} {β : Type v} {s : set α} (f : α → β) :
    f '' s ∪ f '' (sᶜ) = range f :=
  sorry

theorem image_preimage_eq_inter_range {α : Type u} {β : Type v} {f : α → β} {t : set β} :
    f '' (f ⁻¹' t) = t ∩ range f :=
  sorry

theorem image_preimage_eq_of_subset {α : Type u} {β : Type v} {f : α → β} {s : set β}
    (hs : s ⊆ range f) : f '' (f ⁻¹' s) = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f '' (f ⁻¹' s) = s)) image_preimage_eq_inter_range))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ range f = s)) (inter_eq_self_of_subset_left hs)))
      (Eq.refl s))

theorem image_preimage_eq_iff {α : Type u} {β : Type v} {f : α → β} {s : set β} :
    f '' (f ⁻¹' s) = s ↔ s ⊆ range f :=
  sorry

theorem preimage_subset_preimage_iff {α : Type u} {β : Type v} {s : set α} {t : set α} {f : β → α}
    (hs : s ⊆ range f) : f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
  sorry

theorem preimage_eq_preimage' {α : Type u} {β : Type v} {s : set α} {t : set α} {f : β → α}
    (hs : s ⊆ range f) (ht : t ⊆ range f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  sorry

@[simp] theorem preimage_inter_range {α : Type u} {β : Type v} {f : α → β} {s : set β} :
    f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  ext fun (x : α) => and_iff_left (Exists.intro x rfl)

@[simp] theorem preimage_range_inter {α : Type u} {β : Type v} {f : α → β} {s : set β} :
    f ⁻¹' (range f ∩ s) = f ⁻¹' s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f ⁻¹' (range f ∩ s) = f ⁻¹' s)) (inter_comm (range f) s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (f ⁻¹' (s ∩ range f) = f ⁻¹' s)) preimage_inter_range))
      (Eq.refl (f ⁻¹' s)))

theorem preimage_image_preimage {α : Type u} {β : Type v} {f : α → β} {s : set β} :
    f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s)) image_preimage_eq_inter_range))
    (eq.mpr (id (Eq._oldrec (Eq.refl (f ⁻¹' (s ∩ range f) = f ⁻¹' s)) preimage_inter_range))
      (Eq.refl (f ⁻¹' s)))

@[simp] theorem quot_mk_range_eq {α : Type u} [setoid α] :
    (range fun (x : α) => quotient.mk x) = univ :=
  iff.mpr range_iff_surjective quot.exists_rep

theorem range_const_subset {α : Type u} {ι : Sort x} {c : α} :
    (range fun (x : ι) => c) ⊆ singleton c :=
  iff.mpr range_subset_iff fun (x : ι) => rfl

@[simp] theorem range_const {α : Type u} {ι : Sort x} [Nonempty ι] {c : α} :
    (range fun (x : ι) => c) = singleton c :=
  sorry

theorem diagonal_eq_range {α : Type u_1} : diagonal α = range fun (x : α) => (x, x) := sorry

theorem preimage_singleton_nonempty {α : Type u} {β : Type v} {f : α → β} {y : β} :
    set.nonempty (f ⁻¹' singleton y) ↔ y ∈ range f :=
  iff.rfl

theorem preimage_singleton_eq_empty {α : Type u} {β : Type v} {f : α → β} {y : β} :
    f ⁻¹' singleton y = ∅ ↔ ¬y ∈ range f :=
  iff.trans (iff.symm not_nonempty_iff_eq_empty) (not_congr preimage_singleton_nonempty)

theorem range_subset_singleton {α : Type u} {ι : Sort x} {f : ι → α} {x : α} :
    range f ⊆ singleton x ↔ f = function.const ι x :=
  sorry

theorem image_compl_preimage {α : Type u} {β : Type v} {f : α → β} {s : set β} :
    f '' (f ⁻¹' sᶜ) = range f \ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f '' (f ⁻¹' sᶜ) = range f \ s)) (compl_eq_univ_diff (f ⁻¹' s))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (f '' (univ \ f ⁻¹' s) = range f \ s)) image_diff_preimage))
      (eq.mpr (id (Eq._oldrec (Eq.refl (f '' univ \ s = range f \ s)) image_univ))
        (Eq.refl (range f \ s))))

@[simp] theorem range_sigma_mk {α : Type u} {β : α → Type u_1} (a : α) :
    range (sigma.mk a) = sigma.fst ⁻¹' singleton a :=
  sorry

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def range_factorization {β : Type v} {ι : Sort x} (f : ι → β) : ι → ↥(range f) :=
  fun (i : ι) => { val := f i, property := mem_range_self i }

theorem range_factorization_eq {β : Type v} {ι : Sort x} {f : ι → β} :
    subtype.val ∘ range_factorization f = f :=
  funext fun (i : ι) => rfl

theorem surjective_onto_range {α : Type u} {ι : Sort x} {f : ι → α} :
    function.surjective (range_factorization f) :=
  sorry

theorem image_eq_range {α : Type u} {β : Type v} (f : α → β) (s : set α) :
    f '' s = range fun (x : ↥s) => f ↑x :=
  sorry

@[simp] theorem sum.elim_range {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → γ)
    (g : β → γ) : range (sum.elim f g) = range f ∪ range g :=
  sorry

theorem range_ite_subset' {α : Type u} {β : Type v} {p : Prop} [Decidable p] {f : α → β}
    {g : α → β} : range (ite p f g) ⊆ range f ∪ range g :=
  sorry

theorem range_ite_subset {α : Type u} {β : Type v} {p : α → Prop} [decidable_pred p] {f : α → β}
    {g : α → β} : (range fun (x : α) => ite (p x) (f x) (g x)) ⊆ range f ∪ range g :=
  sorry

@[simp] theorem preimage_range {α : Type u} {β : Type v} (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
theorem range_unique {α : Type u} {ι : Sort x} {f : ι → α} [h : unique ι] :
    range f = singleton (f Inhabited.default) :=
  sorry

theorem range_diff_image_subset {α : Type u} {β : Type v} (f : α → β) (s : set α) :
    range f \ f '' s ⊆ f '' (sᶜ) :=
  sorry

theorem range_diff_image {α : Type u} {β : Type v} {f : α → β} (H : function.injective f)
    (s : set α) : range f \ f '' s = f '' (sᶜ) :=
  sorry

/-- The set `s` is pairwise `r` if `r x y` for all *distinct* `x y ∈ s`. -/
def pairwise_on {α : Type u} (s : set α) (r : α → α → Prop) :=
  ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x ≠ y → r x y

theorem pairwise_on.mono {α : Type u} {s : set α} {t : set α} {r : α → α → Prop} (h : t ⊆ s)
    (hp : pairwise_on s r) : pairwise_on t r :=
  fun (x : α) (xt : x ∈ t) (y : α) (yt : y ∈ t) => hp x (h xt) y (h yt)

theorem pairwise_on.mono' {α : Type u} {s : set α} {r : α → α → Prop} {r' : α → α → Prop}
    (H : ∀ (a b : α), r a b → r' a b) (hp : pairwise_on s r) : pairwise_on s r' :=
  fun (x : α) (xs : x ∈ s) (y : α) (ys : y ∈ s) (h : x ≠ y) => H x y (hp x xs y ys h)

/-- If and only if `f` takes pairwise equal values on `s`, there is
some value it takes everywhere on `s`. -/
theorem pairwise_on_eq_iff_exists_eq {α : Type u} {β : Type v} [Nonempty β] (s : set α)
    (f : α → β) :
    (pairwise_on s fun (x y : α) => f x = f y) ↔ ∃ (z : β), ∀ (x : α), x ∈ s → f x = z :=
  sorry

end set


namespace function


theorem surjective.preimage_injective {α : Type u_2} {β : Type u_3} {f : α → β}
    (hf : surjective f) : injective (set.preimage f) :=
  fun (s t : set β) => iff.mp (set.preimage_eq_preimage hf)

theorem injective.preimage_image {α : Type u_2} {β : Type u_3} {f : α → β} (hf : injective f)
    (s : set α) : f ⁻¹' (f '' s) = s :=
  set.preimage_image_eq s hf

theorem injective.preimage_surjective {α : Type u_2} {β : Type u_3} {f : α → β} (hf : injective f) :
    surjective (set.preimage f) :=
  sorry

theorem surjective.image_preimage {α : Type u_2} {β : Type u_3} {f : α → β} (hf : surjective f)
    (s : set β) : f '' (f ⁻¹' s) = s :=
  set.image_preimage_eq s hf

theorem surjective.image_surjective {α : Type u_2} {β : Type u_3} {f : α → β} (hf : surjective f) :
    surjective (set.image f) :=
  sorry

theorem injective.image_injective {α : Type u_2} {β : Type u_3} {f : α → β} (hf : injective f) :
    injective (set.image f) :=
  sorry

theorem surjective.preimage_subset_preimage_iff {α : Type u_2} {β : Type u_3} {f : α → β}
    {s : set β} {t : set β} (hf : surjective f) : f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
  set.preimage_subset_preimage_iff
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ⊆ set.range f)) (surjective.range_eq hf)))
      (set.subset_univ s))

theorem surjective.range_comp {ι : Sort u_1} {α : Type u_2} {ι' : Sort u_3} {f : ι → ι'}
    (hf : surjective f) (g : ι' → α) : set.range (g ∘ f) = set.range g :=
  set.ext fun (y : α) => iff.symm (surjective.exists hf)

theorem injective.nonempty_apply_iff {α : Type u_2} {β : Type u_3} {f : set α → set β}
    (hf : injective f) (h2 : f ∅ = ∅) {s : set α} : set.nonempty (f s) ↔ set.nonempty s :=
  sorry

end function


/-! ### Image and preimage on subtypes -/

namespace subtype


theorem coe_image {α : Type u_1} {p : α → Prop} {s : set (Subtype p)} :
    coe '' s = set_of fun (x : α) => ∃ (h : p x), { val := x, property := h } ∈ s :=
  sorry

theorem range_coe {α : Type u_1} {s : set α} : set.range coe = s := sorry

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {α : Type u_1} {s : set α} : set.range val = s := range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp] theorem range_coe_subtype {α : Type u_1} {p : α → Prop} :
    set.range coe = set_of fun (x : α) => p x :=
  range_coe

@[simp] theorem coe_preimage_self {α : Type u_1} (s : set α) : coe ⁻¹' s = set.univ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe ⁻¹' s = set.univ)) (Eq.symm (set.preimage_range coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe ⁻¹' s = coe ⁻¹' set.range coe)) range_coe))
      (Eq.refl (coe ⁻¹' s)))

theorem range_val_subtype {α : Type u_1} {p : α → Prop} :
    set.range val = set_of fun (x : α) => p x :=
  range_coe

theorem coe_image_subset {α : Type u_1} (s : set α) (t : set ↥s) : coe '' t ⊆ s := sorry

theorem coe_image_univ {α : Type u_1} (s : set α) : coe '' set.univ = s :=
  Eq.trans set.image_univ range_coe

@[simp] theorem image_preimage_coe {α : Type u_1} (s : set α) (t : set α) :
    coe '' (coe ⁻¹' t) = t ∩ s :=
  Eq.trans set.image_preimage_eq_inter_range (congr_arg (has_inter.inter t) range_coe)

theorem image_preimage_val {α : Type u_1} (s : set α) (t : set α) : val '' (val ⁻¹' t) = t ∩ s :=
  image_preimage_coe s t

theorem preimage_coe_eq_preimage_coe_iff {α : Type u_1} {s : set α} {t : set α} {u : set α} :
    coe ⁻¹' t = coe ⁻¹' u ↔ t ∩ s = u ∩ s :=
  sorry

theorem preimage_val_eq_preimage_val_iff {α : Type u_1} (s : set α) (t : set α) (u : set α) :
    val ⁻¹' t = val ⁻¹' u ↔ t ∩ s = u ∩ s :=
  preimage_coe_eq_preimage_coe_iff

theorem exists_set_subtype {α : Type u_1} {t : set α} (p : set α → Prop) :
    (∃ (s : set ↥t), p (coe '' s)) ↔ ∃ (s : set α), s ⊆ t ∧ p s :=
  sorry

theorem preimage_coe_nonempty {α : Type u_1} {s : set α} {t : set α} :
    set.nonempty (coe ⁻¹' t) ↔ set.nonempty (s ∩ t) :=
  sorry

theorem preimage_coe_eq_empty {α : Type u_1} {s : set α} {t : set α} : coe ⁻¹' t = ∅ ↔ s ∩ t = ∅ :=
  sorry

@[simp] theorem preimage_coe_compl {α : Type u_1} (s : set α) : coe ⁻¹' (sᶜ) = ∅ :=
  iff.mpr preimage_coe_eq_empty (set.inter_compl_self s)

@[simp] theorem preimage_coe_compl' {α : Type u_1} (s : set α) : coe ⁻¹' s = ∅ :=
  iff.mpr preimage_coe_eq_empty (set.compl_inter_self s)

end subtype


namespace set


/-! ### Lemmas about cartesian product of sets -/

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def prod {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) : set (α × β) :=
  set_of fun (p : α × β) => prod.fst p ∈ s ∧ prod.snd p ∈ t

theorem prod_eq {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) :
    set.prod s t = prod.fst ⁻¹' s ∩ prod.snd ⁻¹' t :=
  rfl

theorem mem_prod_eq {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {p : α × β} :
    p ∈ set.prod s t = (prod.fst p ∈ s ∧ prod.snd p ∈ t) :=
  rfl

@[simp] theorem mem_prod {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {p : α × β} :
    p ∈ set.prod s t ↔ prod.fst p ∈ s ∧ prod.snd p ∈ t :=
  iff.rfl

@[simp] theorem prod_mk_mem_set_prod_eq {α : Type u_1} {β : Type u_2} {s : set α} {t : set β}
    {a : α} {b : β} : (a, b) ∈ set.prod s t = (a ∈ s ∧ b ∈ t) :=
  rfl

theorem mk_mem_prod {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {a : α} {b : β}
    (a_in : a ∈ s) (b_in : b ∈ t) : (a, b) ∈ set.prod s t :=
  { left := a_in, right := b_in }

theorem prod_mono {α : Type u_1} {β : Type u_2} {s₁ : set α} {s₂ : set α} {t₁ : set β} {t₂ : set β}
    (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : set.prod s₁ t₁ ⊆ set.prod s₂ t₂ :=
  sorry

theorem prod_subset_iff {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {P : set (α × β)} :
    set.prod s t ⊆ P ↔ ∀ (x : α), x ∈ s → ∀ (y : β), y ∈ t → (x, y) ∈ P :=
  sorry

theorem forall_prod_set {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {p : α × β → Prop} :
    (∀ (x : α × β), x ∈ set.prod s t → p x) ↔ ∀ (x : α), x ∈ s → ∀ (y : β), y ∈ t → p (x, y) :=
  prod_subset_iff

theorem exists_prod_set {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {p : α × β → Prop} :
    (∃ (x : α × β), ∃ (H : x ∈ set.prod s t), p x) ↔
        ∃ (x : α), ∃ (H : x ∈ s), ∃ (y : β), ∃ (H : y ∈ t), p (x, y) :=
  sorry

@[simp] theorem prod_empty {α : Type u_1} {β : Type u_2} {s : set α} : set.prod s ∅ = ∅ := sorry

@[simp] theorem empty_prod {α : Type u_1} {β : Type u_2} {t : set β} : set.prod ∅ t = ∅ := sorry

@[simp] theorem univ_prod_univ {α : Type u_1} {β : Type u_2} : set.prod univ univ = univ := sorry

theorem univ_prod {α : Type u_1} {β : Type u_2} {t : set β} : set.prod univ t = prod.snd ⁻¹' t :=
  sorry

theorem prod_univ {α : Type u_1} {β : Type u_2} {s : set α} : set.prod s univ = prod.fst ⁻¹' s :=
  sorry

@[simp] theorem singleton_prod {α : Type u_1} {β : Type u_2} {t : set β} {a : α} :
    set.prod (singleton a) t = Prod.mk a '' t :=
  sorry

@[simp] theorem prod_singleton {α : Type u_1} {β : Type u_2} {s : set α} {b : β} :
    set.prod s (singleton b) = (fun (a : α) => (a, b)) '' s :=
  sorry

theorem singleton_prod_singleton {α : Type u_1} {β : Type u_2} {a : α} {b : β} :
    set.prod (singleton a) (singleton b) = singleton (a, b) :=
  sorry

@[simp] theorem union_prod {α : Type u_1} {β : Type u_2} {s₁ : set α} {s₂ : set α} {t : set β} :
    set.prod (s₁ ∪ s₂) t = set.prod s₁ t ∪ set.prod s₂ t :=
  sorry

@[simp] theorem prod_union {α : Type u_1} {β : Type u_2} {s : set α} {t₁ : set β} {t₂ : set β} :
    set.prod s (t₁ ∪ t₂) = set.prod s t₁ ∪ set.prod s t₂ :=
  sorry

theorem prod_inter_prod {α : Type u_1} {β : Type u_2} {s₁ : set α} {s₂ : set α} {t₁ : set β}
    {t₂ : set β} : set.prod s₁ t₁ ∩ set.prod s₂ t₂ = set.prod (s₁ ∩ s₂) (t₁ ∩ t₂) :=
  sorry

theorem insert_prod {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {a : α} :
    set.prod (insert a s) t = Prod.mk a '' t ∪ set.prod s t :=
  sorry

theorem prod_insert {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {b : β} :
    set.prod s (insert b t) = (fun (a : α) => (a, b)) '' s ∪ set.prod s t :=
  sorry

theorem prod_preimage_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : set α}
    {t : set β} {f : γ → α} {g : δ → β} :
    set.prod (f ⁻¹' s) (g ⁻¹' t) =
        (fun (p : γ × δ) => (f (prod.fst p), g (prod.snd p))) ⁻¹' set.prod s t :=
  rfl

theorem prod_preimage_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : set α} {t : set β}
    {f : γ → α} :
    set.prod (f ⁻¹' s) t = (fun (p : γ × β) => (f (prod.fst p), prod.snd p)) ⁻¹' set.prod s t :=
  rfl

theorem prod_preimage_right {α : Type u_1} {β : Type u_2} {δ : Type u_4} {s : set α} {t : set β}
    {g : δ → β} :
    set.prod s (g ⁻¹' t) = (fun (p : α × δ) => (prod.fst p, g (prod.snd p))) ⁻¹' set.prod s t :=
  rfl

theorem mk_preimage_prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : set α} {t : set β}
    (f : γ → α) (g : γ → β) : (fun (x : γ) => (f x, g x)) ⁻¹' set.prod s t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

@[simp] theorem mk_preimage_prod_left {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {y : β}
    (h : y ∈ t) : (fun (x : α) => (x, y)) ⁻¹' set.prod s t = s :=
  sorry

@[simp] theorem mk_preimage_prod_right {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {x : α}
    (h : x ∈ s) : Prod.mk x ⁻¹' set.prod s t = t :=
  sorry

@[simp] theorem mk_preimage_prod_left_eq_empty {α : Type u_1} {β : Type u_2} {s : set α} {t : set β}
    {y : β} (hy : ¬y ∈ t) : (fun (x : α) => (x, y)) ⁻¹' set.prod s t = ∅ :=
  sorry

@[simp] theorem mk_preimage_prod_right_eq_empty {α : Type u_1} {β : Type u_2} {s : set α}
    {t : set β} {x : α} (hx : ¬x ∈ s) : Prod.mk x ⁻¹' set.prod s t = ∅ :=
  sorry

theorem mk_preimage_prod_left_eq_if {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {y : β}
    [decidable_pred fun (_x : β) => _x ∈ t] :
    (fun (x : α) => (x, y)) ⁻¹' set.prod s t = ite (y ∈ t) s ∅ :=
  sorry

theorem mk_preimage_prod_right_eq_if {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} {x : α}
    [decidable_pred fun (_x : α) => _x ∈ s] : Prod.mk x ⁻¹' set.prod s t = ite (x ∈ s) t ∅ :=
  sorry

theorem mk_preimage_prod_left_fn_eq_if {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : set α}
    {t : set β} {y : β} [decidable_pred fun (_x : β) => _x ∈ t] (f : γ → α) :
    (fun (x : γ) => (f x, y)) ⁻¹' set.prod s t = ite (y ∈ t) (f ⁻¹' s) ∅ :=
  sorry

theorem mk_preimage_prod_right_fn_eq_if {α : Type u_1} {β : Type u_2} {δ : Type u_4} {s : set α}
    {t : set β} {x : α} [decidable_pred fun (_x : α) => _x ∈ s] (g : δ → β) :
    (fun (y : δ) => (x, g y)) ⁻¹' set.prod s t = ite (x ∈ s) (g ⁻¹' t) ∅ :=
  sorry

theorem image_swap_eq_preimage_swap {α : Type u_1} {β : Type u_2} :
    image prod.swap = preimage prod.swap :=
  image_eq_preimage_of_inverse prod.swap_left_inverse prod.swap_right_inverse

theorem preimage_swap_prod {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    prod.swap ⁻¹' set.prod t s = set.prod s t :=
  sorry

theorem image_swap_prod {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    prod.swap '' set.prod t s = set.prod s t :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (prod.swap '' set.prod t s = set.prod s t)) image_swap_eq_preimage_swap))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (prod.swap ⁻¹' set.prod t s = set.prod s t)) preimage_swap_prod))
      (Eq.refl (set.prod s t)))

theorem prod_image_image_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : set α}
    {t : set β} {m₁ : α → γ} {m₂ : β → δ} :
    set.prod (m₁ '' s) (m₂ '' t) =
        (fun (p : α × β) => (m₁ (prod.fst p), m₂ (prod.snd p))) '' set.prod s t :=
  sorry

theorem prod_range_range_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {m₁ : α → γ}
    {m₂ : β → δ} :
    set.prod (range m₁) (range m₂) = range fun (p : α × β) => (m₁ (prod.fst p), m₂ (prod.snd p)) :=
  sorry

theorem prod_range_univ_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {m₁ : α → γ} :
    set.prod (range m₁) univ = range fun (p : α × β) => (m₁ (prod.fst p), prod.snd p) :=
  sorry

theorem prod_univ_range_eq {α : Type u_1} {β : Type u_2} {δ : Type u_3} {m₂ : β → δ} :
    set.prod univ (range m₂) = range fun (p : α × β) => (prod.fst p, m₂ (prod.snd p)) :=
  sorry

theorem nonempty.prod {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    set.nonempty s → set.nonempty t → set.nonempty (set.prod s t) :=
  sorry

theorem nonempty.fst {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    set.nonempty (set.prod s t) → set.nonempty s :=
  sorry

theorem nonempty.snd {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    set.nonempty (set.prod s t) → set.nonempty t :=
  sorry

theorem prod_nonempty_iff {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    set.nonempty (set.prod s t) ↔ set.nonempty s ∧ set.nonempty t :=
  { mp :=
      fun (h : set.nonempty (set.prod s t)) => { left := nonempty.fst h, right := nonempty.snd h },
    mpr := fun (h : set.nonempty s ∧ set.nonempty t) => nonempty.prod (and.left h) (and.right h) }

theorem prod_eq_empty_iff {α : Type u_1} {β : Type u_2} {s : set α} {t : set β} :
    set.prod s t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  sorry

theorem prod_sub_preimage_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : set α} {t : set β}
    {W : set γ} {f : α × β → γ} :
    set.prod s t ⊆ f ⁻¹' W ↔ ∀ (a : α) (b : β), a ∈ s → b ∈ t → f (a, b) ∈ W :=
  sorry

theorem fst_image_prod_subset {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) :
    prod.fst '' set.prod s t ⊆ s :=
  sorry

theorem prod_subset_preimage_fst {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) :
    set.prod s t ⊆ prod.fst ⁻¹' s :=
  iff.mp image_subset_iff (fst_image_prod_subset s t)

theorem fst_image_prod {α : Type u_1} {β : Type u_2} (s : set β) {t : set α} (ht : set.nonempty t) :
    prod.fst '' set.prod s t = s :=
  sorry

theorem snd_image_prod_subset {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) :
    prod.snd '' set.prod s t ⊆ t :=
  sorry

theorem prod_subset_preimage_snd {α : Type u_1} {β : Type u_2} (s : set α) (t : set β) :
    set.prod s t ⊆ prod.snd ⁻¹' t :=
  iff.mp image_subset_iff (snd_image_prod_subset s t)

theorem snd_image_prod {α : Type u_1} {β : Type u_2} {s : set α} (hs : set.nonempty s) (t : set β) :
    prod.snd '' set.prod s t = t :=
  sorry

/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
theorem prod_subset_prod_iff {α : Type u_1} {β : Type u_2} {s : set α} {s₁ : set α} {t : set β}
    {t₁ : set β} : set.prod s t ⊆ set.prod s₁ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ :=
  sorry

/-! ### Lemmas about set-indexed products of sets -/

/-- Given an index set `i` and a family of sets `s : Π i, set (α i)`, `pi i s`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `π a`
whenever `a ∈ i`. -/
def pi {ι : Type u_1} {α : ι → Type u_2} (s : set ι) (t : (i : ι) → set (α i)) :
    set ((i : ι) → α i) :=
  set_of fun (f : (i : ι) → α i) => ∀ (i : ι), i ∈ s → f i ∈ t i

@[simp] theorem mem_pi {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)}
    {f : (i : ι) → α i} : f ∈ pi s t ↔ ∀ (i : ι), i ∈ s → f i ∈ t i :=
  iff.refl (f ∈ pi s t)

@[simp] theorem mem_univ_pi {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)}
    {f : (i : ι) → α i} : f ∈ pi univ t ↔ ∀ (i : ι), f i ∈ t i :=
  sorry

@[simp] theorem empty_pi {ι : Type u_1} {α : ι → Type u_2} (s : (i : ι) → set (α i)) :
    pi ∅ s = univ :=
  sorry

@[simp] theorem pi_univ {ι : Type u_1} {α : ι → Type u_2} (s : set ι) :
    (pi s fun (i : ι) => univ) = univ :=
  eq_univ_of_forall
    fun (f : (i : ι) → (fun (i : ι) => α i) i) (i : ι) (hi : i ∈ s) => mem_univ (f i)

theorem pi_mono {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t₁ : (i : ι) → set (α i)}
    {t₂ : (i : ι) → set (α i)} (h : ∀ (i : ι), i ∈ s → t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ :=
  fun (x : (i : ι) → α i) (hx : x ∈ pi s t₁) (i : ι) (hi : i ∈ s) => h i hi (hx i hi)

theorem pi_inter_distrib {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)}
    {t₁ : (i : ι) → set (α i)} : (pi s fun (i : ι) => t i ∩ t₁ i) = pi s t ∩ pi s t₁ :=
  sorry

theorem pi_congr {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {s₁ : set ι}
    {t : (i : ι) → set (α i)} {t₁ : (i : ι) → set (α i)} (h : s = s₁)
    (h' : ∀ (i : ι), i ∈ s → t i = t₁ i) : pi s t = pi s₁ t₁ :=
  sorry

theorem pi_eq_empty {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)} {i : ι}
    (hs : i ∈ s) (ht : t i = ∅) : pi s t = ∅ :=
  sorry

theorem univ_pi_eq_empty {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)} {i : ι}
    (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht

theorem pi_nonempty_iff {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)} :
    set.nonempty (pi s t) ↔ ∀ (i : ι), ∃ (x : α i), i ∈ s → x ∈ t i :=
  sorry

theorem univ_pi_nonempty_iff {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)} :
    set.nonempty (pi univ t) ↔ ∀ (i : ι), set.nonempty (t i) :=
  sorry

theorem pi_eq_empty_iff {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)} :
    pi s t = ∅ ↔ ∃ (i : ι), (α i → False) ∨ i ∈ s ∧ t i = ∅ :=
  sorry

theorem univ_pi_eq_empty_iff {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)} :
    pi univ t = ∅ ↔ ∃ (i : ι), t i = ∅ :=
  sorry

@[simp] theorem insert_pi {ι : Type u_1} {α : ι → Type u_2} (i : ι) (s : set ι)
    (t : (i : ι) → set (α i)) : pi (insert i s) t = function.eval i ⁻¹' t i ∩ pi s t :=
  sorry

@[simp] theorem singleton_pi {ι : Type u_1} {α : ι → Type u_2} (i : ι) (t : (i : ι) → set (α i)) :
    pi (singleton i) t = function.eval i ⁻¹' t i :=
  sorry

theorem singleton_pi' {ι : Type u_1} {α : ι → Type u_2} (i : ι) (t : (i : ι) → set (α i)) :
    pi (singleton i) t = set_of fun (x : (i : ι) → α i) => x i ∈ t i :=
  singleton_pi i t

theorem pi_if {ι : Type u_1} {α : ι → Type u_2} {p : ι → Prop} [h : decidable_pred p] (s : set ι)
    (t₁ : (i : ι) → set (α i)) (t₂ : (i : ι) → set (α i)) :
    (pi s fun (i : ι) => ite (p i) (t₁ i) (t₂ i)) =
        pi (has_sep.sep (fun (i : ι) => p i) s) t₁ ∩ pi (has_sep.sep (fun (i : ι) => ¬p i) s) t₂ :=
  sorry

theorem union_pi {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {s₁ : set ι}
    {t : (i : ι) → set (α i)} : pi (s ∪ s₁) t = pi s t ∩ pi s₁ t :=
  sorry

@[simp] theorem pi_inter_compl {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)}
    (s : set ι) : pi s t ∩ pi (sᶜ) t = pi univ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (pi s t ∩ pi (sᶜ) t = pi univ t)) (Eq.symm union_pi)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (pi (s ∪ (sᶜ)) t = pi univ t)) (union_compl_self s)))
      (Eq.refl (pi univ t)))

theorem pi_update_of_not_mem {ι : Type u_1} {α : ι → Type u_2} {s : set ι} [DecidableEq ι]
    {β : ι → Type u_3} {i : ι} (hi : ¬i ∈ s) (f : (j : ι) → α j) (a : α i)
    (t : (j : ι) → α j → set (β j)) :
    (pi s fun (j : ι) => t j (function.update f i a j)) = pi s fun (j : ι) => t j (f j) :=
  sorry

theorem pi_update_of_mem {ι : Type u_1} {α : ι → Type u_2} {s : set ι} [DecidableEq ι]
    {β : ι → Type u_3} {i : ι} (hi : i ∈ s) (f : (j : ι) → α j) (a : α i)
    (t : (j : ι) → α j → set (β j)) :
    (pi s fun (j : ι) => t j (function.update f i a j)) =
        (set_of fun (x : (i : ι) → β i) => x i ∈ t i a) ∩
          pi (s \ singleton i) fun (j : ι) => t j (f j) :=
  sorry

theorem univ_pi_update {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι] {β : ι → Type u_3} (i : ι)
    (f : (j : ι) → α j) (a : α i) (t : (j : ι) → α j → set (β j)) :
    (pi univ fun (j : ι) => t j (function.update f i a j)) =
        (set_of fun (x : (i : ι) → β i) => x i ∈ t i a) ∩
          pi (singleton iᶜ) fun (j : ι) => t j (f j) :=
  sorry

theorem univ_pi_update_univ {ι : Type u_1} {α : ι → Type u_2} [DecidableEq ι] (i : ι)
    (s : set (α i)) : pi univ (function.update (fun (j : ι) => univ) i s) = function.eval i ⁻¹' s :=
  sorry

theorem eval_image_pi {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)}
    {i : ι} (hs : i ∈ s) (ht : set.nonempty (pi s t)) : function.eval i '' pi s t = t i :=
  sorry

@[simp] theorem eval_image_univ_pi {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)}
    {i : ι} (ht : set.nonempty (pi univ t)) : (fun (f : (i : ι) → α i) => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht

theorem update_preimage_pi {ι : Type u_1} {α : ι → Type u_2} {s : set ι} {t : (i : ι) → set (α i)}
    {i : ι} {f : (i : ι) → α i} (hi : i ∈ s) (hf : ∀ (j : ι), j ∈ s → j ≠ i → f j ∈ t j) :
    function.update f i ⁻¹' pi s t = t i :=
  sorry

theorem update_preimage_univ_pi {ι : Type u_1} {α : ι → Type u_2} {t : (i : ι) → set (α i)} {i : ι}
    {f : (i : ι) → α i} (hf : ∀ (j : ι), j ≠ i → f j ∈ t j) :
    function.update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun (j : ι) (_x : j ∈ univ) => hf j

theorem subset_pi_eval_image {ι : Type u_1} {α : ι → Type u_2} (s : set ι)
    (u : set ((i : ι) → α i)) : u ⊆ pi s fun (i : ι) => function.eval i '' u :=
  fun (f : (i : ι) → α i) (hf : f ∈ u) (i : ι) (hi : i ∈ s) =>
    Exists.intro f { left := hf, right := rfl }

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) : ↥s → ↥t :=
  fun (x : ↥s) => { val := ↑x, property := sorry }

@[simp] theorem inclusion_self {α : Type u_1} {s : set α} (x : ↥s) :
    inclusion (subset.refl s) x = x :=
  subtype.cases_on x
    fun (x_val : α) (x_property : x_val ∈ s) =>
      Eq.refl (inclusion (subset.refl s) { val := x_val, property := x_property })

@[simp] theorem inclusion_right {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) (x : ↥t)
    (m : ↑x ∈ s) : inclusion h { val := ↑x, property := m } = x :=
  sorry

@[simp] theorem inclusion_inclusion {α : Type u_1} {s : set α} {t : set α} {u : set α} (hst : s ⊆ t)
    (htu : t ⊆ u) (x : ↥s) : inclusion htu (inclusion hst x) = inclusion (subset.trans hst htu) x :=
  subtype.cases_on x
    fun (x_val : α) (x_property : x_val ∈ s) =>
      Eq.refl (inclusion htu (inclusion hst { val := x_val, property := x_property }))

@[simp] theorem coe_inclusion {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) (x : ↥s) :
    ↑(inclusion h x) = ↑x :=
  rfl

theorem inclusion_injective {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) :
    function.injective (inclusion h) :=
  sorry

theorem eq_of_inclusion_surjective {α : Type u_1} {s : set α} {t : set α} {h : s ⊆ t}
    (h_surj : function.surjective (inclusion h)) : s = t :=
  sorry

theorem range_inclusion {α : Type u_1} {s : set α} {t : set α} (h : s ⊆ t) :
    range (inclusion h) = set_of fun (x : ↥t) => ↑x ∈ s :=
  sorry

/-! ### Injectivity and surjectivity lemmas for image and preimage -/

@[simp] theorem preimage_injective {α : Type u} {β : Type v} {f : α → β} :
    function.injective (preimage f) ↔ function.surjective f :=
  sorry

@[simp] theorem preimage_surjective {α : Type u} {β : Type v} {f : α → β} :
    function.surjective (preimage f) ↔ function.injective f :=
  sorry

@[simp] theorem image_surjective {α : Type u} {β : Type v} {f : α → β} :
    function.surjective (image f) ↔ function.surjective f :=
  sorry

@[simp] theorem image_injective {α : Type u} {β : Type v} {f : α → β} :
    function.injective (image f) ↔ function.injective f :=
  sorry

/-! ### Lemmas about images of binary and ternary functions -/

/-- The image of a binary function `f : α → β → γ` as a function `set α → set β → set γ`.
  Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.
-/
def image2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ) (s : set α) (t : set β) :
    set γ :=
  set_of fun (c : γ) => ∃ (a : α), ∃ (b : β), a ∈ s ∧ b ∈ t ∧ f a b = c

theorem mem_image2_eq {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} {c : γ} : c ∈ image2 f s t = ∃ (a : α), ∃ (b : β), a ∈ s ∧ b ∈ t ∧ f a b = c :=
  rfl

@[simp] theorem mem_image2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} {c : γ} : c ∈ image2 f s t ↔ ∃ (a : α), ∃ (b : β), a ∈ s ∧ b ∈ t ∧ f a b = c :=
  iff.rfl

theorem mem_image2_of_mem {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} {a : α} {b : β} (h1 : a ∈ s) (h2 : b ∈ t) : f a b ∈ image2 f s t :=
  Exists.intro a (Exists.intro b { left := h1, right := { left := h2, right := rfl } })

theorem mem_image2_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} {a : α} {b : β} (hf : function.injective2 f) :
    f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  sorry

/-- image2 is monotone with respect to `⊆`. -/
theorem image2_subset {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {s' : set α} {t : set β} {t' : set β} (hs : s ⊆ s') (ht : t ⊆ t') :
    image2 f s t ⊆ image2 f s' t' :=
  sorry

theorem forall_image2_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} {p : γ → Prop} :
    (∀ (z : γ), z ∈ image2 f s t → p z) ↔ ∀ (x : α), x ∈ s → ∀ (y : β), y ∈ t → p (f x y) :=
  sorry

@[simp] theorem image2_subset_iff {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {s : set α} {t : set β} {u : set γ} :
    image2 f s t ⊆ u ↔ ∀ (x : α), x ∈ s → ∀ (y : β), y ∈ t → f x y ∈ u :=
  forall_image2_iff

theorem image2_union_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {s' : set α} {t : set β} : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t :=
  sorry

theorem image2_union_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} {t' : set β} : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' :=
  sorry

@[simp] theorem image2_empty_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {t : set β} : image2 f ∅ t = ∅ :=
  sorry

@[simp] theorem image2_empty_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {s : set α} : image2 f s ∅ = ∅ :=
  sorry

theorem image2_inter_subset_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {s : set α} {s' : set α} {t : set β} : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
  sorry

theorem image2_inter_subset_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {s : set α} {t : set β} {t' : set β} : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
  sorry

@[simp] theorem image2_singleton_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {t : set β} {a : α} : image2 f (singleton a) t = f a '' t :=
  sorry

@[simp] theorem image2_singleton_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ}
    {s : set α} {b : β} : image2 f s (singleton b) = (fun (a : α) => f a b) '' s :=
  sorry

theorem image2_singleton {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {a : α}
    {b : β} : image2 f (singleton a) (singleton b) = singleton (f a b) :=
  sorry

theorem image2_congr {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {f' : α → β → γ}
    {s : set α} {t : set β} (h : ∀ (a : α), a ∈ s → ∀ (b : β), b ∈ t → f a b = f' a b) :
    image2 f s t = image2 f' s t :=
  sorry

/-- A common special case of `image2_congr` -/
theorem image2_congr' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {f' : α → β → γ}
    {s : set α} {t : set β} (h : ∀ (a : α) (b : β), f a b = f' a b) :
    image2 f s t = image2 f' s t :=
  image2_congr fun (a : α) (_x : a ∈ s) (b : β) (_x : b ∈ t) => h a b

/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `set α → set β → set γ → set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def image3 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} (g : α → β → γ → δ)
    (s : set α) (t : set β) (u : set γ) : set δ :=
  set_of fun (d : δ) => ∃ (a : α), ∃ (b : β), ∃ (c : γ), a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d

@[simp] theorem mem_image3 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    {g : α → β → γ → δ} {s : set α} {t : set β} {u : set γ} {d : δ} :
    d ∈ image3 g s t u ↔ ∃ (a : α), ∃ (b : β), ∃ (c : γ), a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
  iff.rfl

theorem image3_congr {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {g : α → β → γ → δ}
    {g' : α → β → γ → δ} {s : set α} {t : set β} {u : set γ}
    (h : ∀ (a : α), a ∈ s → ∀ (b : β), b ∈ t → ∀ (c : γ), c ∈ u → g a b c = g' a b c) :
    image3 g s t u = image3 g' s t u :=
  sorry

/-- A common special case of `image3_congr` -/
theorem image3_congr' {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    {g : α → β → γ → δ} {g' : α → β → γ → δ} {s : set α} {t : set β} {u : set γ}
    (h : ∀ (a : α) (b : β) (c : γ), g a b c = g' a b c) : image3 g s t u = image3 g' s t u :=
  image3_congr fun (a : α) (_x : a ∈ s) (b : β) (_x : b ∈ t) (c : γ) (_x : c ∈ u) => h a b c

theorem image2_image2_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    {ε : Type u_5} {s : set α} {t : set β} {u : set γ} (f : δ → γ → ε) (g : α → β → δ) :
    image2 f (image2 g s t) u = image3 (fun (a : α) (b : β) (c : γ) => f (g a b) c) s t u :=
  sorry

theorem image2_image2_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4}
    {ε : Type u_5} {s : set α} {t : set β} {u : set γ} (f : α → δ → ε) (g : β → γ → δ) :
    image2 f s (image2 g t u) = image3 (fun (a : α) (b : β) (c : γ) => f a (g b c)) s t u :=
  sorry

theorem image2_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {ε : Type u_5}
    {s : set α} {t : set β} {u : set γ} {ε' : Type u_6} {f : δ → γ → ε} {g : α → β → δ}
    {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ (a : α) (b : β) (c : γ), f (g a b) c = f' a (g' b c)) :
    image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
  sorry

theorem image_image2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : set α}
    {t : set β} (f : α → β → γ) (g : γ → δ) :
    g '' image2 f s t = image2 (fun (a : α) (b : β) => g (f a b)) s t :=
  sorry

theorem image2_image_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : set α}
    {t : set β} (f : γ → β → δ) (g : α → γ) :
    image2 f (g '' s) t = image2 (fun (a : α) (b : β) => f (g a) b) s t :=
  sorry

theorem image2_image_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {s : set α}
    {t : set β} (f : α → γ → δ) (g : β → γ) :
    image2 f s (g '' t) = image2 (fun (a : α) (b : β) => f a (g b)) s t :=
  sorry

theorem image2_swap {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β → γ) (s : set α)
    (t : set β) : image2 f s t = image2 (fun (a : β) (b : α) => f b a) t s :=
  sorry

@[simp] theorem image2_left {α : Type u_1} {β : Type u_2} {s : set α} {t : set β}
    (h : set.nonempty t) : image2 (fun (x : α) (y : β) => x) s t = s :=
  sorry

@[simp] theorem image2_right {α : Type u_1} {β : Type u_2} {s : set α} {t : set β}
    (h : set.nonempty s) : image2 (fun (x : α) (y : β) => y) s t = t :=
  sorry

@[simp] theorem image_prod {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : set α} {t : set β}
    (f : α → β → γ) :
    (fun (x : α × β) => f (prod.fst x) (prod.snd x)) '' set.prod s t = image2 f s t :=
  sorry

theorem nonempty.image2 {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {s : set α}
    {t : set β} (hs : set.nonempty s) (ht : set.nonempty t) : set.nonempty (image2 f s t) :=
  sorry

end set


namespace subsingleton


theorem eq_univ_of_nonempty {α : Type u_1} [subsingleton α] {s : set α} :
    set.nonempty s → s = set.univ :=
  sorry

theorem set_cases {α : Type u_1} [subsingleton α] {p : set α → Prop} (h0 : p ∅) (h1 : p set.univ)
    (s : set α) : p s :=
  or.elim (set.eq_empty_or_nonempty s) (fun (h : s = ∅) => Eq.symm h ▸ h0)
    fun (h : set.nonempty s) => Eq.symm (eq_univ_of_nonempty h) ▸ h1

end Mathlib