/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.finset_ops
import Mathlib.tactic.monotonicity.default
import Mathlib.tactic.apply
import Mathlib.tactic.nth_rewrite.default
import Mathlib.PostPort

universes u_4 l u_1 u u_2 u_3 

namespace Mathlib

/-!
# Finite sets

mathlib has several different models for finite sets,
and it can be confusing when you're first getting used to them!

This file builds the basic theory of `finset α`,
modelled as a `multiset α` without duplicates.

It's "constructive" in the since that there is an underlying list of elements,
although this is wrapped in a quotient by permutations,
so anytime you actually use this list you're obligated to show you didn't depend on the ordering.

There's also the typeclass `fintype α`
(which asserts that there is some `finset α` containing every term of type `α`)
as well as the predicate `finite` on `s : set α` (which asserts `nonempty (fintype s)`).
-/

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure finset (α : Type u_4) where
  val : multiset α
  nodup : multiset.nodup val

namespace finset


theorem eq_of_veq {α : Type u_1} {s : finset α} {t : finset α} : val s = val t → s = t := sorry

@[simp] theorem val_inj {α : Type u_1} {s : finset α} {t : finset α} : val s = val t ↔ s = t :=
  { mp := eq_of_veq, mpr := congr_arg fun {s : finset α} => val s }

@[simp] theorem erase_dup_eq_self {α : Type u_1} [DecidableEq α] (s : finset α) :
    multiset.erase_dup (val s) = val s :=
  iff.mpr multiset.erase_dup_eq_self (nodup s)

protected instance has_decidable_eq {α : Type u_1} [DecidableEq α] : DecidableEq (finset α) := sorry

/-! ### membership -/

protected instance has_mem {α : Type u_1} : has_mem α (finset α) :=
  has_mem.mk fun (a : α) (s : finset α) => a ∈ val s

theorem mem_def {α : Type u_1} {a : α} {s : finset α} : a ∈ s ↔ a ∈ val s := iff.rfl

@[simp] theorem mem_mk {α : Type u_1} {a : α} {s : multiset α} {nd : multiset.nodup s} :
    a ∈ mk s nd ↔ a ∈ s :=
  iff.rfl

protected instance decidable_mem {α : Type u_1} [h : DecidableEq α] (a : α) (s : finset α) :
    Decidable (a ∈ s) :=
  multiset.decidable_mem a (val s)

/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
protected instance set.has_coe_t {α : Type u_1} : has_coe_t (finset α) (set α) :=
  has_coe_t.mk fun (s : finset α) => set_of fun (x : α) => x ∈ s

@[simp] theorem mem_coe {α : Type u_1} {a : α} {s : finset α} : a ∈ ↑s ↔ a ∈ s := iff.rfl

@[simp] theorem set_of_mem {α : Type u_1} {s : finset α} : (set_of fun (a : α) => a ∈ s) = ↑s := rfl

@[simp] theorem coe_mem {α : Type u_1} {s : finset α} (x : ↥↑s) : ↑x ∈ s := subtype.property x

@[simp] theorem mk_coe {α : Type u_1} {s : finset α} (x : ↥↑s) {h : ↑x ∈ ↑s} :
    { val := ↑x, property := h } = x :=
  subtype.coe_eta x h

protected instance decidable_mem' {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    Decidable (a ∈ ↑s) :=
  finset.decidable_mem a s

/-! ### extensionality -/

theorem ext_iff {α : Type u_1} {s₁ : finset α} {s₂ : finset α} :
    s₁ = s₂ ↔ ∀ (a : α), a ∈ s₁ ↔ a ∈ s₂ :=
  iff.trans (iff.symm val_inj) (multiset.nodup_ext (nodup s₁) (nodup s₂))

theorem ext {α : Type u_1} {s₁ : finset α} {s₂ : finset α} :
    (∀ (a : α), a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  iff.mpr ext_iff

@[simp] theorem coe_inj {α : Type u_1} {s₁ : finset α} {s₂ : finset α} : ↑s₁ = ↑s₂ ↔ s₁ = s₂ :=
  iff.trans set.ext_iff (iff.symm ext_iff)

theorem coe_injective {α : Type u_1} : function.injective coe :=
  fun (s t : finset α) => iff.mp coe_inj

/-! ### subset -/

protected instance has_subset {α : Type u_1} : has_subset (finset α) :=
  has_subset.mk fun (s₁ s₂ : finset α) => ∀ {a : α}, a ∈ s₁ → a ∈ s₂

theorem subset_def {α : Type u_1} {s₁ : finset α} {s₂ : finset α} : s₁ ⊆ s₂ ↔ val s₁ ⊆ val s₂ :=
  iff.rfl

@[simp] theorem subset.refl {α : Type u_1} (s : finset α) : s ⊆ s := multiset.subset.refl (val s)

theorem subset_of_eq {α : Type u_1} {s : finset α} {t : finset α} (h : s = t) : s ⊆ t :=
  h ▸ subset.refl s

theorem subset.trans {α : Type u_1} {s₁ : finset α} {s₂ : finset α} {s₃ : finset α} :
    s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  multiset.subset.trans

theorem superset.trans {α : Type u_1} {s₁ : finset α} {s₂ : finset α} {s₃ : finset α} :
    s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ :=
  fun (h' : s₁ ⊇ s₂) (h : s₂ ⊇ s₃) => subset.trans h h'

-- TODO: these should be global attributes, but this will require fixing other files

theorem mem_of_subset {α : Type u_1} {s₁ : finset α} {s₂ : finset α} {a : α} :
    s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  multiset.mem_of_subset

theorem subset.antisymm {α : Type u_1} {s₁ : finset α} {s₂ : finset α} (H₁ : s₁ ⊆ s₂)
    (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun (a : α) => { mp := H₁, mpr := H₂ }

theorem subset_iff {α : Type u_1} {s₁ : finset α} {s₂ : finset α} :
    s₁ ⊆ s₂ ↔ ∀ {x : α}, x ∈ s₁ → x ∈ s₂ :=
  iff.rfl

@[simp] theorem coe_subset {α : Type u_1} {s₁ : finset α} {s₂ : finset α} : ↑s₁ ⊆ ↑s₂ ↔ s₁ ⊆ s₂ :=
  iff.rfl

@[simp] theorem val_le_iff {α : Type u_1} {s₁ : finset α} {s₂ : finset α} :
    val s₁ ≤ val s₂ ↔ s₁ ⊆ s₂ :=
  multiset.le_iff_subset (nodup s₁)

protected instance has_ssubset {α : Type u_1} : has_ssubset (finset α) :=
  has_ssubset.mk fun (a b : finset α) => a ⊆ b ∧ ¬b ⊆ a

protected instance partial_order {α : Type u_1} : partial_order (finset α) :=
  partial_order.mk has_subset.subset has_ssubset.ssubset subset.refl subset.trans subset.antisymm

theorem subset.antisymm_iff {α : Type u_1} {s₁ : finset α} {s₂ : finset α} :
    s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iff

@[simp] theorem le_iff_subset {α : Type u_1} {s₁ : finset α} {s₂ : finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  iff.rfl

@[simp] theorem lt_iff_ssubset {α : Type u_1} {s₁ : finset α} {s₂ : finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  iff.rfl

@[simp] theorem coe_ssubset {α : Type u_1} {s₁ : finset α} {s₂ : finset α} : ↑s₁ ⊂ ↑s₂ ↔ s₁ ⊂ s₂ :=
  sorry

@[simp] theorem val_lt_iff {α : Type u_1} {s₁ : finset α} {s₂ : finset α} :
    val s₁ < val s₂ ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff (not_congr val_le_iff)

theorem ssubset_iff_of_subset {α : Type u_1} {s₁ : finset α} {s₂ : finset α} (h : s₁ ⊆ s₂) :
    s₁ ⊂ s₂ ↔ ∃ (x : α), ∃ (H : x ∈ s₂), ¬x ∈ s₁ :=
  set.ssubset_iff_of_subset h

/-! ### Nonempty -/

/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty {α : Type u_1} (s : finset α) := ∃ (x : α), x ∈ s

@[simp] theorem coe_nonempty {α : Type u_1} {s : finset α} : set.nonempty ↑s ↔ finset.nonempty s :=
  iff.rfl

theorem nonempty.bex {α : Type u_1} {s : finset α} (h : finset.nonempty s) : ∃ (x : α), x ∈ s := h

theorem nonempty.mono {α : Type u_1} {s : finset α} {t : finset α} (hst : s ⊆ t)
    (hs : finset.nonempty s) : finset.nonempty t :=
  set.nonempty.mono hst hs

theorem nonempty.forall_const {α : Type u_1} {s : finset α} (h : finset.nonempty s) {p : Prop} :
    (∀ (x : α), x ∈ s → p) ↔ p :=
  sorry

/-! ### empty -/

/-- The empty finset -/
protected def empty {α : Type u_1} : finset α := mk 0 multiset.nodup_zero

protected instance has_emptyc {α : Type u_1} : has_emptyc (finset α) := has_emptyc.mk finset.empty

protected instance inhabited {α : Type u_1} : Inhabited (finset α) := { default := ∅ }

@[simp] theorem empty_val {α : Type u_1} : val ∅ = 0 := rfl

@[simp] theorem not_mem_empty {α : Type u_1} (a : α) : ¬a ∈ ∅ := id

@[simp] theorem not_nonempty_empty {α : Type u_1} : ¬finset.nonempty ∅ :=
  fun (_x : finset.nonempty ∅) =>
    (fun (_a : finset.nonempty ∅) =>
        Exists.dcases_on _a fun (w : α) (h : w ∈ ∅) => idRhs False (not_mem_empty w h))
      _x

@[simp] theorem mk_zero {α : Type u_1} : mk 0 multiset.nodup_zero = ∅ := rfl

theorem ne_empty_of_mem {α : Type u_1} {a : α} {s : finset α} (h : a ∈ s) : s ≠ ∅ :=
  fun (e : s = ∅) => not_mem_empty a (e ▸ h)

theorem nonempty.ne_empty {α : Type u_1} {s : finset α} (h : finset.nonempty s) : s ≠ ∅ :=
  exists.elim h fun (a : α) => ne_empty_of_mem

@[simp] theorem empty_subset {α : Type u_1} (s : finset α) : ∅ ⊆ s := multiset.zero_subset (val s)

theorem eq_empty_of_forall_not_mem {α : Type u_1} {s : finset α} (H : ∀ (x : α), ¬x ∈ s) : s = ∅ :=
  eq_of_veq (multiset.eq_zero_of_forall_not_mem H)

theorem eq_empty_iff_forall_not_mem {α : Type u_1} {s : finset α} : s = ∅ ↔ ∀ (x : α), ¬x ∈ s :=
  { mp := fun (ᾰ : s = ∅) (x : α) => Eq._oldrec id (Eq.symm ᾰ),
    mpr := fun (h : ∀ (x : α), ¬x ∈ s) => eq_empty_of_forall_not_mem h }

@[simp] theorem val_eq_zero {α : Type u_1} {s : finset α} : val s = 0 ↔ s = ∅ := val_inj

theorem subset_empty {α : Type u_1} {s : finset α} : s ⊆ ∅ ↔ s = ∅ :=
  iff.trans multiset.subset_zero val_eq_zero

theorem nonempty_of_ne_empty {α : Type u_1} {s : finset α} (h : s ≠ ∅) : finset.nonempty s :=
  multiset.exists_mem_of_ne_zero (mt (iff.mp val_eq_zero) h)

theorem nonempty_iff_ne_empty {α : Type u_1} {s : finset α} : finset.nonempty s ↔ s ≠ ∅ :=
  { mp := nonempty.ne_empty, mpr := nonempty_of_ne_empty }

@[simp] theorem not_nonempty_iff_eq_empty {α : Type u_1} {s : finset α} :
    ¬finset.nonempty s ↔ s = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬finset.nonempty s ↔ s = ∅)) (propext nonempty_iff_ne_empty)))
    not_not

theorem eq_empty_or_nonempty {α : Type u_1} (s : finset α) : s = ∅ ∨ finset.nonempty s :=
  classical.by_cases Or.inl fun (h : ¬s = ∅) => Or.inr (nonempty_of_ne_empty h)

@[simp] theorem coe_empty {α : Type u_1} : ↑∅ = ∅ := rfl

/-- A `finset` for an empty type is empty. -/
theorem eq_empty_of_not_nonempty {α : Type u_1} (h : ¬Nonempty α) (s : finset α) : s = ∅ :=
  eq_empty_of_forall_not_mem fun (x : α) => false.elim (iff.mp not_nonempty_iff_imp_false h x)

/-! ### singleton -/

/--
`{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
protected instance has_singleton {α : Type u_1} : has_singleton α (finset α) :=
  has_singleton.mk fun (a : α) => mk (singleton a) (multiset.nodup_singleton a)

@[simp] theorem singleton_val {α : Type u_1} (a : α) : val (singleton a) = a ::ₘ 0 := rfl

@[simp] theorem mem_singleton {α : Type u_1} {a : α} {b : α} : b ∈ singleton a ↔ b = a :=
  multiset.mem_singleton

theorem not_mem_singleton {α : Type u_1} {a : α} {b : α} : ¬a ∈ singleton b ↔ a ≠ b :=
  not_congr mem_singleton

theorem mem_singleton_self {α : Type u_1} (a : α) : a ∈ singleton a := Or.inl rfl

theorem singleton_inj {α : Type u_1} {a : α} {b : α} : singleton a = singleton b ↔ a = b :=
  { mp := fun (h : singleton a = singleton b) => iff.mp mem_singleton (h ▸ mem_singleton_self a),
    mpr := congr_arg fun {a : α} => singleton a }

@[simp] theorem singleton_nonempty {α : Type u_1} (a : α) : finset.nonempty (singleton a) :=
  Exists.intro a (mem_singleton_self a)

@[simp] theorem singleton_ne_empty {α : Type u_1} (a : α) : singleton a ≠ ∅ :=
  nonempty.ne_empty (singleton_nonempty a)

@[simp] theorem coe_singleton {α : Type u_1} (a : α) : ↑(singleton a) = singleton a := sorry

theorem eq_singleton_iff_unique_mem {α : Type u_1} {s : finset α} {a : α} :
    s = singleton a ↔ a ∈ s ∧ ∀ (x : α), x ∈ s → x = a :=
  sorry

theorem eq_singleton_iff_nonempty_unique_mem {α : Type u_1} {s : finset α} {a : α} :
    s = singleton a ↔ finset.nonempty s ∧ ∀ (x : α), x ∈ s → x = a :=
  sorry

theorem singleton_iff_unique_mem {α : Type u_1} (s : finset α) :
    (∃ (a : α), s = singleton a) ↔ exists_unique fun (a : α) => a ∈ s :=
  sorry

theorem singleton_subset_set_iff {α : Type u_1} {s : set α} {a : α} : ↑(singleton a) ⊆ s ↔ a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑(singleton a) ⊆ s ↔ a ∈ s)) (coe_singleton a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (singleton a ⊆ s ↔ a ∈ s)) (propext set.singleton_subset_iff)))
      (iff.refl (a ∈ s)))

@[simp] theorem singleton_subset_iff {α : Type u_1} {s : finset α} {a : α} :
    singleton a ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff

/-! ### cons -/

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint.  -/
def cons {α : Type u_1} (a : α) (s : finset α) (h : ¬a ∈ s) : finset α := mk (a ::ₘ val s) sorry

@[simp] theorem mem_cons {α : Type u_1} {a : α} {s : finset α} {h : ¬a ∈ s} {b : α} :
    b ∈ cons a s h ↔ b = a ∨ b ∈ s :=
  sorry

@[simp] theorem cons_val {α : Type u_1} {a : α} {s : finset α} (h : ¬a ∈ s) :
    val (cons a s h) = a ::ₘ val s :=
  rfl

@[simp] theorem mk_cons {α : Type u_1} {a : α} {s : multiset α} (h : multiset.nodup (a ::ₘ s)) :
    mk (a ::ₘ s) h =
        cons a (mk s (and.right (iff.mp multiset.nodup_cons h)))
          (and.left (iff.mp multiset.nodup_cons h)) :=
  rfl

@[simp] theorem nonempty_cons {α : Type u_1} {a : α} {s : finset α} (h : ¬a ∈ s) :
    finset.nonempty (cons a s h) :=
  Exists.intro a (iff.mpr mem_cons (Or.inl rfl))

@[simp] theorem nonempty_mk_coe {α : Type u_1} {l : List α} {hl : multiset.nodup ↑l} :
    finset.nonempty (mk (↑l) hl) ↔ l ≠ [] :=
  sorry

/-! ### disjoint union -/

/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disj_union {α : Type u_1} (s : finset α) (t : finset α) (h : ∀ (a : α), a ∈ s → ¬a ∈ t) :
    finset α :=
  mk (val s + val t) sorry

@[simp] theorem mem_disj_union {α : Type u_1} {s : finset α} {t : finset α}
    {h : ∀ (a : α), a ∈ s → ¬a ∈ t} {a : α} : a ∈ disj_union s t h ↔ a ∈ s ∨ a ∈ t :=
  sorry

/-! ### insert -/

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
protected instance has_insert {α : Type u_1} [DecidableEq α] : has_insert α (finset α) :=
  has_insert.mk fun (a : α) (s : finset α) => mk (multiset.ndinsert a (val s)) sorry

theorem insert_def {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    insert a s = mk (multiset.ndinsert a (val s)) (multiset.nodup_ndinsert a (nodup s)) :=
  rfl

@[simp] theorem insert_val {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    val (insert a s) = multiset.ndinsert a (val s) :=
  rfl

theorem insert_val' {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    val (insert a s) = multiset.erase_dup (a ::ₘ val s) :=
  sorry

theorem insert_val_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : ¬a ∈ s) :
    val (insert a s) = a ::ₘ val s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (val (insert a s) = a ::ₘ val s)) (insert_val a s)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (multiset.ndinsert a (val s) = a ::ₘ val s))
          (multiset.ndinsert_of_not_mem h)))
      (Eq.refl (a ::ₘ val s)))

@[simp] theorem mem_insert {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α} :
    a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  multiset.mem_ndinsert

theorem mem_insert_self {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) : a ∈ insert a s :=
  multiset.mem_ndinsert_self a (val s)

theorem mem_insert_of_mem {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α}
    (h : a ∈ s) : a ∈ insert b s :=
  multiset.mem_ndinsert_of_mem h

theorem mem_of_mem_insert_of_ne {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α}
    (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  or.resolve_left (iff.mp mem_insert h)

@[simp] theorem cons_eq_insert {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) (h : ¬a ∈ s) :
    cons a s h = insert a s :=
  sorry

@[simp] theorem coe_insert {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    ↑(insert a s) = insert a ↑s :=
  sorry

theorem mem_insert_coe {α : Type u_1} [DecidableEq α] {s : finset α} {x : α} {y : α} :
    x ∈ insert y s ↔ x ∈ insert y ↑s :=
  sorry

protected instance is_lawful_singleton {α : Type u_1} [DecidableEq α] :
    is_lawful_singleton α (finset α) :=
  is_lawful_singleton.mk
    fun (a : α) =>
      ext
        fun (a_1 : α) =>
          eq.mpr
            (id
              (Eq.trans
                ((fun (a a_2 : Prop) (e_1 : a = a_2) (b b_1 : Prop) (e_2 : b = b_1) =>
                    congr (congr_arg Iff e_1) e_2)
                  (a_1 ∈ insert a ∅) (a_1 = a)
                  (Eq.trans
                    (Eq.trans (propext mem_insert)
                      ((fun (a a_2 : Prop) (e_1 : a = a_2) (b b_1 : Prop) (e_2 : b = b_1) =>
                          congr (congr_arg Or e_1) e_2)
                        (a_1 = a) (a_1 = a) (Eq.refl (a_1 = a)) (a_1 ∈ ∅) False
                        (propext
                          ((fun {α : Type u_1} (a : α) => iff_false_intro (not_mem_empty a)) a_1))))
                    (propext (or_false (a_1 = a))))
                  (a_1 ∈ singleton a) (a_1 = a) (propext mem_singleton))
                (propext (iff_self (a_1 = a)))))
            trivial

@[simp] theorem insert_eq_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : a ∈ s) :
    insert a s = s :=
  eq_of_veq (multiset.ndinsert_of_mem h)

@[simp] theorem insert_singleton_self_eq {α : Type u_1} [DecidableEq α] (a : α) :
    insert a (singleton a) = singleton a :=
  insert_eq_of_mem (mem_singleton_self a)

theorem insert.comm {α : Type u_1} [DecidableEq α] (a : α) (b : α) (s : finset α) :
    insert a (insert b s) = insert b (insert a s) :=
  sorry

theorem insert_singleton_comm {α : Type u_1} [DecidableEq α] (a : α) (b : α) :
    insert a (singleton b) = insert b (singleton a) :=
  sorry

@[simp] theorem insert_idem {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    insert a (insert a s) = insert a s :=
  sorry

@[simp] theorem insert_nonempty {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    finset.nonempty (insert a s) :=
  Exists.intro a (mem_insert_self a s)

@[simp] theorem insert_ne_empty {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    insert a s ≠ ∅ :=
  nonempty.ne_empty (insert_nonempty a s)

/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/

protected instance has_insert.insert.nonempty {α : Type u} [DecidableEq α] (i : α) (s : finset α) :
    Nonempty ↥↑(insert i s) :=
  set.nonempty.to_subtype (iff.mpr coe_nonempty (insert_nonempty i s))

theorem ne_insert_of_not_mem {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) {a : α}
    (h : ¬a ∈ s) : s ≠ insert a t :=
  sorry

theorem insert_subset {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} {t : finset α} :
    insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  sorry

theorem subset_insert {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) : s ⊆ insert a s :=
  fun (b : α) => mem_insert_of_mem

theorem insert_subset_insert {α : Type u_1} [DecidableEq α] (a : α) {s : finset α} {t : finset α}
    (h : s ⊆ t) : insert a s ⊆ insert a t :=
  iff.mpr insert_subset { left := mem_insert_self a t, right := subset.trans h (subset_insert a t) }

theorem ssubset_iff {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    s ⊂ t ↔ ∃ (a : α), ∃ (H : ¬a ∈ s), insert a s ⊆ t :=
  sorry

theorem ssubset_insert {α : Type u_1} [DecidableEq α] {s : finset α} {a : α} (h : ¬a ∈ s) :
    s ⊂ insert a s :=
  iff.mpr ssubset_iff (Exists.intro a (Exists.intro h (subset.refl (insert a s))))

protected theorem induction {α : Type u_1} {p : finset α → Prop} [DecidableEq α] (h₁ : p ∅)
    (h₂ : ∀ {a : α} {s : finset α}, ¬a ∈ s → p s → p (insert a s)) (s : finset α) : p s :=
  sorry

/--
To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
protected theorem induction_on {α : Type u_1} {p : finset α → Prop} [DecidableEq α] (s : finset α)
    (h₁ : p ∅) (h₂ : ∀ {a : α} {s : finset α}, ¬a ∈ s → p s → p (insert a s)) : p s :=
  finset.induction h₁ h₂ s

/--
To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
theorem induction_on' {α : Type u_1} {p : finset α → Prop} [DecidableEq α] (S : finset α) (h₁ : p ∅)
    (h₂ : ∀ {a : α} {s : finset α}, a ∈ S → s ⊆ S → ¬a ∈ s → p s → p (insert a s)) : p S :=
  sorry

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtype_insert_equiv_option {α : Type u_1} [DecidableEq α] {t : finset α} {x : α} (h : ¬x ∈ t) :
    (Subtype fun (i : α) => i ∈ insert x t) ≃ Option (Subtype fun (i : α) => i ∈ t) :=
  equiv.mk
    (fun (y : Subtype fun (i : α) => i ∈ insert x t) =>
      dite (↑y = x) (fun (h : ↑y = x) => none)
        fun (h : ¬↑y = x) => some { val := ↑y, property := sorry })
    (fun (y : Option (Subtype fun (i : α) => i ∈ t)) =>
      option.elim y { val := x, property := sorry }
        fun (z : Subtype fun (i : α) => i ∈ t) => { val := ↑z, property := sorry })
    sorry sorry

/-! ### union -/

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
protected instance has_union {α : Type u_1} [DecidableEq α] : has_union (finset α) :=
  has_union.mk fun (s₁ s₂ : finset α) => mk (multiset.ndunion (val s₁) (val s₂)) sorry

theorem union_val_nd {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    val (s₁ ∪ s₂) = multiset.ndunion (val s₁) (val s₂) :=
  rfl

@[simp] theorem union_val {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    val (s₁ ∪ s₂) = val s₁ ∪ val s₂ :=
  multiset.ndunion_eq_union (nodup s₁)

@[simp] theorem mem_union {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} {s₂ : finset α} :
    a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  multiset.mem_ndunion

@[simp] theorem disj_union_eq_union {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α)
    (h : ∀ (a : α), a ∈ s → ¬a ∈ t) : disj_union s t h = s ∪ t :=
  sorry

theorem mem_union_left {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} (s₂ : finset α)
    (h : a ∈ s₁) : a ∈ s₁ ∪ s₂ :=
  iff.mpr mem_union (Or.inl h)

theorem mem_union_right {α : Type u_1} [DecidableEq α] {a : α} {s₂ : finset α} (s₁ : finset α)
    (h : a ∈ s₂) : a ∈ s₁ ∪ s₂ :=
  iff.mpr mem_union (Or.inr h)

theorem forall_mem_union {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    {p : α → Prop} :
    (∀ (ab : α), ab ∈ s₁ ∪ s₂ → p ab) ↔ (∀ (a : α), a ∈ s₁ → p a) ∧ ∀ (b : α), b ∈ s₂ → p b :=
  sorry

theorem not_mem_union {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} {s₂ : finset α} :
    ¬a ∈ s₁ ∪ s₂ ↔ ¬a ∈ s₁ ∧ ¬a ∈ s₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (¬a ∈ s₁ ∪ s₂ ↔ ¬a ∈ s₁ ∧ ¬a ∈ s₂)) (propext mem_union)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (¬(a ∈ s₁ ∨ a ∈ s₂) ↔ ¬a ∈ s₁ ∧ ¬a ∈ s₂)) (propext not_or_distrib)))
      (iff.refl (¬a ∈ s₁ ∧ ¬a ∈ s₂)))

@[simp] theorem coe_union {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    ↑(s₁ ∪ s₂) = ↑s₁ ∪ ↑s₂ :=
  set.ext fun (x : α) => mem_union

theorem union_subset {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α} {s₃ : finset α}
    (h₁ : s₁ ⊆ s₃) (h₂ : s₂ ⊆ s₃) : s₁ ∪ s₂ ⊆ s₃ :=
  iff.mp val_le_iff (iff.mpr multiset.ndunion_le { left := h₁, right := iff.mpr val_le_iff h₂ })

theorem subset_union_left {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ ⊆ s₁ ∪ s₂ :=
  fun (x : α) => mem_union_left s₂

theorem subset_union_right {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₂ ⊆ s₁ ∪ s₂ :=
  fun (x : α) => mem_union_right s₁

theorem union_subset_union {α : Type u_1} [DecidableEq α] {s1 : finset α} {t1 : finset α}
    {s2 : finset α} {t2 : finset α} (h1 : s1 ⊆ t1) (h2 : s2 ⊆ t2) : s1 ∪ s2 ⊆ t1 ∪ t2 :=
  sorry

theorem union_comm {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ ∪ s₂ = s₂ ∪ s₁ :=
  sorry

protected instance has_union.union.is_commutative {α : Type u_1} [DecidableEq α] :
    is_commutative (finset α) has_union.union :=
  is_commutative.mk union_comm

@[simp] theorem union_assoc {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  sorry

protected instance has_union.union.is_associative {α : Type u_1} [DecidableEq α] :
    is_associative (finset α) has_union.union :=
  is_associative.mk union_assoc

@[simp] theorem union_idempotent {α : Type u_1} [DecidableEq α] (s : finset α) : s ∪ s = s :=
  ext fun (_x : α) => iff.trans mem_union (or_self (_x ∈ s))

protected instance has_union.union.is_idempotent {α : Type u_1} [DecidableEq α] :
    is_idempotent (finset α) has_union.union :=
  is_idempotent.mk union_idempotent

theorem union_left_comm {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  sorry

theorem union_right_comm {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  sorry

theorem union_self {α : Type u_1} [DecidableEq α] (s : finset α) : s ∪ s = s := union_idempotent s

@[simp] theorem union_empty {α : Type u_1} [DecidableEq α] (s : finset α) : s ∪ ∅ = s :=
  ext fun (x : α) => iff.trans mem_union (or_false (x ∈ s))

@[simp] theorem empty_union {α : Type u_1} [DecidableEq α] (s : finset α) : ∅ ∪ s = s :=
  ext fun (x : α) => iff.trans mem_union (false_or (x ∈ s))

theorem insert_eq {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    insert a s = singleton a ∪ s :=
  rfl

@[simp] theorem insert_union {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) (t : finset α) :
    insert a s ∪ t = insert a (s ∪ t) :=
  sorry

@[simp] theorem union_insert {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) (t : finset α) :
    s ∪ insert a t = insert a (s ∪ t) :=
  sorry

theorem insert_union_distrib {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) (t : finset α) :
    insert a (s ∪ t) = insert a s ∪ insert a t :=
  sorry

@[simp] theorem union_eq_left_iff_subset {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : s ∪ t = s ↔ t ⊆ s :=
  { mp :=
      fun (h : s ∪ t = s) => eq.mp (Eq._oldrec (Eq.refl (t ⊆ s ∪ t)) h) (subset_union_right s t),
    mpr :=
      fun (h : t ⊆ s) => subset.antisymm (union_subset (subset.refl s) h) (subset_union_left s t) }

@[simp] theorem left_eq_union_iff_subset {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : s = s ∪ t ↔ t ⊆ s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (s = s ∪ t ↔ t ⊆ s)) (Eq.symm (propext union_eq_left_iff_subset))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s = s ∪ t ↔ s ∪ t = s)) (propext eq_comm)))
      (iff.refl (s ∪ t = s)))

@[simp] theorem union_eq_right_iff_subset {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : t ∪ s = s ↔ t ⊆ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (t ∪ s = s ↔ t ⊆ s)) (union_comm t s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ t = s ↔ t ⊆ s)) (propext union_eq_left_iff_subset)))
      (iff.refl (t ⊆ s)))

@[simp] theorem right_eq_union_iff_subset {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : s = t ∪ s ↔ t ⊆ s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (s = t ∪ s ↔ t ⊆ s)) (Eq.symm (propext union_eq_right_iff_subset))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s = t ∪ s ↔ t ∪ s = s)) (propext eq_comm)))
      (iff.refl (t ∪ s = s)))

/--
To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union {α : Type u_1} [DecidableEq α] (P : finset α → finset α → Prop)
    (symm : ∀ {a b : finset α}, P a b → P b a) (empty_right : ∀ {a : finset α}, P a ∅)
    (singletons : ∀ {a b : α}, P (singleton a) (singleton b))
    (union_of : ∀ {a b c : finset α}, P a c → P b c → P (a ∪ b) c) (a : finset α) (b : finset α) :
    P a b :=
  sorry

/-! ### inter -/

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
protected instance has_inter {α : Type u_1} [DecidableEq α] : has_inter (finset α) :=
  has_inter.mk fun (s₁ s₂ : finset α) => mk (multiset.ndinter (val s₁) (val s₂)) sorry

theorem inter_val_nd {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    val (s₁ ∩ s₂) = multiset.ndinter (val s₁) (val s₂) :=
  rfl

@[simp] theorem inter_val {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    val (s₁ ∩ s₂) = val s₁ ∩ val s₂ :=
  multiset.ndinter_eq_inter (nodup s₁)

@[simp] theorem mem_inter {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} {s₂ : finset α} :
    a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  multiset.mem_ndinter

theorem mem_of_mem_inter_left {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} {s₂ : finset α}
    (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  and.left (iff.mp mem_inter h)

theorem mem_of_mem_inter_right {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α}
    {s₂ : finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  and.right (iff.mp mem_inter h)

theorem mem_inter_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} {s₂ : finset α} :
    a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  iff.mp and_imp (iff.mpr mem_inter)

theorem inter_subset_left {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ ∩ s₂ ⊆ s₁ :=
  fun (a : α) => mem_of_mem_inter_left

theorem inter_subset_right {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ ∩ s₂ ⊆ s₂ :=
  fun (a : α) => mem_of_mem_inter_right

theorem subset_inter {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    {s₃ : finset α} : s₁ ⊆ s₂ → s₁ ⊆ s₃ → s₁ ⊆ s₂ ∩ s₃ :=
  sorry

@[simp] theorem coe_inter {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    ↑(s₁ ∩ s₂) = ↑s₁ ∩ ↑s₂ :=
  set.ext fun (_x : α) => mem_inter

@[simp] theorem union_inter_cancel_left {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : (s ∪ t) ∩ s = s :=
  sorry

@[simp] theorem union_inter_cancel_right {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : (s ∪ t) ∩ t = t :=
  sorry

theorem inter_comm {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ ∩ s₂ = s₂ ∩ s₁ :=
  sorry

@[simp] theorem inter_assoc {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
  sorry

theorem inter_left_comm {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  sorry

theorem inter_right_comm {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  sorry

@[simp] theorem inter_self {α : Type u_1} [DecidableEq α] (s : finset α) : s ∩ s = s :=
  ext fun (_x : α) => iff.trans mem_inter (and_self (_x ∈ s))

@[simp] theorem inter_empty {α : Type u_1} [DecidableEq α] (s : finset α) : s ∩ ∅ = ∅ :=
  ext fun (_x : α) => iff.trans mem_inter (and_false (_x ∈ s))

@[simp] theorem empty_inter {α : Type u_1} [DecidableEq α] (s : finset α) : ∅ ∩ s = ∅ :=
  ext fun (_x : α) => iff.trans mem_inter (false_and (_x ∈ s))

@[simp] theorem inter_union_self {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s ∩ (t ∪ s) = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ (t ∪ s) = s)) (inter_comm s (t ∪ s))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((t ∪ s) ∩ s = s)) union_inter_cancel_right)) (Eq.refl s))

@[simp] theorem insert_inter_of_mem {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    {a : α} (h : a ∈ s₂) : insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  sorry

@[simp] theorem inter_insert_of_mem {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    {a : α} (h : a ∈ s₁) : s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
  sorry

@[simp] theorem insert_inter_of_not_mem {α : Type u_1} [DecidableEq α] {s₁ : finset α}
    {s₂ : finset α} {a : α} (h : ¬a ∈ s₂) : insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  sorry

@[simp] theorem inter_insert_of_not_mem {α : Type u_1} [DecidableEq α] {s₁ : finset α}
    {s₂ : finset α} {a : α} (h : ¬a ∈ s₁) : s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s₁ ∩ insert a s₂ = s₁ ∩ s₂)) (inter_comm s₁ (insert a s₂))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (insert a s₂ ∩ s₁ = s₁ ∩ s₂)) (insert_inter_of_not_mem h)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (s₂ ∩ s₁ = s₁ ∩ s₂)) (inter_comm s₂ s₁)))
        (Eq.refl (s₁ ∩ s₂))))

@[simp] theorem singleton_inter_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    (H : a ∈ s) : singleton a ∩ s = singleton a :=
  (fun (this : insert a ∅ ∩ s = insert a ∅) => this)
    (eq.mpr (id (Eq._oldrec (Eq.refl (insert a ∅ ∩ s = insert a ∅)) (insert_inter_of_mem H)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (insert a (∅ ∩ s) = insert a ∅)) (empty_inter s)))
        (Eq.refl (insert a ∅))))

@[simp] theorem singleton_inter_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    (H : ¬a ∈ s) : singleton a ∩ s = ∅ :=
  sorry

@[simp] theorem inter_singleton_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    (h : a ∈ s) : s ∩ singleton a = singleton a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ singleton a = singleton a)) (inter_comm s (singleton a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (singleton a ∩ s = singleton a)) (singleton_inter_of_mem h)))
      (Eq.refl (singleton a)))

@[simp] theorem inter_singleton_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    (h : ¬a ∈ s) : s ∩ singleton a = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∩ singleton a = ∅)) (inter_comm s (singleton a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (singleton a ∩ s = ∅)) (singleton_inter_of_not_mem h)))
      (Eq.refl ∅))

theorem inter_subset_inter {α : Type u_1} [DecidableEq α] {x : finset α} {y : finset α}
    {s : finset α} {t : finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
  sorry

theorem inter_subset_inter_right {α : Type u_1} [DecidableEq α] {x : finset α} {y : finset α}
    {s : finset α} (h : x ⊆ y) : x ∩ s ⊆ y ∩ s :=
  inter_subset_inter h (subset.refl s)

theorem inter_subset_inter_left {α : Type u_1} [DecidableEq α] {x : finset α} {y : finset α}
    {s : finset α} (h : x ⊆ y) : s ∩ x ⊆ s ∩ y :=
  inter_subset_inter (subset.refl s) h

/-! ### lattice laws -/

protected instance lattice {α : Type u_1} [DecidableEq α] : lattice (finset α) :=
  lattice.mk has_union.union partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry
    has_inter.inter sorry sorry sorry

@[simp] theorem sup_eq_union {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s ⊔ t = s ∪ t :=
  rfl

@[simp] theorem inf_eq_inter {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s ⊓ t = s ∩ t :=
  rfl

protected instance semilattice_inf_bot {α : Type u_1} [DecidableEq α] :
    semilattice_inf_bot (finset α) :=
  semilattice_inf_bot.mk ∅ lattice.le lattice.lt sorry sorry sorry empty_subset lattice.inf sorry
    sorry sorry

protected instance semilattice_sup_bot {α : Type u_1} [DecidableEq α] :
    semilattice_sup_bot (finset α) :=
  semilattice_sup_bot.mk semilattice_inf_bot.bot semilattice_inf_bot.le semilattice_inf_bot.lt sorry
    sorry sorry sorry lattice.sup sorry sorry sorry

protected instance distrib_lattice {α : Type u_1} [DecidableEq α] : distrib_lattice (finset α) :=
  distrib_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry
    lattice.inf sorry sorry sorry sorry

theorem inter_distrib_left {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α)
    (u : finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left

theorem inter_distrib_right {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α)
    (u : finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right

theorem union_distrib_left {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α)
    (u : finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left

theorem union_distrib_right {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α)
    (u : finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right

theorem union_eq_empty_iff {α : Type u_1} [DecidableEq α] (A : finset α) (B : finset α) :
    A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ :=
  sup_eq_bot_iff

/-! ### erase -/

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase {α : Type u_1} [DecidableEq α] (s : finset α) (a : α) : finset α :=
  mk (multiset.erase (val s) a) sorry

@[simp] theorem erase_val {α : Type u_1} [DecidableEq α] (s : finset α) (a : α) :
    val (erase s a) = multiset.erase (val s) a :=
  rfl

@[simp] theorem mem_erase {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α} :
    a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
  multiset.mem_erase_iff_of_nodup (nodup s)

theorem not_mem_erase {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) : ¬a ∈ erase s a :=
  multiset.mem_erase_of_nodup (nodup s)

@[simp] theorem erase_empty {α : Type u_1} [DecidableEq α] (a : α) : erase ∅ a = ∅ := rfl

theorem ne_of_mem_erase {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α} :
    b ∈ erase s a → b ≠ a :=
  eq.mpr (id (imp_congr_eq (propext mem_erase) (Eq.refl (b ≠ a)))) and.left

theorem mem_of_mem_erase {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α} :
    b ∈ erase s a → b ∈ s :=
  multiset.mem_of_mem_erase

theorem mem_erase_of_ne_of_mem {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α} :
    a ≠ b → a ∈ s → a ∈ erase s b :=
  eq.mpr (id (imp_congr_eq (Eq.refl (a ≠ b)) (imp_congr_eq (Eq.refl (a ∈ s)) (propext mem_erase))))
    And.intro

/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
theorem eq_of_mem_of_not_mem_erase {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : finset α}
    (hs : b ∈ s) (hsa : ¬b ∈ erase s a) : b = a :=
  sorry

theorem erase_insert {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : ¬a ∈ s) :
    erase (insert a s) a = s :=
  sorry

theorem insert_erase {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : a ∈ s) :
    insert a (erase s a) = s :=
  sorry

theorem erase_subset_erase {α : Type u_1} [DecidableEq α] (a : α) {s : finset α} {t : finset α}
    (h : s ⊆ t) : erase s a ⊆ erase t a :=
  iff.mp val_le_iff (multiset.erase_le_erase a (iff.mpr val_le_iff h))

theorem erase_subset {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) : erase s a ⊆ s :=
  multiset.erase_subset a (val s)

@[simp] theorem coe_erase {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    ↑(erase s a) = ↑s \ singleton a :=
  sorry

theorem erase_ssubset {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : a ∈ s) :
    erase s a ⊂ s :=
  trans_rel_left has_ssubset.ssubset (ssubset_insert (not_mem_erase a s)) (insert_erase h)

theorem erase_eq_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : ¬a ∈ s) :
    erase s a = s :=
  eq_of_veq (multiset.erase_of_not_mem h)

theorem subset_insert_iff {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} {t : finset α} :
    s ⊆ insert a t ↔ erase s a ⊆ t :=
  sorry

theorem erase_insert_subset {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    erase (insert a s) a ⊆ s :=
  iff.mp subset_insert_iff (subset.refl (insert a s))

theorem insert_erase_subset {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    s ⊆ insert a (erase s a) :=
  iff.mpr subset_insert_iff (subset.refl (erase s a))

/-! ### sdiff -/

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
protected instance has_sdiff {α : Type u_1} [DecidableEq α] : has_sdiff (finset α) :=
  has_sdiff.mk fun (s₁ s₂ : finset α) => mk (val s₁ - val s₂) sorry

@[simp] theorem mem_sdiff {α : Type u_1} [DecidableEq α] {a : α} {s₁ : finset α} {s₂ : finset α} :
    a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ ¬a ∈ s₂ :=
  multiset.mem_sub_of_nodup (nodup s₁)

theorem not_mem_sdiff_of_mem_right {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    {t : finset α} (h : a ∈ t) : ¬a ∈ s \ t :=
  sorry

theorem sdiff_union_of_subset {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ :=
  sorry

theorem union_sdiff_of_subset {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    (h : s₁ ⊆ s₂) : s₁ ∪ s₂ \ s₁ = s₂ :=
  Eq.trans (union_comm s₁ (s₂ \ s₁)) (sdiff_union_of_subset h)

theorem inter_sdiff {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) (u : finset α) :
    s ∩ (t \ u) = s ∩ t \ u :=
  sorry

@[simp] theorem inter_sdiff_self {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ ∩ (s₂ \ s₁) = ∅ :=
  sorry

@[simp] theorem sdiff_inter_self {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₂ \ s₁ ∩ s₁ = ∅ :=
  Eq.trans (inter_comm (s₂ \ s₁) s₁) (inter_sdiff_self s₁ s₂)

@[simp] theorem sdiff_self {α : Type u_1} [DecidableEq α] (s₁ : finset α) : s₁ \ s₁ = ∅ := sorry

theorem sdiff_inter_distrib_right {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (s₃ : finset α) : s₁ \ (s₂ ∩ s₃) = s₁ \ s₂ ∪ s₁ \ s₃ :=
  sorry

@[simp] theorem sdiff_inter_self_left {α : Type u_1} [DecidableEq α] (s₁ : finset α)
    (s₂ : finset α) : s₁ \ (s₁ ∩ s₂) = s₁ \ s₂ :=
  sorry

@[simp] theorem sdiff_inter_self_right {α : Type u_1} [DecidableEq α] (s₁ : finset α)
    (s₂ : finset α) : s₁ \ (s₂ ∩ s₁) = s₁ \ s₂ :=
  sorry

@[simp] theorem sdiff_empty {α : Type u_1} [DecidableEq α] {s₁ : finset α} : s₁ \ ∅ = s₁ := sorry

theorem sdiff_subset_sdiff {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α}
    {t₁ : finset α} {t₂ : finset α} (h₁ : t₁ ⊆ t₂) (h₂ : s₂ ⊆ s₁) : t₁ \ s₁ ⊆ t₂ \ s₂ :=
  sorry

theorem sdiff_subset_self {α : Type u_1} [DecidableEq α] {s₁ : finset α} {s₂ : finset α} :
    s₁ \ s₂ ⊆ s₁ :=
  sorry

@[simp] theorem coe_sdiff {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    ↑(s₁ \ s₂) = ↑s₁ \ ↑s₂ :=
  set.ext fun (_x : α) => mem_sdiff

@[simp] theorem union_sdiff_self_eq_union {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : s ∪ t \ s = s ∪ t :=
  sorry

@[simp] theorem sdiff_union_self_eq_union {α : Type u_1} [DecidableEq α] {s : finset α}
    {t : finset α} : s \ t ∪ t = s ∪ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ∪ t = s ∪ t)) (union_comm (s \ t) t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t ∪ s \ t = s ∪ t)) union_sdiff_self_eq_union))
      (eq.mpr (id (Eq._oldrec (Eq.refl (t ∪ s = s ∪ t)) (union_comm t s))) (Eq.refl (s ∪ t))))

theorem union_sdiff_symm {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    s ∪ t \ s = t ∪ s \ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ t \ s = t ∪ s \ t)) union_sdiff_self_eq_union))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ t = t ∪ s \ t)) union_sdiff_self_eq_union))
      (eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ t = t ∪ s)) (union_comm s t))) (Eq.refl (t ∪ s))))

theorem sdiff_union_inter {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s \ t ∪ s ∩ t = s :=
  sorry

@[simp] theorem sdiff_idem {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s \ t \ t = s \ t :=
  sorry

theorem sdiff_eq_empty_iff_subset {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    s \ t = ∅ ↔ s ⊆ t :=
  sorry

@[simp] theorem empty_sdiff {α : Type u_1} [DecidableEq α] (s : finset α) : ∅ \ s = ∅ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (∅ \ s = ∅)) (propext sdiff_eq_empty_iff_subset)))
    (empty_subset s)

theorem insert_sdiff_of_not_mem {α : Type u_1} [DecidableEq α] (s : finset α) {t : finset α} {x : α}
    (h : ¬x ∈ t) : insert x s \ t = insert x (s \ t) :=
  sorry

theorem insert_sdiff_of_mem {α : Type u_1} [DecidableEq α] (s : finset α) {t : finset α} {x : α}
    (h : x ∈ t) : insert x s \ t = s \ t :=
  sorry

@[simp] theorem insert_sdiff_insert {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α)
    (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem s (mem_insert_self x t)

theorem sdiff_insert_of_not_mem {α : Type u_1} [DecidableEq α] {s : finset α} {x : α} (h : ¬x ∈ s)
    (t : finset α) : s \ insert x t = s \ t :=
  sorry

@[simp] theorem sdiff_subset {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s \ t ⊆ s :=
  sorry

theorem union_sdiff_distrib {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α)
    (t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sorry

theorem sdiff_union_distrib {α : Type u_1} [DecidableEq α] (s : finset α) (t₁ : finset α)
    (t₂ : finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sorry

theorem union_sdiff_self {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    (s ∪ t) \ t = s \ t :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((s ∪ t) \ t = s \ t)) (union_sdiff_distrib s t t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ∪ t \ t = s \ t)) (sdiff_self t)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (s \ t ∪ ∅ = s \ t)) (union_empty (s \ t))))
        (Eq.refl (s \ t))))

theorem sdiff_singleton_eq_erase {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    s \ singleton a = erase s a :=
  sorry

theorem sdiff_sdiff_self_left {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    s \ (s \ t) = s ∩ t :=
  sorry

theorem inter_eq_inter_of_sdiff_eq_sdiff {α : Type u_1} [DecidableEq α] {s : finset α}
    {t₁ : finset α} {t₂ : finset α} : s \ t₁ = s \ t₂ → s ∩ t₁ = s ∩ t₂ :=
  sorry

/-! ### attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the
  subtype `{x // x ∈ s}`. -/
def attach {α : Type u_1} (s : finset α) : finset (Subtype fun (x : α) => x ∈ s) :=
  mk (multiset.attach (val s)) sorry

theorem sizeof_lt_sizeof_of_mem {α : Type u_1} [SizeOf α] {x : α} {s : finset α} (hx : x ∈ s) :
    sizeof x < sizeof s :=
  sorry

@[simp] theorem attach_val {α : Type u_1} (s : finset α) :
    val (attach s) = multiset.attach (val s) :=
  rfl

@[simp] theorem mem_attach {α : Type u_1} (s : finset α) (x : Subtype fun (x : α) => x ∈ s) :
    x ∈ attach s :=
  multiset.mem_attach (val s)

@[simp] theorem attach_empty {α : Type u_1} : attach ∅ = ∅ := rfl

/-! ### piecewise -/

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type u_1} {δ : α → Sort u_2} (s : finset α) (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] (i : α) : δ i :=
  ite (i ∈ s) (f i) (g i)

@[simp] theorem piecewise_insert_self {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    (f : (i : α) → δ i) (g : (i : α) → δ i) [DecidableEq α] {j : α}
    [(i : α) → Decidable (i ∈ insert j s)] : piecewise (insert j s) f g j = f j :=
  sorry

@[simp] theorem piecewise_empty {α : Type u_1} {δ : α → Sort u_4} (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(i : α) → Decidable (i ∈ ∅)] : piecewise ∅ f g = g :=
  sorry

theorem piecewise_coe {α : Type u_1} {δ : α → Sort u_4} (s : finset α) (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [(j : α) → Decidable (j ∈ ↑s)] :
    set.piecewise (↑s) f g = piecewise s f g :=
  sorry

@[simp] theorem piecewise_eq_of_mem {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] {i : α} (hi : i ∈ s) :
    piecewise s f g i = f i :=
  sorry

@[simp] theorem piecewise_eq_of_not_mem {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] {i : α} (hi : ¬i ∈ s) :
    piecewise s f g i = g i :=
  sorry

theorem piecewise_congr {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    [(j : α) → Decidable (j ∈ s)] {f : (i : α) → δ i} {f' : (i : α) → δ i} {g : (i : α) → δ i}
    {g' : (i : α) → δ i} (hf : ∀ (i : α), i ∈ s → f i = f' i)
    (hg : ∀ (i : α), ¬i ∈ s → g i = g' i) : piecewise s f g = piecewise s f' g' :=
  funext fun (i : α) => if_ctx_congr iff.rfl (hf i) (hg i)

@[simp] theorem piecewise_insert_of_ne {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [DecidableEq α] {i : α}
    {j : α} [(i : α) → Decidable (i ∈ insert j s)] (h : i ≠ j) :
    piecewise (insert j s) f g i = piecewise s f g i :=
  sorry

theorem piecewise_insert {α : Type u_1} {δ : α → Sort u_4} (s : finset α) (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [DecidableEq α] (j : α)
    [(i : α) → Decidable (i ∈ insert j s)] :
    piecewise (insert j s) f g = function.update (piecewise s f g) j (f j) :=
  sorry

theorem piecewise_cases {α : Type u_1} {δ : α → Sort u_4} (s : finset α) (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] {i : α} (p : δ i → Prop) (hf : p (f i))
    (hg : p (g i)) : p (piecewise s f g i) :=
  sorry

theorem piecewise_mem_set_pi {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} {t : set α} {t' : (i : α) → set (δ i)} {f : (i : α) → δ i}
    {g : (i : α) → δ i} (hf : f ∈ set.pi t t') (hg : g ∈ set.pi t t') :
    piecewise s f g ∈ set.pi t t' :=
  eq.mpr (id (Eq._oldrec (Eq.refl (piecewise s f g ∈ set.pi t t')) (Eq.symm (piecewise_coe s f g))))
    (set.piecewise_mem_pi (↑s) hf hg)

theorem piecewise_singleton {α : Type u_1} {δ : α → Sort u_4} (f : (i : α) → δ i)
    (g : (i : α) → δ i) [DecidableEq α] (i : α) :
    piecewise (singleton i) f g = function.update g i (f i) :=
  sorry

theorem piecewise_piecewise_of_subset_left {α : Type u_1} {δ : α → Sort u_4} {s : finset α}
    {t : finset α} [(i : α) → Decidable (i ∈ s)] [(i : α) → Decidable (i ∈ t)] (h : s ⊆ t)
    (f₁ : (a : α) → δ a) (f₂ : (a : α) → δ a) (g : (a : α) → δ a) :
    piecewise s (piecewise t f₁ f₂) g = piecewise s f₁ g :=
  piecewise_congr s (fun (i : α) (hi : i ∈ s) => piecewise_eq_of_mem t f₁ f₂ (h hi))
    fun (_x : α) (_x_1 : ¬_x ∈ s) => rfl

@[simp] theorem piecewise_idem_left {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    [(j : α) → Decidable (j ∈ s)] (f₁ : (a : α) → δ a) (f₂ : (a : α) → δ a) (g : (a : α) → δ a) :
    piecewise s (piecewise s f₁ f₂) g = piecewise s f₁ g :=
  piecewise_piecewise_of_subset_left (subset.refl s) f₁ f₂ g

theorem piecewise_piecewise_of_subset_right {α : Type u_1} {δ : α → Sort u_4} {s : finset α}
    {t : finset α} [(i : α) → Decidable (i ∈ s)] [(i : α) → Decidable (i ∈ t)] (h : t ⊆ s)
    (f : (a : α) → δ a) (g₁ : (a : α) → δ a) (g₂ : (a : α) → δ a) :
    piecewise s f (piecewise t g₁ g₂) = piecewise s f g₂ :=
  piecewise_congr s (fun (_x : α) (_x_1 : _x ∈ s) => rfl)
    fun (i : α) (hi : ¬i ∈ s) => piecewise_eq_of_not_mem t g₁ g₂ (mt h hi)

@[simp] theorem piecewise_idem_right {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    [(j : α) → Decidable (j ∈ s)] (f : (a : α) → δ a) (g₁ : (a : α) → δ a) (g₂ : (a : α) → δ a) :
    piecewise s f (piecewise s g₁ g₂) = piecewise s f g₂ :=
  piecewise_piecewise_of_subset_right (subset.refl s) f g₁ g₂

theorem update_eq_piecewise {α : Type u_1} {β : Type u_2} [DecidableEq α] (f : α → β) (i : α)
    (v : β) : function.update f i v = piecewise (singleton i) (fun (j : α) => v) f :=
  Eq.symm (piecewise_singleton (fun (i : α) => v) f i)

theorem update_piecewise {α : Type u_1} {δ : α → Sort u_4} (s : finset α) (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [DecidableEq α] (i : α) (v : δ i) :
    function.update (piecewise s f g) i v =
        piecewise s (function.update f i v) (function.update g i v) :=
  sorry

theorem update_piecewise_of_mem {α : Type u_1} {δ : α → Sort u_4} (s : finset α) (f : (i : α) → δ i)
    (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [DecidableEq α] {i : α} (hi : i ∈ s)
    (v : δ i) : function.update (piecewise s f g) i v = piecewise s (function.update f i v) g :=
  sorry

theorem update_piecewise_of_not_mem {α : Type u_1} {δ : α → Sort u_4} (s : finset α)
    (f : (i : α) → δ i) (g : (i : α) → δ i) [(j : α) → Decidable (j ∈ s)] [DecidableEq α] {i : α}
    (hi : ¬i ∈ s) (v : δ i) :
    function.update (piecewise s f g) i v = piecewise s f (function.update g i v) :=
  sorry

theorem piecewise_le_of_le_of_le {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {g : (i : α) → δ i}
    {h : (i : α) → δ i} (Hf : f ≤ h) (Hg : g ≤ h) : piecewise s f g ≤ h :=
  fun (x : α) => piecewise_cases s f g (fun (_x : δ x) => _x ≤ h x) (Hf x) (Hg x)

theorem le_piecewise_of_le_of_le {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {g : (i : α) → δ i}
    {h : (i : α) → δ i} (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ piecewise s f g :=
  fun (x : α) => piecewise_cases s f g (fun (y : δ x) => h x ≤ y) (Hf x) (Hg x)

theorem piecewise_le_piecewise' {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {g : (i : α) → δ i}
    {f' : (i : α) → δ i} {g' : (i : α) → δ i} (Hf : ∀ (x : α), x ∈ s → f x ≤ f' x)
    (Hg : ∀ (x : α), ¬x ∈ s → g x ≤ g' x) : piecewise s f g ≤ piecewise s f' g' :=
  sorry

theorem piecewise_le_piecewise {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {g : (i : α) → δ i}
    {f' : (i : α) → δ i} {g' : (i : α) → δ i} (Hf : f ≤ f') (Hg : g ≤ g') :
    piecewise s f g ≤ piecewise s f' g' :=
  piecewise_le_piecewise' s (fun (x : α) (_x : x ∈ s) => Hf x) fun (x : α) (_x : ¬x ∈ s) => Hg x

theorem piecewise_mem_Icc_of_mem_of_mem {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {f₁ : (i : α) → δ i}
    {g : (i : α) → δ i} {g₁ : (i : α) → δ i} (hf : f ∈ set.Icc f₁ g₁) (hg : g ∈ set.Icc f₁ g₁) :
    piecewise s f g ∈ set.Icc f₁ g₁ :=
  { left := le_piecewise_of_le_of_le s (and.left hf) (and.left hg),
    right := piecewise_le_of_le_of_le s (and.right hf) (and.right hg) }

theorem piecewise_mem_Icc {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {g : (i : α) → δ i}
    (h : f ≤ g) : piecewise s f g ∈ set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem s (iff.mpr set.left_mem_Icc h) (iff.mpr set.right_mem_Icc h)

theorem piecewise_mem_Icc' {α : Type u_1} (s : finset α) [(j : α) → Decidable (j ∈ s)]
    {δ : α → Type u_2} [(i : α) → preorder (δ i)] {f : (i : α) → δ i} {g : (i : α) → δ i}
    (h : g ≤ f) : piecewise s f g ∈ set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem s (iff.mpr set.right_mem_Icc h) (iff.mpr set.left_mem_Icc h)

protected instance decidable_dforall_finset {α : Type u_1} {s : finset α}
    {p : (a : α) → a ∈ s → Prop} [hp : (a : α) → (h : a ∈ s) → Decidable (p a h)] :
    Decidable (∀ (a : α) (h : a ∈ s), p a h) :=
  multiset.decidable_dforall_multiset

/-- decidable equality for functions whose domain is bounded by finsets -/
protected instance decidable_eq_pi_finset {α : Type u_1} {s : finset α} {β : α → Type u_2}
    [h : (a : α) → DecidableEq (β a)] : DecidableEq ((a : α) → a ∈ s → β a) :=
  multiset.decidable_eq_pi_multiset

protected instance decidable_dexists_finset {α : Type u_1} {s : finset α}
    {p : (a : α) → a ∈ s → Prop} [hp : (a : α) → (h : a ∈ s) → Decidable (p a h)] :
    Decidable (∃ (a : α), ∃ (h : a ∈ s), p a h) :=
  multiset.decidable_dexists_multiset

/-! ### filter -/

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : finset α) : finset α :=
  mk (multiset.filter p (val s)) sorry

@[simp] theorem filter_val {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : finset α) :
    val (filter p s) = multiset.filter p (val s) :=
  rfl

@[simp] theorem filter_subset {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : finset α) :
    filter p s ⊆ s :=
  multiset.filter_subset p (val s)

@[simp] theorem mem_filter {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : finset α} {a : α} :
    a ∈ filter p s ↔ a ∈ s ∧ p a :=
  multiset.mem_filter

theorem filter_ssubset {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : finset α} :
    filter p s ⊂ s ↔ ∃ (x : α), ∃ (H : x ∈ s), ¬p x :=
  sorry

theorem filter_filter {α : Type u_1} (p : α → Prop) (q : α → Prop) [decidable_pred p]
    [decidable_pred q] (s : finset α) :
    filter q (filter p s) = filter (fun (a : α) => p a ∧ q a) s :=
  sorry

theorem filter_true {α : Type u_1} {s : finset α} [h : decidable_pred fun (_x : α) => True] :
    filter (fun (_x : α) => True) s = s :=
  sorry

@[simp] theorem filter_false {α : Type u_1} {h : decidable_pred fun (a : α) => False}
    (s : finset α) : filter (fun (a : α) => False) s = ∅ :=
  sorry

/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp] theorem filter_true_of_mem {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : finset α}
    (h : ∀ (x : α), x ∈ s → p x) : filter p s = s :=
  sorry

/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : finset α}
    (h : ∀ (x : α), x ∈ s → ¬p x) : filter p s = ∅ :=
  sorry

theorem filter_congr {α : Type u_1} {p : α → Prop} {q : α → Prop} [decidable_pred p]
    [decidable_pred q] {s : finset α} (H : ∀ (x : α), x ∈ s → (p x ↔ q x)) :
    filter p s = filter q s :=
  eq_of_veq (multiset.filter_congr H)

theorem filter_empty {α : Type u_1} (p : α → Prop) [decidable_pred p] : filter p ∅ = ∅ :=
  iff.mp subset_empty (filter_subset p ∅)

theorem filter_subset_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] {s : finset α}
    {t : finset α} (h : s ⊆ t) : filter p s ⊆ filter p t :=
  fun (a : α) (ha : a ∈ filter p s) =>
    iff.mpr mem_filter
      { left := h (and.left (iff.mp mem_filter ha)), right := and.right (iff.mp mem_filter ha) }

@[simp] theorem coe_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : finset α) :
    ↑(filter p s) = has_sep.sep (fun (x : α) => p x) ↑s :=
  set.ext fun (_x : α) => mem_filter

theorem filter_singleton {α : Type u_1} (p : α → Prop) [decidable_pred p] (a : α) :
    filter p (singleton a) = ite (p a) (singleton a) ∅ :=
  sorry

theorem filter_union {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α]
    (s₁ : finset α) (s₂ : finset α) : filter p (s₁ ∪ s₂) = filter p s₁ ∪ filter p s₂ :=
  sorry

theorem filter_union_right {α : Type u_1} (p : α → Prop) (q : α → Prop) [decidable_pred p]
    [decidable_pred q] [DecidableEq α] (s : finset α) :
    filter p s ∪ filter q s = filter (fun (x : α) => p x ∨ q x) s :=
  sorry

theorem filter_mem_eq_inter {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    [(i : α) → Decidable (i ∈ t)] : filter (fun (i : α) => i ∈ t) s = s ∩ t :=
  sorry

theorem filter_inter {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] (s : finset α)
    (t : finset α) : filter p s ∩ t = filter p (s ∩ t) :=
  sorry

theorem inter_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] (s : finset α)
    (t : finset α) : s ∩ filter p t = filter p (s ∩ t) :=
  sorry

theorem filter_insert {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] (a : α)
    (s : finset α) : filter p (insert a s) = ite (p a) (insert a (filter p s)) (filter p s) :=
  sorry

theorem filter_or {α : Type u_1} (p : α → Prop) (q : α → Prop) [decidable_pred p] [decidable_pred q]
    [DecidableEq α] [decidable_pred fun (a : α) => p a ∨ q a] (s : finset α) :
    filter (fun (a : α) => p a ∨ q a) s = filter p s ∪ filter q s :=
  sorry

theorem filter_and {α : Type u_1} (p : α → Prop) (q : α → Prop) [decidable_pred p]
    [decidable_pred q] [DecidableEq α] [decidable_pred fun (a : α) => p a ∧ q a] (s : finset α) :
    filter (fun (a : α) => p a ∧ q a) s = filter p s ∩ filter q s :=
  sorry

theorem filter_not {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α]
    [decidable_pred fun (a : α) => ¬p a] (s : finset α) :
    filter (fun (a : α) => ¬p a) s = s \ filter p s :=
  sorry

theorem sdiff_eq_filter {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ \ s₂ = filter (fun (_x : α) => ¬_x ∈ s₂) s₁ :=
  sorry

theorem sdiff_eq_self {α : Type u_1} [DecidableEq α] (s₁ : finset α) (s₂ : finset α) :
    s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ :=
  sorry

theorem filter_union_filter_neg_eq {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α]
    [decidable_pred fun (a : α) => ¬p a] (s : finset α) :
    filter p s ∪ filter (fun (a : α) => ¬p a) s = s :=
  sorry

theorem filter_inter_filter_neg_eq {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α]
    (s : finset α) : filter p s ∩ filter (fun (a : α) => ¬p a) s = ∅ :=
  sorry

theorem subset_union_elim {α : Type u_1} [DecidableEq α] {s : finset α} {t₁ : set α} {t₂ : set α}
    (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ (s₁ : finset α), ∃ (s₂ : finset α), s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ :=
  sorry

/- We can simplify an application of filter where the decidability is inferred in "the wrong way" -/

@[simp] theorem filter_congr_decidable {α : Type u_1} (s : finset α) (p : α → Prop)
    (h : decidable_pred p) [decidable_pred p] : filter p s = filter p s :=
  sorry

/-- The following instance allows us to write `{ x ∈ s | p x }` for `finset.filter s p`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{ x ∈ s | p x }` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{ x ∈ s | p x }` to `finset.filter s p`. If `p` happens to be decidable, the
  simp-lemma `filter_congr_decidable` will make sure that `finset.filter` uses the right instance
  for decidability.
-/
protected instance has_sep {α : Type u_1} : has_sep α (finset α) :=
  has_sep.mk fun (p : α → Prop) (x : finset α) => filter p x

@[simp] theorem sep_def {α : Type u_1} (s : finset α) (p : α → Prop) :
    has_sep.sep (fun (x : α) => p x) s = filter p s :=
  rfl

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
-- This is not a good simp lemma, as it would prevent `finset.mem_filter` from firing

-- on, e.g. `x ∈ s.filter(eq b)`.

theorem filter_eq {β : Type u_2} [DecidableEq β] (s : finset β) (b : β) :
    filter (Eq b) s = ite (b ∈ s) (singleton b) ∅ :=
  sorry

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' {β : Type u_2} [DecidableEq β] (s : finset β) (b : β) :
    filter (fun (a : β) => a = b) s = ite (b ∈ s) (singleton b) ∅ :=
  trans (filter_congr fun (_x : β) (_x_1 : _x ∈ s) => { mp := Eq.symm, mpr := Eq.symm })
    (filter_eq s b)

theorem filter_ne {β : Type u_2} [DecidableEq β] (s : finset β) (b : β) :
    filter (fun (a : β) => b ≠ a) s = erase s b :=
  sorry

theorem filter_ne' {β : Type u_2} [DecidableEq β] (s : finset β) (b : β) :
    filter (fun (a : β) => a ≠ b) s = erase s b :=
  trans (filter_congr fun (_x : β) (_x_1 : _x ∈ s) => { mp := ne.symm, mpr := ne.symm })
    (filter_ne s b)

/-! ### range -/

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : finset ℕ := mk (multiset.range n) (multiset.nodup_range n)

@[simp] theorem range_coe (n : ℕ) : val (range n) = multiset.range n := rfl

@[simp] theorem mem_range {n : ℕ} {m : ℕ} : m ∈ range n ↔ m < n := multiset.mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_one : range 1 = singleton 0 := rfl

theorem range_succ {n : ℕ} : range (Nat.succ n) = insert n (range n) :=
  eq_of_veq
    (Eq.trans (multiset.range_succ n)
      (Eq.symm (multiset.ndinsert_of_not_mem multiset.not_mem_range_self)))

theorem range_add_one {n : ℕ} : range (n + 1) = insert n (range n) := range_succ

@[simp] theorem not_mem_range_self {n : ℕ} : ¬n ∈ range n := multiset.not_mem_range_self

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := multiset.self_mem_range_succ n

@[simp] theorem range_subset {n : ℕ} {m : ℕ} : range n ⊆ range m ↔ n ≤ m := multiset.range_subset

theorem range_mono : monotone range := fun (_x _x_1 : ℕ) => iff.mpr range_subset

theorem mem_range_succ_iff {a : ℕ} {b : ℕ} : a ∈ range (Nat.succ b) ↔ a ≤ b :=
  iff.trans mem_range nat.lt_succ_iff

/- useful rules for calculations with quantifiers -/

theorem exists_mem_empty_iff {α : Type u_1} (p : α → Prop) : (∃ (x : α), x ∈ ∅ ∧ p x) ↔ False :=
  sorry

theorem exists_mem_insert {α : Type u_1} [d : DecidableEq α] (a : α) (s : finset α) (p : α → Prop) :
    (∃ (x : α), x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ (x : α), x ∈ s ∧ p x :=
  sorry

theorem forall_mem_empty_iff {α : Type u_1} (p : α → Prop) : (∀ (x : α), x ∈ ∅ → p x) ↔ True :=
  iff_true_intro fun (_x : α) => false.elim

theorem forall_mem_insert {α : Type u_1} [d : DecidableEq α] (a : α) (s : finset α) (p : α → Prop) :
    (∀ (x : α), x ∈ insert a s → p x) ↔ p a ∧ ∀ (x : α), x ∈ s → p x :=
  sorry

end finset


/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def not_mem_range_equiv (k : ℕ) : (Subtype fun (n : ℕ) => ¬n ∈ multiset.range k) ≃ ℕ :=
  equiv.mk (fun (i : Subtype fun (n : ℕ) => ¬n ∈ multiset.range k) => subtype.val i - k)
    (fun (j : ℕ) => { val := j + k, property := sorry }) sorry sorry

@[simp] theorem coe_not_mem_range_equiv (k : ℕ) :
    ⇑(not_mem_range_equiv k) = fun (i : Subtype fun (n : ℕ) => ¬n ∈ multiset.range k) => ↑i - k :=
  rfl

@[simp] theorem coe_not_mem_range_equiv_symm (k : ℕ) :
    ⇑(equiv.symm (not_mem_range_equiv k)) =
        fun (j : ℕ) =>
          { val := j + k,
            property :=
              eq.mpr
                (id
                  (Eq.trans
                    (Eq.trans
                      ((fun (a a_1 : Prop) (e_1 : a = a_1) => congr_arg Not e_1)
                        (j + k ∈ multiset.range k) (j < 0)
                        (Eq.trans (propext multiset.mem_range) (propext add_lt_iff_neg_right)))
                      (propext not_lt))
                    (propext ((fun {α : Type} (a : α) => iff_true_intro (zero_le a)) j))))
                trivial } :=
  rfl

namespace option


/-- Construct an empty or singleton finset from an `option` -/
def to_finset {α : Type u_1} (o : Option α) : finset α := sorry

@[simp] theorem to_finset_none {α : Type u_1} : to_finset none = ∅ := rfl

@[simp] theorem to_finset_some {α : Type u_1} {a : α} : to_finset (some a) = singleton a := rfl

@[simp] theorem mem_to_finset {α : Type u_1} {a : α} {o : Option α} : a ∈ to_finset o ↔ a ∈ o :=
  sorry

end option


/-! ### erase_dup on list and multiset -/

namespace multiset


/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def to_finset {α : Type u_1} [DecidableEq α] (s : multiset α) : finset α :=
  finset.mk (erase_dup s) sorry

@[simp] theorem to_finset_val {α : Type u_1} [DecidableEq α] (s : multiset α) :
    finset.val (to_finset s) = erase_dup s :=
  rfl

theorem to_finset_eq {α : Type u_1} [DecidableEq α] {s : multiset α} (n : nodup s) :
    finset.mk s n = to_finset s :=
  iff.mp finset.val_inj (Eq.symm (iff.mpr erase_dup_eq_self n))

@[simp] theorem mem_to_finset {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} :
    a ∈ to_finset s ↔ a ∈ s :=
  mem_erase_dup

@[simp] theorem to_finset_zero {α : Type u_1} [DecidableEq α] : to_finset 0 = ∅ := rfl

@[simp] theorem to_finset_cons {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) :
    to_finset (a ::ₘ s) = insert a (to_finset s) :=
  finset.eq_of_veq erase_dup_cons

@[simp] theorem to_finset_add {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    to_finset (s + t) = to_finset s ∪ to_finset t :=
  sorry

@[simp] theorem to_finset_nsmul {α : Type u_1} [DecidableEq α] (s : multiset α) (n : ℕ)
    (hn : n ≠ 0) : to_finset (n •ℕ s) = to_finset s :=
  sorry

@[simp] theorem to_finset_inter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    to_finset (s ∩ t) = to_finset s ∩ to_finset t :=
  sorry

@[simp] theorem to_finset_union {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) :
    to_finset (s ∪ t) = to_finset s ∪ to_finset t :=
  sorry

theorem to_finset_eq_empty {α : Type u_1} [DecidableEq α] {m : multiset α} :
    to_finset m = ∅ ↔ m = 0 :=
  iff.trans (iff.symm finset.val_inj) erase_dup_eq_zero

@[simp] theorem to_finset_subset {α : Type u_1} [DecidableEq α] (m1 : multiset α)
    (m2 : multiset α) : to_finset m1 ⊆ to_finset m2 ↔ m1 ⊆ m2 :=
  sorry

end multiset


namespace finset


@[simp] theorem val_to_finset {α : Type u_1} [DecidableEq α] (s : finset α) :
    multiset.to_finset (val s) = s :=
  sorry

end finset


namespace list


/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset {α : Type u_1} [DecidableEq α] (l : List α) : finset α := multiset.to_finset ↑l

@[simp] theorem to_finset_val {α : Type u_1} [DecidableEq α] (l : List α) :
    finset.val (to_finset l) = ↑(erase_dup l) :=
  rfl

theorem to_finset_eq {α : Type u_1} [DecidableEq α] {l : List α} (n : nodup l) :
    finset.mk (↑l) n = to_finset l :=
  multiset.to_finset_eq n

@[simp] theorem mem_to_finset {α : Type u_1} [DecidableEq α] {a : α} {l : List α} :
    a ∈ to_finset l ↔ a ∈ l :=
  mem_erase_dup

@[simp] theorem to_finset_nil {α : Type u_1} [DecidableEq α] : to_finset [] = ∅ := rfl

@[simp] theorem to_finset_cons {α : Type u_1} [DecidableEq α] {a : α} {l : List α} :
    to_finset (a :: l) = insert a (to_finset l) :=
  sorry

theorem to_finset_surj_on {α : Type u_1} [DecidableEq α] :
    set.surj_on to_finset (set_of fun (l : List α) => nodup l) set.univ :=
  sorry

theorem to_finset_surjective {α : Type u_1} [DecidableEq α] : function.surjective to_finset := sorry

end list


namespace finset


/-! ### map -/

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map {α : Type u_1} {β : Type u_2} (f : α ↪ β) (s : finset α) : finset β :=
  mk (multiset.map (⇑f) (val s)) sorry

@[simp] theorem map_val {α : Type u_1} {β : Type u_2} (f : α ↪ β) (s : finset α) :
    val (map f s) = multiset.map (⇑f) (val s) :=
  rfl

@[simp] theorem map_empty {α : Type u_1} {β : Type u_2} (f : α ↪ β) : map f ∅ = ∅ := rfl

@[simp] theorem mem_map {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s : finset α} {b : β} :
    b ∈ map f s ↔ ∃ (a : α), ∃ (H : a ∈ s), coe_fn f a = b :=
  sorry

theorem mem_map' {α : Type u_1} {β : Type u_2} (f : α ↪ β) {a : α} {s : finset α} :
    coe_fn f a ∈ map f s ↔ a ∈ s :=
  multiset.mem_map_of_injective (function.embedding.inj' f)

theorem mem_map_of_mem {α : Type u_1} {β : Type u_2} (f : α ↪ β) {a : α} {s : finset α} :
    a ∈ s → coe_fn f a ∈ map f s :=
  iff.mpr (mem_map' f)

@[simp] theorem coe_map {α : Type u_1} {β : Type u_2} (f : α ↪ β) (s : finset α) :
    ↑(map f s) = ⇑f '' ↑s :=
  set.ext fun (x : β) => iff.trans mem_map (iff.symm set.mem_image_iff_bex)

theorem coe_map_subset_range {α : Type u_1} {β : Type u_2} (f : α ↪ β) (s : finset α) :
    ↑(map f s) ⊆ set.range ⇑f :=
  trans_rel_right has_subset.subset (coe_map f s) (set.image_subset_range ⇑f ↑s)

theorem map_to_finset {α : Type u_1} {β : Type u_2} {f : α ↪ β} [DecidableEq α] [DecidableEq β]
    {s : multiset α} : map f (multiset.to_finset s) = multiset.to_finset (multiset.map (⇑f) s) :=
  sorry

@[simp] theorem map_refl {α : Type u_1} {s : finset α} : map (function.embedding.refl α) s = s :=
  sorry

theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α ↪ β} {s : finset α}
    {g : β ↪ γ} : map g (map f s) = map (function.embedding.trans f g) s :=
  sorry

theorem map_subset_map {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s₁ : finset α} {s₂ : finset α} :
    map f s₁ ⊆ map f s₂ ↔ s₁ ⊆ s₂ :=
  sorry

theorem map_inj {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s₁ : finset α} {s₂ : finset α} :
    map f s₁ = map f s₂ ↔ s₁ = s₂ :=
  sorry

/-- Associate to an embedding `f` from `α` to `β` the embedding that maps a finset to its image
under `f`. -/
def map_embedding {α : Type u_1} {β : Type u_2} (f : α ↪ β) : finset α ↪ finset β :=
  function.embedding.mk (map f) sorry

@[simp] theorem map_embedding_apply {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s : finset α} :
    coe_fn (map_embedding f) s = map f s :=
  rfl

theorem map_filter {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s : finset α} {p : β → Prop}
    [decidable_pred p] : filter p (map f s) = map f (filter (p ∘ ⇑f) s) :=
  sorry

theorem map_union {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] {f : α ↪ β}
    (s₁ : finset α) (s₂ : finset α) : map f (s₁ ∪ s₂) = map f s₁ ∪ map f s₂ :=
  sorry

theorem map_inter {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] {f : α ↪ β}
    (s₁ : finset α) (s₂ : finset α) : map f (s₁ ∩ s₂) = map f s₁ ∩ map f s₂ :=
  sorry

@[simp] theorem map_singleton {α : Type u_1} {β : Type u_2} (f : α ↪ β) (a : α) :
    map f (singleton a) = singleton (coe_fn f a) :=
  sorry

@[simp] theorem map_insert {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] (f : α ↪ β)
    (a : α) (s : finset α) : map f (insert a s) = insert (coe_fn f a) (map f s) :=
  sorry

@[simp] theorem map_eq_empty {α : Type u_1} {β : Type u_2} {f : α ↪ β} {s : finset α} :
    map f s = ∅ ↔ s = ∅ :=
  sorry

theorem attach_map_val {α : Type u_1} {s : finset α} :
    map (function.embedding.subtype fun (x : α) => x ∈ s) (attach s) = s :=
  sorry

theorem nonempty.map {α : Type u_1} {β : Type u_2} {s : finset α} (h : finset.nonempty s)
    (f : α ↪ β) : finset.nonempty (map f s) :=
  sorry

theorem range_add_one' (n : ℕ) :
    range (n + 1) =
        insert 0
          (map (function.embedding.mk (fun (i : ℕ) => i + 1) fun (i j : ℕ) => nat.succ.inj)
            (range n)) :=
  sorry

/-! ### image -/

/-- `image f s` is the forward image of `s` under `f`. -/
def image {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) (s : finset α) : finset β :=
  multiset.to_finset (multiset.map f (val s))

@[simp] theorem image_val {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) (s : finset α) :
    val (image f s) = multiset.erase_dup (multiset.map f (val s)) :=
  rfl

@[simp] theorem image_empty {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) :
    image f ∅ = ∅ :=
  rfl

@[simp] theorem mem_image {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} {s : finset α}
    {b : β} : b ∈ image f s ↔ ∃ (a : α), ∃ (H : a ∈ s), f a = b :=
  sorry

theorem mem_image_of_mem {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) {a : α}
    {s : finset α} (h : a ∈ s) : f a ∈ image f s :=
  iff.mpr mem_image (Exists.intro a (Exists.intro h rfl))

theorem filter_mem_image_eq_image {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β)
    (s : finset α) (t : finset β) (h : ∀ (x : α), x ∈ s → f x ∈ t) :
    filter (fun (y : β) => y ∈ image f s) t = image f s :=
  sorry

theorem fiber_nonempty_iff_mem_image {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β)
    (s : finset α) (y : β) : finset.nonempty (filter (fun (x : α) => f x = y) s) ↔ y ∈ image f s :=
  sorry

@[simp] theorem coe_image {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α} {f : α → β} :
    ↑(image f s) = f '' ↑s :=
  set.ext fun (_x : β) => iff.trans mem_image (iff.symm set.mem_image_iff_bex)

theorem nonempty.image {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α}
    (h : finset.nonempty s) (f : α → β) : finset.nonempty (image f s) :=
  sorry

theorem image_to_finset {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} [DecidableEq α]
    {s : multiset α} : image f (multiset.to_finset s) = multiset.to_finset (multiset.map f s) :=
  sorry

theorem image_val_of_inj_on {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} {s : finset α}
    (H : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) :
    val (image f s) = multiset.map f (val s) :=
  iff.mpr multiset.erase_dup_eq_self (multiset.nodup_map_on H (nodup s))

@[simp] theorem image_id {α : Type u_1} {s : finset α} [DecidableEq α] : image id s = s := sorry

theorem image_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq β] {f : α → β}
    {s : finset α} [DecidableEq γ] {g : β → γ} : image g (image f s) = image (g ∘ f) s :=
  sorry

theorem image_subset_image {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} {s₁ : finset α}
    {s₂ : finset α} (h : s₁ ⊆ s₂) : image f s₁ ⊆ image f s₂ :=
  sorry

theorem image_subset_iff {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α} {t : finset β}
    {f : α → β} : image f s ⊆ t ↔ ∀ (x : α), x ∈ s → f x ∈ t :=
  sorry

theorem image_mono {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) : monotone (image f) :=
  fun (_x _x_1 : finset α) => image_subset_image

theorem coe_image_subset_range {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β}
    {s : finset α} : ↑(image f s) ⊆ set.range f :=
  trans_rel_right has_subset.subset coe_image (set.image_subset_range f ↑s)

theorem image_filter {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} {s : finset α}
    {p : β → Prop} [decidable_pred p] : filter p (image f s) = image f (filter (p ∘ f) s) :=
  sorry

theorem image_union {α : Type u_1} {β : Type u_2} [DecidableEq β] [DecidableEq α] {f : α → β}
    (s₁ : finset α) (s₂ : finset α) : image f (s₁ ∪ s₂) = image f s₁ ∪ image f s₂ :=
  sorry

theorem image_inter {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} [DecidableEq α]
    (s₁ : finset α) (s₂ : finset α) (hf : ∀ (x y : α), f x = f y → x = y) :
    image f (s₁ ∩ s₂) = image f s₁ ∩ image f s₂ :=
  sorry

@[simp] theorem image_singleton {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α → β) (a : α) :
    image f (singleton a) = singleton (f a) :=
  sorry

@[simp] theorem image_insert {α : Type u_1} {β : Type u_2} [DecidableEq β] [DecidableEq α]
    (f : α → β) (a : α) (s : finset α) : image f (insert a s) = insert (f a) (image f s) :=
  sorry

@[simp] theorem image_eq_empty {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β}
    {s : finset α} : image f s = ∅ ↔ s = ∅ :=
  sorry

theorem attach_image_val {α : Type u_1} [DecidableEq α] {s : finset α} :
    image subtype.val (attach s) = s :=
  sorry

@[simp] theorem attach_insert {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} :
    attach (insert a s) =
        insert { val := a, property := mem_insert_self a s }
          (image
            (fun (x : Subtype fun (x : α) => x ∈ s) =>
              { val := subtype.val x, property := mem_insert_of_mem (subtype.property x) })
            (attach s)) :=
  sorry

theorem map_eq_image {α : Type u_1} {β : Type u_2} [DecidableEq β] (f : α ↪ β) (s : finset α) :
    map f s = image (⇑f) s :=
  eq_of_veq (Eq.symm (iff.mpr multiset.erase_dup_eq_self (nodup (map f s))))

theorem image_const {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α}
    (h : finset.nonempty s) (b : β) : image (fun (a : α) => b) s = singleton b :=
  sorry

/--
Because `finset.image` requires a `decidable_eq` instances for the target type,
we can only construct a `functor finset` when working classically.
-/
protected instance functor [(P : Prop) → Decidable P] : Functor finset :=
  { map := fun (α β : Type u_1) (f : α → β) (s : finset α) => image f s,
    mapConst :=
      fun (α β : Type u_1) => (fun (f : β → α) (s : finset β) => image f s) ∘ function.const β }

protected instance is_lawful_functor [(P : Prop) → Decidable P] : is_lawful_functor finset :=
  is_lawful_functor.mk (fun (α : Type u_1) (x : finset α) => image_id)
    fun (α β γ : Type u_1) (f : α → β) (g : β → γ) (s : finset α) => Eq.symm image_image

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`.  -/
protected def subtype {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : finset α) :
    finset (Subtype p) :=
  map
    (function.embedding.mk
      (fun (x : Subtype fun (x : α) => x ∈ filter p s) =>
        { val := subtype.val x, property := sorry })
      sorry)
    (attach (filter p s))

@[simp] theorem mem_subtype {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : finset α}
    {a : Subtype p} : a ∈ finset.subtype p s ↔ ↑a ∈ s :=
  sorry

theorem subtype_eq_empty {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : finset α} :
    finset.subtype p s = ∅ ↔ ∀ (x : α), p x → ¬x ∈ s :=
  sorry

/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp] theorem subtype_map {α : Type u_1} {s : finset α} (p : α → Prop) [decidable_pred p] :
    map (function.embedding.subtype p) (finset.subtype p s) = filter p s :=
  sorry

/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
theorem subtype_map_of_mem {α : Type u_1} {s : finset α} {p : α → Prop} [decidable_pred p]
    (h : ∀ (x : α), x ∈ s → p x) : map (function.embedding.subtype p) (finset.subtype p s) = s :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (map (function.embedding.subtype p) (finset.subtype p s) = s))
        (subtype_map p)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (filter p s = s)) (filter_true_of_mem h))) (Eq.refl s))

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
theorem property_of_mem_map_subtype {α : Type u_1} {p : α → Prop}
    (s : finset (Subtype fun (x : α) => p x)) {a : α}
    (h : a ∈ map (function.embedding.subtype fun (x : α) => p x) s) : p a :=
  sorry

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
theorem not_mem_map_subtype_of_not_property {α : Type u_1} {p : α → Prop}
    (s : finset (Subtype fun (x : α) => p x)) {a : α} (h : ¬p a) :
    ¬a ∈ map (function.embedding.subtype fun (x : α) => p x) s :=
  mt (property_of_mem_map_subtype s) h

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
theorem map_subtype_subset {α : Type u_1} {t : set α} (s : finset ↥t) :
    ↑(map (function.embedding.subtype fun (x : α) => x ∈ t) s) ⊆ t :=
  sorry

theorem subset_image_iff {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} {s : finset β}
    {t : set α} : ↑s ⊆ f '' t ↔ ∃ (s' : finset α), ↑s' ⊆ t ∧ image f s' = s :=
  sorry

end finset


theorem multiset.to_finset_map {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    (f : α → β) (m : multiset α) :
    multiset.to_finset (multiset.map f m) = finset.image f (multiset.to_finset m) :=
  iff.mp finset.val_inj (Eq.symm (multiset.erase_dup_map_erase_dup_eq f m))

namespace finset


/-! ### card -/

/-- `card s` is the cardinality (number of elements) of `s`. -/
def card {α : Type u_1} (s : finset α) : ℕ := coe_fn multiset.card (val s)

theorem card_def {α : Type u_1} (s : finset α) : card s = coe_fn multiset.card (val s) := rfl

@[simp] theorem card_mk {α : Type u_1} {m : multiset α} {nodup : multiset.nodup m} :
    card (mk m nodup) = coe_fn multiset.card m :=
  rfl

@[simp] theorem card_empty {α : Type u_1} : card ∅ = 0 := rfl

@[simp] theorem card_eq_zero {α : Type u_1} {s : finset α} : card s = 0 ↔ s = ∅ :=
  iff.trans multiset.card_eq_zero val_eq_zero

theorem card_pos {α : Type u_1} {s : finset α} : 0 < card s ↔ finset.nonempty s :=
  iff.trans pos_iff_ne_zero (iff.trans (not_congr card_eq_zero) (iff.symm nonempty_iff_ne_empty))

theorem card_ne_zero_of_mem {α : Type u_1} {s : finset α} {a : α} (h : a ∈ s) : card s ≠ 0 :=
  iff.mpr (not_congr card_eq_zero) (ne_empty_of_mem h)

theorem card_eq_one {α : Type u_1} {s : finset α} : card s = 1 ↔ ∃ (a : α), s = singleton a := sorry

@[simp] theorem card_insert_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    (h : ¬a ∈ s) : card (insert a s) = card s + 1 :=
  sorry

theorem card_insert_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} (h : a ∈ s) :
    card (insert a s) = card s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (card (insert a s) = card s)) (insert_eq_of_mem h)))
    (Eq.refl (card s))

theorem card_insert_le {α : Type u_1} [DecidableEq α] (a : α) (s : finset α) :
    card (insert a s) ≤ card s + 1 :=
  sorry

@[simp] theorem card_singleton {α : Type u_1} (a : α) : card (singleton a) = 1 :=
  multiset.card_singleton a

theorem card_singleton_inter {α : Type u_1} [DecidableEq α] {x : α} {s : finset α} :
    card (singleton x ∩ s) ≤ 1 :=
  sorry

theorem card_erase_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} :
    a ∈ s → card (erase s a) = Nat.pred (card s) :=
  multiset.card_erase_of_mem

theorem card_erase_lt_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} :
    a ∈ s → card (erase s a) < card s :=
  multiset.card_erase_lt_of_mem

theorem card_erase_le {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} :
    card (erase s a) ≤ card s :=
  multiset.card_erase_le

theorem pred_card_le_card_erase {α : Type u_1} [DecidableEq α] {a : α} {s : finset α} :
    card s - 1 ≤ card (erase s a) :=
  sorry

@[simp] theorem card_range (n : ℕ) : card (range n) = n := multiset.card_range n

@[simp] theorem card_attach {α : Type u_1} {s : finset α} : card (attach s) = card s :=
  multiset.card_attach

end finset


theorem multiset.to_finset_card_le {α : Type u_1} [DecidableEq α] (m : multiset α) :
    finset.card (multiset.to_finset m) ≤ coe_fn multiset.card m :=
  multiset.card_le_of_le (multiset.erase_dup_le m)

theorem list.to_finset_card_le {α : Type u_1} [DecidableEq α] (l : List α) :
    finset.card (list.to_finset l) ≤ list.length l :=
  multiset.to_finset_card_le (quotient.mk l)

namespace finset


theorem card_image_le {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β} {s : finset α} :
    card (image f s) ≤ card s :=
  sorry

theorem card_image_of_inj_on {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β}
    {s : finset α} (H : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) :
    card (image f s) = card s :=
  sorry

theorem card_image_of_injective {α : Type u_1} {β : Type u_2} [DecidableEq β] {f : α → β}
    (s : finset α) (H : function.injective f) : card (image f s) = card s :=
  card_image_of_inj_on fun (x : α) (_x : x ∈ s) (y : α) (_x : y ∈ s) (h : f x = f y) => H h

theorem fiber_card_ne_zero_iff_mem_image {α : Type u_1} {β : Type u_2} (s : finset α) (f : α → β)
    [DecidableEq β] (y : β) : card (filter (fun (x : α) => f x = y) s) ≠ 0 ↔ y ∈ image f s :=
  sorry

@[simp] theorem card_map {α : Type u_1} {β : Type u_2} (f : α ↪ β) {s : finset α} :
    card (map f s) = card s :=
  multiset.card_map (⇑f) (val s)

@[simp] theorem card_subtype {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : finset α) :
    card (finset.subtype p s) = card (filter p s) :=
  sorry

theorem card_eq_of_bijective {α : Type u_1} {s : finset α} {n : ℕ} (f : (i : ℕ) → i < n → α)
    (hf : ∀ (a : α), a ∈ s → ∃ (i : ℕ), ∃ (h : i < n), f i h = a)
    (hf' : ∀ (i : ℕ) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j : ℕ) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : card s = n :=
  sorry

theorem card_eq_succ {α : Type u_1} [DecidableEq α] {s : finset α} {n : ℕ} :
    card s = n + 1 ↔ ∃ (a : α), ∃ (t : finset α), ¬a ∈ t ∧ insert a t = s ∧ card t = n :=
  sorry

theorem card_le_of_subset {α : Type u_1} {s : finset α} {t : finset α} : s ⊆ t → card s ≤ card t :=
  multiset.card_le_of_le ∘ iff.mpr val_le_iff

theorem eq_of_subset_of_card_le {α : Type u_1} {s : finset α} {t : finset α} (h : s ⊆ t)
    (h₂ : card t ≤ card s) : s = t :=
  eq_of_veq (multiset.eq_of_le_of_card_le (iff.mpr val_le_iff h) h₂)

theorem card_lt_card {α : Type u_1} {s : finset α} {t : finset α} (h : s ⊂ t) : card s < card t :=
  multiset.card_lt_of_lt (iff.mpr val_lt_iff h)

theorem card_le_card_of_inj_on {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β}
    (f : α → β) (hf : ∀ (a : α), a ∈ s → f a ∈ t)
    (f_inj : ∀ (a₁ : α), a₁ ∈ s → ∀ (a₂ : α), a₂ ∈ s → f a₁ = f a₂ → a₁ = a₂) : card s ≤ card t :=
  sorry

/--
If there are more pigeons than pigeonholes, then there are two pigeons
in the same pigeonhole.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to {α : Type u_1} {β : Type u_2} {s : finset α}
    {t : finset β} (hc : card t < card s) {f : α → β} (hf : ∀ (a : α), a ∈ s → f a ∈ t) :
    ∃ (x : α), ∃ (H : x ∈ s), ∃ (y : α), ∃ (H : y ∈ s), x ≠ y ∧ f x = f y :=
  sorry

theorem card_le_of_inj_on {α : Type u_1} {n : ℕ} {s : finset α} (f : ℕ → α)
    (hf : ∀ (i : ℕ), i < n → f i ∈ s) (f_inj : ∀ (i j : ℕ), i < n → j < n → f i = f j → i = j) :
    n ≤ card s :=
  sorry

/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strong_induction_on {α : Type u_1} {p : finset α → Sort u_2} (s : finset α) :
    ((s : finset α) → ((t : finset α) → t ⊂ s → p t) → p s) → p s :=
  sorry

theorem case_strong_induction_on {α : Type u_1} [DecidableEq α] {p : finset α → Prop} (s : finset α)
    (h₀ : p ∅)
    (h₁ : ∀ (a : α) (s : finset α), ¬a ∈ s → (∀ (t : finset α), t ⊆ s → p t) → p (insert a s)) :
    p s :=
  sorry

theorem card_congr {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β}
    (f : (a : α) → a ∈ s → β) (h₁ : ∀ (a : α) (ha : a ∈ s), f a ha ∈ t)
    (h₂ : ∀ (a b : α) (ha : a ∈ s) (hb : b ∈ s), f a ha = f b hb → a = b)
    (h₃ : ∀ (b : β), b ∈ t → ∃ (a : α), ∃ (ha : a ∈ s), f a ha = b) : card s = card t :=
  sorry

theorem card_union_add_card_inter {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    card (s ∪ t) + card (s ∩ t) = card s + card t :=
  sorry

theorem card_union_le {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    card (s ∪ t) ≤ card s + card t :=
  card_union_add_card_inter s t ▸ nat.le_add_right (card (s ∪ t)) (card (s ∩ t))

theorem card_union_eq {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    (h : disjoint s t) : card (s ∪ t) = card s + card t :=
  sorry

theorem surj_on_of_inj_on_of_card_le {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β}
    (f : (a : α) → a ∈ s → β) (hf : ∀ (a : α) (ha : a ∈ s), f a ha ∈ t)
    (hinj : ∀ (a₁ a₂ : α) (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s), f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂)
    (hst : card t ≤ card s) (b : β) (H : b ∈ t) : ∃ (a : α), ∃ (ha : a ∈ s), b = f a ha :=
  sorry

theorem inj_on_of_surj_on_of_card_le {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β}
    (f : (a : α) → a ∈ s → β) (hf : ∀ (a : α) (ha : a ∈ s), f a ha ∈ t)
    (hsurj : ∀ (b : β), b ∈ t → ∃ (a : α), ∃ (ha : a ∈ s), b = f a ha) (hst : card s ≤ card t)
    {a₁ : α} {a₂ : α} (ha₁ : a₁ ∈ s) (ha₂ : a₂ ∈ s) (ha₁a₂ : f a₁ ha₁ = f a₂ ha₂) : a₁ = a₂ :=
  sorry

/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/

/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bUnion {α : Type u_1} {β : Type u_2} [DecidableEq β] (s : finset α)
    (t : α → finset β) : finset β :=
  multiset.to_finset (multiset.bind (val s) fun (a : α) => val (t a))

@[simp] theorem bUnion_val {α : Type u_1} {β : Type u_2} [DecidableEq β] (s : finset α)
    (t : α → finset β) :
    val (finset.bUnion s t) = multiset.erase_dup (multiset.bind (val s) fun (a : α) => val (t a)) :=
  rfl

@[simp] theorem bUnion_empty {α : Type u_1} {β : Type u_2} [DecidableEq β] {t : α → finset β} :
    finset.bUnion ∅ t = ∅ :=
  rfl

@[simp] theorem mem_bUnion {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α}
    {t : α → finset β} {b : β} : b ∈ finset.bUnion s t ↔ ∃ (a : α), ∃ (H : a ∈ s), b ∈ t a :=
  sorry

@[simp] theorem bUnion_insert {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α}
    {t : α → finset β} [DecidableEq α] {a : α} :
    finset.bUnion (insert a s) t = t a ∪ finset.bUnion s t :=
  sorry

-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]

@[simp] theorem singleton_bUnion {α : Type u_1} {β : Type u_2} [DecidableEq β] {t : α → finset β}
    {a : α} : finset.bUnion (singleton a) t = t a :=
  sorry

theorem bUnion_inter {α : Type u_1} {β : Type u_2} [DecidableEq β] (s : finset α) (f : α → finset β)
    (t : finset β) : finset.bUnion s f ∩ t = finset.bUnion s fun (x : α) => f x ∩ t :=
  sorry

theorem inter_bUnion {α : Type u_1} {β : Type u_2} [DecidableEq β] (t : finset β) (s : finset α)
    (f : α → finset β) : t ∩ finset.bUnion s f = finset.bUnion s fun (x : α) => t ∩ f x :=
  sorry

theorem image_bUnion {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq β] [DecidableEq γ]
    {f : α → β} {s : finset α} {t : β → finset γ} :
    finset.bUnion (image f s) t = finset.bUnion s fun (a : α) => t (f a) :=
  sorry

theorem bUnion_image {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq β] [DecidableEq γ]
    {s : finset α} {t : α → finset β} {f : β → γ} :
    image f (finset.bUnion s t) = finset.bUnion s fun (a : α) => image f (t a) :=
  sorry

theorem bind_to_finset {α : Type u_1} {β : Type u_2} [DecidableEq β] [DecidableEq α]
    (s : multiset α) (t : α → multiset β) :
    multiset.to_finset (multiset.bind s t) =
        finset.bUnion (multiset.to_finset s) fun (a : α) => multiset.to_finset (t a) :=
  sorry

theorem bUnion_mono {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α} {t₁ : α → finset β}
    {t₂ : α → finset β} (h : ∀ (a : α), a ∈ s → t₁ a ⊆ t₂ a) :
    finset.bUnion s t₁ ⊆ finset.bUnion s t₂ :=
  sorry

theorem bUnion_subset_bUnion_of_subset_left {β : Type u_2} [DecidableEq β] {α : Type u_1}
    {s₁ : finset α} {s₂ : finset α} (t : α → finset β) (h : s₁ ⊆ s₂) :
    finset.bUnion s₁ t ⊆ finset.bUnion s₂ t :=
  sorry

theorem bUnion_singleton {α : Type u_1} {β : Type u_2} [DecidableEq β] {s : finset α} {f : α → β} :
    (finset.bUnion s fun (a : α) => singleton (f a)) = image f s :=
  sorry

@[simp] theorem bUnion_singleton_eq_self {α : Type u_1} {s : finset α} [DecidableEq α] :
    finset.bUnion s singleton = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finset.bUnion s singleton = s)) bUnion_singleton)) image_id

theorem bUnion_filter_eq_of_maps_to {α : Type u_1} {β : Type u_2} [DecidableEq β] [DecidableEq α]
    {s : finset α} {t : finset β} {f : α → β} (h : ∀ (x : α), x ∈ s → f x ∈ t) :
    (finset.bUnion t fun (a : β) => filter (fun (c : α) => f c = a) s) = s :=
  sorry

theorem image_bUnion_filter_eq {α : Type u_1} {β : Type u_2} [DecidableEq β] [DecidableEq α]
    (s : finset β) (g : β → α) :
    (finset.bUnion (image g s) fun (a : α) => filter (fun (c : β) => g c = a) s) = s :=
  bUnion_filter_eq_of_maps_to fun (x : β) => mem_image_of_mem g

/-! ### prod -/

/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product {α : Type u_1} {β : Type u_2} (s : finset α) (t : finset β) :
    finset (α × β) :=
  mk (multiset.product (val s) (val t)) sorry

@[simp] theorem product_val {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β} :
    val (finset.product s t) = multiset.product (val s) (val t) :=
  rfl

@[simp] theorem mem_product {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β}
    {p : α × β} : p ∈ finset.product s t ↔ prod.fst p ∈ s ∧ prod.snd p ∈ t :=
  multiset.mem_product

theorem subset_product {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    {s : finset (α × β)} : s ⊆ finset.product (image prod.fst s) (image prod.snd s) :=
  fun (p : α × β) (hp : p ∈ s) =>
    iff.mpr mem_product
      { left := mem_image_of_mem prod.fst hp, right := mem_image_of_mem prod.snd hp }

theorem product_eq_bUnion {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β]
    (s : finset α) (t : finset β) :
    finset.product s t = finset.bUnion s fun (a : α) => image (fun (b : β) => (a, b)) t :=
  sorry

@[simp] theorem card_product {α : Type u_1} {β : Type u_2} (s : finset α) (t : finset β) :
    card (finset.product s t) = card s * card t :=
  multiset.card_product (val s) (val t)

theorem filter_product {α : Type u_1} {β : Type u_2} {s : finset α} {t : finset β} (p : α → Prop)
    (q : β → Prop) [decidable_pred p] [decidable_pred q] :
    filter (fun (x : α × β) => p (prod.fst x) ∧ q (prod.snd x)) (finset.product s t) =
        finset.product (filter p s) (filter q t) :=
  sorry

theorem filter_product_card {α : Type u_1} {β : Type u_2} (s : finset α) (t : finset β)
    (p : α → Prop) (q : β → Prop) [decidable_pred p] [decidable_pred q] :
    card (filter (fun (x : α × β) => p (prod.fst x) ↔ q (prod.snd x)) (finset.product s t)) =
        card (filter p s) * card (filter q t) +
          card (filter (Not ∘ p) s) * card (filter (Not ∘ q) t) :=
  sorry

/-! ### sigma -/

/-- `sigma s t` is the set of dependent pairs `⟨a, b⟩` such that `a ∈ s` and `b ∈ t a`. -/
protected def sigma {α : Type u_1} {σ : α → Type u_4} (s : finset α) (t : (a : α) → finset (σ a)) :
    finset (sigma fun (a : α) => σ a) :=
  mk (multiset.sigma (val s) fun (a : α) => val (t a)) sorry

@[simp] theorem mem_sigma {α : Type u_1} {σ : α → Type u_4} {s : finset α}
    {t : (a : α) → finset (σ a)} {p : sigma σ} :
    p ∈ finset.sigma s t ↔ sigma.fst p ∈ s ∧ sigma.snd p ∈ t (sigma.fst p) :=
  multiset.mem_sigma

theorem sigma_mono {α : Type u_1} {σ : α → Type u_4} {s₁ : finset α} {s₂ : finset α}
    {t₁ : (a : α) → finset (σ a)} {t₂ : (a : α) → finset (σ a)} (H1 : s₁ ⊆ s₂)
    (H2 : ∀ (a : α), t₁ a ⊆ t₂ a) : finset.sigma s₁ t₁ ⊆ finset.sigma s₂ t₂ :=
  sorry

theorem sigma_eq_bUnion {α : Type u_1} {σ : α → Type u_4} [DecidableEq (sigma fun (a : α) => σ a)]
    (s : finset α) (t : (a : α) → finset (σ a)) :
    finset.sigma s t = finset.bUnion s fun (a : α) => map (function.embedding.sigma_mk a) (t a) :=
  sorry

/-! ### disjoint -/

theorem disjoint_left {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint s t ↔ ∀ {a : α}, a ∈ s → ¬a ∈ t :=
  sorry

theorem disjoint_val {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint s t ↔ multiset.disjoint (val s) (val t) :=
  disjoint_left

theorem disjoint_iff_inter_eq_empty {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

protected instance decidable_disjoint {α : Type u_1} [DecidableEq α] (U : finset α) (V : finset α) :
    Decidable (disjoint U V) :=
  decidable_of_decidable_of_iff (finset.has_decidable_eq (U ⊓ V) ⊥) sorry

theorem disjoint_right {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint s t ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (disjoint s t ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s)) (propext disjoint.comm)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (disjoint t s ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s)) (propext disjoint_left)))
      (iff.refl (∀ {a : α}, a ∈ t → ¬a ∈ s)))

theorem disjoint_iff_ne {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint s t ↔ ∀ (a : α), a ∈ s → ∀ (b : α), b ∈ t → a ≠ b :=
  sorry

theorem disjoint_of_subset_left {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    {u : finset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
  iff.mpr disjoint_left fun (x : α) (m₁ : x ∈ s) => iff.mp disjoint_left d x (h m₁)

theorem disjoint_of_subset_right {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    {u : finset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
  iff.mpr disjoint_right fun (x : α) (m₁ : x ∈ t) => iff.mp disjoint_right d x (h m₁)

@[simp] theorem disjoint_empty_left {α : Type u_1} [DecidableEq α] (s : finset α) : disjoint ∅ s :=
  disjoint_bot_left

@[simp] theorem disjoint_empty_right {α : Type u_1} [DecidableEq α] (s : finset α) : disjoint s ∅ :=
  disjoint_bot_right

@[simp] theorem singleton_disjoint {α : Type u_1} [DecidableEq α] {s : finset α} {a : α} :
    disjoint (singleton a) s ↔ ¬a ∈ s :=
  sorry

@[simp] theorem disjoint_singleton {α : Type u_1} [DecidableEq α] {s : finset α} {a : α} :
    disjoint s (singleton a) ↔ ¬a ∈ s :=
  iff.trans disjoint.comm singleton_disjoint

@[simp] theorem disjoint_insert_left {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    {t : finset α} : disjoint (insert a s) t ↔ ¬a ∈ t ∧ disjoint s t :=
  sorry

@[simp] theorem disjoint_insert_right {α : Type u_1} [DecidableEq α] {a : α} {s : finset α}
    {t : finset α} : disjoint s (insert a t) ↔ ¬a ∈ s ∧ disjoint s t :=
  sorry

@[simp] theorem disjoint_union_left {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    {u : finset α} : disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
  sorry

@[simp] theorem disjoint_union_right {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    {u : finset α} : disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
  sorry

theorem sdiff_disjoint {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint (t \ s) s :=
  iff.mpr disjoint_left fun (a : α) (ha : a ∈ t \ s) => and.right (iff.mp mem_sdiff ha)

theorem disjoint_sdiff {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    disjoint s (t \ s) :=
  disjoint.symm sdiff_disjoint

theorem disjoint_sdiff_inter {α : Type u_1} [DecidableEq α] (s : finset α) (t : finset α) :
    disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right s t) sdiff_disjoint

theorem sdiff_eq_self_iff_disjoint {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} :
    s \ t = s ↔ disjoint s t :=
  sorry

theorem sdiff_eq_self_of_disjoint {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    (h : disjoint s t) : s \ t = s :=
  iff.mpr sdiff_eq_self_iff_disjoint h

theorem disjoint_self_iff_empty {α : Type u_1} [DecidableEq α] (s : finset α) :
    disjoint s s ↔ s = ∅ :=
  disjoint_self

theorem disjoint_bUnion_left {α : Type u_1} [DecidableEq α] {ι : Type u_2} (s : finset ι)
    (f : ι → finset α) (t : finset α) :
    disjoint (finset.bUnion s f) t ↔ ∀ (i : ι), i ∈ s → disjoint (f i) t :=
  sorry

theorem disjoint_bUnion_right {α : Type u_1} [DecidableEq α] {ι : Type u_2} (s : finset α)
    (t : finset ι) (f : ι → finset α) :
    disjoint s (finset.bUnion t f) ↔ ∀ (i : ι), i ∈ t → disjoint s (f i) :=
  sorry

@[simp] theorem card_disjoint_union {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    (h : disjoint s t) : card (s ∪ t) = card s + card t :=
  sorry

theorem card_sdiff {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α} (h : s ⊆ t) :
    card (t \ s) = card t - card s :=
  sorry

theorem disjoint_filter {α : Type u_1} [DecidableEq α] {s : finset α} {p : α → Prop} {q : α → Prop}
    [decidable_pred p] [decidable_pred q] :
    disjoint (filter p s) (filter q s) ↔ ∀ (x : α), x ∈ s → p x → ¬q x :=
  sorry

theorem disjoint_filter_filter {α : Type u_1} [DecidableEq α] {s : finset α} {t : finset α}
    {p : α → Prop} {q : α → Prop} [decidable_pred p] [decidable_pred q] :
    disjoint s t → disjoint (filter p s) (filter q t) :=
  disjoint.mono (filter_subset p s) (filter_subset q t)

theorem disjoint_iff_disjoint_coe {α : Type u_1} {a : finset α} {b : finset α} [DecidableEq α] :
    disjoint a b ↔ disjoint ↑a ↑b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (disjoint a b ↔ disjoint ↑a ↑b)) (propext disjoint_left)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl ((∀ {a_1 : α}, a_1 ∈ a → ¬a_1 ∈ b) ↔ disjoint ↑a ↑b))
          (propext set.disjoint_left)))
      (iff.refl (∀ {a_1 : α}, a_1 ∈ a → ¬a_1 ∈ b)))

theorem filter_card_add_filter_neg_card_eq_card {α : Type u_1} {s : finset α} (p : α → Prop)
    [decidable_pred p] : card (filter p s) + card (filter (Not ∘ p) s) = card s :=
  sorry

/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag {α : Type u_1} (s : finset α) [DecidableEq α] : finset (α × α) :=
  filter (fun (a : α × α) => prod.fst a = prod.snd a) (finset.product s s)

/-- Given a finite set `s`, the off-diagonal, `s.off_diag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def off_diag {α : Type u_1} (s : finset α) [DecidableEq α] : finset (α × α) :=
  filter (fun (a : α × α) => prod.fst a ≠ prod.snd a) (finset.product s s)

@[simp] theorem mem_diag {α : Type u_1} (s : finset α) [DecidableEq α] (x : α × α) :
    x ∈ diag s ↔ prod.fst x ∈ s ∧ prod.fst x = prod.snd x :=
  sorry

@[simp] theorem mem_off_diag {α : Type u_1} (s : finset α) [DecidableEq α] (x : α × α) :
    x ∈ off_diag s ↔ prod.fst x ∈ s ∧ prod.snd x ∈ s ∧ prod.fst x ≠ prod.snd x :=
  sorry

@[simp] theorem diag_card {α : Type u_1} (s : finset α) [DecidableEq α] : card (diag s) = card s :=
  sorry

@[simp] theorem off_diag_card {α : Type u_1} (s : finset α) [DecidableEq α] :
    card (off_diag s) = card s * card s - card s :=
  sorry

/--
Given a set A and a set B inside it, we can shrink A to any appropriate size, and keep B
inside it.
-/
theorem exists_intermediate_set {α : Type u_1} {A : finset α} {B : finset α} (i : ℕ)
    (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
    ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
  sorry

/-- We can shrink A to any smaller size. -/
theorem exists_smaller_set {α : Type u_1} (A : finset α) (i : ℕ) (h₁ : i ≤ card A) :
    ∃ (B : finset α), B ⊆ A ∧ card B = i :=
  sorry

/-- `finset.fin_range k` is the finset `{0, 1, ..., k-1}`, as a `finset (fin k)`. -/
def fin_range (k : ℕ) : finset (fin k) := mk (↑(list.fin_range k)) (list.nodup_fin_range k)

@[simp] theorem fin_range_card {k : ℕ} : card (fin_range k) = k := sorry

@[simp] theorem mem_fin_range {k : ℕ} (m : fin k) : m ∈ fin_range k := list.mem_fin_range m

@[simp] theorem coe_fin_range (k : ℕ) : ↑(fin_range k) = set.univ :=
  set.eq_univ_of_forall mem_fin_range

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ (m : ℕ), m ∈ s → m < n) : finset (fin n) :=
  mk (multiset.pmap (fun (a : ℕ) (ha : a < n) => { val := a, property := ha }) (val s) h) sorry

@[simp] theorem mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ (m : ℕ), m ∈ s → m < n) {a : fin n} :
    a ∈ attach_fin s h ↔ ↑a ∈ s :=
  sorry

@[simp] theorem card_attach_fin {n : ℕ} (s : finset ℕ) (h : ∀ (m : ℕ), m ∈ s → m < n) :
    card (attach_fin s h) = card s :=
  multiset.card_pmap (fun (a : ℕ) (ha : a < n) => { val := a, property := ha }) (val s) h

/-! ### choose -/

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : finset α)
    (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : Subtype fun (a : α) => a ∈ l ∧ p a :=
  multiset.choose_x p (val l) hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : finset α)
    (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : α :=
  ↑(choose_x p l hp)

theorem choose_spec {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : finset α)
    (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  subtype.property (choose_x p l hp)

theorem choose_mem {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : finset α)
    (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : choose p l hp ∈ l :=
  and.left (choose_spec p l hp)

theorem choose_property {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : finset α)
    (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : p (choose p l hp) :=
  and.right (choose_spec p l hp)

theorem lt_wf {α : Type u_1} : well_founded Less :=
  (fun (H : subrelation Less (inv_image Less card)) =>
      subrelation.wf H (inv_image.wf card nat.lt_wf))
    fun (x y : finset α) (hxy : x < y) => card_lt_card hxy

end finset


namespace equiv


/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finset_congr {α : Type u_1} {β : Type u_2} (e : α ≃ β) : finset α ≃ finset β :=
  mk (fun (s : finset α) => finset.map (equiv.to_embedding e) s)
    (fun (s : finset β) => finset.map (equiv.to_embedding (equiv.symm e)) s) sorry sorry

@[simp] theorem finset_congr_apply {α : Type u_1} {β : Type u_2} (e : α ≃ β) (s : finset α) :
    coe_fn (equiv.finset_congr e) s = finset.map (equiv.to_embedding e) s :=
  rfl

@[simp] theorem finset_congr_symm_apply {α : Type u_1} {β : Type u_2} (e : α ≃ β) (s : finset β) :
    coe_fn (equiv.symm (equiv.finset_congr e)) s =
        finset.map (equiv.to_embedding (equiv.symm e)) s :=
  rfl

end equiv


namespace list


theorem to_finset_card_of_nodup {α : Type u_1} [DecidableEq α] {l : List α} (h : nodup l) :
    finset.card (to_finset l) = length l :=
  congr_arg (⇑multiset.card) (iff.mpr multiset.erase_dup_eq_self h)

end list


namespace multiset


theorem to_finset_card_of_nodup {α : Type u_1} [DecidableEq α] {l : multiset α} (h : nodup l) :
    finset.card (to_finset l) = coe_fn card l :=
  congr_arg (⇑card) (iff.mpr erase_dup_eq_self h)

theorem disjoint_to_finset {α : Type u_1} [DecidableEq α] (m1 : multiset α) (m2 : multiset α) :
    disjoint (to_finset m1) (to_finset m2) ↔ disjoint m1 m2 :=
  sorry

end Mathlib