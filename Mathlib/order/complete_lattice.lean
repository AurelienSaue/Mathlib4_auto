/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.bounds
import Mathlib.PostPort

universes u_6 l u_1 u_2 u_4 u_5 u_3 

namespace Mathlib

/-!
# Theory of complete lattices

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supr (f : ι → α)` and `infi (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class complete_lattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class complete_linear_order`: a linear ordered complete lattice.

## Naming conventions

We use `Sup`/`Inf`/`supr`/`infi` for the corresponding functions in the statement. Sometimes we
also use `bsupr`/`binfi` for "bounded` supremum or infimum, i.e. one of `⨆ i ∈ s, f i`,
`⨆ i (hi : p i), f i`, or more generally `⨆ i (hi : p i), f i hi`.

## Notation

* `⨆ i, f i` : `supr f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infi f`, the infimum of the range of `f`.
-/

/-- class for the `Sup` operator -/
/-- class for the `Inf` operator -/
class has_Sup (α : Type u_6) 
where
  Sup : set α → α

class has_Inf (α : Type u_6) 
where
  Inf : set α → α

/-- Supremum of a set -/
/-- Infimum of a set -/
/-- Indexed supremum -/
/-- Indexed infimum -/
def supr {α : Type u_1} [has_Sup α] {ι : Sort u_2} (s : ι → α) : α :=
  Sup (set.range s)

def infi {α : Type u_1} [has_Inf α] {ι : Sort u_2} (s : ι → α) : α :=
  Inf (set.range s)

protected instance has_Inf_to_nonempty (α : Type u_1) [has_Inf α] : Nonempty α :=
  Nonempty.intro (Inf ∅)

protected instance has_Sup_to_nonempty (α : Type u_1) [has_Sup α] : Nonempty α :=
  Nonempty.intro (Sup ∅)

protected instance order_dual.has_Sup (α : Type u_1) [has_Inf α] : has_Sup (order_dual α) :=
  has_Sup.mk Inf

protected instance order_dual.has_Inf (α : Type u_1) [has_Sup α] : has_Inf (order_dual α) :=
  has_Inf.mk Sup

/-- A complete lattice is a bounded lattice which
  has suprema and infima for every subset. -/
class complete_lattice (α : Type u_6) 
extends bounded_lattice α, has_Sup α, has_Inf α
where
  le_Sup : ∀ (s : set α) (a : α), a ∈ s → a ≤ Sup s
  Sup_le : ∀ (s : set α) (a : α), (∀ (b : α), b ∈ s → b ≤ a) → Sup s ≤ a
  Inf_le : ∀ (s : set α) (a : α), a ∈ s → Inf s ≤ a
  le_Inf : ∀ (s : set α) (a : α), (∀ (b : α), b ∈ s → a ≤ b) → a ≤ Inf s

/-- Create a `complete_lattice` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup, bot, top
  ..complete_lattice_of_Inf my_T _ }
```
-/
def complete_lattice_of_Inf (α : Type u_1) [H1 : partial_order α] [H2 : has_Inf α] (is_glb_Inf : ∀ (s : set α), is_glb s (Inf s)) : complete_lattice α :=
  complete_lattice.mk (fun (a b : α) => Inf (set_of fun (x : α) => a ≤ x ∧ b ≤ x)) partial_order.le partial_order.lt
    partial_order.le_refl partial_order.le_trans partial_order.le_antisymm sorry sorry sorry
    (fun (a b : α) => Inf (insert a (singleton b))) sorry sorry sorry (Inf ∅) sorry (Inf set.univ) sorry
    (fun (s : set α) => Inf (upper_bounds s)) Inf sorry sorry sorry sorry

/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf, bot, top
  ..complete_lattice_of_Sup my_T _ }
```
-/
def complete_lattice_of_Sup (α : Type u_1) [H1 : partial_order α] [H2 : has_Sup α] (is_lub_Sup : ∀ (s : set α), is_lub s (Sup s)) : complete_lattice α :=
  complete_lattice.mk (fun (a b : α) => Sup (insert a (singleton b))) partial_order.le partial_order.lt
    partial_order.le_refl partial_order.le_trans partial_order.le_antisymm sorry sorry sorry
    (fun (a b : α) => Sup (set_of fun (x : α) => x ≤ a ∧ x ≤ b)) sorry sorry sorry (Sup set.univ) sorry (Sup ∅) sorry Sup
    (fun (s : set α) => Sup (lower_bounds s)) sorry sorry sorry sorry

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class complete_linear_order (α : Type u_6) 
extends linear_order α, complete_lattice α
where

namespace order_dual


protected instance complete_lattice (α : Type u_1) [complete_lattice α] : complete_lattice (order_dual α) :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry Sup Inf
    complete_lattice.Inf_le complete_lattice.le_Inf complete_lattice.le_Sup complete_lattice.Sup_le

protected instance complete_linear_order (α : Type u_1) [complete_linear_order α] : complete_linear_order (order_dual α) :=
  complete_linear_order.mk complete_lattice.sup complete_lattice.le complete_lattice.lt sorry sorry sorry sorry sorry
    sorry complete_lattice.inf sorry sorry sorry complete_lattice.top sorry complete_lattice.bot sorry
    complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry sorry linear_order.decidable_le
    linear_order.decidable_eq linear_order.decidable_lt

end order_dual


theorem le_Sup {α : Type u_1} [complete_lattice α] {s : set α} {a : α} : a ∈ s → a ≤ Sup s :=
  complete_lattice.le_Sup s a

theorem Sup_le {α : Type u_1} [complete_lattice α] {s : set α} {a : α} : (∀ (b : α), b ∈ s → b ≤ a) → Sup s ≤ a :=
  complete_lattice.Sup_le s a

theorem Inf_le {α : Type u_1} [complete_lattice α] {s : set α} {a : α} : a ∈ s → Inf s ≤ a :=
  complete_lattice.Inf_le s a

theorem le_Inf {α : Type u_1} [complete_lattice α] {s : set α} {a : α} : (∀ (b : α), b ∈ s → a ≤ b) → a ≤ Inf s :=
  complete_lattice.le_Inf s a

theorem is_lub_Sup {α : Type u_1} [complete_lattice α] (s : set α) : is_lub s (Sup s) :=
  { left := fun (x : α) => le_Sup, right := fun (x : α) => Sup_le }

theorem is_lub.Sup_eq {α : Type u_1} [complete_lattice α] {s : set α} {a : α} (h : is_lub s a) : Sup s = a :=
  is_lub.unique (is_lub_Sup s) h

theorem is_glb_Inf {α : Type u_1} [complete_lattice α] (s : set α) : is_glb s (Inf s) :=
  { left := fun (a : α) => Inf_le, right := fun (a : α) => le_Inf }

theorem is_glb.Inf_eq {α : Type u_1} [complete_lattice α] {s : set α} {a : α} (h : is_glb s a) : Inf s = a :=
  is_glb.unique (is_glb_Inf s) h

theorem le_Sup_of_le {α : Type u_1} [complete_lattice α] {s : set α} {a : α} {b : α} (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
  le_trans h (le_Sup hb)

theorem Inf_le_of_le {α : Type u_1} [complete_lattice α] {s : set α} {a : α} {b : α} (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
  le_trans (Inf_le hb) h

theorem Sup_le_Sup {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} (h : s ⊆ t) : Sup s ≤ Sup t :=
  is_lub.mono (is_lub_Sup s) (is_lub_Sup t) h

theorem Inf_le_Inf {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} (h : s ⊆ t) : Inf t ≤ Inf s :=
  is_glb.mono (is_glb_Inf s) (is_glb_Inf t) h

@[simp] theorem Sup_le_iff {α : Type u_1} [complete_lattice α] {s : set α} {a : α} : Sup s ≤ a ↔ ∀ (b : α), b ∈ s → b ≤ a :=
  is_lub_le_iff (is_lub_Sup s)

@[simp] theorem le_Inf_iff {α : Type u_1} [complete_lattice α] {s : set α} {a : α} : a ≤ Inf s ↔ ∀ (b : α), b ∈ s → a ≤ b :=
  le_is_glb_iff (is_glb_Inf s)

theorem Sup_le_Sup_of_forall_exists_le {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} (h : ∀ (x : α) (H : x ∈ s), ∃ (y : α), ∃ (H : y ∈ t), x ≤ y) : Sup s ≤ Sup t := sorry

theorem Inf_le_Inf_of_forall_exists_le {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} (h : ∀ (x : α) (H : x ∈ s), ∃ (y : α), ∃ (H : y ∈ t), y ≤ x) : Inf t ≤ Inf s := sorry

theorem Inf_le_Sup {α : Type u_1} [complete_lattice α] {s : set α} (hs : set.nonempty s) : Inf s ≤ Sup s :=
  is_glb_le_is_lub (is_glb_Inf s) (is_lub_Sup s) hs

-- TODO: it is weird that we have to add union_def

theorem Sup_union {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} : Sup (s ∪ t) = Sup s ⊔ Sup t :=
  is_lub.Sup_eq (is_lub.union (is_lub_Sup s) (is_lub_Sup t))

theorem Sup_inter_le {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} : Sup (s ∩ t) ≤ Sup s ⊓ Sup t := sorry

/-
  Sup_le (assume a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/

theorem Inf_union {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} : Inf (s ∪ t) = Inf s ⊓ Inf t :=
  is_glb.Inf_eq (is_glb.union (is_glb_Inf s) (is_glb_Inf t))

theorem le_Inf_inter {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} : Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
  Sup_inter_le

@[simp] theorem Sup_empty {α : Type u_1} [complete_lattice α] : Sup ∅ = ⊥ :=
  is_lub.Sup_eq is_lub_empty

@[simp] theorem Inf_empty {α : Type u_1} [complete_lattice α] : Inf ∅ = ⊤ :=
  is_glb.Inf_eq is_glb_empty

@[simp] theorem Sup_univ {α : Type u_1} [complete_lattice α] : Sup set.univ = ⊤ :=
  is_lub.Sup_eq is_lub_univ

@[simp] theorem Inf_univ {α : Type u_1} [complete_lattice α] : Inf set.univ = ⊥ :=
  is_glb.Inf_eq is_glb_univ

-- TODO(Jeremy): get this automatically

@[simp] theorem Sup_insert {α : Type u_1} [complete_lattice α] {a : α} {s : set α} : Sup (insert a s) = a ⊔ Sup s :=
  is_lub.Sup_eq (is_lub.insert a (is_lub_Sup s))

@[simp] theorem Inf_insert {α : Type u_1} [complete_lattice α] {a : α} {s : set α} : Inf (insert a s) = a ⊓ Inf s :=
  is_glb.Inf_eq (is_glb.insert a (is_glb_Inf s))

theorem Sup_le_Sup_of_subset_instert_bot {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} (h : s ⊆ insert ⊥ t) : Sup s ≤ Sup t :=
  le_trans (Sup_le_Sup h) (le_of_eq (trans Sup_insert bot_sup_eq))

theorem Inf_le_Inf_of_subset_insert_top {α : Type u_1} [complete_lattice α] {s : set α} {t : set α} (h : s ⊆ insert ⊤ t) : Inf t ≤ Inf s :=
  le_trans (le_of_eq (trans (Eq.symm top_inf_eq) (Eq.symm Inf_insert))) (Inf_le_Inf h)

-- We will generalize this to conditionally complete lattices in `cSup_singleton`.

theorem Sup_singleton {α : Type u_1} [complete_lattice α] {a : α} : Sup (singleton a) = a :=
  is_lub.Sup_eq is_lub_singleton

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.

theorem Inf_singleton {α : Type u_1} [complete_lattice α] {a : α} : Inf (singleton a) = a :=
  is_glb.Inf_eq is_glb_singleton

theorem Sup_pair {α : Type u_1} [complete_lattice α] {a : α} {b : α} : Sup (insert a (singleton b)) = a ⊔ b :=
  is_lub.Sup_eq is_lub_pair

theorem Inf_pair {α : Type u_1} [complete_lattice α] {a : α} {b : α} : Inf (insert a (singleton b)) = a ⊓ b :=
  is_glb.Inf_eq is_glb_pair

@[simp] theorem Inf_eq_top {α : Type u_1} [complete_lattice α] {s : set α} : Inf s = ⊤ ↔ ∀ (a : α), a ∈ s → a = ⊤ :=
  { mp := fun (h : Inf s = ⊤) (a : α) (ha : a ∈ s) => top_unique (h ▸ Inf_le ha),
    mpr :=
      fun (h : ∀ (a : α), a ∈ s → a = ⊤) => top_unique (le_Inf fun (a : α) (ha : a ∈ s) => iff.mpr top_le_iff (h a ha)) }

theorem eq_singleton_top_of_Inf_eq_top_of_nonempty {α : Type u_1} [complete_lattice α] {s : set α} (h_inf : Inf s = ⊤) (hne : set.nonempty s) : s = singleton ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s = singleton ⊤)) (propext set.eq_singleton_iff_nonempty_unique_mem)))
    { left := hne, right := eq.mp (Eq._oldrec (Eq.refl (Inf s = ⊤)) (propext Inf_eq_top)) h_inf }

@[simp] theorem Sup_eq_bot {α : Type u_1} [complete_lattice α] {s : set α} : Sup s = ⊥ ↔ ∀ (a : α), a ∈ s → a = ⊥ :=
  Inf_eq_top

theorem eq_singleton_bot_of_Sup_eq_bot_of_nonempty {α : Type u_1} [complete_lattice α] {s : set α} (h_sup : Sup s = ⊥) (hne : set.nonempty s) : s = singleton ⊥ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s = singleton ⊥)) (propext set.eq_singleton_iff_nonempty_unique_mem)))
    { left := hne, right := eq.mp (Eq._oldrec (Eq.refl (Sup s = ⊥)) (propext Sup_eq_bot)) h_sup }

theorem Inf_lt_iff {α : Type u_1} [complete_linear_order α] {s : set α} {b : α} : Inf s < b ↔ ∃ (a : α), ∃ (H : a ∈ s), a < b :=
  is_glb_lt_iff (is_glb_Inf s)

theorem lt_Sup_iff {α : Type u_1} [complete_linear_order α] {s : set α} {b : α} : b < Sup s ↔ ∃ (a : α), ∃ (H : a ∈ s), b < a :=
  lt_is_lub_iff (is_lub_Sup s)

theorem Sup_eq_top {α : Type u_1} [complete_linear_order α] {s : set α} : Sup s = ⊤ ↔ ∀ (b : α) (H : b < ⊤), ∃ (a : α), ∃ (H : a ∈ s), b < a := sorry

theorem Inf_eq_bot {α : Type u_1} [complete_linear_order α] {s : set α} : Inf s = ⊥ ↔ ∀ (b : α) (H : b > ⊥), ∃ (a : α), ∃ (H : a ∈ s), a < b :=
  Sup_eq_top

theorem lt_supr_iff {α : Type u_1} {ι : Sort u_4} [complete_linear_order α] {a : α} {f : ι → α} : a < supr f ↔ ∃ (i : ι), a < f i :=
  iff.trans lt_Sup_iff set.exists_range_iff

theorem infi_lt_iff {α : Type u_1} {ι : Sort u_4} [complete_linear_order α] {a : α} {f : ι → α} : infi f < a ↔ ∃ (i : ι), f i < a :=
  iff.trans Inf_lt_iff set.exists_range_iff

/-
### supr & infi
-/

-- TODO: this declaration gives error when starting smt state

--@[ematch]

theorem le_supr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (s : ι → α) (i : ι) : s i ≤ supr s :=
  le_Sup (Exists.intro i rfl)

theorem le_supr' {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (s : ι → α) (i : ι) : s i ≤ supr s :=
  le_Sup (Exists.intro i rfl)

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] theorem le_supr' (s : ι → α) (i : ι) : (: s i :) ≤ (: supr s :) :=
le_Sup ⟨i, rfl⟩
-/

theorem is_lub_supr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} : is_lub (set.range s) (supr fun (j : ι) => s j) :=
  is_lub_Sup (set.range s)

theorem is_lub.supr_eq {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} (h : is_lub (set.range s) a) : (supr fun (j : ι) => s j) = a :=
  is_lub.Sup_eq h

theorem is_glb_infi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} : is_glb (set.range s) (infi fun (j : ι) => s j) :=
  is_glb_Inf (set.range s)

theorem is_glb.infi_eq {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} (h : is_glb (set.range s) a) : (infi fun (j : ι) => s j) = a :=
  is_glb.Inf_eq h

theorem le_supr_of_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} (i : ι) (h : a ≤ s i) : a ≤ supr s :=
  le_trans h (le_supr s i)

theorem le_bsupr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} (i : ι) (hi : p i) : f i hi ≤ supr fun (i : ι) => supr fun (hi : p i) => f i hi :=
  le_supr_of_le i (le_supr (f i) hi)

theorem le_bsupr_of_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {a : α} {p : ι → Prop} {f : (i : ι) → p i → α} (i : ι) (hi : p i) (h : a ≤ f i hi) : a ≤ supr fun (i : ι) => supr fun (hi : p i) => f i hi :=
  le_trans h (le_bsupr i hi)

theorem supr_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} (h : ∀ (i : ι), s i ≤ a) : supr s ≤ a := sorry

theorem bsupr_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {a : α} {p : ι → Prop} {f : (i : ι) → p i → α} (h : ∀ (i : ι) (hi : p i), f i hi ≤ a) : (supr fun (i : ι) => supr fun (hi : p i) => f i hi) ≤ a :=
  supr_le fun (i : ι) => supr_le (h i)

theorem bsupr_le_supr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (p : ι → Prop) (f : ι → α) : (supr fun (i : ι) => supr fun (H : p i) => f i) ≤ supr fun (i : ι) => f i :=
  bsupr_le fun (i : ι) (hi : p i) => le_supr f i

theorem supr_le_supr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {t : ι → α} (h : ∀ (i : ι), s i ≤ t i) : supr s ≤ supr t :=
  supr_le fun (i : ι) => le_supr_of_le i (h i)

theorem supr_le_supr2 {α : Type u_1} {ι : Sort u_4} {ι₂ : Sort u_5} [complete_lattice α] {s : ι → α} {t : ι₂ → α} (h : ∀ (i : ι), ∃ (j : ι₂), s i ≤ t j) : supr s ≤ supr t :=
  supr_le fun (j : ι) => exists.elim (h j) le_supr_of_le

theorem bsupr_le_bsupr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} {g : (i : ι) → p i → α} (h : ∀ (i : ι) (hi : p i), f i hi ≤ g i hi) : (supr fun (i : ι) => supr fun (hi : p i) => f i hi) ≤ supr fun (i : ι) => supr fun (hi : p i) => g i hi :=
  bsupr_le fun (i : ι) (hi : p i) => le_trans (h i hi) (le_bsupr i hi)

theorem supr_le_supr_const {α : Type u_1} {ι : Sort u_4} {ι₂ : Sort u_5} [complete_lattice α] {a : α} (h : ι → ι₂) : (supr fun (i : ι) => a) ≤ supr fun (j : ι₂) => a :=
  supr_le ((le_supr fun (j : ι₂) => a) ∘ h)

@[simp] theorem supr_le_iff {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} : supr s ≤ a ↔ ∀ (i : ι), s i ≤ a :=
  iff.trans (is_lub_le_iff is_lub_supr) set.forall_range_iff

theorem supr_lt_iff {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} : supr s < a ↔ ∃ (b : α), ∃ (H : b < a), ∀ (i : ι), s i ≤ b := sorry

theorem Sup_eq_supr {α : Type u_1} [complete_lattice α] {s : set α} : Sup s = supr fun (a : α) => supr fun (H : a ∈ s) => a :=
  le_antisymm (Sup_le fun (b : α) (h : b ∈ s) => le_supr_of_le b (le_supr (fun (h : b ∈ s) => b) h))
    (supr_le fun (b : α) => supr_le fun (h : b ∈ s) => le_Sup h)

theorem le_supr_iff {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} : a ≤ supr s ↔ ∀ (b : α), (∀ (i : ι), s i ≤ b) → a ≤ b :=
  { mp := fun (h : a ≤ supr s) (b : α) (hb : ∀ (i : ι), s i ≤ b) => le_trans h (supr_le hb),
    mpr := fun (h : ∀ (b : α), (∀ (i : ι), s i ≤ b) → a ≤ b) => h (supr s) fun (i : ι) => le_supr s i }

theorem monotone.le_map_supr {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] {s : ι → α} [complete_lattice β] {f : α → β} (hf : monotone f) : (supr fun (i : ι) => f (s i)) ≤ f (supr s) :=
  supr_le fun (i : ι) => hf (le_supr s i)

theorem monotone.le_map_supr2 {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : monotone f) {ι' : ι → Sort u_3} (s : (i : ι) → ι' i → α) : (supr fun (i : ι) => supr fun (h : ι' i) => f (s i h)) ≤ f (supr fun (i : ι) => supr fun (h : ι' i) => s i h) :=
  le_trans (supr_le_supr fun (i : ι) => monotone.le_map_supr hf) (monotone.le_map_supr hf)

theorem monotone.le_map_Sup {α : Type u_1} {β : Type u_2} [complete_lattice α] [complete_lattice β] {s : set α} {f : α → β} (hf : monotone f) : (supr fun (a : α) => supr fun (H : a ∈ s) => f a) ≤ f (Sup s) :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((supr fun (a : α) => supr fun (H : a ∈ s) => f a) ≤ f (Sup s))) Sup_eq_supr))
    (monotone.le_map_supr2 hf fun (a : α) (H : a ∈ s) => a)

theorem supr_comp_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {ι' : Sort u_2} (f : ι' → α) (g : ι → ι') : (supr fun (x : ι) => f (g x)) ≤ supr fun (y : ι') => f y :=
  supr_le_supr2 fun (x : ι) => Exists.intro (g x) (le_refl (f (g x)))

theorem monotone.supr_comp_eq {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] [preorder β] {f : β → α} (hf : monotone f) {s : ι → β} (hs : ∀ (x : β), ∃ (i : ι), x ≤ s i) : (supr fun (x : ι) => f (s x)) = supr fun (y : β) => f y :=
  le_antisymm (supr_comp_le f fun (x : ι) => s x)
    (supr_le_supr2 fun (x : β) => Exists.imp (fun (i : ι) (hi : x ≤ s i) => hf hi) (hs x))

theorem function.surjective.supr_comp {ι : Sort u_4} {ι₂ : Sort u_5} {α : Type u_1} [has_Sup α] {f : ι → ι₂} (hf : function.surjective f) (g : ι₂ → α) : (supr fun (x : ι) => g (f x)) = supr fun (y : ι₂) => g y := sorry

theorem supr_congr {ι : Sort u_4} {ι₂ : Sort u_5} {α : Type u_1} [has_Sup α] {f : ι → α} {g : ι₂ → α} (h : ι → ι₂) (h1 : function.surjective h) (h2 : ∀ (x : ι), g (h x) = f x) : (supr fun (x : ι) => f x) = supr fun (y : ι₂) => g y := sorry

-- TODO: finish doesn't do well here.

theorem supr_congr_Prop {α : Type u_1} [has_Sup α] {p : Prop} {q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q) (f : ∀ (x : q), f₁ (iff.mpr pq x) = f₂ x) : supr f₁ = supr f₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (supr f₁ = supr f₂)) (Eq.symm (funext f))))
    (Eq.symm
      (function.surjective.supr_comp (fun (h : p) => Exists.intro (iff.mp pq h) (Eq.refl (iff.mpr pq (iff.mp pq h)))) f₁))

theorem infi_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (s : ι → α) (i : ι) : infi s ≤ s i :=
  Inf_le (Exists.intro i rfl)

theorem infi_le' {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (s : ι → α) (i : ι) : infi s ≤ s i :=
  Inf_le (Exists.intro i rfl)

theorem infi_le_of_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} (i : ι) (h : s i ≤ a) : infi s ≤ a :=
  le_trans (infi_le s i) h

theorem binfi_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} (i : ι) (hi : p i) : (infi fun (i : ι) => infi fun (hi : p i) => f i hi) ≤ f i hi :=
  infi_le_of_le i (infi_le (f i) hi)

theorem binfi_le_of_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {a : α} {p : ι → Prop} {f : (i : ι) → p i → α} (i : ι) (hi : p i) (h : f i hi ≤ a) : (infi fun (i : ι) => infi fun (hi : p i) => f i hi) ≤ a :=
  le_trans (binfi_le i hi) h

theorem le_infi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} (h : ∀ (i : ι), a ≤ s i) : a ≤ infi s := sorry

theorem le_binfi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {a : α} {p : ι → Prop} {f : (i : ι) → p i → α} (h : ∀ (i : ι) (hi : p i), a ≤ f i hi) : a ≤ infi fun (i : ι) => infi fun (hi : p i) => f i hi :=
  le_infi fun (i : ι) => le_infi (h i)

theorem infi_le_binfi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (p : ι → Prop) (f : ι → α) : (infi fun (i : ι) => f i) ≤ infi fun (i : ι) => infi fun (H : p i) => f i :=
  le_binfi fun (i : ι) (hi : p i) => infi_le f i

theorem infi_le_infi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {t : ι → α} (h : ∀ (i : ι), s i ≤ t i) : infi s ≤ infi t :=
  le_infi fun (i : ι) => infi_le_of_le i (h i)

theorem infi_le_infi2 {α : Type u_1} {ι : Sort u_4} {ι₂ : Sort u_5} [complete_lattice α] {s : ι → α} {t : ι₂ → α} (h : ∀ (j : ι₂), ∃ (i : ι), s i ≤ t j) : infi s ≤ infi t :=
  le_infi fun (j : ι₂) => exists.elim (h j) infi_le_of_le

theorem binfi_le_binfi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} {g : (i : ι) → p i → α} (h : ∀ (i : ι) (hi : p i), f i hi ≤ g i hi) : (infi fun (i : ι) => infi fun (hi : p i) => f i hi) ≤ infi fun (i : ι) => infi fun (hi : p i) => g i hi :=
  le_binfi fun (i : ι) (hi : p i) => le_trans (binfi_le i hi) (h i hi)

theorem infi_le_infi_const {α : Type u_1} {ι : Sort u_4} {ι₂ : Sort u_5} [complete_lattice α] {a : α} (h : ι₂ → ι) : (infi fun (i : ι) => a) ≤ infi fun (j : ι₂) => a :=
  le_infi ((infi_le fun (i : ι) => a) ∘ h)

@[simp] theorem le_infi_iff {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} {a : α} : a ≤ infi s ↔ ∀ (i : ι), a ≤ s i :=
  { mp := fun (this : a ≤ infi s) (i : ι) => le_trans this (infi_le s i), mpr := le_infi }

theorem Inf_eq_infi {α : Type u_1} [complete_lattice α] {s : set α} : Inf s = infi fun (a : α) => infi fun (H : a ∈ s) => a :=
  Sup_eq_supr

theorem monotone.map_infi_le {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] {s : ι → α} [complete_lattice β] {f : α → β} (hf : monotone f) : f (infi s) ≤ infi fun (i : ι) => f (s i) :=
  le_infi fun (i : ι) => hf (infi_le s i)

theorem monotone.map_infi2_le {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] [complete_lattice β] {f : α → β} (hf : monotone f) {ι' : ι → Sort u_3} (s : (i : ι) → ι' i → α) : f (infi fun (i : ι) => infi fun (h : ι' i) => s i h) ≤ infi fun (i : ι) => infi fun (h : ι' i) => f (s i h) :=
  monotone.le_map_supr2 (monotone.order_dual hf) fun (i : ι) (h : ι' i) => s i h

theorem monotone.map_Inf_le {α : Type u_1} {β : Type u_2} [complete_lattice α] [complete_lattice β] {s : set α} {f : α → β} (hf : monotone f) : f (Inf s) ≤ infi fun (a : α) => infi fun (H : a ∈ s) => f a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (f (Inf s) ≤ infi fun (a : α) => infi fun (H : a ∈ s) => f a)) Inf_eq_infi))
    (monotone.map_infi2_le hf fun (a : α) (H : a ∈ s) => a)

theorem le_infi_comp {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {ι' : Sort u_2} (f : ι' → α) (g : ι → ι') : (infi fun (y : ι') => f y) ≤ infi fun (x : ι) => f (g x) :=
  infi_le_infi2 fun (x : ι) => Exists.intro (g x) (le_refl (f (g x)))

theorem monotone.infi_comp_eq {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] [preorder β] {f : β → α} (hf : monotone f) {s : ι → β} (hs : ∀ (x : β), ∃ (i : ι), s i ≤ x) : (infi fun (x : ι) => f (s x)) = infi fun (y : β) => f y :=
  le_antisymm (infi_le_infi2 fun (x : β) => Exists.imp (fun (i : ι) (hi : s i ≤ x) => hf hi) (hs x))
    (le_infi_comp (fun (y : β) => f y) fun (x : ι) => s x)

theorem function.surjective.infi_comp {ι : Sort u_4} {ι₂ : Sort u_5} {α : Type u_1} [has_Inf α] {f : ι → ι₂} (hf : function.surjective f) (g : ι₂ → α) : (infi fun (x : ι) => g (f x)) = infi fun (y : ι₂) => g y :=
  function.surjective.supr_comp hf g

theorem infi_congr {ι : Sort u_4} {ι₂ : Sort u_5} {α : Type u_1} [has_Inf α] {f : ι → α} {g : ι₂ → α} (h : ι → ι₂) (h1 : function.surjective h) (h2 : ∀ (x : ι), g (h x) = f x) : (infi fun (x : ι) => f x) = infi fun (y : ι₂) => g y :=
  supr_congr h h1 h2

theorem infi_congr_Prop {α : Type u_1} [has_Inf α] {p : Prop} {q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q) (f : ∀ (x : q), f₁ (iff.mpr pq x) = f₂ x) : infi f₁ = infi f₂ :=
  supr_congr_Prop pq f

theorem supr_const_le {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {x : α} : (supr fun (h : ι) => x) ≤ x :=
  supr_le fun (_x : ι) => le_rfl

theorem le_infi_const {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {x : α} : x ≤ infi fun (h : ι) => x :=
  le_infi fun (_x : ι) => le_rfl

-- We will generalize this to conditionally complete lattices in `cinfi_const`.

theorem infi_const {α : Type u_1} {ι : Sort u_4} [complete_lattice α] [Nonempty ι] {a : α} : (infi fun (b : ι) => a) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((infi fun (b : ι) => a) = a)) (infi.equations._eqn_1 fun (b : ι) => a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Inf (set.range fun (b : ι) => a) = a)) set.range_const))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Inf (singleton a) = a)) Inf_singleton)) (Eq.refl a)))

-- We will generalize this to conditionally complete lattices in `csupr_const`.

theorem supr_const {α : Type u_1} {ι : Sort u_4} [complete_lattice α] [Nonempty ι] {a : α} : (supr fun (b : ι) => a) = a :=
  infi_const

@[simp] theorem infi_top {α : Type u_1} {ι : Sort u_4} [complete_lattice α] : (infi fun (i : ι) => ⊤) = ⊤ :=
  top_unique (le_infi fun (i : ι) => le_refl ⊤)

@[simp] theorem supr_bot {α : Type u_1} {ι : Sort u_4} [complete_lattice α] : (supr fun (i : ι) => ⊥) = ⊥ :=
  infi_top

@[simp] theorem infi_eq_top {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} : infi s = ⊤ ↔ ∀ (i : ι), s i = ⊤ :=
  iff.trans Inf_eq_top set.forall_range_iff

@[simp] theorem supr_eq_bot {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {s : ι → α} : supr s = ⊥ ↔ ∀ (i : ι), s i = ⊥ :=
  iff.trans Sup_eq_bot set.forall_range_iff

@[simp] theorem infi_pos {α : Type u_1} [complete_lattice α] {p : Prop} {f : p → α} (hp : p) : (infi fun (h : p) => f h) = f hp :=
  le_antisymm (infi_le (fun (h : p) => f h) hp) (le_infi fun (h : p) => le_refl (f hp))

@[simp] theorem infi_neg {α : Type u_1} [complete_lattice α] {p : Prop} {f : p → α} (hp : ¬p) : (infi fun (h : p) => f h) = ⊤ :=
  le_antisymm le_top (le_infi fun (h : p) => false.elim (hp h))

@[simp] theorem supr_pos {α : Type u_1} [complete_lattice α] {p : Prop} {f : p → α} (hp : p) : (supr fun (h : p) => f h) = f hp :=
  le_antisymm (supr_le fun (h : p) => le_refl (f h)) (le_supr f hp)

@[simp] theorem supr_neg {α : Type u_1} [complete_lattice α] {p : Prop} {f : p → α} (hp : ¬p) : (supr fun (h : p) => f h) = ⊥ :=
  le_antisymm (supr_le fun (h : p) => false.elim (hp h)) bot_le

theorem supr_eq_dif {α : Type u_1} [complete_lattice α] {p : Prop} [Decidable p] (a : p → α) : (supr fun (h : p) => a h) = dite p (fun (h : p) => a h) fun (h : ¬p) => ⊥ := sorry

theorem supr_eq_if {α : Type u_1} [complete_lattice α] {p : Prop} [Decidable p] (a : α) : (supr fun (h : p) => a) = ite p a ⊥ :=
  supr_eq_dif fun (_x : p) => a

theorem infi_eq_dif {α : Type u_1} [complete_lattice α] {p : Prop} [Decidable p] (a : p → α) : (infi fun (h : p) => a h) = dite p (fun (h : p) => a h) fun (h : ¬p) => ⊤ :=
  supr_eq_dif fun (h : p) => a h

theorem infi_eq_if {α : Type u_1} [complete_lattice α] {p : Prop} [Decidable p] (a : α) : (infi fun (h : p) => a) = ite p a ⊤ :=
  infi_eq_dif fun (_x : p) => a

-- TODO: should this be @[simp]?

theorem infi_comm {α : Type u_1} {ι : Sort u_4} {ι₂ : Sort u_5} [complete_lattice α] {f : ι → ι₂ → α} : (infi fun (i : ι) => infi fun (j : ι₂) => f i j) = infi fun (j : ι₂) => infi fun (i : ι) => f i j :=
  le_antisymm (le_infi fun (i : ι₂) => le_infi fun (j : ι) => infi_le_of_le j (infi_le (fun (j_1 : ι₂) => f j j_1) i))
    (le_infi fun (j : ι) => le_infi fun (i : ι₂) => infi_le_of_le i (infi_le (fun (i_1 : ι) => f i_1 i) j))

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/

-- TODO: should this be @[simp]?

theorem supr_comm {α : Type u_1} {ι : Sort u_4} {ι₂ : Sort u_5} [complete_lattice α] {f : ι → ι₂ → α} : (supr fun (i : ι) => supr fun (j : ι₂) => f i j) = supr fun (j : ι₂) => supr fun (i : ι) => f i j :=
  infi_comm

@[simp] theorem infi_infi_eq_left {α : Type u_1} {β : Type u_2} [complete_lattice α] {b : β} {f : (x : β) → x = b → α} : (infi fun (x : β) => infi fun (h : x = b) => f x h) = f b rfl := sorry

@[simp] theorem infi_infi_eq_right {α : Type u_1} {β : Type u_2} [complete_lattice α] {b : β} {f : (x : β) → b = x → α} : (infi fun (x : β) => infi fun (h : b = x) => f x h) = f b rfl := sorry

@[simp] theorem supr_supr_eq_left {α : Type u_1} {β : Type u_2} [complete_lattice α] {b : β} {f : (x : β) → x = b → α} : (supr fun (x : β) => supr fun (h : x = b) => f x h) = f b rfl :=
  infi_infi_eq_left

@[simp] theorem supr_supr_eq_right {α : Type u_1} {β : Type u_2} [complete_lattice α] {b : β} {f : (x : β) → b = x → α} : (supr fun (x : β) => supr fun (h : b = x) => f x h) = f b rfl :=
  infi_infi_eq_right

theorem infi_subtype {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : Subtype p → α} : (infi fun (x : Subtype p) => f x) = infi fun (i : ι) => infi fun (h : p i) => f { val := i, property := h } := sorry

theorem infi_subtype' {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} : (infi fun (i : ι) => infi fun (h : p i) => f i h) = infi fun (x : Subtype p) => f (↑x) (subtype.property x) :=
  Eq.symm infi_subtype

theorem infi_subtype'' {α : Type u_1} [complete_lattice α] {ι : Type u_2} (s : set ι) (f : ι → α) : (infi fun (i : ↥s) => f ↑i) = infi fun (t : ι) => infi fun (H : t ∈ s) => f t :=
  infi_subtype

theorem infi_inf_eq {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {f : ι → α} {g : ι → α} : (infi fun (x : ι) => f x ⊓ g x) = (infi fun (x : ι) => f x) ⊓ infi fun (x : ι) => g x := sorry

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/

theorem infi_inf {α : Type u_1} {ι : Sort u_4} [complete_lattice α] [h : Nonempty ι] {f : ι → α} {a : α} : (infi fun (x : ι) => f x) ⊓ a = infi fun (x : ι) => f x ⊓ a := sorry

theorem inf_infi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ infi fun (x : ι) => f x) = infi fun (x : ι) => a ⊓ f x := sorry

theorem binfi_inf {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} {a : α} (h : ∃ (i : ι), p i) : (infi fun (i : ι) => infi fun (h : p i) => f i h) ⊓ a = infi fun (i : ι) => infi fun (h : p i) => f i h ⊓ a := sorry

theorem inf_binfi {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} {a : α} (h : ∃ (i : ι), p i) : (a ⊓ infi fun (i : ι) => infi fun (h : p i) => f i h) = infi fun (i : ι) => infi fun (h : p i) => a ⊓ f i h := sorry

theorem supr_sup_eq {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {g : β → α} : (supr fun (x : β) => f x ⊔ g x) = (supr fun (x : β) => f x) ⊔ supr fun (x : β) => g x :=
  infi_inf_eq

theorem supr_sup {α : Type u_1} {ι : Sort u_4} [complete_lattice α] [h : Nonempty ι] {f : ι → α} {a : α} : (supr fun (x : ι) => f x) ⊔ a = supr fun (x : ι) => f x ⊔ a :=
  infi_inf

theorem sup_supr {α : Type u_1} {ι : Sort u_4} [complete_lattice α] [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ supr fun (x : ι) => f x) = supr fun (x : ι) => a ⊔ f x :=
  inf_infi

/- supr and infi under Prop -/

@[simp] theorem infi_false {α : Type u_1} [complete_lattice α] {s : False → α} : infi s = ⊤ :=
  le_antisymm le_top (le_infi fun (i : False) => false.elim i)

@[simp] theorem supr_false {α : Type u_1} [complete_lattice α] {s : False → α} : supr s = ⊥ :=
  le_antisymm (supr_le fun (i : False) => false.elim i) bot_le

@[simp] theorem infi_true {α : Type u_1} [complete_lattice α] {s : True → α} : infi s = s trivial :=
  le_antisymm (infi_le s trivial)
    (le_infi
      fun (_x : True) => (fun (_a : True) => true.dcases_on _a (idRhs (s trivial ≤ s trivial) (le_refl (s trivial)))) _x)

@[simp] theorem supr_true {α : Type u_1} [complete_lattice α] {s : True → α} : supr s = s trivial := sorry

@[simp] theorem infi_exists {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : Exists p → α} : (infi fun (x : Exists p) => f x) = infi fun (i : ι) => infi fun (h : p i) => f (Exists.intro i h) := sorry

@[simp] theorem supr_exists {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : Exists p → α} : (supr fun (x : Exists p) => f x) = supr fun (i : ι) => supr fun (h : p i) => f (Exists.intro i h) :=
  infi_exists

theorem infi_and {α : Type u_1} [complete_lattice α] {p : Prop} {q : Prop} {s : p ∧ q → α} : infi s = infi fun (h₁ : p) => infi fun (h₂ : q) => s { left := h₁, right := h₂ } := sorry

/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
theorem infi_and' {α : Type u_1} [complete_lattice α] {p : Prop} {q : Prop} {s : p → q → α} : (infi fun (h₁ : p) => infi fun (h₂ : q) => s h₁ h₂) = infi fun (h : p ∧ q) => s (and.left h) (and.right h) :=
  Eq.symm infi_and

theorem supr_and {α : Type u_1} [complete_lattice α] {p : Prop} {q : Prop} {s : p ∧ q → α} : supr s = supr fun (h₁ : p) => supr fun (h₂ : q) => s { left := h₁, right := h₂ } :=
  infi_and

/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
theorem supr_and' {α : Type u_1} [complete_lattice α] {p : Prop} {q : Prop} {s : p → q → α} : (supr fun (h₁ : p) => supr fun (h₂ : q) => s h₁ h₂) = supr fun (h : p ∧ q) => s (and.left h) (and.right h) :=
  Eq.symm supr_and

theorem infi_or {α : Type u_1} [complete_lattice α] {p : Prop} {q : Prop} {s : p ∨ q → α} : infi s = (infi fun (h : p) => s (Or.inl h)) ⊓ infi fun (h : q) => s (Or.inr h) := sorry

theorem supr_or {α : Type u_1} [complete_lattice α] {p : Prop} {q : Prop} {s : p ∨ q → α} : (supr fun (x : p ∨ q) => s x) = (supr fun (i : p) => s (Or.inl i)) ⊔ supr fun (j : q) => s (Or.inr j) :=
  infi_or

theorem Sup_range {ι : Sort u_4} {α : Type u_1} [has_Sup α] {f : ι → α} : Sup (set.range f) = supr f :=
  rfl

theorem Inf_range {ι : Sort u_4} {α : Type u_1} [has_Inf α] {f : ι → α} : Inf (set.range f) = infi f :=
  rfl

theorem supr_range {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] {g : β → α} {f : ι → β} : (supr fun (b : β) => supr fun (H : b ∈ set.range f) => g b) = supr fun (i : ι) => g (f i) := sorry

theorem infi_range {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [complete_lattice α] {g : β → α} {f : ι → β} : (infi fun (b : β) => infi fun (H : b ∈ set.range f) => g b) = infi fun (i : ι) => g (f i) :=
  supr_range

theorem Inf_image {α : Type u_1} {β : Type u_2} [complete_lattice α] {s : set β} {f : β → α} : Inf (f '' s) = infi fun (a : β) => infi fun (H : a ∈ s) => f a := sorry

theorem Sup_image {α : Type u_1} {β : Type u_2} [complete_lattice α] {s : set β} {f : β → α} : Sup (f '' s) = supr fun (a : β) => supr fun (H : a ∈ s) => f a :=
  Inf_image

/-
### supr and infi under set constructions
-/

theorem infi_emptyset {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} : (infi fun (x : β) => infi fun (H : x ∈ ∅) => f x) = ⊤ := sorry

theorem supr_emptyset {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} : (supr fun (x : β) => supr fun (H : x ∈ ∅) => f x) = ⊥ := sorry

theorem infi_univ {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} : (infi fun (x : β) => infi fun (H : x ∈ set.univ) => f x) = infi fun (x : β) => f x := sorry

theorem supr_univ {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} : (supr fun (x : β) => supr fun (H : x ∈ set.univ) => f x) = supr fun (x : β) => f x := sorry

theorem infi_union {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {s : set β} {t : set β} : (infi fun (x : β) => infi fun (H : x ∈ s ∪ t) => f x) =
  (infi fun (x : β) => infi fun (H : x ∈ s) => f x) ⊓ infi fun (x : β) => infi fun (H : x ∈ t) => f x := sorry

theorem infi_split {α : Type u_1} {β : Type u_2} [complete_lattice α] (f : β → α) (p : β → Prop) : (infi fun (i : β) => f i) =
  (infi fun (i : β) => infi fun (h : p i) => f i) ⊓ infi fun (i : β) => infi fun (h : ¬p i) => f i := sorry

theorem infi_split_single {α : Type u_1} {β : Type u_2} [complete_lattice α] (f : β → α) (i₀ : β) : (infi fun (i : β) => f i) = f i₀ ⊓ infi fun (i : β) => infi fun (h : i ≠ i₀) => f i := sorry

theorem infi_le_infi_of_subset {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {s : set β} {t : set β} (h : s ⊆ t) : (infi fun (x : β) => infi fun (H : x ∈ t) => f x) ≤ infi fun (x : β) => infi fun (H : x ∈ s) => f x := sorry

theorem supr_union {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {s : set β} {t : set β} : (supr fun (x : β) => supr fun (H : x ∈ s ∪ t) => f x) =
  (supr fun (x : β) => supr fun (H : x ∈ s) => f x) ⊔ supr fun (x : β) => supr fun (H : x ∈ t) => f x :=
  infi_union

theorem supr_split {α : Type u_1} {β : Type u_2} [complete_lattice α] (f : β → α) (p : β → Prop) : (supr fun (i : β) => f i) =
  (supr fun (i : β) => supr fun (h : p i) => f i) ⊔ supr fun (i : β) => supr fun (h : ¬p i) => f i :=
  infi_split (fun (i : β) => f i) fun (i : β) => p i

theorem supr_split_single {α : Type u_1} {β : Type u_2} [complete_lattice α] (f : β → α) (i₀ : β) : (supr fun (i : β) => f i) = f i₀ ⊔ supr fun (i : β) => supr fun (h : i ≠ i₀) => f i :=
  infi_split_single (fun (i : β) => f i) i₀

theorem supr_le_supr_of_subset {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {s : set β} {t : set β} (h : s ⊆ t) : (supr fun (x : β) => supr fun (H : x ∈ s) => f x) ≤ supr fun (x : β) => supr fun (H : x ∈ t) => f x :=
  infi_le_infi_of_subset h

theorem infi_insert {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {s : set β} {b : β} : (infi fun (x : β) => infi fun (H : x ∈ insert b s) => f x) = f b ⊓ infi fun (x : β) => infi fun (H : x ∈ s) => f x :=
  Eq.trans infi_union (congr_arg (fun (x : α) => x ⊓ infi fun (x : β) => infi fun (H : x ∈ s) => f x) infi_infi_eq_left)

theorem supr_insert {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {s : set β} {b : β} : (supr fun (x : β) => supr fun (H : x ∈ insert b s) => f x) = f b ⊔ supr fun (x : β) => supr fun (H : x ∈ s) => f x :=
  Eq.trans supr_union (congr_arg (fun (x : α) => x ⊔ supr fun (x : β) => supr fun (H : x ∈ s) => f x) supr_supr_eq_left)

theorem infi_singleton {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {b : β} : (infi fun (x : β) => infi fun (H : x ∈ singleton b) => f x) = f b := sorry

theorem infi_pair {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {a : β} {b : β} : (infi fun (x : β) => infi fun (H : x ∈ insert a (singleton b)) => f x) = f a ⊓ f b := sorry

theorem supr_singleton {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {b : β} : (supr fun (x : β) => supr fun (H : x ∈ singleton b) => f x) = f b :=
  infi_singleton

theorem supr_pair {α : Type u_1} {β : Type u_2} [complete_lattice α] {f : β → α} {a : β} {b : β} : (supr fun (x : β) => supr fun (H : x ∈ insert a (singleton b)) => f x) = f a ⊔ f b := sorry

theorem infi_image {α : Type u_1} {β : Type u_2} [complete_lattice α] {γ : Type u_3} {f : β → γ} {g : γ → α} {t : set β} : (infi fun (c : γ) => infi fun (H : c ∈ f '' t) => g c) = infi fun (b : β) => infi fun (H : b ∈ t) => g (f b) := sorry

theorem supr_image {α : Type u_1} {β : Type u_2} [complete_lattice α] {γ : Type u_3} {f : β → γ} {g : γ → α} {t : set β} : (supr fun (c : γ) => supr fun (H : c ∈ f '' t) => g c) = supr fun (b : β) => supr fun (H : b ∈ t) => g (f b) :=
  infi_image

/-!
### `supr` and `infi` under `Type`
-/

theorem infi_of_empty' {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (h : ι → False) {s : ι → α} : infi s = ⊤ :=
  top_unique (le_infi fun (i : ι) => false.elim (h i))

theorem supr_of_empty' {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (h : ι → False) {s : ι → α} : supr s = ⊥ :=
  bot_unique (supr_le fun (i : ι) => false.elim (h i))

theorem infi_of_empty {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (h : ¬Nonempty ι) {s : ι → α} : infi s = ⊤ :=
  infi_of_empty' fun (i : ι) => h (Nonempty.intro i)

theorem supr_of_empty {α : Type u_1} {ι : Sort u_4} [complete_lattice α] (h : ¬Nonempty ι) {s : ι → α} : supr s = ⊥ :=
  supr_of_empty' fun (i : ι) => h (Nonempty.intro i)

@[simp] theorem infi_empty {α : Type u_1} [complete_lattice α] {s : empty → α} : infi s = ⊤ :=
  infi_of_empty nonempty_empty

@[simp] theorem supr_empty {α : Type u_1} [complete_lattice α] {s : empty → α} : supr s = ⊥ :=
  supr_of_empty nonempty_empty

theorem supr_bool_eq {α : Type u_1} [complete_lattice α] {f : Bool → α} : (supr fun (b : Bool) => f b) = f tt ⊔ f false := sorry

theorem infi_bool_eq {α : Type u_1} [complete_lattice α] {f : Bool → α} : (infi fun (b : Bool) => f b) = f tt ⊓ f false :=
  supr_bool_eq

theorem is_glb_binfi {α : Type u_1} {β : Type u_2} [complete_lattice α] {s : set β} {f : β → α} : is_glb (f '' s) (infi fun (x : β) => infi fun (H : x ∈ s) => f x) := sorry

theorem supr_subtype {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : Subtype p → α} : (supr fun (x : Subtype p) => f x) = supr fun (i : ι) => supr fun (h : p i) => f { val := i, property := h } :=
  infi_subtype

theorem supr_subtype' {α : Type u_1} {ι : Sort u_4} [complete_lattice α] {p : ι → Prop} {f : (i : ι) → p i → α} : (supr fun (i : ι) => supr fun (h : p i) => f i h) = supr fun (x : Subtype p) => f (↑x) (subtype.property x) :=
  Eq.symm supr_subtype

theorem Sup_eq_supr' {α : Type u_1} [complete_lattice α] {s : set α} : Sup s = supr fun (x : ↥s) => ↑x := sorry

theorem is_lub_bsupr {α : Type u_1} {β : Type u_2} [complete_lattice α] {s : set β} {f : β → α} : is_lub (f '' s) (supr fun (x : β) => supr fun (H : x ∈ s) => f x) := sorry

theorem infi_sigma {α : Type u_1} {β : Type u_2} [complete_lattice α] {p : β → Type u_3} {f : sigma p → α} : (infi fun (x : sigma p) => f x) = infi fun (i : β) => infi fun (h : p i) => f (sigma.mk i h) := sorry

theorem supr_sigma {α : Type u_1} {β : Type u_2} [complete_lattice α] {p : β → Type u_3} {f : sigma p → α} : (supr fun (x : sigma p) => f x) = supr fun (i : β) => supr fun (h : p i) => f (sigma.mk i h) :=
  infi_sigma

theorem infi_prod {α : Type u_1} {β : Type u_2} [complete_lattice α] {γ : Type u_3} {f : β × γ → α} : (infi fun (x : β × γ) => f x) = infi fun (i : β) => infi fun (j : γ) => f (i, j) := sorry

theorem supr_prod {α : Type u_1} {β : Type u_2} [complete_lattice α] {γ : Type u_3} {f : β × γ → α} : (supr fun (x : β × γ) => f x) = supr fun (i : β) => supr fun (j : γ) => f (i, j) :=
  infi_prod

theorem infi_sum {α : Type u_1} {β : Type u_2} [complete_lattice α] {γ : Type u_3} {f : β ⊕ γ → α} : (infi fun (x : β ⊕ γ) => f x) = (infi fun (i : β) => f (sum.inl i)) ⊓ infi fun (j : γ) => f (sum.inr j) := sorry

theorem supr_sum {α : Type u_1} {β : Type u_2} [complete_lattice α] {γ : Type u_3} {f : β ⊕ γ → α} : (supr fun (x : β ⊕ γ) => f x) = (supr fun (i : β) => f (sum.inl i)) ⊔ supr fun (j : γ) => f (sum.inr j) :=
  infi_sum

/-!
### `supr` and `infi` under `ℕ`
-/

theorem supr_ge_eq_supr_nat_add {α : Type u_1} [complete_lattice α] {u : ℕ → α} (n : ℕ) : (supr fun (i : ℕ) => supr fun (H : i ≥ n) => u i) = supr fun (i : ℕ) => u (i + n) := sorry

theorem infi_ge_eq_infi_nat_add {α : Type u_1} [complete_lattice α] {u : ℕ → α} (n : ℕ) : (infi fun (i : ℕ) => infi fun (H : i ≥ n) => u i) = infi fun (i : ℕ) => u (i + n) :=
  supr_ge_eq_supr_nat_add n

theorem supr_eq_top {α : Type u_1} {ι : Sort u_4} [complete_linear_order α] (f : ι → α) : supr f = ⊤ ↔ ∀ (b : α), b < ⊤ → ∃ (i : ι), b < f i := sorry

theorem infi_eq_bot {α : Type u_1} {ι : Sort u_4} [complete_linear_order α] (f : ι → α) : infi f = ⊥ ↔ ∀ (b : α), b > ⊥ → ∃ (i : ι), f i < b := sorry

/-!
### Instances
-/

protected instance complete_lattice_Prop : complete_lattice Prop :=
  complete_lattice.mk bounded_distrib_lattice.sup bounded_distrib_lattice.le bounded_distrib_lattice.lt sorry sorry sorry
    sorry sorry sorry bounded_distrib_lattice.inf sorry sorry sorry bounded_distrib_lattice.top sorry
    bounded_distrib_lattice.bot sorry (fun (s : set Prop) => ∃ (a : Prop), ∃ (H : a ∈ s), a)
    (fun (s : set Prop) => ∀ (a : Prop), a ∈ s → a) sorry sorry sorry sorry

theorem Inf_Prop_eq {s : set Prop} : Inf s = ∀ (p : Prop), p ∈ s → p :=
  rfl

theorem Sup_Prop_eq {s : set Prop} : Sup s = ∃ (p : Prop), ∃ (H : p ∈ s), p :=
  rfl

theorem infi_Prop_eq {ι : Sort u_1} {p : ι → Prop} : (infi fun (i : ι) => p i) = ∀ (i : ι), p i := sorry

theorem supr_Prop_eq {ι : Sort u_1} {p : ι → Prop} : (supr fun (i : ι) => p i) = ∃ (i : ι), p i := sorry

protected instance pi.has_Sup {α : Type u_1} {β : α → Type u_2} [(i : α) → has_Sup (β i)] : has_Sup ((i : α) → β i) :=
  has_Sup.mk fun (s : set ((i : α) → β i)) (i : α) => supr fun (f : ↥s) => coe f i

protected instance pi.has_Inf {α : Type u_1} {β : α → Type u_2} [(i : α) → has_Inf (β i)] : has_Inf ((i : α) → β i) :=
  has_Inf.mk fun (s : set ((i : α) → β i)) (i : α) => infi fun (f : ↥s) => coe f i

protected instance pi.complete_lattice {α : Type u_1} {β : α → Type u_2} [(i : α) → complete_lattice (β i)] : complete_lattice ((i : α) → β i) :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry Sup Inf sorry sorry sorry
    sorry

theorem Inf_apply {α : Type u_1} {β : α → Type u_2} [(i : α) → has_Inf (β i)] {s : set ((a : α) → β a)} {a : α} : Inf s a = infi fun (f : ↥s) => coe f a :=
  rfl

theorem infi_apply {α : Type u_1} {β : α → Type u_2} {ι : Sort u_3} [(i : α) → has_Inf (β i)] {f : ι → (a : α) → β a} {a : α} : infi (fun (i : ι) => f i) a = infi fun (i : ι) => f i a := sorry

theorem Sup_apply {α : Type u_1} {β : α → Type u_2} [(i : α) → has_Sup (β i)] {s : set ((a : α) → β a)} {a : α} : Sup s a = supr fun (f : ↥s) => coe f a :=
  rfl

theorem supr_apply {α : Type u_1} {β : α → Type u_2} {ι : Sort u_3} [(i : α) → has_Sup (β i)] {f : ι → (a : α) → β a} {a : α} : supr (fun (i : ι) => f i) a = supr fun (i : ι) => f i a :=
  infi_apply

theorem monotone_Sup_of_monotone {α : Type u_1} {β : Type u_2} [preorder α] [complete_lattice β] {s : set (α → β)} (m_s : ∀ (f : α → β), f ∈ s → monotone f) : monotone (Sup s) :=
  fun (x y : α) (h : x ≤ y) => supr_le fun (f : ↥s) => le_supr_of_le f (m_s (↑f) (subtype.property f) h)

theorem monotone_Inf_of_monotone {α : Type u_1} {β : Type u_2} [preorder α] [complete_lattice β] {s : set (α → β)} (m_s : ∀ (f : α → β), f ∈ s → monotone f) : monotone (Inf s) :=
  fun (x y : α) (h : x ≤ y) => le_infi fun (f : ↥s) => infi_le_of_le f (m_s (↑f) (subtype.property f) h)

namespace prod


protected instance has_Inf (α : Type u_1) (β : Type u_2) [has_Inf α] [has_Inf β] : has_Inf (α × β) :=
  has_Inf.mk fun (s : set (α × β)) => (Inf (fst '' s), Inf (snd '' s))

protected instance has_Sup (α : Type u_1) (β : Type u_2) [has_Sup α] [has_Sup β] : has_Sup (α × β) :=
  has_Sup.mk fun (s : set (α × β)) => (Sup (fst '' s), Sup (snd '' s))

protected instance complete_lattice (α : Type u_1) (β : Type u_2) [complete_lattice α] [complete_lattice β] : complete_lattice (α × β) :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry Sup Inf sorry sorry sorry
    sorry

