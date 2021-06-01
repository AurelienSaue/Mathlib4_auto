/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.set.intervals.basic
import Mathlib.algebra.ordered_group
import Mathlib.PostPort

universes u u_1 w v 

namespace Mathlib

/-!

# Upper / lower bounds

In this file we define:

* `upper_bounds`, `lower_bounds` : the set of upper bounds (resp., lower bounds) of a set;
* `bdd_above s`, `bdd_below s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `is_least s a`, `is_greatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `is_lub s a`, `is_glb s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.

We also prove various lemmas about monotonicity, behaviour under `∪`, `∩`, `insert`, and provide
formulas for `∅`, `univ`, and intervals.
-/

/-!
### Definitions
-/

/-- The set of upper bounds of a set. -/
/-- The set of lower bounds of a set. -/
def upper_bounds {α : Type u} [preorder α] (s : set α) : set α :=
  set_of fun (x : α) => ∀ {a : α}, a ∈ s → a ≤ x

def lower_bounds {α : Type u} [preorder α] (s : set α) : set α :=
  set_of fun (x : α) => ∀ {a : α}, a ∈ s → x ≤ a

/-- A set is bounded above if there exists an upper bound. -/
/-- A set is bounded below if there exists a lower bound. -/
def bdd_above {α : Type u} [preorder α] (s : set α) := set.nonempty (upper_bounds s)

def bdd_below {α : Type u} [preorder α] (s : set α) := set.nonempty (lower_bounds s)

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists -/
def is_least {α : Type u} [preorder α] (s : set α) (a : α) := a ∈ s ∧ a ∈ lower_bounds s

def is_greatest {α : Type u} [preorder α] (s : set α) (a : α) := a ∈ s ∧ a ∈ upper_bounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def is_lub {α : Type u} [preorder α] (s : set α) : α → Prop := is_least (upper_bounds s)

def is_glb {α : Type u} [preorder α] (s : set α) : α → Prop := is_greatest (lower_bounds s)

theorem mem_upper_bounds {α : Type u} [preorder α] {s : set α} {a : α} :
    a ∈ upper_bounds s ↔ ∀ (x : α), x ∈ s → x ≤ a :=
  iff.rfl

theorem mem_lower_bounds {α : Type u} [preorder α] {s : set α} {a : α} :
    a ∈ lower_bounds s ↔ ∀ (x : α), x ∈ s → a ≤ x :=
  iff.rfl

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` such that `x`
is not greater than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(y ≤ x)`. A version for linear orders is called `not_bdd_above_iff`. -/
theorem not_bdd_above_iff' {α : Type u} [preorder α] {s : set α} :
    ¬bdd_above s ↔ ∀ (x : α), ∃ (y : α), ∃ (H : y ∈ s), ¬y ≤ x :=
  sorry

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` such that `x`
is not less than or equal to `y`. This version only assumes `preorder` structure and uses
`¬(x ≤ y)`. A version for linear orders is called `not_bdd_below_iff`. -/
theorem not_bdd_below_iff' {α : Type u} [preorder α] {s : set α} :
    ¬bdd_below s ↔ ∀ (x : α), ∃ (y : α), ∃ (H : y ∈ s), ¬x ≤ y :=
  not_bdd_above_iff'

/-- A set `s` is not bounded above if and only if for each `x` there exists `y ∈ s` that is greater
than `x`. A version for preorders is called `not_bdd_above_iff'`. -/
theorem not_bdd_above_iff {α : Type u_1} [linear_order α] {s : set α} :
    ¬bdd_above s ↔ ∀ (x : α), ∃ (y : α), ∃ (H : y ∈ s), x < y :=
  sorry

/-- A set `s` is not bounded below if and only if for each `x` there exists `y ∈ s` that is less
than `x`. A version for preorders is called `not_bdd_below_iff'`. -/
theorem not_bdd_below_iff {α : Type u_1} [linear_order α] {s : set α} :
    ¬bdd_below s ↔ ∀ (x : α), ∃ (y : α), ∃ (H : y ∈ s), y < x :=
  not_bdd_above_iff

/-!
### Monotonicity
-/

theorem upper_bounds_mono_set {α : Type u} [preorder α] {s : set α} {t : set α} (hst : s ⊆ t) :
    upper_bounds t ⊆ upper_bounds s :=
  fun (b : α) (hb : b ∈ upper_bounds t) (x : α) (h : x ∈ s) => hb (hst h)

theorem lower_bounds_mono_set {α : Type u} [preorder α] {s : set α} {t : set α} (hst : s ⊆ t) :
    lower_bounds t ⊆ lower_bounds s :=
  fun (b : α) (hb : b ∈ lower_bounds t) (x : α) (h : x ∈ s) => hb (hst h)

theorem upper_bounds_mono_mem {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (hab : a ≤ b) :
    a ∈ upper_bounds s → b ∈ upper_bounds s :=
  fun (ha : a ∈ upper_bounds s) (x : α) (h : x ∈ s) => le_trans (ha h) hab

theorem lower_bounds_mono_mem {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (hab : a ≤ b) :
    b ∈ lower_bounds s → a ∈ lower_bounds s :=
  fun (hb : b ∈ lower_bounds s) (x : α) (h : x ∈ s) => le_trans hab (hb h)

theorem upper_bounds_mono {α : Type u} [preorder α] {s : set α} {t : set α} (hst : s ⊆ t) {a : α}
    {b : α} (hab : a ≤ b) : a ∈ upper_bounds t → b ∈ upper_bounds s :=
  fun (ha : a ∈ upper_bounds t) => upper_bounds_mono_set hst (upper_bounds_mono_mem hab ha)

theorem lower_bounds_mono {α : Type u} [preorder α] {s : set α} {t : set α} (hst : s ⊆ t) {a : α}
    {b : α} (hab : a ≤ b) : b ∈ lower_bounds t → a ∈ lower_bounds s :=
  fun (hb : b ∈ lower_bounds t) => lower_bounds_mono_set hst (lower_bounds_mono_mem hab hb)

/-- If `s ⊆ t` and `t` is bounded above, then so is `s`. -/
theorem bdd_above.mono {α : Type u} [preorder α] {s : set α} {t : set α} (h : s ⊆ t) :
    bdd_above t → bdd_above s :=
  set.nonempty.mono (upper_bounds_mono_set h)

/-- If `s ⊆ t` and `t` is bounded below, then so is `s`. -/
theorem bdd_below.mono {α : Type u} [preorder α] {s : set α} {t : set α} (h : s ⊆ t) :
    bdd_below t → bdd_below s :=
  set.nonempty.mono (lower_bounds_mono_set h)

/-- If `a` is a least upper bound for sets `s` and `p`, then it is a least upper bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem is_lub.of_subset_of_superset {α : Type u} [preorder α] {a : α} {s : set α} {t : set α}
    {p : set α} (hs : is_lub s a) (hp : is_lub p a) (hst : s ⊆ t) (htp : t ⊆ p) : is_lub t a :=
  { left := upper_bounds_mono_set htp (and.left hp),
    right := lower_bounds_mono_set (upper_bounds_mono_set hst) (and.right hs) }

/-- If `a` is a greatest lower bound for sets `s` and `p`, then it is a greater lower bound for any
set `t`, `s ⊆ t ⊆ p`. -/
theorem is_glb.of_subset_of_superset {α : Type u} [preorder α] {a : α} {s : set α} {t : set α}
    {p : set α} (hs : is_glb s a) (hp : is_glb p a) (hst : s ⊆ t) (htp : t ⊆ p) : is_glb t a :=
  is_lub.of_subset_of_superset hs hp hst htp

theorem is_least.mono {α : Type u} [preorder α] {s : set α} {t : set α} {a : α} {b : α}
    (ha : is_least s a) (hb : is_least t b) (hst : s ⊆ t) : b ≤ a :=
  and.right hb a (hst (and.left ha))

theorem is_greatest.mono {α : Type u} [preorder α] {s : set α} {t : set α} {a : α} {b : α}
    (ha : is_greatest s a) (hb : is_greatest t b) (hst : s ⊆ t) : a ≤ b :=
  and.right hb a (hst (and.left ha))

theorem is_lub.mono {α : Type u} [preorder α] {s : set α} {t : set α} {a : α} {b : α}
    (ha : is_lub s a) (hb : is_lub t b) (hst : s ⊆ t) : a ≤ b :=
  is_least.mono hb ha (upper_bounds_mono_set hst)

theorem is_glb.mono {α : Type u} [preorder α] {s : set α} {t : set α} {a : α} {b : α}
    (ha : is_glb s a) (hb : is_glb t b) (hst : s ⊆ t) : b ≤ a :=
  is_greatest.mono hb ha (lower_bounds_mono_set hst)

/-!
### Conversions
-/

theorem is_least.is_glb {α : Type u} [preorder α] {s : set α} {a : α} (h : is_least s a) :
    is_glb s a :=
  { left := and.right h, right := fun (b : α) (hb : b ∈ lower_bounds s) => hb (and.left h) }

theorem is_greatest.is_lub {α : Type u} [preorder α] {s : set α} {a : α} (h : is_greatest s a) :
    is_lub s a :=
  { left := and.right h, right := fun (b : α) (hb : b ∈ upper_bounds s) => hb (and.left h) }

theorem is_lub.upper_bounds_eq {α : Type u} [preorder α] {s : set α} {a : α} (h : is_lub s a) :
    upper_bounds s = set.Ici a :=
  sorry

theorem is_glb.lower_bounds_eq {α : Type u} [preorder α] {s : set α} {a : α} (h : is_glb s a) :
    lower_bounds s = set.Iic a :=
  is_lub.upper_bounds_eq h

theorem is_least.lower_bounds_eq {α : Type u} [preorder α] {s : set α} {a : α} (h : is_least s a) :
    lower_bounds s = set.Iic a :=
  is_glb.lower_bounds_eq (is_least.is_glb h)

theorem is_greatest.upper_bounds_eq {α : Type u} [preorder α] {s : set α} {a : α}
    (h : is_greatest s a) : upper_bounds s = set.Ici a :=
  is_lub.upper_bounds_eq (is_greatest.is_lub h)

theorem is_lub_le_iff {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (h : is_lub s a) :
    a ≤ b ↔ b ∈ upper_bounds s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b ↔ b ∈ upper_bounds s)) (is_lub.upper_bounds_eq h)))
    (iff.refl (a ≤ b))

theorem le_is_glb_iff {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (h : is_glb s a) :
    b ≤ a ↔ b ∈ lower_bounds s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b ≤ a ↔ b ∈ lower_bounds s)) (is_glb.lower_bounds_eq h)))
    (iff.refl (b ≤ a))

/-- If `s` has a least upper bound, then it is bounded above. -/
theorem is_lub.bdd_above {α : Type u} [preorder α] {s : set α} {a : α} (h : is_lub s a) :
    bdd_above s :=
  Exists.intro a (and.left h)

/-- If `s` has a greatest lower bound, then it is bounded below. -/
theorem is_glb.bdd_below {α : Type u} [preorder α] {s : set α} {a : α} (h : is_glb s a) :
    bdd_below s :=
  Exists.intro a (and.left h)

/-- If `s` has a greatest element, then it is bounded above. -/
theorem is_greatest.bdd_above {α : Type u} [preorder α] {s : set α} {a : α} (h : is_greatest s a) :
    bdd_above s :=
  Exists.intro a (and.right h)

/-- If `s` has a least element, then it is bounded below. -/
theorem is_least.bdd_below {α : Type u} [preorder α] {s : set α} {a : α} (h : is_least s a) :
    bdd_below s :=
  Exists.intro a (and.right h)

theorem is_least.nonempty {α : Type u} [preorder α] {s : set α} {a : α} (h : is_least s a) :
    set.nonempty s :=
  Exists.intro a (and.left h)

theorem is_greatest.nonempty {α : Type u} [preorder α] {s : set α} {a : α} (h : is_greatest s a) :
    set.nonempty s :=
  Exists.intro a (and.left h)

/-!
### Union and intersection
-/

@[simp] theorem upper_bounds_union {α : Type u} [preorder α] {s : set α} {t : set α} :
    upper_bounds (s ∪ t) = upper_bounds s ∩ upper_bounds t :=
  sorry

@[simp] theorem lower_bounds_union {α : Type u} [preorder α] {s : set α} {t : set α} :
    lower_bounds (s ∪ t) = lower_bounds s ∩ lower_bounds t :=
  upper_bounds_union

theorem union_upper_bounds_subset_upper_bounds_inter {α : Type u} [preorder α] {s : set α}
    {t : set α} : upper_bounds s ∪ upper_bounds t ⊆ upper_bounds (s ∩ t) :=
  set.union_subset (upper_bounds_mono_set (set.inter_subset_left s t))
    (upper_bounds_mono_set (set.inter_subset_right s t))

theorem union_lower_bounds_subset_lower_bounds_inter {α : Type u} [preorder α] {s : set α}
    {t : set α} : lower_bounds s ∪ lower_bounds t ⊆ lower_bounds (s ∩ t) :=
  union_upper_bounds_subset_upper_bounds_inter

theorem is_least_union_iff {α : Type u} [preorder α] {a : α} {s : set α} {t : set α} :
    is_least (s ∪ t) a ↔ is_least s a ∧ a ∈ lower_bounds t ∨ a ∈ lower_bounds s ∧ is_least t a :=
  sorry

theorem is_greatest_union_iff {α : Type u} [preorder α] {s : set α} {t : set α} {a : α} :
    is_greatest (s ∪ t) a ↔
        is_greatest s a ∧ a ∈ upper_bounds t ∨ a ∈ upper_bounds s ∧ is_greatest t a :=
  is_least_union_iff

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem bdd_above.inter_of_left {α : Type u} [preorder α] {s : set α} {t : set α}
    (h : bdd_above s) : bdd_above (s ∩ t) :=
  bdd_above.mono (set.inter_subset_left s t) h

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem bdd_above.inter_of_right {α : Type u} [preorder α] {s : set α} {t : set α}
    (h : bdd_above t) : bdd_above (s ∩ t) :=
  bdd_above.mono (set.inter_subset_right s t) h

/-- If `s` is bounded, then so is `s ∩ t` -/
theorem bdd_below.inter_of_left {α : Type u} [preorder α] {s : set α} {t : set α}
    (h : bdd_below s) : bdd_below (s ∩ t) :=
  bdd_below.mono (set.inter_subset_left s t) h

/-- If `t` is bounded, then so is `s ∩ t` -/
theorem bdd_below.inter_of_right {α : Type u} [preorder α] {s : set α} {t : set α}
    (h : bdd_below t) : bdd_below (s ∩ t) :=
  bdd_below.mono (set.inter_subset_right s t) h

/-- If `s` and `t` are bounded above sets in a `semilattice_sup`, then so is `s ∪ t`. -/
theorem bdd_above.union {γ : Type w} [semilattice_sup γ] {s : set γ} {t : set γ} :
    bdd_above s → bdd_above t → bdd_above (s ∪ t) :=
  sorry

/-- The union of two sets is bounded above if and only if each of the sets is. -/
theorem bdd_above_union {γ : Type w} [semilattice_sup γ] {s : set γ} {t : set γ} :
    bdd_above (s ∪ t) ↔ bdd_above s ∧ bdd_above t :=
  sorry

theorem bdd_below.union {γ : Type w} [semilattice_inf γ] {s : set γ} {t : set γ} :
    bdd_below s → bdd_below t → bdd_below (s ∪ t) :=
  bdd_above.union

/--The union of two sets is bounded above if and only if each of the sets is.-/
theorem bdd_below_union {γ : Type w} [semilattice_inf γ] {s : set γ} {t : set γ} :
    bdd_below (s ∪ t) ↔ bdd_below s ∧ bdd_below t :=
  bdd_above_union

/-- If `a` is the least upper bound of `s` and `b` is the least upper bound of `t`,
then `a ⊔ b` is the least upper bound of `s ∪ t`. -/
theorem is_lub.union {γ : Type w} [semilattice_sup γ] {a : γ} {b : γ} {s : set γ} {t : set γ}
    (hs : is_lub s a) (ht : is_lub t b) : is_lub (s ∪ t) (a ⊔ b) :=
  sorry

/-- If `a` is the greatest lower bound of `s` and `b` is the greatest lower bound of `t`,
then `a ⊓ b` is the greatest lower bound of `s ∪ t`. -/
theorem is_glb.union {γ : Type w} [semilattice_inf γ] {a₁ : γ} {a₂ : γ} {s : set γ} {t : set γ}
    (hs : is_glb s a₁) (ht : is_glb t a₂) : is_glb (s ∪ t) (a₁ ⊓ a₂) :=
  is_lub.union hs ht

/-- If `a` is the least element of `s` and `b` is the least element of `t`,
then `min a b` is the least element of `s ∪ t`. -/
theorem is_least.union {γ : Type w} [linear_order γ] {a : γ} {b : γ} {s : set γ} {t : set γ}
    (ha : is_least s a) (hb : is_least t b) : is_least (s ∪ t) (min a b) :=
  sorry

/-- If `a` is the greatest element of `s` and `b` is the greatest element of `t`,
then `max a b` is the greatest element of `s ∪ t`. -/
theorem is_greatest.union {γ : Type w} [linear_order γ] {a : γ} {b : γ} {s : set γ} {t : set γ}
    (ha : is_greatest s a) (hb : is_greatest t b) : is_greatest (s ∪ t) (max a b) :=
  sorry

/-!
### Specific sets

#### Unbounded intervals
-/

theorem is_least_Ici {α : Type u} [preorder α] {a : α} : is_least (set.Ici a) a :=
  { left := set.left_mem_Ici, right := fun (x : α) => id }

theorem is_greatest_Iic {α : Type u} [preorder α] {a : α} : is_greatest (set.Iic a) a :=
  { left := set.right_mem_Iic, right := fun (x : α) => id }

theorem is_lub_Iic {α : Type u} [preorder α] {a : α} : is_lub (set.Iic a) a :=
  is_greatest.is_lub is_greatest_Iic

theorem is_glb_Ici {α : Type u} [preorder α] {a : α} : is_glb (set.Ici a) a :=
  is_least.is_glb is_least_Ici

theorem upper_bounds_Iic {α : Type u} [preorder α] {a : α} : upper_bounds (set.Iic a) = set.Ici a :=
  is_lub.upper_bounds_eq is_lub_Iic

theorem lower_bounds_Ici {α : Type u} [preorder α] {a : α} : lower_bounds (set.Ici a) = set.Iic a :=
  is_glb.lower_bounds_eq is_glb_Ici

theorem bdd_above_Iic {α : Type u} [preorder α] {a : α} : bdd_above (set.Iic a) :=
  is_lub.bdd_above is_lub_Iic

theorem bdd_below_Ici {α : Type u} [preorder α] {a : α} : bdd_below (set.Ici a) :=
  is_glb.bdd_below is_glb_Ici

theorem bdd_above_Iio {α : Type u} [preorder α] {a : α} : bdd_above (set.Iio a) :=
  Exists.intro a fun (x : α) (hx : x ∈ set.Iio a) => le_of_lt hx

theorem bdd_below_Ioi {α : Type u} [preorder α] {a : α} : bdd_below (set.Ioi a) :=
  Exists.intro a fun (x : α) (hx : x ∈ set.Ioi a) => le_of_lt hx

theorem is_lub_Iio {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} :
    is_lub (set.Iio a) a :=
  { left := fun (x : γ) (hx : x ∈ set.Iio a) => le_of_lt hx,
    right := fun (y : γ) (hy : y ∈ upper_bounds (set.Iio a)) => le_of_forall_ge_of_dense hy }

theorem is_glb_Ioi {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} :
    is_glb (set.Ioi a) a :=
  is_lub_Iio

theorem upper_bounds_Iio {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} :
    upper_bounds (set.Iio a) = set.Ici a :=
  is_lub.upper_bounds_eq is_lub_Iio

theorem lower_bounds_Ioi {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} :
    lower_bounds (set.Ioi a) = set.Iic a :=
  is_glb.lower_bounds_eq is_glb_Ioi

/-!
#### Singleton
-/

theorem is_greatest_singleton {α : Type u} [preorder α] {a : α} : is_greatest (singleton a) a :=
  { left := set.mem_singleton a,
    right := fun (x : α) (hx : x ∈ singleton a) => le_of_eq (set.eq_of_mem_singleton hx) }

theorem is_least_singleton {α : Type u} [preorder α] {a : α} : is_least (singleton a) a :=
  is_greatest_singleton

theorem is_lub_singleton {α : Type u} [preorder α] {a : α} : is_lub (singleton a) a :=
  is_greatest.is_lub is_greatest_singleton

theorem is_glb_singleton {α : Type u} [preorder α] {a : α} : is_glb (singleton a) a :=
  is_least.is_glb is_least_singleton

theorem bdd_above_singleton {α : Type u} [preorder α] {a : α} : bdd_above (singleton a) :=
  is_lub.bdd_above is_lub_singleton

theorem bdd_below_singleton {α : Type u} [preorder α] {a : α} : bdd_below (singleton a) :=
  is_glb.bdd_below is_glb_singleton

@[simp] theorem upper_bounds_singleton {α : Type u} [preorder α] {a : α} :
    upper_bounds (singleton a) = set.Ici a :=
  is_lub.upper_bounds_eq is_lub_singleton

@[simp] theorem lower_bounds_singleton {α : Type u} [preorder α] {a : α} :
    lower_bounds (singleton a) = set.Iic a :=
  is_glb.lower_bounds_eq is_glb_singleton

/-!
#### Bounded intervals
-/

theorem bdd_above_Icc {α : Type u} [preorder α] {a : α} {b : α} : bdd_above (set.Icc a b) :=
  Exists.intro b fun (_x : α) => and.right

theorem bdd_below_Icc {α : Type u} [preorder α] {a : α} {b : α} : bdd_below (set.Icc a b) :=
  Exists.intro a fun (_x : α) => and.left

theorem bdd_above_Ico {α : Type u} [preorder α] {a : α} {b : α} : bdd_above (set.Ico a b) :=
  bdd_above.mono set.Ico_subset_Icc_self bdd_above_Icc

theorem bdd_below_Ico {α : Type u} [preorder α] {a : α} {b : α} : bdd_below (set.Ico a b) :=
  bdd_below.mono set.Ico_subset_Icc_self bdd_below_Icc

theorem bdd_above_Ioc {α : Type u} [preorder α] {a : α} {b : α} : bdd_above (set.Ioc a b) :=
  bdd_above.mono set.Ioc_subset_Icc_self bdd_above_Icc

theorem bdd_below_Ioc {α : Type u} [preorder α] {a : α} {b : α} : bdd_below (set.Ioc a b) :=
  bdd_below.mono set.Ioc_subset_Icc_self bdd_below_Icc

theorem bdd_above_Ioo {α : Type u} [preorder α] {a : α} {b : α} : bdd_above (set.Ioo a b) :=
  bdd_above.mono set.Ioo_subset_Icc_self bdd_above_Icc

theorem bdd_below_Ioo {α : Type u} [preorder α] {a : α} {b : α} : bdd_below (set.Ioo a b) :=
  bdd_below.mono set.Ioo_subset_Icc_self bdd_below_Icc

theorem is_greatest_Icc {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) :
    is_greatest (set.Icc a b) b :=
  { left := iff.mpr set.right_mem_Icc h, right := fun (x : α) => and.right }

theorem is_lub_Icc {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : is_lub (set.Icc a b) b :=
  is_greatest.is_lub (is_greatest_Icc h)

theorem upper_bounds_Icc {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) :
    upper_bounds (set.Icc a b) = set.Ici b :=
  is_lub.upper_bounds_eq (is_lub_Icc h)

theorem is_least_Icc {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) :
    is_least (set.Icc a b) a :=
  { left := iff.mpr set.left_mem_Icc h, right := fun (x : α) => and.left }

theorem is_glb_Icc {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : is_glb (set.Icc a b) a :=
  is_least.is_glb (is_least_Icc h)

theorem lower_bounds_Icc {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) :
    lower_bounds (set.Icc a b) = set.Iic a :=
  is_glb.lower_bounds_eq (is_glb_Icc h)

theorem is_greatest_Ioc {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) :
    is_greatest (set.Ioc a b) b :=
  { left := iff.mpr set.right_mem_Ioc h, right := fun (x : α) => and.right }

theorem is_lub_Ioc {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : is_lub (set.Ioc a b) b :=
  is_greatest.is_lub (is_greatest_Ioc h)

theorem upper_bounds_Ioc {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) :
    upper_bounds (set.Ioc a b) = set.Ici b :=
  is_lub.upper_bounds_eq (is_lub_Ioc h)

theorem is_least_Ico {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) :
    is_least (set.Ico a b) a :=
  { left := iff.mpr set.left_mem_Ico h, right := fun (x : α) => and.left }

theorem is_glb_Ico {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : is_glb (set.Ico a b) a :=
  is_least.is_glb (is_least_Ico h)

theorem lower_bounds_Ico {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) :
    lower_bounds (set.Ico a b) = set.Iic a :=
  is_glb.lower_bounds_eq (is_glb_Ico h)

theorem is_glb_Ioo {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ} (hab : a < b) :
    is_glb (set.Ioo a b) a :=
  sorry

theorem lower_bounds_Ioo {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ}
    (hab : a < b) : lower_bounds (set.Ioo a b) = set.Iic a :=
  is_glb.lower_bounds_eq (is_glb_Ioo hab)

theorem is_glb_Ioc {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ} (hab : a < b) :
    is_glb (set.Ioc a b) a :=
  is_glb.of_subset_of_superset (is_glb_Ioo hab) (is_glb_Icc (le_of_lt hab)) set.Ioo_subset_Ioc_self
    set.Ioc_subset_Icc_self

theorem lower_bound_Ioc {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ}
    (hab : a < b) : lower_bounds (set.Ioc a b) = set.Iic a :=
  is_glb.lower_bounds_eq (is_glb_Ioc hab)

theorem is_lub_Ioo {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ} (hab : a < b) :
    is_lub (set.Ioo a b) b :=
  sorry

theorem upper_bounds_Ioo {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ}
    (hab : a < b) : upper_bounds (set.Ioo a b) = set.Ici b :=
  is_lub.upper_bounds_eq (is_lub_Ioo hab)

theorem is_lub_Ico {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ} (hab : a < b) :
    is_lub (set.Ico a b) b :=
  sorry

theorem upper_bounds_Ico {γ : Type w} [linear_order γ] [densely_ordered γ] {a : γ} {b : γ}
    (hab : a < b) : upper_bounds (set.Ico a b) = set.Ici b :=
  is_lub.upper_bounds_eq (is_lub_Ico hab)

theorem bdd_below_iff_subset_Ici {α : Type u} [preorder α] {s : set α} :
    bdd_below s ↔ ∃ (a : α), s ⊆ set.Ici a :=
  iff.rfl

theorem bdd_above_iff_subset_Iic {α : Type u} [preorder α] {s : set α} :
    bdd_above s ↔ ∃ (a : α), s ⊆ set.Iic a :=
  iff.rfl

theorem bdd_below_bdd_above_iff_subset_Icc {α : Type u} [preorder α] {s : set α} :
    bdd_below s ∧ bdd_above s ↔ ∃ (a : α), ∃ (b : α), s ⊆ set.Icc a b :=
  sorry

/-!
### Univ
-/

theorem order_top.upper_bounds_univ {γ : Type w} [order_top γ] :
    upper_bounds set.univ = singleton ⊤ :=
  sorry

theorem is_greatest_univ {γ : Type w} [order_top γ] : is_greatest set.univ ⊤ := sorry

theorem is_lub_univ {γ : Type w} [order_top γ] : is_lub set.univ ⊤ :=
  is_greatest.is_lub is_greatest_univ

theorem order_bot.lower_bounds_univ {γ : Type w} [order_bot γ] :
    lower_bounds set.univ = singleton ⊥ :=
  order_top.upper_bounds_univ

theorem is_least_univ {γ : Type w} [order_bot γ] : is_least set.univ ⊥ := is_greatest_univ

theorem is_glb_univ {γ : Type w} [order_bot γ] : is_glb set.univ ⊥ := is_least.is_glb is_least_univ

theorem no_top_order.upper_bounds_univ {α : Type u} [preorder α] [no_top_order α] :
    upper_bounds set.univ = ∅ :=
  sorry

theorem no_bot_order.lower_bounds_univ {α : Type u} [preorder α] [no_bot_order α] :
    lower_bounds set.univ = ∅ :=
  no_top_order.upper_bounds_univ

/-!
### Empty set
-/

@[simp] theorem upper_bounds_empty {α : Type u} [preorder α] : upper_bounds ∅ = set.univ := sorry

@[simp] theorem lower_bounds_empty {α : Type u} [preorder α] : lower_bounds ∅ = set.univ :=
  upper_bounds_empty

@[simp] theorem bdd_above_empty {α : Type u} [preorder α] [Nonempty α] : bdd_above ∅ := sorry

@[simp] theorem bdd_below_empty {α : Type u} [preorder α] [Nonempty α] : bdd_below ∅ := sorry

theorem is_glb_empty {γ : Type w} [order_top γ] : is_glb ∅ ⊤ := sorry

theorem is_lub_empty {γ : Type w} [order_bot γ] : is_lub ∅ ⊥ := is_glb_empty

theorem is_lub.nonempty {α : Type u} [preorder α] {s : set α} {a : α} [no_bot_order α]
    (hs : is_lub s a) : set.nonempty s :=
  sorry

theorem is_glb.nonempty {α : Type u} [preorder α] {s : set α} {a : α} [no_top_order α]
    (hs : is_glb s a) : set.nonempty s :=
  is_lub.nonempty hs

theorem nonempty_of_not_bdd_above {α : Type u} [preorder α] {s : set α} [ha : Nonempty α]
    (h : ¬bdd_above s) : set.nonempty s :=
  nonempty.elim ha
    fun (x : α) =>
      Exists.imp (fun (a : α) (ha : ∃ (H : a ∈ s), ¬a ≤ x) => Exists.fst ha)
        (iff.mp not_bdd_above_iff' h x)

theorem nonempty_of_not_bdd_below {α : Type u} [preorder α] {s : set α} [ha : Nonempty α]
    (h : ¬bdd_below s) : set.nonempty s :=
  nonempty_of_not_bdd_above h

/-!
### insert
-/

/-- Adding a point to a set preserves its boundedness above. -/
@[simp] theorem bdd_above_insert {γ : Type w} [semilattice_sup γ] (a : γ) {s : set γ} :
    bdd_above (insert a s) ↔ bdd_above s :=
  sorry

theorem bdd_above.insert {γ : Type w} [semilattice_sup γ] (a : γ) {s : set γ} (hs : bdd_above s) :
    bdd_above (insert a s) :=
  iff.mpr (bdd_above_insert a) hs

/--Adding a point to a set preserves its boundedness below.-/
@[simp] theorem bdd_below_insert {γ : Type w} [semilattice_inf γ] (a : γ) {s : set γ} :
    bdd_below (insert a s) ↔ bdd_below s :=
  sorry

theorem bdd_below.insert {γ : Type w} [semilattice_inf γ] (a : γ) {s : set γ} (hs : bdd_below s) :
    bdd_below (insert a s) :=
  iff.mpr (bdd_below_insert a) hs

theorem is_lub.insert {γ : Type w} [semilattice_sup γ] (a : γ) {b : γ} {s : set γ}
    (hs : is_lub s b) : is_lub (insert a s) (a ⊔ b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_lub (insert a s) (a ⊔ b))) (set.insert_eq a s)))
    (is_lub.union is_lub_singleton hs)

theorem is_glb.insert {γ : Type w} [semilattice_inf γ] (a : γ) {b : γ} {s : set γ}
    (hs : is_glb s b) : is_glb (insert a s) (a ⊓ b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_glb (insert a s) (a ⊓ b))) (set.insert_eq a s)))
    (is_glb.union is_glb_singleton hs)

theorem is_greatest.insert {γ : Type w} [linear_order γ] (a : γ) {b : γ} {s : set γ}
    (hs : is_greatest s b) : is_greatest (insert a s) (max a b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_greatest (insert a s) (max a b))) (set.insert_eq a s)))
    (is_greatest.union is_greatest_singleton hs)

theorem is_least.insert {γ : Type w} [linear_order γ] (a : γ) {b : γ} {s : set γ}
    (hs : is_least s b) : is_least (insert a s) (min a b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_least (insert a s) (min a b))) (set.insert_eq a s)))
    (is_least.union is_least_singleton hs)

@[simp] theorem upper_bounds_insert {α : Type u} [preorder α] (a : α) (s : set α) :
    upper_bounds (insert a s) = set.Ici a ∩ upper_bounds s :=
  sorry

@[simp] theorem lower_bounds_insert {α : Type u} [preorder α] (a : α) (s : set α) :
    lower_bounds (insert a s) = set.Iic a ∩ lower_bounds s :=
  sorry

/-- When there is a global maximum, every set is bounded above. -/
@[simp] protected theorem order_top.bdd_above {γ : Type w} [order_top γ] (s : set γ) :
    bdd_above s :=
  Exists.intro ⊤ fun (a : γ) (ha : a ∈ s) => order_top.le_top a

/-- When there is a global minimum, every set is bounded below. -/
@[simp] protected theorem order_bot.bdd_below {γ : Type w} [order_bot γ] (s : set γ) :
    bdd_below s :=
  Exists.intro ⊥ fun (a : γ) (ha : a ∈ s) => order_bot.bot_le a

/-!
### Pair
-/

theorem is_lub_pair {γ : Type w} [semilattice_sup γ] {a : γ} {b : γ} :
    is_lub (insert a (singleton b)) (a ⊔ b) :=
  is_lub.insert a is_lub_singleton

theorem is_glb_pair {γ : Type w} [semilattice_inf γ] {a : γ} {b : γ} :
    is_glb (insert a (singleton b)) (a ⊓ b) :=
  is_glb.insert a is_glb_singleton

theorem is_least_pair {γ : Type w} [linear_order γ] {a : γ} {b : γ} :
    is_least (insert a (singleton b)) (min a b) :=
  is_least.insert a is_least_singleton

theorem is_greatest_pair {γ : Type w} [linear_order γ] {a : γ} {b : γ} :
    is_greatest (insert a (singleton b)) (max a b) :=
  is_greatest.insert a is_greatest_singleton

/-!
### (In)equalities with the least upper bound and the greatest lower bound
-/

theorem lower_bounds_le_upper_bounds {α : Type u} [preorder α] {s : set α} {a : α} {b : α}
    (ha : a ∈ lower_bounds s) (hb : b ∈ upper_bounds s) : set.nonempty s → a ≤ b :=
  fun (ᾰ : set.nonempty s) =>
    Exists.dcases_on ᾰ fun (ᾰ_w : α) (ᾰ_h : ᾰ_w ∈ s) => idRhs (a ≤ b) (le_trans (ha ᾰ_h) (hb ᾰ_h))

theorem is_glb_le_is_lub {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (ha : is_glb s a)
    (hb : is_lub s b) (hs : set.nonempty s) : a ≤ b :=
  lower_bounds_le_upper_bounds (and.left ha) (and.left hb) hs

theorem is_lub_lt_iff {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (ha : is_lub s a) :
    a < b ↔ ∃ (c : α), ∃ (H : c ∈ upper_bounds s), c < b :=
  sorry

theorem lt_is_glb_iff {α : Type u} [preorder α] {s : set α} {a : α} {b : α} (ha : is_glb s a) :
    b < a ↔ ∃ (c : α), ∃ (H : c ∈ lower_bounds s), b < c :=
  is_lub_lt_iff ha

theorem is_least.unique {α : Type u} [partial_order α] {s : set α} {a : α} {b : α}
    (Ha : is_least s a) (Hb : is_least s b) : a = b :=
  le_antisymm (and.right Ha b (and.left Hb)) (and.right Hb a (and.left Ha))

theorem is_least.is_least_iff_eq {α : Type u} [partial_order α] {s : set α} {a : α} {b : α}
    (Ha : is_least s a) : is_least s b ↔ a = b :=
  { mp := is_least.unique Ha, mpr := fun (h : a = b) => h ▸ Ha }

theorem is_greatest.unique {α : Type u} [partial_order α] {s : set α} {a : α} {b : α}
    (Ha : is_greatest s a) (Hb : is_greatest s b) : a = b :=
  le_antisymm (and.right Hb a (and.left Ha)) (and.right Ha b (and.left Hb))

theorem is_greatest.is_greatest_iff_eq {α : Type u} [partial_order α] {s : set α} {a : α} {b : α}
    (Ha : is_greatest s a) : is_greatest s b ↔ a = b :=
  { mp := is_greatest.unique Ha, mpr := fun (h : a = b) => h ▸ Ha }

theorem is_lub.unique {α : Type u} [partial_order α] {s : set α} {a : α} {b : α} (Ha : is_lub s a)
    (Hb : is_lub s b) : a = b :=
  is_least.unique Ha Hb

theorem is_glb.unique {α : Type u} [partial_order α] {s : set α} {a : α} {b : α} (Ha : is_glb s a)
    (Hb : is_glb s b) : a = b :=
  is_greatest.unique Ha Hb

theorem lt_is_lub_iff {α : Type u} [linear_order α] {s : set α} {a : α} {b : α} (h : is_lub s a) :
    b < a ↔ ∃ (c : α), ∃ (H : c ∈ s), b < c :=
  sorry

theorem is_glb_lt_iff {α : Type u} [linear_order α] {s : set α} {a : α} {b : α} (h : is_glb s a) :
    a < b ↔ ∃ (c : α), ∃ (H : c ∈ s), c < b :=
  lt_is_lub_iff h

theorem is_lub.exists_between {α : Type u} [linear_order α] {s : set α} {a : α} {b : α}
    (h : is_lub s a) (hb : b < a) : ∃ (c : α), ∃ (H : c ∈ s), b < c ∧ c ≤ a :=
  sorry

theorem is_lub.exists_between' {α : Type u} [linear_order α] {s : set α} {a : α} {b : α}
    (h : is_lub s a) (h' : ¬a ∈ s) (hb : b < a) : ∃ (c : α), ∃ (H : c ∈ s), b < c ∧ c < a :=
  sorry

theorem is_glb.exists_between {α : Type u} [linear_order α] {s : set α} {a : α} {b : α}
    (h : is_glb s a) (hb : a < b) : ∃ (c : α), ∃ (H : c ∈ s), a ≤ c ∧ c < b :=
  sorry

theorem is_glb.exists_between' {α : Type u} [linear_order α] {s : set α} {a : α} {b : α}
    (h : is_glb s a) (h' : ¬a ∈ s) (hb : a < b) : ∃ (c : α), ∃ (H : c ∈ s), a < c ∧ c < b :=
  sorry

/-!
### Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

theorem is_glb.exists_between_self_add {α : Type u} [linear_ordered_add_comm_group α] {s : set α}
    {a : α} {ε : α} (h : is_glb s a) (hε : 0 < ε) : ∃ (b : α), ∃ (H : b ∈ s), a ≤ b ∧ b < a + ε :=
  is_glb.exists_between h (lt_add_of_pos_right a hε)

theorem is_glb.exists_between_self_add' {α : Type u} [linear_ordered_add_comm_group α] {s : set α}
    {a : α} {ε : α} (h : is_glb s a) (h₂ : ¬a ∈ s) (hε : 0 < ε) :
    ∃ (b : α), ∃ (H : b ∈ s), a < b ∧ b < a + ε :=
  is_glb.exists_between' h h₂ (lt_add_of_pos_right a hε)

theorem is_lub.exists_between_sub_self {α : Type u} [linear_ordered_add_comm_group α] {s : set α}
    {a : α} {ε : α} (h : is_lub s a) (hε : 0 < ε) : ∃ (b : α), ∃ (H : b ∈ s), a - ε < b ∧ b ≤ a :=
  is_lub.exists_between h (sub_lt_self a hε)

theorem is_lub.exists_between_sub_self' {α : Type u} [linear_ordered_add_comm_group α] {s : set α}
    {a : α} {ε : α} (h : is_lub s a) (h₂ : ¬a ∈ s) (hε : 0 < ε) :
    ∃ (b : α), ∃ (H : b ∈ s), a - ε < b ∧ b < a :=
  is_lub.exists_between' h h₂ (sub_lt_self a hε)

/-!
### Images of upper/lower bounds under monotone functions
-/

namespace monotone


theorem mem_upper_bounds_image {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (Hf : monotone f) {a : α} {s : set α} (Ha : a ∈ upper_bounds s) : f a ∈ upper_bounds (f '' s) :=
  set.ball_image_of_ball fun (x : α) (H : x ∈ s) => Hf (Ha H)

theorem mem_lower_bounds_image {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (Hf : monotone f) {a : α} {s : set α} (Ha : a ∈ lower_bounds s) : f a ∈ lower_bounds (f '' s) :=
  set.ball_image_of_ball fun (x : α) (H : x ∈ s) => Hf (Ha H)

/-- The image under a monotone function of a set which is bounded above is bounded above. -/
theorem map_bdd_above {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α}
    (hf : monotone f) : bdd_above s → bdd_above (f '' s) :=
  sorry

/-- The image under a monotone function of a set which is bounded below is bounded below. -/
theorem map_bdd_below {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β} {s : set α}
    (hf : monotone f) : bdd_below s → bdd_below (f '' s) :=
  sorry

/-- A monotone map sends a least element of a set to a least element of its image. -/
theorem map_is_least {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (Hf : monotone f) {a : α} {s : set α} (Ha : is_least s a) : is_least (f '' s) (f a) :=
  { left := set.mem_image_of_mem f (and.left Ha),
    right := mem_lower_bounds_image Hf (and.right Ha) }

/-- A monotone map sends a greatest element of a set to a greatest element of its image. -/
theorem map_is_greatest {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (Hf : monotone f) {a : α} {s : set α} (Ha : is_greatest s a) : is_greatest (f '' s) (f a) :=
  { left := set.mem_image_of_mem f (and.left Ha),
    right := mem_upper_bounds_image Hf (and.right Ha) }

theorem is_lub_image_le {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (Hf : monotone f) {a : α} {s : set α} (Ha : is_lub s a) {b : β} (Hb : is_lub (f '' s) b) :
    b ≤ f a :=
  and.right Hb (f a) (mem_upper_bounds_image Hf (and.left Ha))

theorem le_is_glb_image {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (Hf : monotone f) {a : α} {s : set α} (Ha : is_glb s a) {b : β} (Hb : is_glb (f '' s) b) :
    f a ≤ b :=
  and.right Hb (f a) (mem_lower_bounds_image Hf (and.left Ha))

end monotone


theorem is_glb.of_image {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (hf : ∀ {x y : α}, f x ≤ f y ↔ x ≤ y) {s : set α} {x : α} (hx : is_glb (f '' s) (f x)) :
    is_glb s x :=
  sorry

theorem is_lub.of_image {α : Type u} {β : Type v} [preorder α] [preorder β] {f : α → β}
    (hf : ∀ {x y : α}, f x ≤ f y ↔ x ≤ y) {s : set α} {x : α} (hx : is_lub (f '' s) (f x)) :
    is_lub s x :=
  is_glb.of_image (fun (x y : order_dual α) => hf) hx

end Mathlib