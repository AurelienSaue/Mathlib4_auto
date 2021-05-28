/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.alias
import Mathlib.tactic.lint.default
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!
# Lemmas about inequalities

This file contains some lemmas about `≤`/`≥`/`<`/`>`, and `cmp`.

* We simplify `a ≥ b` and `a > b` to `b ≤ a` and `b < a`, respectively. This way we can formulate
  all lemmas using `≤`/`<` avoiding duplication.

* In some cases we introduce dot syntax aliases so that, e.g., from
  `(hab : a ≤ b) (hbc : b ≤ c) (hbc' : b < c)` one can prove `hab.trans hbc : a ≤ c` and
  `hab.trans_lt hbc' : a < c`.
-/

theorem has_le.le.trans {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a ≤ b → b ≤ c → a ≤ c :=
  le_trans

theorem has_le.le.trans_lt {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a ≤ b → b < c → a < c :=
  lt_of_le_of_lt

theorem has_le.le.antisymm {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → b ≤ a → a = b :=
  le_antisymm

theorem has_le.le.lt_of_ne {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → a ≠ b → a < b :=
  lt_of_le_of_ne

theorem has_le.le.lt_of_not_le {α : Type u} [preorder α] {a : α} {b : α} : a ≤ b → ¬b ≤ a → a < b :=
  lt_of_le_not_le

theorem has_le.le.lt_or_eq {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → a < b ∨ a = b :=
  lt_or_eq_of_le

theorem has_lt.lt.le {α : Type u} [preorder α] {a : α} {b : α} : a < b → a ≤ b :=
  le_of_lt

theorem has_lt.lt.trans {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a < b → b < c → a < c :=
  lt_trans

theorem has_lt.lt.trans_le {α : Type u} [preorder α] {a : α} {b : α} {c : α} : a < b → b ≤ c → a < c :=
  lt_of_lt_of_le

theorem has_lt.lt.ne {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : a ≠ b :=
  ne_of_lt

theorem has_lt.lt.not_lt {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : ¬b < a :=
  lt_asymm

theorem eq.le {α : Type u} [preorder α] {a : α} {b : α} : a = b → a ≤ b :=
  le_of_eq

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rfl {α : Type u} [preorder α] {x : α} : x ≤ x :=
  le_refl x

namespace eq


/--
If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`,
because `le` is used almost exclusively in mathlib.
-/
protected theorem ge {α : Type u} [preorder α] {x : α} {y : α} (h : x = y) : y ≤ x :=
  le (Eq.symm h)

end eq


theorem eq.trans_le {α : Type u} [preorder α] {x : α} {y : α} {z : α} (h1 : x = y) (h2 : y ≤ z) : x ≤ z :=
  has_le.le.trans (eq.le h1) h2

namespace has_le.le


protected theorem ge {α : Type u} [HasLessEq α] {x : α} {y : α} (h : x ≤ y) : y ≥ x :=
  h

theorem trans_eq {α : Type u} [preorder α] {x : α} {y : α} {z : α} (h1 : x ≤ y) (h2 : y = z) : x ≤ z :=
  trans h1 (eq.le h2)

theorem lt_iff_ne {α : Type u} [partial_order α] {x : α} {y : α} (h : x ≤ y) : x < y ↔ x ≠ y :=
  { mp := fun (h : x < y) => has_lt.lt.ne h, mpr := lt_of_ne h }

theorem le_iff_eq {α : Type u} [partial_order α] {x : α} {y : α} (h : x ≤ y) : y ≤ x ↔ y = x :=
  { mp := fun (h' : y ≤ x) => antisymm h' h, mpr := eq.le }

theorem lt_or_le {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
  or.imp id (fun (hc : a ≥ c) => le_trans hc h) (lt_or_ge a c)

theorem le_or_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
  or.imp id (fun (hc : a > c) => lt_of_lt_of_le hc h) (le_or_gt a c)

theorem le_or_le {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
  or.elim (le_or_lt h c) Or.inl fun (h : c < b) => Or.inr (le_of_lt h)

end has_le.le


namespace has_lt.lt


protected theorem gt {α : Type u} [HasLess α] {x : α} {y : α} (h : x < y) : y > x :=
  h

protected theorem false {α : Type u} [preorder α] {x : α} : x < x → False :=
  lt_irrefl x

theorem ne' {α : Type u} [preorder α] {x : α} {y : α} (h : x < y) : y ≠ x :=
  ne.symm (ne h)

theorem lt_or_lt {α : Type u} [linear_order α] {x : α} {y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
  or.elim (lt_or_ge z y) Or.inr fun (hz : z ≥ y) => Or.inl (trans_le h hz)

end has_lt.lt


namespace ge


end ge


protected theorem ge.le {α : Type u} [HasLessEq α] {x : α} {y : α} (h : x ≥ y) : y ≤ x :=
  h

namespace gt


end gt


protected theorem gt.lt {α : Type u} [HasLess α] {x : α} {y : α} (h : x > y) : y < x :=
  h

theorem ge_of_eq {α : Type u} [preorder α] {a : α} {b : α} (h : a = b) : a ≥ b :=
  eq.ge h

@[simp] theorem ge_iff_le {α : Type u} [preorder α] {a : α} {b : α} : a ≥ b ↔ b ≤ a :=
  iff.rfl

@[simp] theorem gt_iff_lt {α : Type u} [preorder α] {a : α} {b : α} : a > b ↔ b < a :=
  iff.rfl

theorem not_le_of_lt {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : ¬b ≤ a :=
  and.right (le_not_le_of_lt h)

theorem has_lt.lt.not_le {α : Type u} [preorder α] {a : α} {b : α} (h : a < b) : ¬b ≤ a :=
  not_le_of_lt

theorem not_lt_of_le {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : ¬b < a :=
  fun (ᾰ : b < a) => idRhs False (has_lt.lt.not_le ᾰ h)

theorem has_le.le.not_lt {α : Type u} [preorder α] {a : α} {b : α} (h : a ≤ b) : ¬b < a :=
  not_lt_of_le

theorem le_iff_eq_or_lt {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b ↔ a = b ∨ a < b :=
  iff.trans le_iff_lt_or_eq or.comm

theorem lt_iff_le_and_ne {α : Type u} [partial_order α] {a : α} {b : α} : a < b ↔ a ≤ b ∧ a ≠ b := sorry

theorem eq_iff_le_not_lt {α : Type u} [partial_order α] {a : α} {b : α} : a = b ↔ a ≤ b ∧ ¬a < b := sorry

theorem eq_or_lt_of_le {α : Type u} [partial_order α] {a : α} {b : α} (h : a ≤ b) : a = b ∨ a < b :=
  or.symm (has_le.le.lt_or_eq h)

theorem has_le.le.eq_or_lt {α : Type u} [partial_order α] {a : α} {b : α} (h : a ≤ b) : a = b ∨ a < b :=
  eq_or_lt_of_le

theorem ne.le_iff_lt {α : Type u} [partial_order α] {a : α} {b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
  { mp := fun (h' : a ≤ b) => lt_of_le_of_ne h' h, mpr := fun (h : a < b) => has_lt.lt.le h }

@[simp] theorem ne_iff_lt_iff_le {α : Type u} [partial_order α] {a : α} {b : α} : a ≠ b ↔ a < b ↔ a ≤ b :=
  { mp := fun (h : a ≠ b ↔ a < b) => classical.by_cases le_of_eq (le_of_lt ∘ iff.mp h),
    mpr := fun (h : a ≤ b) => { mp := lt_of_le_of_ne h, mpr := ne_of_lt } }

theorem lt_of_not_ge' {α : Type u} [linear_order α] {a : α} {b : α} (h : ¬b ≤ a) : a < b :=
  has_le.le.lt_of_not_le (or.resolve_right (le_total a b) h) h

theorem lt_iff_not_ge' {α : Type u} [linear_order α] {x : α} {y : α} : x < y ↔ ¬y ≤ x :=
  { mp := not_le_of_gt, mpr := lt_of_not_ge' }

theorem le_of_not_lt {α : Type u} [linear_order α] {a : α} {b : α} : ¬a < b → b ≤ a :=
  iff.mp not_lt

theorem lt_or_le {α : Type u} [linear_order α] (a : α) (b : α) : a < b ∨ b ≤ a :=
  lt_or_ge

theorem le_or_lt {α : Type u} [linear_order α] (a : α) (b : α) : a ≤ b ∨ b < a :=
  le_or_gt

theorem ne.lt_or_lt {α : Type u} [linear_order α] {a : α} {b : α} (h : a ≠ b) : a < b ∨ b < a :=
  lt_or_gt_of_ne h

theorem not_lt_iff_eq_or_lt {α : Type u} [linear_order α] {a : α} {b : α} : ¬a < b ↔ a = b ∨ b < a :=
  iff.trans not_lt (iff.trans le_iff_eq_or_lt (or_congr eq_comm iff.rfl))

theorem exists_ge_of_linear {α : Type u} [linear_order α] (a : α) (b : α) : ∃ (c : α), a ≤ c ∧ b ≤ c := sorry

theorem lt_imp_lt_of_le_imp_le {α : Type u} {β : Type u_1} [linear_order α] [preorder β] {a : α} {b : α} {c : β} {d : β} (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
  lt_of_not_ge' fun (h' : a ≤ b) => has_le.le.not_lt (H h') h

theorem le_imp_le_of_lt_imp_lt {α : Type u} {β : Type u_1} [preorder α] [linear_order β] {a : α} {b : α} {c : β} {d : β} (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
  le_of_not_gt fun (h' : c > d) => has_lt.lt.not_le (H h') h

theorem le_imp_le_iff_lt_imp_lt {α : Type u} {β : Type u_1} [linear_order α] [linear_order β] {a : α} {b : α} {c : β} {d : β} : a ≤ b → c ≤ d ↔ d < c → b < a :=
  { mp := lt_imp_lt_of_le_imp_le, mpr := le_imp_le_of_lt_imp_lt }

theorem lt_iff_lt_of_le_iff_le' {α : Type u} {β : Type u_1} [preorder α] [preorder β] {a : α} {b : α} {c : β} {d : β} (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  iff.trans lt_iff_le_not_le (iff.trans (and_congr H' (not_congr H)) (iff.symm lt_iff_le_not_le))

theorem lt_iff_lt_of_le_iff_le {α : Type u} {β : Type u_1} [linear_order α] [linear_order β] {a : α} {b : α} {c : β} {d : β} (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
  iff.trans (iff.symm not_le) (iff.trans (not_congr H) not_le)

theorem le_iff_le_iff_lt_iff_lt {α : Type u} {β : Type u_1} [linear_order α] [linear_order β] {a : α} {b : α} {c : β} {d : β} : a ≤ b ↔ c ≤ d ↔ (b < a ↔ d < c) :=
  { mp := lt_iff_lt_of_le_iff_le,
    mpr := fun (H : b < a ↔ d < c) => iff.trans (iff.symm not_lt) (iff.trans (not_congr H) not_lt) }

theorem eq_of_forall_le_iff {α : Type u} [partial_order α] {a : α} {b : α} (H : ∀ (c : α), c ≤ a ↔ c ≤ b) : a = b :=
  le_antisymm (iff.mp (H a) (le_refl a)) (iff.mpr (H b) (le_refl b))

theorem le_of_forall_le {α : Type u} [preorder α] {a : α} {b : α} (H : ∀ (c : α), c ≤ a → c ≤ b) : a ≤ b :=
  H a (le_refl a)

theorem le_of_forall_le' {α : Type u} [preorder α] {a : α} {b : α} (H : ∀ (c : α), a ≤ c → b ≤ c) : b ≤ a :=
  H a (le_refl a)

theorem le_of_forall_lt {α : Type u} [linear_order α] {a : α} {b : α} (H : ∀ (c : α), c < a → c < b) : a ≤ b :=
  le_of_not_lt fun (h : b < a) => lt_irrefl b (H b h)

theorem forall_lt_iff_le {α : Type u} [linear_order α] {a : α} {b : α} : (∀ {c : α}, c < a → c < b) ↔ a ≤ b :=
  { mp := le_of_forall_lt, mpr := fun (h : a ≤ b) (c : α) (hca : c < a) => lt_of_lt_of_le hca h }

theorem le_of_forall_lt' {α : Type u} [linear_order α] {a : α} {b : α} (H : ∀ (c : α), a < c → b < c) : b ≤ a :=
  le_of_not_lt fun (h : a < b) => lt_irrefl b (H b h)

theorem forall_lt_iff_le' {α : Type u} [linear_order α] {a : α} {b : α} : (∀ {c : α}, a < c → b < c) ↔ b ≤ a :=
  { mp := le_of_forall_lt', mpr := fun (h : b ≤ a) (c : α) (hac : a < c) => lt_of_le_of_lt h hac }

theorem eq_of_forall_ge_iff {α : Type u} [partial_order α] {a : α} {b : α} (H : ∀ (c : α), a ≤ c ↔ b ≤ c) : a = b :=
  le_antisymm (iff.mpr (H b) (le_refl b)) (iff.mp (H a) (le_refl a))

/-- monotonicity of `≤` with respect to `→` -/
theorem le_implies_le_of_le_of_le {α : Type u} {a : α} {b : α} {c : α} {d : α} [preorder α] (h₀ : c ≤ a) (h₁ : b ≤ d) : a ≤ b → c ≤ d :=
  fun (h₂ : a ≤ b) => le_trans (le_trans h₀ h₂) h₁

namespace decidable


-- See Note [decidable namespace]

theorem le_imp_le_iff_lt_imp_lt {α : Type u} {β : Type u_1} [linear_order α] [linear_order β] {a : α} {b : α} {c : β} {d : β} : a ≤ b → c ≤ d ↔ d < c → b < a :=
  { mp := lt_imp_lt_of_le_imp_le, mpr := le_imp_le_of_lt_imp_lt }

-- See Note [decidable namespace]

theorem le_iff_le_iff_lt_iff_lt {α : Type u} {β : Type u_1} [linear_order α] [linear_order β] {a : α} {b : α} {c : β} {d : β} : a ≤ b ↔ c ≤ d ↔ (b < a ↔ d < c) :=
  { mp := lt_iff_lt_of_le_iff_le,
    mpr := fun (H : b < a ↔ d < c) => iff.trans (iff.symm not_lt) (iff.trans (not_congr H) not_lt) }

end decidable


/-- Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements
`x` and `y`, returns a three-way comparison result `ordering`. -/
def cmp_le {α : Type u_1} [HasLessEq α] [DecidableRel LessEq] (x : α) (y : α) : ordering :=
  ite (x ≤ y) (ite (y ≤ x) ordering.eq ordering.lt) ordering.gt

theorem cmp_le_swap {α : Type u_1} [HasLessEq α] [is_total α LessEq] [DecidableRel LessEq] (x : α) (y : α) : ordering.swap (cmp_le x y) = cmp_le y x := sorry

theorem cmp_le_eq_cmp {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq] [DecidableRel Less] (x : α) (y : α) : cmp_le x y = cmp x y := sorry

namespace ordering


/-- `compares o a b` means that `a` and `b` have the ordering relation
  `o` between them, assuming that the relation `a < b` is defined -/
@[simp] def compares {α : Type u} [HasLess α] : ordering → α → α → Prop :=
  sorry

theorem compares_swap {α : Type u} [HasLess α] {a : α} {b : α} {o : ordering} : compares (swap o) a b ↔ compares o b a :=
  ordering.cases_on o iff.rfl eq_comm iff.rfl

theorem compares.of_swap {α : Type u} [HasLess α] {a : α} {b : α} {o : ordering} : compares (swap o) a b → compares o b a :=
  iff.mp compares_swap

theorem swap_eq_iff_eq_swap {o : ordering} {o' : ordering} : swap o = o' ↔ o = swap o' := sorry

theorem compares.eq_lt {α : Type u} [preorder α] {o : ordering} {a : α} {b : α} : compares o a b → (o = lt ↔ a < b) := sorry

theorem compares.ne_lt {α : Type u} [preorder α] {o : ordering} {a : α} {b : α} : compares o a b → (o ≠ lt ↔ b ≤ a) := sorry

theorem compares.eq_eq {α : Type u} [preorder α] {o : ordering} {a : α} {b : α} : compares o a b → (o = eq ↔ a = b) := sorry

theorem compares.eq_gt {α : Type u} [preorder α] {o : ordering} {a : α} {b : α} (h : compares o a b) : o = gt ↔ b < a :=
  iff.trans (iff.symm swap_eq_iff_eq_swap) (compares.eq_lt (compares.swap h))

theorem compares.ne_gt {α : Type u} [preorder α] {o : ordering} {a : α} {b : α} (h : compares o a b) : o ≠ gt ↔ a ≤ b :=
  iff.trans (not_congr (iff.symm swap_eq_iff_eq_swap)) (compares.ne_lt (compares.swap h))

theorem compares.le_total {α : Type u} [preorder α] {a : α} {b : α} {o : ordering} : compares o a b → a ≤ b ∨ b ≤ a := sorry

theorem compares.le_antisymm {α : Type u} [preorder α] {a : α} {b : α} {o : ordering} : compares o a b → a ≤ b → b ≤ a → a = b := sorry

theorem compares.inj {α : Type u} [preorder α] {o₁ : ordering} {o₂ : ordering} {a : α} {b : α} : compares o₁ a b → compares o₂ a b → o₁ = o₂ := sorry

theorem compares_iff_of_compares_impl {α : Type u} {β : Type u_1} [linear_order α] [preorder β] {a : α} {b : α} {a' : β} {b' : β} (h : ∀ {o : ordering}, compares o a b → compares o a' b') (o : ordering) : compares o a b ↔ compares o a' b' := sorry

theorem swap_or_else (o₁ : ordering) (o₂ : ordering) : swap (or_else o₁ o₂) = or_else (swap o₁) (swap o₂) :=
  ordering.cases_on o₁ (Eq.refl (swap (or_else lt o₂))) (Eq.refl (swap (or_else eq o₂))) (Eq.refl (swap (or_else gt o₂)))

theorem or_else_eq_lt (o₁ : ordering) (o₂ : ordering) : or_else o₁ o₂ = lt ↔ o₁ = lt ∨ o₁ = eq ∧ o₂ = lt :=
  ordering.cases_on o₁ (ordering.cases_on o₂ (of_as_true trivial) (of_as_true trivial) (of_as_true trivial))
    (ordering.cases_on o₂ (of_as_true trivial) (of_as_true trivial) (of_as_true trivial))
    (ordering.cases_on o₂ (of_as_true trivial) (of_as_true trivial) (of_as_true trivial))

end ordering


theorem cmp_compares {α : Type u} [linear_order α] (a : α) (b : α) : ordering.compares (cmp a b) a b := sorry

theorem cmp_swap {α : Type u} [preorder α] [DecidableRel Less] (a : α) (b : α) : ordering.swap (cmp a b) = cmp b a := sorry

/-- Generate a linear order structure from a preorder and `cmp` function. -/
def linear_order_of_compares {α : Type u} [preorder α] (cmp : α → α → ordering) (h : ∀ (a b : α), ordering.compares (cmp a b) a b) : linear_order α :=
  linear_order.mk preorder.le preorder.lt preorder.le_refl preorder.le_trans sorry sorry
    (fun (a b : α) => decidable_of_iff (cmp a b ≠ ordering.gt) sorry)
    (fun (a b : α) => decidable_of_iff (cmp a b = ordering.eq) sorry)
    fun (a b : α) => decidable_of_iff (cmp a b = ordering.lt) sorry

@[simp] theorem cmp_eq_lt_iff {α : Type u} [linear_order α] (x : α) (y : α) : cmp x y = ordering.lt ↔ x < y :=
  ordering.compares.eq_lt (cmp_compares x y)

@[simp] theorem cmp_eq_eq_iff {α : Type u} [linear_order α] (x : α) (y : α) : cmp x y = ordering.eq ↔ x = y :=
  ordering.compares.eq_eq (cmp_compares x y)

@[simp] theorem cmp_eq_gt_iff {α : Type u} [linear_order α] (x : α) (y : α) : cmp x y = ordering.gt ↔ y < x :=
  ordering.compares.eq_gt (cmp_compares x y)

@[simp] theorem cmp_self_eq_eq {α : Type u} [linear_order α] (x : α) : cmp x x = ordering.eq :=
  eq.mpr (id (Eq._oldrec (Eq.refl (cmp x x = ordering.eq)) (propext (cmp_eq_eq_iff x x)))) (Eq.refl x)

theorem cmp_eq_cmp_symm {α : Type u} [linear_order α] {x : α} {y : α} {β : Type u_1} [linear_order β] {x' : β} {y' : β} : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' := sorry

theorem lt_iff_lt_of_cmp_eq_cmp {α : Type u} [linear_order α] {x : α} {y : α} {β : Type u_1} [linear_order β] {x' : β} {y' : β} (h : cmp x y = cmp x' y') : x < y ↔ x' < y' := sorry

theorem le_iff_le_of_cmp_eq_cmp {α : Type u} [linear_order α] {x : α} {y : α} {β : Type u_1} [linear_order β] {x' : β} {y' : β} (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' := sorry

