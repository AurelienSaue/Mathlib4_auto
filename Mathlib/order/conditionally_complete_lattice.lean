/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.nat.enat
import Mathlib.data.set.intervals.ord_connected
import Mathlib.PostPort

universes u_1 u_4 l u_3 u_2 

namespace Mathlib

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset s
has a least upper bound and a greatest lower bound, denoted below by Sup s and Inf s.
Typical examples are real, nat, int with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates bdd_above and bdd_below to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of Sup and Inf
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix Inf and Sup in the statements by c, giving cInf and cSup. For instance,
Inf_le is a statement in complete lattices ensuring Inf s ≤ x, while cInf_le is the same
statement in conditionally complete lattices with an additional assumption that s is
bounded below.
-/

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/

protected instance with_top.has_Sup {α : Type u_1} [preorder α] [has_Sup α] : has_Sup (with_top α) :=
  has_Sup.mk fun (S : set (with_top α)) => ite (⊤ ∈ S) ⊤ (ite (bdd_above (coe ⁻¹' S)) ↑(Sup (coe ⁻¹' S)) ⊤)

protected instance with_top.has_Inf {α : Type u_1} [has_Inf α] : has_Inf (with_top α) :=
  has_Inf.mk fun (S : set (with_top α)) => ite (S ⊆ singleton ⊤) ⊤ ↑(Inf (coe ⁻¹' S))

protected instance with_bot.has_Sup {α : Type u_1} [has_Sup α] : has_Sup (with_bot α) :=
  has_Sup.mk Inf

protected instance with_bot.has_Inf {α : Type u_1} [preorder α] [has_Inf α] : has_Inf (with_bot α) :=
  has_Inf.mk Sup

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_lattice (α : Type u_4) 
extends lattice α, has_Sup α, has_Inf α
where
  le_cSup : ∀ (s : set α) (a : α), bdd_above s → a ∈ s → a ≤ Sup s
  cSup_le : ∀ (s : set α) (a : α), set.nonempty s → a ∈ upper_bounds s → Sup s ≤ a
  cInf_le : ∀ (s : set α) (a : α), bdd_below s → a ∈ s → Inf s ≤ a
  le_cInf : ∀ (s : set α) (a : α), set.nonempty s → a ∈ lower_bounds s → a ≤ Inf s

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_linear_order (α : Type u_4) 
extends linear_order α, conditionally_complete_lattice α
where

/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class conditionally_complete_linear_order_bot (α : Type u_4) 
extends order_bot α, conditionally_complete_linear_order α
where
  cSup_empty : Sup ∅ = ⊥

/- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/

protected instance conditionally_complete_lattice_of_complete_lattice {α : Type u_1} [complete_lattice α] : conditionally_complete_lattice α :=
  conditionally_complete_lattice.mk complete_lattice.sup complete_lattice.le complete_lattice.lt complete_lattice.le_refl
    complete_lattice.le_trans complete_lattice.le_antisymm complete_lattice.le_sup_left complete_lattice.le_sup_right
    complete_lattice.sup_le complete_lattice.inf complete_lattice.inf_le_left complete_lattice.inf_le_right
    complete_lattice.le_inf complete_lattice.Sup complete_lattice.Inf sorry sorry sorry sorry

protected instance conditionally_complete_linear_order_of_complete_linear_order {α : Type u_1} [complete_linear_order α] : conditionally_complete_linear_order α :=
  conditionally_complete_linear_order.mk conditionally_complete_lattice.sup conditionally_complete_lattice.le
    conditionally_complete_lattice.lt sorry sorry sorry sorry sorry sorry conditionally_complete_lattice.inf sorry sorry
    sorry conditionally_complete_lattice.Sup conditionally_complete_lattice.Inf sorry sorry sorry sorry
    complete_linear_order.le_total complete_linear_order.decidable_le complete_linear_order.decidable_eq
    complete_linear_order.decidable_lt

theorem le_cSup {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (h₁ : bdd_above s) (h₂ : a ∈ s) : a ≤ Sup s :=
  conditionally_complete_lattice.le_cSup s a h₁ h₂

theorem cSup_le {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (h₁ : set.nonempty s) (h₂ : ∀ (b : α), b ∈ s → b ≤ a) : Sup s ≤ a :=
  conditionally_complete_lattice.cSup_le s a h₁ h₂

theorem cInf_le {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (h₁ : bdd_below s) (h₂ : a ∈ s) : Inf s ≤ a :=
  conditionally_complete_lattice.cInf_le s a h₁ h₂

theorem le_cInf {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (h₁ : set.nonempty s) (h₂ : ∀ (b : α), b ∈ s → a ≤ b) : a ≤ Inf s :=
  conditionally_complete_lattice.le_cInf s a h₁ h₂

theorem le_cSup_of_le {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} {b : α} (_x : bdd_above s) (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
  le_trans h (le_cSup _x hb)

theorem cInf_le_of_le {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} {b : α} (_x : bdd_below s) (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
  le_trans (cInf_le _x hb) h

theorem cSup_le_cSup {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (_x : bdd_above t) : set.nonempty s → s ⊆ t → Sup s ≤ Sup t :=
  fun (_x_1 : set.nonempty s) (h : s ⊆ t) => cSup_le _x_1 fun (a : α) (ha : a ∈ s) => le_cSup _x (h ha)

theorem cInf_le_cInf {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (_x : bdd_below t) : set.nonempty s → s ⊆ t → Inf t ≤ Inf s :=
  fun (_x_1 : set.nonempty s) (h : s ⊆ t) => le_cInf _x_1 fun (a : α) (ha : a ∈ s) => cInf_le _x (h ha)

theorem is_lub_cSup {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (ne : set.nonempty s) (H : bdd_above s) : is_lub s (Sup s) :=
  { left := fun (x : α) => le_cSup H, right := fun (x : α) => cSup_le ne }

theorem is_glb_cInf {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (ne : set.nonempty s) (H : bdd_below s) : is_glb s (Inf s) :=
  { left := fun (x : α) => cInf_le H, right := fun (x : α) => le_cInf ne }

theorem is_lub.cSup_eq {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (H : is_lub s a) (ne : set.nonempty s) : Sup s = a :=
  is_lub.unique (is_lub_cSup ne (Exists.intro a (and.left H))) H

/-- A greatest element of a set is the supremum of this set. -/
theorem is_greatest.cSup_eq {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (H : is_greatest s a) : Sup s = a :=
  is_lub.cSup_eq (is_greatest.is_lub H) (is_greatest.nonempty H)

theorem is_glb.cInf_eq {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (H : is_glb s a) (ne : set.nonempty s) : Inf s = a :=
  is_glb.unique (is_glb_cInf ne (Exists.intro a (and.left H))) H

/-- A least element of a set is the infimum of this set. -/
theorem is_least.cInf_eq {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (H : is_least s a) : Inf s = a :=
  is_glb.cInf_eq (is_least.is_glb H) (is_least.nonempty H)

theorem subset_Icc_cInf_cSup {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (hb : bdd_below s) (ha : bdd_above s) : s ⊆ set.Icc (Inf s) (Sup s) :=
  fun (x : α) (hx : x ∈ s) => { left := cInf_le hb hx, right := le_cSup ha hx }

theorem cSup_le_iff {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (hb : bdd_above s) (ne : set.nonempty s) : Sup s ≤ a ↔ ∀ (b : α), b ∈ s → b ≤ a :=
  is_lub_le_iff (is_lub_cSup ne hb)

theorem le_cInf_iff {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (hb : bdd_below s) (ne : set.nonempty s) : a ≤ Inf s ↔ ∀ (b : α), b ∈ s → a ≤ b :=
  le_is_glb_iff (is_glb_cInf ne hb)

theorem cSup_lower_bounds_eq_cInf {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (h : bdd_below s) (hs : set.nonempty s) : Sup (lower_bounds s) = Inf s :=
  is_lub.unique
    (is_lub_cSup h (set.nonempty.mono (fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ lower_bounds s) => hy hx) hs))
    (is_greatest.is_lub (is_glb_cInf hs h))

theorem cInf_upper_bounds_eq_cSup {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (h : bdd_above s) (hs : set.nonempty s) : Inf (upper_bounds s) = Sup s :=
  is_glb.unique
    (is_glb_cInf h (set.nonempty.mono (fun (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ upper_bounds s) => hy hx) hs))
    (is_least.is_glb (is_lub_cSup hs h))

/--Introduction rule to prove that b is the supremum of s: it suffices to check that b
is larger than all elements of s, and that this is not the case of any `w<b`.-/
theorem cSup_intro {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {b : α} (_x : set.nonempty s) : (∀ (a : α), a ∈ s → a ≤ b) → (∀ (w : α), w < b → ∃ (a : α), ∃ (H : a ∈ s), w < a) → Sup s = b := sorry

/--Introduction rule to prove that b is the infimum of s: it suffices to check that b
is smaller than all elements of s, and that this is not the case of any `w>b`.-/
theorem cInf_intro {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {b : α} (_x : set.nonempty s) : (∀ (a : α), a ∈ s → b ≤ a) → (∀ (w : α), b < w → ∃ (a : α), ∃ (H : a ∈ s), a < w) → Inf s = b := sorry

/--b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem lt_cSup_of_lt {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} {b : α} (_x : bdd_above s) : a ∈ s → b < a → b < Sup s :=
  fun (_x_1 : a ∈ s) (_x_2 : b < a) => lt_of_lt_of_le _x_2 (le_cSup _x _x_1)

/--Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem cInf_lt_of_lt {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} {b : α} (_x : bdd_below s) : a ∈ s → a < b → Inf s < b :=
  fun (_x_1 : a ∈ s) (_x_2 : a < b) => lt_of_le_of_lt (cInf_le _x _x_1) _x_2

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (sne : set.nonempty s) (tne : set.nonempty t) (hst : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ t → x ≤ y) : set.nonempty (upper_bounds s ∩ lower_bounds t) :=
  Exists.intro (Inf t)
    { left := fun (x : α) (hx : x ∈ s) => le_cInf tne (hst x hx),
      right := fun (y : α) (hy : y ∈ t) => cInf_le (set.nonempty.mono hst sne) hy }

/--The supremum of a singleton is the element of the singleton-/
@[simp] theorem cSup_singleton {α : Type u_1} [conditionally_complete_lattice α] (a : α) : Sup (singleton a) = a :=
  is_greatest.cSup_eq is_greatest_singleton

/--The infimum of a singleton is the element of the singleton-/
@[simp] theorem cInf_singleton {α : Type u_1} [conditionally_complete_lattice α] (a : α) : Inf (singleton a) = a :=
  is_least.cInf_eq is_least_singleton

/--If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup {α : Type u_1} [conditionally_complete_lattice α] {s : set α} (hb : bdd_below s) (ha : bdd_above s) (ne : set.nonempty s) : Inf s ≤ Sup s :=
  is_glb_le_is_lub (is_glb_cInf ne hb) (is_lub_cSup ne ha) ne

/--The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (hs : bdd_above s) (sne : set.nonempty s) (ht : bdd_above t) (tne : set.nonempty t) : Sup (s ∪ t) = Sup s ⊔ Sup t :=
  is_lub.cSup_eq (is_lub.union (is_lub_cSup sne hs) (is_lub_cSup tne ht)) (set.nonempty.inl sne)

/--The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (hs : bdd_below s) (sne : set.nonempty s) (ht : bdd_below t) (tne : set.nonempty t) : Inf (s ∪ t) = Inf s ⊓ Inf t :=
  is_glb.cInf_eq (is_glb.union (is_glb_cInf sne hs) (is_glb_cInf tne ht)) (set.nonempty.inl sne)

/--The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (_x : bdd_above s) : bdd_above t → set.nonempty (s ∩ t) → Sup (s ∩ t) ≤ Sup s ⊓ Sup t := sorry

/--The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {t : set α} (_x : bdd_below s) : bdd_below t → set.nonempty (s ∩ t) → Inf s ⊔ Inf t ≤ Inf (s ∩ t) := sorry

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (hs : bdd_above s) (sne : set.nonempty s) : Sup (insert a s) = a ⊔ Sup s :=
  is_lub.cSup_eq (is_lub.insert a (is_lub_cSup sne hs)) (set.insert_nonempty a s)

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert {α : Type u_1} [conditionally_complete_lattice α] {s : set α} {a : α} (hs : bdd_below s) (sne : set.nonempty s) : Inf (insert a s) = a ⊓ Inf s :=
  is_glb.cInf_eq (is_glb.insert a (is_glb_cInf sne hs)) (set.insert_nonempty a s)

@[simp] theorem cInf_Ici {α : Type u_1} [conditionally_complete_lattice α] {a : α} : Inf (set.Ici a) = a :=
  is_least.cInf_eq is_least_Ici

@[simp] theorem cSup_Iic {α : Type u_1} [conditionally_complete_lattice α] {a : α} : Sup (set.Iic a) = a :=
  is_greatest.cSup_eq is_greatest_Iic

/--The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem csupr_le_csupr {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] {f : ι → α} {g : ι → α} (B : bdd_above (set.range g)) (H : ∀ (x : ι), f x ≤ g x) : supr f ≤ supr g := sorry

/--The indexed supremum of a function is bounded above by a uniform bound-/
theorem csupr_le {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] [Nonempty ι] {f : ι → α} {c : α} (H : ∀ (x : ι), f x ≤ c) : supr f ≤ c :=
  cSup_le (set.range_nonempty f)
    (eq.mpr (id (Eq._oldrec (Eq.refl (∀ (b : α), b ∈ set.range f → b ≤ c)) (propext set.forall_range_iff))) H)

/--The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_csupr {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] {f : ι → α} (H : bdd_above (set.range f)) (c : ι) : f c ≤ supr f :=
  le_cSup H (set.mem_range_self c)

/--The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem cinfi_le_cinfi {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] {f : ι → α} {g : ι → α} (B : bdd_below (set.range f)) (H : ∀ (x : ι), f x ≤ g x) : infi f ≤ infi g := sorry

/--The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_cinfi {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] [Nonempty ι] {f : ι → α} {c : α} (H : ∀ (x : ι), c ≤ f x) : c ≤ infi f :=
  le_cInf (set.range_nonempty f)
    (eq.mpr (id (Eq._oldrec (Eq.refl (∀ (b : α), b ∈ set.range f → c ≤ b)) (propext set.forall_range_iff))) H)

/--The indexed infimum of a function is bounded above by the value taken at one point-/
theorem cinfi_le {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] {f : ι → α} (H : bdd_below (set.range f)) (c : ι) : infi f ≤ f c :=
  cInf_le H (set.mem_range_self c)

@[simp] theorem cinfi_const {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] [hι : Nonempty ι] {a : α} : (infi fun (b : ι) => a) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((infi fun (b : ι) => a) = a)) (infi.equations._eqn_1 fun (b : ι) => a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Inf (set.range fun (b : ι) => a) = a)) set.range_const))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Inf (singleton a) = a)) (cInf_singleton a))) (Eq.refl a)))

@[simp] theorem csupr_const {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] [hι : Nonempty ι] {a : α} : (supr fun (b : ι) => a) = a :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((supr fun (b : ι) => a) = a)) (supr.equations._eqn_1 fun (b : ι) => a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Sup (set.range fun (b : ι) => a) = a)) set.range_const))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Sup (singleton a) = a)) (cSup_singleton a))) (Eq.refl a)))

theorem infi_unique {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] [unique ι] {s : ι → α} : (infi fun (i : ι) => s i) = s Inhabited.default := sorry

theorem supr_unique {α : Type u_1} {ι : Sort u_3} [conditionally_complete_lattice α] [unique ι] {s : ι → α} : (supr fun (i : ι) => s i) = s Inhabited.default := sorry

@[simp] theorem infi_unit {α : Type u_1} [conditionally_complete_lattice α] {f : Unit → α} : (infi fun (x : Unit) => f x) = f Unit.unit := sorry

@[simp] theorem supr_unit {α : Type u_1} [conditionally_complete_lattice α] {f : Unit → α} : (supr fun (x : Unit) => f x) = f Unit.unit := sorry

/-- Nested intervals lemma: if `f` is a monotonically increasing sequence, `g` is a monotonically
decreasing sequence, and `f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals
`[f n, g n]`. -/
theorem csupr_mem_Inter_Icc_of_mono_incr_of_mono_decr {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] [Nonempty β] [semilattice_sup β] {f : β → α} {g : β → α} (hf : monotone f) (hg : ∀ {m n : β}, m ≤ n → g n ≤ g m) (h : ∀ (n : β), f n ≤ g n) : (supr fun (n : β) => f n) ∈ set.Inter fun (n : β) => set.Icc (f n) (g n) := sorry

/-- Nested intervals lemma: if `[f n, g n]` is a monotonically decreasing sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupr_mem_Inter_Icc_of_mono_decr_Icc {α : Type u_1} {β : Type u_2} [conditionally_complete_lattice α] [Nonempty β] [semilattice_sup β] {f : β → α} {g : β → α} (h : ∀ {m n : β}, m ≤ n → set.Icc (f n) (g n) ⊆ set.Icc (f m) (g m)) (h' : ∀ (n : β), f n ≤ g n) : (supr fun (n : β) => f n) ∈ set.Inter fun (n : β) => set.Icc (f n) (g n) :=
  csupr_mem_Inter_Icc_of_mono_incr_of_mono_decr
    (fun (m n : β) (hmn : m ≤ n) => and.left (iff.mp (set.Icc_subset_Icc_iff (h' n)) (h hmn)))
    (fun (m n : β) (hmn : m ≤ n) => and.right (iff.mp (set.Icc_subset_Icc_iff (h' n)) (h hmn))) h'

/-- Nested intervals lemma: if `[f n, g n]` is a monotonically decreasing sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupr_mem_Inter_Icc_of_mono_decr_Icc_nat {α : Type u_1} [conditionally_complete_lattice α] {f : ℕ → α} {g : ℕ → α} (h : ∀ (n : ℕ), set.Icc (f (n + 1)) (g (n + 1)) ⊆ set.Icc (f n) (g n)) (h' : ∀ (n : ℕ), f n ≤ g n) : (supr fun (n : ℕ) => f n) ∈ set.Inter fun (n : ℕ) => set.Icc (f n) (g n) :=
  csupr_mem_Inter_Icc_of_mono_decr_Icc (monotone_of_monotone_nat h) h'

protected instance pi.conditionally_complete_lattice {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → conditionally_complete_lattice (α i)] : conditionally_complete_lattice ((i : ι) → α i) :=
  conditionally_complete_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf
    sorry sorry sorry Sup Inf sorry sorry sorry sorry

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
theorem exists_lt_of_lt_cSup {α : Type u_1} [conditionally_complete_linear_order α] {s : set α} {b : α} (hs : set.nonempty s) (hb : b < Sup s) : ∃ (a : α), ∃ (H : a ∈ s), b < a := sorry

/--
Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_csupr {α : Type u_1} {ι : Sort u_3} [conditionally_complete_linear_order α] {b : α} [Nonempty ι] {f : ι → α} (h : b < supr f) : ∃ (i : ι), b < f i := sorry

/--When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
theorem exists_lt_of_cInf_lt {α : Type u_1} [conditionally_complete_linear_order α] {s : set α} {b : α} (hs : set.nonempty s) (hb : Inf s < b) : ∃ (a : α), ∃ (H : a ∈ s), a < b := sorry

/--
Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_cinfi_lt {α : Type u_1} {ι : Sort u_3} [conditionally_complete_linear_order α] {a : α} [Nonempty ι] {f : ι → α} (h : infi f < a) : ∃ (i : ι), f i < a := sorry

/--Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_intro' {α : Type u_1} [conditionally_complete_linear_order α] {s : set α} {b : α} (_x : set.nonempty s) (h_is_ub : ∀ (a : α), a ∈ s → a ≤ b) (h_b_le_ub : ∀ (ub : α), (∀ (a : α), a ∈ s → a ≤ ub) → b ≤ ub) : Sup s = b :=
  le_antisymm ((fun (this : Sup s ≤ b) => this) (cSup_le _x h_is_ub))
    ((fun (this : b ≤ Sup s) => this) (h_b_le_ub (Sup s) fun (a : α) => le_cSup (Exists.intro b h_is_ub)))

theorem cSup_empty {α : Type u_1} [conditionally_complete_linear_order_bot α] : Sup ∅ = ⊥ :=
  conditionally_complete_linear_order_bot.cSup_empty

namespace nat


protected instance has_Inf : has_Inf ℕ :=
  has_Inf.mk
    fun (s : set ℕ) => dite (∃ (n : ℕ), n ∈ s) (fun (h : ∃ (n : ℕ), n ∈ s) => nat.find h) fun (h : ¬∃ (n : ℕ), n ∈ s) => 0

protected instance has_Sup : has_Sup ℕ :=
  has_Sup.mk
    fun (s : set ℕ) =>
      dite (∃ (n : ℕ), ∀ (a : ℕ), a ∈ s → a ≤ n) (fun (h : ∃ (n : ℕ), ∀ (a : ℕ), a ∈ s → a ≤ n) => nat.find h)
        fun (h : ¬∃ (n : ℕ), ∀ (a : ℕ), a ∈ s → a ≤ n) => 0

theorem Inf_def {s : set ℕ} (h : set.nonempty s) : Inf s = nat.find h :=
  dif_pos h

theorem Sup_def {s : set ℕ} (h : ∃ (n : ℕ), ∀ (a : ℕ), a ∈ s → a ≤ n) : Sup s = nat.find h :=
  dif_pos h

@[simp] theorem Inf_eq_zero {s : set ℕ} : Inf s = 0 ↔ 0 ∈ s ∨ s = ∅ := sorry

theorem Inf_mem {s : set ℕ} (h : set.nonempty s) : Inf s ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Inf s ∈ s)) (Inf_def h))) (nat.find_spec h)

theorem not_mem_of_lt_Inf {s : set ℕ} {m : ℕ} (hm : m < Inf s) : ¬m ∈ s :=
  or.dcases_on (set.eq_empty_or_nonempty s)
    (fun (h : s = ∅) => Eq._oldrec (fun (hm : m < Inf ∅) => set.not_mem_empty m) (Eq.symm h) hm)
    fun (h : set.nonempty s) => nat.find_min h (eq.mp (Eq._oldrec (Eq.refl (m < Inf s)) (Inf_def h)) hm)

protected theorem Inf_le {s : set ℕ} {m : ℕ} (hm : m ∈ s) : Inf s ≤ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Inf s ≤ m)) (Inf_def (Exists.intro m hm)))) (nat.find_min' (Exists.intro m hm) hm)

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
protected instance lattice : lattice ℕ :=
  Mathlib.lattice_of_linear_order

protected instance conditionally_complete_linear_order_bot : conditionally_complete_linear_order_bot ℕ :=
  conditionally_complete_linear_order_bot.mk lattice.sup order_bot.le order_bot.lt sorry sorry sorry sorry sorry sorry
    lattice.inf sorry sorry sorry Sup Inf sorry sorry sorry sorry sorry linear_order.decidable_le
    linear_order.decidable_eq linear_order.decidable_lt order_bot.bot sorry sorry

end nat


namespace with_top


/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem is_lub_Sup' {β : Type u_1} [conditionally_complete_lattice β] {s : set (with_top β)} (hs : set.nonempty s) : is_lub s (Sup s) := sorry

theorem is_lub_Sup {α : Type u_1} [conditionally_complete_linear_order_bot α] (s : set (with_top α)) : is_lub s (Sup s) := sorry

/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem is_glb_Inf' {β : Type u_1} [conditionally_complete_lattice β] {s : set (with_top β)} (hs : bdd_below s) : is_glb s (Inf s) := sorry

theorem is_glb_Inf {α : Type u_1} [conditionally_complete_linear_order_bot α] (s : set (with_top α)) : is_glb s (Inf s) :=
  dite (bdd_below s) (fun (hs : bdd_below s) => is_glb_Inf' hs)
    fun (hs : ¬bdd_below s) => False._oldrec (hs (Exists.intro ⊥ (id (id fun (a : with_top α) (ᾰ : a ∈ s) => bot_le))))

protected instance complete_linear_order {α : Type u_1} [conditionally_complete_linear_order_bot α] : complete_linear_order (with_top α) :=
  complete_linear_order.mk lattice.sup linear_order.le linear_order.lt sorry sorry sorry sorry sorry sorry lattice.inf
    sorry sorry sorry order_top.top sorry order_bot.bot sorry Sup Inf sorry sorry sorry sorry sorry
    (classical.dec_rel LessEq) linear_order.decidable_eq linear_order.decidable_lt

theorem coe_Sup {α : Type u_1} [conditionally_complete_linear_order_bot α] {s : set α} (hb : bdd_above s) : ↑(Sup s) = supr fun (a : α) => supr fun (H : a ∈ s) => ↑a := sorry

theorem coe_Inf {α : Type u_1} [conditionally_complete_linear_order_bot α] {s : set α} (hs : set.nonempty s) : ↑(Inf s) = infi fun (a : α) => infi fun (H : a ∈ s) => ↑a := sorry

end with_top


namespace enat


protected instance complete_linear_order : complete_linear_order enat :=
  complete_linear_order.mk bounded_lattice.sup linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans
    linear_order.le_antisymm bounded_lattice.le_sup_left bounded_lattice.le_sup_right bounded_lattice.sup_le
    bounded_lattice.inf bounded_lattice.inf_le_left bounded_lattice.inf_le_right bounded_lattice.le_inf
    bounded_lattice.top bounded_lattice.le_top bounded_lattice.bot bounded_lattice.bot_le
    (fun (s : set enat) => coe_fn (equiv.symm with_top_equiv) (Sup (⇑with_top_equiv '' s)))
    (fun (s : set enat) => coe_fn (equiv.symm with_top_equiv) (Inf (⇑with_top_equiv '' s))) sorry sorry sorry sorry
    linear_order.le_total linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt

end enat


protected instance order_dual.conditionally_complete_lattice (α : Type u_1) [conditionally_complete_lattice α] : conditionally_complete_lattice (order_dual α) :=
  conditionally_complete_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf
    sorry sorry sorry Sup Inf cInf_le le_cInf le_cSup cSup_le

protected instance order_dual.conditionally_complete_linear_order (α : Type u_1) [conditionally_complete_linear_order α] : conditionally_complete_linear_order (order_dual α) :=
  conditionally_complete_linear_order.mk conditionally_complete_lattice.sup conditionally_complete_lattice.le
    conditionally_complete_lattice.lt sorry sorry sorry sorry sorry sorry conditionally_complete_lattice.inf sorry sorry
    sorry conditionally_complete_lattice.Sup conditionally_complete_lattice.Inf sorry sorry sorry sorry sorry
    linear_order.decidable_le linear_order.decidable_eq linear_order.decidable_lt

namespace monotone


/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/

theorem le_cSup_image {α : Type u_1} {β : Type u_2} [preorder α] [conditionally_complete_lattice β] {f : α → β} (h_mono : monotone f) {s : set α} {c : α} (hcs : c ∈ s) (h_bdd : bdd_above s) : f c ≤ Sup (f '' s) :=
  le_cSup (map_bdd_above h_mono h_bdd) (set.mem_image_of_mem f hcs)

theorem cSup_image_le {α : Type u_1} {β : Type u_2} [preorder α] [conditionally_complete_lattice β] {f : α → β} (h_mono : monotone f) {s : set α} (hs : set.nonempty s) {B : α} (hB : B ∈ upper_bounds s) : Sup (f '' s) ≤ f B :=
  cSup_le (set.nonempty.image f hs) (mem_upper_bounds_image h_mono hB)

theorem cInf_image_le {α : Type u_1} {β : Type u_2} [preorder α] [conditionally_complete_lattice β] {f : α → β} (h_mono : monotone f) {s : set α} {c : α} (hcs : c ∈ s) (h_bdd : bdd_below s) : Inf (f '' s) ≤ f c :=
  le_cSup_image (fun (x y : order_dual α) (hxy : x ≤ y) => h_mono hxy) hcs h_bdd

theorem le_cInf_image {α : Type u_1} {β : Type u_2} [preorder α] [conditionally_complete_lattice β] {f : α → β} (h_mono : monotone f) {s : set α} (hs : set.nonempty s) {B : α} (hB : B ∈ lower_bounds s) : f B ≤ Inf (f '' s) :=
  cSup_image_le (fun (x y : order_dual α) (hxy : x ≤ y) => h_mono hxy) hs hB

end monotone


/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` naturally inherits the structure of a complete lattice. Note that
for α a conditionally complete lattice, `Sup` and `Inf` both return junk values
for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals [-∞, ∞] are a complete lattice.
-/

/-- Adding a top element to a conditionally complete lattice gives a conditionally complete lattice -/
protected instance with_top.conditionally_complete_lattice {α : Type u_1} [conditionally_complete_lattice α] : conditionally_complete_lattice (with_top α) :=
  conditionally_complete_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf
    sorry sorry sorry Sup Inf sorry sorry sorry sorry

/-- Adding a bottom element to a conditionally complete lattice gives a conditionally complete lattice -/
protected instance with_bot.conditionally_complete_lattice {α : Type u_1} [conditionally_complete_lattice α] : conditionally_complete_lattice (with_bot α) :=
  conditionally_complete_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf
    sorry sorry sorry Sup Inf sorry sorry sorry sorry

/-- Adding a bottom and a top to a conditionally complete lattice gives a bounded lattice-/
protected instance with_top.with_bot.bounded_lattice {α : Type u_1} [conditionally_complete_lattice α] : bounded_lattice (with_top (with_bot α)) :=
  bounded_lattice.mk lattice.sup order_bot.le order_bot.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry
    sorry order_top.top sorry order_bot.bot sorry

theorem with_bot.cSup_empty {α : Type u_1} [conditionally_complete_lattice α] : Sup ∅ = ⊥ := sorry

protected instance with_top.with_bot.complete_lattice {α : Type u_1} [conditionally_complete_lattice α] : complete_lattice (with_top (with_bot α)) :=
  complete_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry Sup Inf sorry sorry sorry
    sorry

/-! ### Subtypes of conditionally complete linear orders

In this section we give conditions on a subset of a conditionally complete linear order, to ensure
that the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

TODO There are several possible variants; the `conditionally_complete_linear_order` could be changed
to `conditionally_complete_linear_order_bot` or `complete_linear_order`.
-/

/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
def subset_has_Sup {α : Type u_1} (s : set α) [has_Sup α] [Inhabited ↥s] : has_Sup ↥s :=
  has_Sup.mk
    fun (t : set ↥s) =>
      dite (Sup (coe '' t) ∈ s) (fun (ht : Sup (coe '' t) ∈ s) => { val := Sup (coe '' t), property := ht })
        fun (ht : ¬Sup (coe '' t) ∈ s) => Inhabited.default

@[simp] theorem subset_Sup_def {α : Type u_1} (s : set α) [has_Sup α] [Inhabited ↥s] : Sup =
  fun (t : set ↥s) =>
    dite (Sup (coe '' t) ∈ s) (fun (ht : Sup (coe '' t) ∈ s) => { val := Sup (coe '' t), property := ht })
      fun (ht : ¬Sup (coe '' t) ∈ s) => Inhabited.default :=
  rfl

theorem subset_Sup_of_within {α : Type u_1} (s : set α) [has_Sup α] [Inhabited ↥s] {t : set ↥s} (h : Sup (coe '' t) ∈ s) : Sup (coe '' t) = ↑(Sup t) := sorry

/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
def subset_has_Inf {α : Type u_1} (s : set α) [has_Inf α] [Inhabited ↥s] : has_Inf ↥s :=
  has_Inf.mk
    fun (t : set ↥s) =>
      dite (Inf (coe '' t) ∈ s) (fun (ht : Inf (coe '' t) ∈ s) => { val := Inf (coe '' t), property := ht })
        fun (ht : ¬Inf (coe '' t) ∈ s) => Inhabited.default

@[simp] theorem subset_Inf_def {α : Type u_1} (s : set α) [has_Inf α] [Inhabited ↥s] : Inf =
  fun (t : set ↥s) =>
    dite (Inf (coe '' t) ∈ s) (fun (ht : Inf (coe '' t) ∈ s) => { val := Inf (coe '' t), property := ht })
      fun (ht : ¬Inf (coe '' t) ∈ s) => Inhabited.default :=
  rfl

theorem subset_Inf_of_within {α : Type u_1} (s : set α) [has_Inf α] [Inhabited ↥s] {t : set ↥s} (h : Inf (coe '' t) ∈ s) : Inf (coe '' t) = ↑(Inf t) := sorry

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets. -/
def subset_conditionally_complete_linear_order {α : Type u_1} (s : set α) [conditionally_complete_linear_order α] [Inhabited ↥s] (h_Sup : ∀ {t : set ↥s}, set.nonempty t → bdd_above t → Sup (coe '' t) ∈ s) (h_Inf : ∀ {t : set ↥s}, set.nonempty t → bdd_below t → Inf (coe '' t) ∈ s) : conditionally_complete_linear_order ↥s :=
  conditionally_complete_linear_order.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf
    sorry sorry sorry Sup Inf sorry sorry sorry sorry sorry linear_order.decidable_le linear_order.decidable_eq
    linear_order.decidable_lt

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem Sup_within_of_ord_connected {α : Type u_1} [conditionally_complete_linear_order α] {s : set α} [hs : set.ord_connected s] {t : set ↥s} (ht : set.nonempty t) (h_bdd : bdd_above t) : Sup (coe '' t) ∈ s := sorry

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem Inf_within_of_ord_connected {α : Type u_1} [conditionally_complete_linear_order α] {s : set α} [hs : set.ord_connected s] {t : set ↥s} (ht : set.nonempty t) (h_bdd : bdd_below t) : Inf (coe '' t) ∈ s := sorry

/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
protected instance ord_connected_subset_conditionally_complete_linear_order {α : Type u_1} (s : set α) [conditionally_complete_linear_order α] [Inhabited ↥s] [set.ord_connected s] : conditionally_complete_linear_order ↥s :=
  subset_conditionally_complete_linear_order s Sup_within_of_ord_connected Inf_within_of_ord_connected

