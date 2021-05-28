/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.group_power.basic
import Mathlib.algebra.order_functions
import Mathlib.algebra.ordered_monoid
import Mathlib.PostPort

universes u_1 u 

namespace Mathlib

/-!
# Basic operations on the natural numbers

This file contains:
- instances on the natural numbers
- some basic lemmas about natural numbers
- extra recursors:
  * `le_rec_on`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `strong_rec'`: recursion based on strong inequalities
- decidability instances on predicates about the natural numbers

-/

/-! ### instances -/

protected instance nat.nontrivial : nontrivial ℕ :=
  nontrivial.mk (Exists.intro 0 (Exists.intro 1 nat.zero_ne_one))

protected instance nat.comm_semiring : comm_semiring ℕ :=
  comm_semiring.mk Nat.add nat.add_assoc 0 nat.zero_add nat.add_zero nat.add_comm Nat.mul nat.mul_assoc 1 nat.one_mul
    nat.mul_one nat.zero_mul nat.mul_zero nat.left_distrib nat.right_distrib nat.mul_comm

protected instance nat.linear_ordered_semiring : linear_ordered_semiring ℕ :=
  linear_ordered_semiring.mk comm_semiring.add comm_semiring.add_assoc comm_semiring.zero comm_semiring.zero_add
    comm_semiring.add_zero comm_semiring.add_comm comm_semiring.mul comm_semiring.mul_assoc comm_semiring.one
    comm_semiring.one_mul comm_semiring.mul_one comm_semiring.zero_mul comm_semiring.mul_zero comm_semiring.left_distrib
    comm_semiring.right_distrib nat.add_left_cancel nat.add_right_cancel linear_order.le nat.lt linear_order.le_refl
    linear_order.le_trans linear_order.le_antisymm nat.add_le_add_left nat.le_of_add_le_add_left sorry
    nat.mul_lt_mul_of_pos_left nat.mul_lt_mul_of_pos_right linear_order.le_total linear_order.decidable_le
    nat.decidable_eq linear_order.decidable_lt sorry

-- all the fields are already included in the linear_ordered_semiring instance

protected instance nat.linear_ordered_cancel_add_comm_monoid : linear_ordered_cancel_add_comm_monoid ℕ :=
  linear_ordered_cancel_add_comm_monoid.mk linear_ordered_semiring.add linear_ordered_semiring.add_assoc
    nat.add_left_cancel linear_ordered_semiring.zero linear_ordered_semiring.zero_add linear_ordered_semiring.add_zero
    linear_ordered_semiring.add_comm linear_ordered_semiring.add_right_cancel linear_ordered_semiring.le
    linear_ordered_semiring.lt linear_ordered_semiring.le_refl linear_ordered_semiring.le_trans
    linear_ordered_semiring.le_antisymm linear_ordered_semiring.add_le_add_left
    linear_ordered_semiring.le_of_add_le_add_left linear_ordered_semiring.le_total linear_ordered_semiring.decidable_le
    linear_ordered_semiring.decidable_eq linear_ordered_semiring.decidable_lt

protected instance nat.linear_ordered_comm_monoid_with_zero : linear_ordered_comm_monoid_with_zero ℕ :=
  linear_ordered_comm_monoid_with_zero.mk linear_ordered_semiring.le linear_ordered_semiring.lt
    linear_ordered_semiring.le_refl linear_ordered_semiring.le_trans linear_ordered_semiring.le_antisymm
    linear_ordered_semiring.le_total linear_ordered_semiring.decidable_le linear_ordered_semiring.decidable_eq
    linear_ordered_semiring.decidable_lt linear_ordered_semiring.mul linear_ordered_semiring.mul_assoc
    linear_ordered_semiring.one linear_ordered_semiring.one_mul linear_ordered_semiring.mul_one sorry
    linear_ordered_semiring.zero linear_ordered_semiring.zero_mul linear_ordered_semiring.mul_zero sorry sorry
    linear_ordered_semiring.zero_le_one

/-! Extra instances to short-circuit type class resolution -/

protected instance nat.add_comm_monoid : add_comm_monoid ℕ :=
  ordered_add_comm_monoid.to_add_comm_monoid ℕ

protected instance nat.add_monoid : add_monoid ℕ :=
  add_right_cancel_monoid.to_add_monoid ℕ

protected instance nat.monoid : monoid ℕ :=
  monoid_with_zero.to_monoid ℕ

protected instance nat.comm_monoid : comm_monoid ℕ :=
  ordered_comm_monoid.to_comm_monoid ℕ

protected instance nat.comm_semigroup : comm_semigroup ℕ :=
  comm_monoid.to_comm_semigroup ℕ

protected instance nat.semigroup : semigroup ℕ :=
  monoid.to_semigroup ℕ

protected instance nat.add_comm_semigroup : add_comm_semigroup ℕ :=
  add_comm_monoid.to_add_comm_semigroup ℕ

protected instance nat.add_semigroup : add_semigroup ℕ :=
  add_monoid.to_add_semigroup ℕ

protected instance nat.distrib : distrib ℕ :=
  semiring.to_distrib ℕ

protected instance nat.semiring : semiring ℕ :=
  ordered_semiring.to_semiring ℕ

protected instance nat.ordered_semiring : ordered_semiring ℕ :=
  linear_ordered_semiring.to_ordered_semiring ℕ

protected instance nat.canonically_ordered_comm_semiring : canonically_ordered_comm_semiring ℕ :=
  canonically_ordered_comm_semiring.mk ordered_add_comm_monoid.add sorry ordered_add_comm_monoid.zero sorry sorry sorry
    ordered_add_comm_monoid.le ordered_add_comm_monoid.lt sorry sorry sorry sorry sorry 0 nat.zero_le sorry
    linear_ordered_semiring.mul sorry linear_ordered_semiring.one sorry sorry sorry sorry sorry sorry sorry sorry

protected instance nat.subtype.semilattice_sup_bot (s : set ℕ) [decidable_pred s] [h : Nonempty ↥s] : semilattice_sup_bot ↥s :=
  semilattice_sup_bot.mk { val := nat.find sorry, property := sorry } linear_order.le linear_order.lt sorry sorry sorry
    sorry lattice.sup sorry sorry sorry

theorem nat.eq_of_mul_eq_mul_right {n : ℕ} {m : ℕ} {k : ℕ} (Hm : 0 < m) (H : n * m = k * m) : n = k :=
  nat.eq_of_mul_eq_mul_left Hm
    (eq.mp (Eq._oldrec (Eq.refl (m * n = k * m)) (mul_comm k m))
      (eq.mp (Eq._oldrec (Eq.refl (n * m = k * m)) (mul_comm n m)) H))

protected instance nat.comm_cancel_monoid_with_zero : comm_cancel_monoid_with_zero ℕ :=
  comm_cancel_monoid_with_zero.mk comm_monoid_with_zero.mul sorry comm_monoid_with_zero.one sorry sorry sorry
    comm_monoid_with_zero.zero sorry sorry sorry sorry

/-!
Inject some simple facts into the type class system.
This `fact` should not be confused with the factorial function `nat.fact`!
-/

protected instance succ_pos'' (n : ℕ) : fact (0 < Nat.succ n) :=
  nat.succ_pos n

protected instance pos_of_one_lt (n : ℕ) [h : fact (1 < n)] : fact (0 < n) :=
  lt_trans zero_lt_one h

namespace nat


/-!
### Recursion and `set.range`
-/

theorem zero_union_range_succ : singleton 0 ∪ set.range Nat.succ = set.univ := sorry

theorem range_of_succ {α : Type u_1} (f : ℕ → α) : singleton (f 0) ∪ set.range (f ∘ Nat.succ) = set.range f := sorry

theorem range_rec {α : Type u_1} (x : α) (f : ℕ → α → α) : (set.range fun (n : ℕ) => Nat.rec x f n) = singleton x ∪ set.range fun (n : ℕ) => Nat.rec (f 0 x) (f ∘ Nat.succ) n := sorry

theorem range_cases_on {α : Type u_1} (x : α) (f : ℕ → α) : (set.range fun (n : ℕ) => nat.cases_on n x f) = singleton x ∪ set.range f :=
  Eq.symm (range_of_succ fun (n : ℕ) => nat.cases_on n x f)

/-! ### The units of the natural numbers as a `monoid` and `add_monoid` -/

theorem units_eq_one (u : units ℕ) : u = 1 :=
  units.ext (eq_one_of_dvd_one (Exists.intro (units.inv u) (Eq.symm (units.val_inv u))))

theorem add_units_eq_zero (u : add_units ℕ) : u = 0 :=
  add_units.ext (and.left (eq_zero_of_add_eq_zero (add_units.val_neg u)))

@[simp] protected theorem is_unit_iff {n : ℕ} : is_unit n ↔ n = 1 := sorry

/-! ### Equalities and inequalities involving zero and one -/

theorem one_lt_iff_ne_zero_and_ne_one {n : ℕ} : 1 < n ↔ n ≠ 0 ∧ n ≠ 1 := sorry

protected theorem mul_ne_zero {n : ℕ} {m : ℕ} (n0 : n ≠ 0) (m0 : m ≠ 0) : n * m ≠ 0 :=
  fun (ᾰ : n * m = 0) => idRhs False (or.elim (eq_zero_of_mul_eq_zero ᾰ) n0 m0)

@[simp] protected theorem mul_eq_zero {a : ℕ} {b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 := sorry

@[simp] protected theorem zero_eq_mul {a : ℕ} {b : ℕ} : 0 = a * b ↔ a = 0 ∨ b = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 = a * b ↔ a = 0 ∨ b = 0)) (propext eq_comm)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a * b = 0 ↔ a = 0 ∨ b = 0)) (propext nat.mul_eq_zero))) (iff.refl (a = 0 ∨ b = 0)))

theorem eq_zero_of_double_le {a : ℕ} (h : bit0 1 * a ≤ a) : a = 0 := sorry

theorem eq_zero_of_mul_le {a : ℕ} {b : ℕ} (hb : bit0 1 ≤ b) (h : b * a ≤ a) : a = 0 :=
  eq_zero_of_double_le (le_trans (mul_le_mul_right a hb) h)

theorem le_zero_iff {i : ℕ} : i ≤ 0 ↔ i = 0 :=
  { mp := eq_zero_of_le_zero, mpr := fun (h : i = 0) => h ▸ le_refl i }

theorem zero_max {m : ℕ} : max 0 m = m :=
  max_eq_right (zero_le m)

theorem one_le_of_lt {n : ℕ} {m : ℕ} (h : n < m) : 1 ≤ m :=
  lt_of_le_of_lt (zero_le n) h

theorem eq_one_of_mul_eq_one_right {m : ℕ} {n : ℕ} (H : m * n = 1) : m = 1 :=
  eq_one_of_dvd_one (Exists.intro n (Eq.symm H))

theorem eq_one_of_mul_eq_one_left {m : ℕ} {n : ℕ} (H : m * n = 1) : n = 1 :=
  eq_one_of_mul_eq_one_right (eq.mpr (id (Eq._oldrec (Eq.refl (n * m = 1)) (mul_comm n m))) H)

/-! ### `succ` -/

theorem eq_of_lt_succ_of_not_lt {a : ℕ} {b : ℕ} (h1 : a < b + 1) (h2 : ¬a < b) : a = b :=
  (fun (h3 : a ≤ b) =>
      or.elim (eq_or_lt_of_not_lt h2) (fun (h : a = b) => h) fun (h : b < a) => absurd h (not_lt_of_ge h3))
    (le_of_lt_succ h1)

theorem one_add (n : ℕ) : 1 + n = Nat.succ n := sorry

@[simp] theorem succ_pos' {n : ℕ} : 0 < Nat.succ n :=
  succ_pos n

theorem succ_inj' {n : ℕ} {m : ℕ} : Nat.succ n = Nat.succ m ↔ n = m :=
  { mp := succ.inj, mpr := congr_arg fun {n : ℕ} => Nat.succ n }

theorem succ_injective : function.injective Nat.succ :=
  fun (x y : ℕ) => succ.inj

theorem succ_le_succ_iff {m : ℕ} {n : ℕ} : Nat.succ m ≤ Nat.succ n ↔ m ≤ n :=
  { mp := le_of_succ_le_succ, mpr := succ_le_succ }

theorem max_succ_succ {m : ℕ} {n : ℕ} : max (Nat.succ m) (Nat.succ n) = Nat.succ (max m n) := sorry

theorem not_succ_lt_self {n : ℕ} : ¬Nat.succ n < n :=
  not_lt_of_ge (le_succ n)

theorem lt_succ_iff {m : ℕ} {n : ℕ} : m < Nat.succ n ↔ m ≤ n :=
  succ_le_succ_iff

theorem succ_le_iff {m : ℕ} {n : ℕ} : Nat.succ m ≤ n ↔ m < n :=
  { mp := lt_of_succ_le, mpr := succ_le_of_lt }

theorem lt_iff_add_one_le {m : ℕ} {n : ℕ} : m < n ↔ m + 1 ≤ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m < n ↔ m + 1 ≤ n)) (propext succ_le_iff))) (iff.refl (m < n))

-- Just a restatement of `nat.lt_succ_iff` using `+1`.

theorem lt_add_one_iff {a : ℕ} {b : ℕ} : a < b + 1 ↔ a ≤ b :=
  lt_succ_iff

-- A flipped version of `lt_add_one_iff`.

theorem lt_one_add_iff {a : ℕ} {b : ℕ} : a < 1 + b ↔ a ≤ b := sorry

-- This is true reflexively, by the definition of `≤` on ℕ,

-- but it's still useful to have, to convince Lean to change the syntactic type.

theorem add_one_le_iff {a : ℕ} {b : ℕ} : a + 1 ≤ b ↔ a < b :=
  iff.refl (a + 1 ≤ b)

theorem one_add_le_iff {a : ℕ} {b : ℕ} : 1 + a ≤ b ↔ a < b := sorry

theorem of_le_succ {n : ℕ} {m : ℕ} (H : n ≤ Nat.succ m) : n ≤ m ∨ n = Nat.succ m :=
  or.imp le_of_lt_succ id (lt_or_eq_of_le H)

theorem succ_lt_succ_iff {m : ℕ} {n : ℕ} : Nat.succ m < Nat.succ n ↔ m < n :=
  { mp := lt_of_succ_lt_succ, mpr := succ_lt_succ }

/-! ### `add` -/

-- Sometimes a bare `nat.add` or similar appears as a consequence of unfolding

-- during pattern matching. These lemmas package them back up as typeclass

-- mediated operations.

@[simp] theorem add_def {a : ℕ} {b : ℕ} : Nat.add a b = a + b :=
  rfl

@[simp] theorem mul_def {a : ℕ} {b : ℕ} : Nat.mul a b = a * b :=
  rfl

theorem exists_eq_add_of_le {m : ℕ} {n : ℕ} : m ≤ n → ∃ (k : ℕ), n = m + k := sorry

theorem exists_eq_add_of_lt {m : ℕ} {n : ℕ} : m < n → ∃ (k : ℕ), n = m + k + 1 := sorry

theorem add_pos_left {m : ℕ} (h : 0 < m) (n : ℕ) : 0 < m + n :=
  gt_of_gt_of_ge (trans_rel_left gt (nat.add_lt_add_right h n) (nat.zero_add n)) (zero_le n)

theorem add_pos_right (m : ℕ) {n : ℕ} (h : 0 < n) : 0 < m + n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < m + n)) (add_comm m n))) (add_pos_left h m)

theorem add_pos_iff_pos_or_pos (m : ℕ) (n : ℕ) : 0 < m + n ↔ 0 < m ∨ 0 < n := sorry

theorem add_eq_one_iff {a : ℕ} {b : ℕ} : a + b = 1 ↔ a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0 := sorry

theorem le_add_one_iff {i : ℕ} {j : ℕ} : i ≤ j + 1 ↔ i ≤ j ∨ i = j + 1 := sorry

theorem add_succ_lt_add {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (hab : a < b) (hcd : c < d) : a + c + 1 < b + d :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + c + 1 < b + d)) (add_assoc a c 1)))
    (add_lt_add_of_lt_of_le hab (iff.mpr succ_le_iff hcd))

/-! ### `pred` -/

@[simp] theorem add_succ_sub_one (n : ℕ) (m : ℕ) : n + Nat.succ m - 1 = n + m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n + Nat.succ m - 1 = n + m)) (add_succ n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Nat.succ (n + m) - 1 = n + m)) (succ_sub_one (n + m)))) (Eq.refl (n + m)))

@[simp] theorem succ_add_sub_one (n : ℕ) (m : ℕ) : Nat.succ n + m - 1 = n + m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Nat.succ n + m - 1 = n + m)) (succ_add n m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Nat.succ (n + m) - 1 = n + m)) (succ_sub_one (n + m)))) (Eq.refl (n + m)))

theorem pred_eq_sub_one (n : ℕ) : Nat.pred n = n - 1 :=
  rfl

theorem pred_eq_of_eq_succ {m : ℕ} {n : ℕ} (H : m = Nat.succ n) : Nat.pred m = n := sorry

@[simp] theorem pred_eq_succ_iff {n : ℕ} {m : ℕ} : Nat.pred n = Nat.succ m ↔ n = m + bit0 1 := sorry

theorem pred_sub (n : ℕ) (m : ℕ) : Nat.pred n - m = Nat.pred (n - m) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Nat.pred n - m = Nat.pred (n - m))) (Eq.symm (sub_one n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n - 1 - m = Nat.pred (n - m))) (nat.sub_sub n 1 m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n - (1 + m) = Nat.pred (n - m))) (one_add m))) (Eq.refl (n - Nat.succ m))))

theorem le_pred_of_lt {n : ℕ} {m : ℕ} (h : m < n) : m ≤ n - 1 :=
  nat.sub_le_sub_right h 1

theorem le_of_pred_lt {m : ℕ} {n : ℕ} : Nat.pred m < n → m ≤ n := sorry

/-- This ensures that `simp` succeeds on `pred (n + 1) = n`. -/
@[simp] theorem pred_one_add (n : ℕ) : Nat.pred (1 + n) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (Nat.pred (1 + n) = n)) (add_comm 1 n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (Nat.pred (n + 1) = n)) (add_one n)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (Nat.pred (Nat.succ n) = n)) (pred_succ n))) (Eq.refl n)))

/-! ### `sub` -/

protected theorem le_sub_add (n : ℕ) (m : ℕ) : n ≤ n - m + m := sorry

theorem sub_add_eq_max (n : ℕ) (m : ℕ) : n - m + m = max n m := sorry

theorem add_sub_eq_max (n : ℕ) (m : ℕ) : n + (m - n) = max n m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n + (m - n) = max n m)) (add_comm n (m - n))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m - n + n = max n m)) (max_comm n m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (m - n + n = max m n)) (sub_add_eq_max m n))) (Eq.refl (max m n))))

theorem sub_add_min (n : ℕ) (m : ℕ) : n - m + min n m = n := sorry

protected theorem add_sub_cancel' {n : ℕ} {m : ℕ} (h : m ≤ n) : m + (n - m) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m + (n - m) = n)) (add_comm m (n - m))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n - m + m = n)) (nat.sub_add_cancel h))) (Eq.refl n))

protected theorem sub_add_sub_cancel {a : ℕ} {b : ℕ} {c : ℕ} (hab : b ≤ a) (hbc : c ≤ b) : a - b + (b - c) = a - c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b + (b - c) = a - c)) (Eq.symm (nat.add_sub_assoc hbc (a - b)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b + b - c = a - c)) (Eq.symm (nat.sub_add_comm hab))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a + b - b - c = a - c)) (nat.add_sub_cancel a b))) (Eq.refl (a - c))))

protected theorem sub_eq_of_eq_add {m : ℕ} {n : ℕ} {k : ℕ} (h : k = m + n) : k - m = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k - m = n)) h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m + n - m = n)) (nat.add_sub_cancel_left m n))) (Eq.refl n))

theorem sub_cancel {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : a ≤ b) (h₂ : a ≤ c) (w : b - a = c - a) : b = c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b = c)) (Eq.symm (nat.sub_add_cancel h₁))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b - a + a = c)) (Eq.symm (nat.sub_add_cancel h₂))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (b - a + a = c - a + a)) w)) (Eq.refl (c - a + a))))

theorem sub_sub_sub_cancel_right {a : ℕ} {b : ℕ} {c : ℕ} (h₂ : c ≤ b) : a - c - (b - c) = a - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - c - (b - c) = a - b)) (nat.sub_sub a c (b - c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - (c + (b - c)) = a - b)) (Eq.symm (nat.add_sub_assoc h₂ c))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a - (c + b - c) = a - b)) (nat.add_sub_cancel_left c b))) (Eq.refl (a - b))))

theorem add_sub_cancel_right (n : ℕ) (m : ℕ) (k : ℕ) : n + (m + k) - k = n + m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (n + (m + k) - k = n + m)) (nat.add_sub_assoc (le_add_left k m) n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + (m + k - k) = n + m)) (nat.add_sub_cancel m k))) (Eq.refl (n + m)))

protected theorem sub_add_eq_add_sub {a : ℕ} {b : ℕ} {c : ℕ} (h : b ≤ a) : a - b + c = a + c - b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a - b + c = a + c - b)) (add_comm a c)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a - b + c = c + a - b)) (nat.add_sub_assoc h c)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a - b + c = c + (a - b))) (add_comm (a - b) c))) (Eq.refl (c + (a - b)))))

theorem sub_min (n : ℕ) (m : ℕ) : n - min n m = n - m :=
  nat.sub_eq_of_eq_add
    (eq.mpr (id (Eq._oldrec (Eq.refl (n = min n m + (n - m))) (add_comm (min n m) (n - m))))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n = n - m + min n m)) (sub_add_min n m))) (Eq.refl n)))

theorem sub_sub_assoc {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : b ≤ a) (h₂ : c ≤ b) : a - (b - c) = a - b + c := sorry

protected theorem lt_of_sub_pos {m : ℕ} {n : ℕ} (h : 0 < n - m) : m < n :=
  lt_of_not_ge
    fun (this : n ≤ m) =>
      (fun (this : n - m = 0) => lt_irrefl 0 (eq.mp (Eq._oldrec (Eq.refl (0 < n - m)) this) h)) (sub_eq_zero_of_le this)

protected theorem lt_of_sub_lt_sub_right {m : ℕ} {n : ℕ} {k : ℕ} : m - k < n - k → m < n :=
  lt_imp_lt_of_le_imp_le fun (h : n ≤ m) => nat.sub_le_sub_right h k

protected theorem lt_of_sub_lt_sub_left {m : ℕ} {n : ℕ} {k : ℕ} : m - n < m - k → k < n :=
  lt_imp_lt_of_le_imp_le (nat.sub_le_sub_left m)

protected theorem sub_lt_self {m : ℕ} {n : ℕ} (h₁ : 0 < m) (h₂ : 0 < n) : m - n < m := sorry

protected theorem le_sub_right_of_add_le {m : ℕ} {n : ℕ} {k : ℕ} (h : m + k ≤ n) : m ≤ n - k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m ≤ n - k)) (Eq.symm (nat.add_sub_cancel m k)))) (nat.sub_le_sub_right h k)

protected theorem le_sub_left_of_add_le {m : ℕ} {n : ℕ} {k : ℕ} (h : k + m ≤ n) : m ≤ n - k :=
  nat.le_sub_right_of_add_le (eq.mp (Eq._oldrec (Eq.refl (k + m ≤ n)) (add_comm k m)) h)

protected theorem lt_sub_right_of_add_lt {m : ℕ} {n : ℕ} {k : ℕ} (h : m + k < n) : m < n - k :=
  lt_of_succ_le
    (nat.le_sub_right_of_add_le
      (eq.mpr (id (Eq._oldrec (Eq.refl (Nat.succ m + k ≤ n)) (succ_add m k))) (succ_le_of_lt h)))

protected theorem lt_sub_left_of_add_lt {m : ℕ} {n : ℕ} {k : ℕ} (h : k + m < n) : m < n - k :=
  nat.lt_sub_right_of_add_lt (eq.mp (Eq._oldrec (Eq.refl (k + m < n)) (add_comm k m)) h)

protected theorem add_lt_of_lt_sub_right {m : ℕ} {n : ℕ} {k : ℕ} (h : m < n - k) : m + k < n :=
  nat.lt_of_sub_lt_sub_right (eq.mpr (id (Eq._oldrec (Eq.refl (m + k - k < n - k)) (nat.add_sub_cancel m k))) h)

protected theorem add_lt_of_lt_sub_left {m : ℕ} {n : ℕ} {k : ℕ} (h : m < n - k) : k + m < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k + m < n)) (add_comm k m))) (nat.add_lt_of_lt_sub_right h)

protected theorem le_add_of_sub_le_right {m : ℕ} {n : ℕ} {k : ℕ} : n - k ≤ m → n ≤ m + k :=
  le_imp_le_of_lt_imp_lt nat.lt_sub_right_of_add_lt

protected theorem le_add_of_sub_le_left {m : ℕ} {n : ℕ} {k : ℕ} : n - k ≤ m → n ≤ k + m :=
  le_imp_le_of_lt_imp_lt nat.lt_sub_left_of_add_lt

protected theorem lt_add_of_sub_lt_right {m : ℕ} {n : ℕ} {k : ℕ} : n - k < m → n < m + k :=
  lt_imp_lt_of_le_imp_le nat.le_sub_right_of_add_le

protected theorem lt_add_of_sub_lt_left {m : ℕ} {n : ℕ} {k : ℕ} : n - k < m → n < k + m :=
  lt_imp_lt_of_le_imp_le nat.le_sub_left_of_add_le

protected theorem sub_le_left_of_le_add {m : ℕ} {n : ℕ} {k : ℕ} : n ≤ k + m → n - k ≤ m :=
  le_imp_le_of_lt_imp_lt nat.add_lt_of_lt_sub_left

protected theorem sub_le_right_of_le_add {m : ℕ} {n : ℕ} {k : ℕ} : n ≤ m + k → n - k ≤ m :=
  le_imp_le_of_lt_imp_lt nat.add_lt_of_lt_sub_right

protected theorem sub_lt_left_iff_lt_add {m : ℕ} {n : ℕ} {k : ℕ} (H : n ≤ k) : k - n < m ↔ k < n + m := sorry

protected theorem le_sub_left_iff_add_le {m : ℕ} {n : ℕ} {k : ℕ} (H : m ≤ k) : n ≤ k - m ↔ m + n ≤ k :=
  iff.mpr le_iff_le_iff_lt_iff_lt (nat.sub_lt_left_iff_lt_add H)

protected theorem le_sub_right_iff_add_le {m : ℕ} {n : ℕ} {k : ℕ} (H : n ≤ k) : m ≤ k - n ↔ m + n ≤ k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m ≤ k - n ↔ m + n ≤ k)) (propext (nat.le_sub_left_iff_add_le H))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + m ≤ k ↔ m + n ≤ k)) (add_comm n m))) (iff.refl (m + n ≤ k)))

protected theorem lt_sub_left_iff_add_lt {m : ℕ} {n : ℕ} {k : ℕ} : n < k - m ↔ m + n < k :=
  { mp := nat.add_lt_of_lt_sub_left, mpr := nat.lt_sub_left_of_add_lt }

protected theorem lt_sub_right_iff_add_lt {m : ℕ} {n : ℕ} {k : ℕ} : m < k - n ↔ m + n < k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m < k - n ↔ m + n < k)) (propext nat.lt_sub_left_iff_add_lt)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n + m < k ↔ m + n < k)) (add_comm n m))) (iff.refl (m + n < k)))

theorem sub_le_left_iff_le_add {m : ℕ} {n : ℕ} {k : ℕ} : m - n ≤ k ↔ m ≤ n + k :=
  iff.mpr le_iff_le_iff_lt_iff_lt nat.lt_sub_left_iff_add_lt

theorem sub_le_right_iff_le_add {m : ℕ} {n : ℕ} {k : ℕ} : m - k ≤ n ↔ m ≤ n + k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m - k ≤ n ↔ m ≤ n + k)) (propext sub_le_left_iff_le_add)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m ≤ k + n ↔ m ≤ n + k)) (add_comm k n))) (iff.refl (m ≤ n + k)))

protected theorem sub_lt_right_iff_lt_add {m : ℕ} {n : ℕ} {k : ℕ} (H : k ≤ m) : m - k < n ↔ m < n + k :=
  eq.mpr (id (Eq._oldrec (Eq.refl (m - k < n ↔ m < n + k)) (propext (nat.sub_lt_left_iff_lt_add H))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (m < k + n ↔ m < n + k)) (add_comm k n))) (iff.refl (m < n + k)))

protected theorem sub_le_sub_left_iff {m : ℕ} {n : ℕ} {k : ℕ} (H : k ≤ m) : m - n ≤ m - k ↔ k ≤ n := sorry

protected theorem sub_lt_sub_right_iff {m : ℕ} {n : ℕ} {k : ℕ} (H : k ≤ m) : m - k < n - k ↔ m < n :=
  lt_iff_lt_of_le_iff_le (nat.sub_le_sub_right_iff n m k H)

protected theorem sub_lt_sub_left_iff {m : ℕ} {n : ℕ} {k : ℕ} (H : n ≤ m) : m - n < m - k ↔ k < n :=
  lt_iff_lt_of_le_iff_le (nat.sub_le_sub_left_iff H)

protected theorem sub_le_iff {m : ℕ} {n : ℕ} {k : ℕ} : m - n ≤ k ↔ m - k ≤ n :=
  iff.trans sub_le_left_iff_le_add (iff.symm sub_le_right_iff_le_add)

protected theorem sub_le_self (n : ℕ) (m : ℕ) : n - m ≤ n :=
  nat.sub_le_left_of_le_add (le_add_left n m)

protected theorem sub_lt_iff {m : ℕ} {n : ℕ} {k : ℕ} (h₁ : n ≤ m) (h₂ : k ≤ m) : m - n < k ↔ m - k < n :=
  iff.trans (nat.sub_lt_left_iff_lt_add h₁) (iff.symm (nat.sub_lt_right_iff_lt_add h₂))

theorem pred_le_iff {n : ℕ} {m : ℕ} : Nat.pred n ≤ m ↔ n ≤ Nat.succ m :=
  sub_le_right_iff_le_add

theorem lt_pred_iff {n : ℕ} {m : ℕ} : n < Nat.pred m ↔ Nat.succ n < m :=
  nat.lt_sub_right_iff_add_lt

theorem lt_of_lt_pred {a : ℕ} {b : ℕ} (h : a < b - 1) : a < b :=
  lt_of_succ_lt (iff.mp lt_pred_iff h)

/-! ### `mul` -/

theorem mul_self_le_mul_self {n : ℕ} {m : ℕ} (h : n ≤ m) : n * n ≤ m * m :=
  mul_le_mul h h (zero_le n) (zero_le m)

theorem mul_self_lt_mul_self {n : ℕ} {m : ℕ} : n < m → n * n < m * m := sorry

theorem mul_self_le_mul_self_iff {n : ℕ} {m : ℕ} : n ≤ m ↔ n * n ≤ m * m := sorry

theorem mul_self_lt_mul_self_iff {n : ℕ} {m : ℕ} : n < m ↔ n * n < m * m :=
  iff.trans (lt_iff_not_ge n m)
    (iff.trans (not_iff_not_of_iff mul_self_le_mul_self_iff) (iff.symm (lt_iff_not_ge (n * n) (m * m))))

theorem le_mul_self (n : ℕ) : n ≤ n * n := sorry

theorem le_mul_of_pos_left {m : ℕ} {n : ℕ} (h : 0 < n) : m ≤ n * m := sorry

theorem le_mul_of_pos_right {m : ℕ} {n : ℕ} (h : 0 < n) : m ≤ m * n := sorry

theorem two_mul_ne_two_mul_add_one {n : ℕ} {m : ℕ} : bit0 1 * n ≠ bit0 1 * m + 1 := sorry

theorem mul_eq_one_iff {a : ℕ} {b : ℕ} : a * b = 1 ↔ a = 1 ∧ b = 1 := sorry

protected theorem mul_left_inj {a : ℕ} {b : ℕ} {c : ℕ} (ha : 0 < a) : b * a = c * a ↔ b = c :=
  { mp := eq_of_mul_eq_mul_right ha, mpr := fun (e : b = c) => e ▸ rfl }

protected theorem mul_right_inj {a : ℕ} {b : ℕ} {c : ℕ} (ha : 0 < a) : a * b = a * c ↔ b = c :=
  { mp := eq_of_mul_eq_mul_left ha, mpr := fun (e : b = c) => e ▸ rfl }

theorem mul_left_injective {a : ℕ} (ha : 0 < a) : function.injective fun (x : ℕ) => x * a :=
  fun (_x _x_1 : ℕ) => eq_of_mul_eq_mul_right ha

theorem mul_right_injective {a : ℕ} (ha : 0 < a) : function.injective fun (x : ℕ) => a * x :=
  fun (_x _x_1 : ℕ) => eq_of_mul_eq_mul_left ha

theorem mul_right_eq_self_iff {a : ℕ} {b : ℕ} (ha : 0 < a) : a * b = a ↔ b = 1 :=
  (fun (this : a * b = a * 1 ↔ b = 1) => eq.mp (Eq._oldrec (Eq.refl (a * b = a * 1 ↔ b = 1)) (mul_one a)) this)
    (nat.mul_right_inj ha)

theorem mul_left_eq_self_iff {a : ℕ} {b : ℕ} (hb : 0 < b) : a * b = b ↔ a = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * b = b ↔ a = 1)) (mul_comm a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a = b ↔ a = 1)) (propext (mul_right_eq_self_iff hb)))) (iff.refl (a = 1)))

theorem lt_succ_iff_lt_or_eq {n : ℕ} {i : ℕ} : n < Nat.succ i ↔ n < i ∨ n = i :=
  iff.trans lt_succ_iff le_iff_lt_or_eq

theorem mul_self_inj {n : ℕ} {m : ℕ} : n * n = m * m ↔ n = m :=
  iff.trans le_antisymm_iff
    (iff.symm (iff.trans le_antisymm_iff (and_congr mul_self_le_mul_self_iff mul_self_le_mul_self_iff)))

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp] theorem rec_zero {C : ℕ → Sort u} (h0 : C 0) (h : (n : ℕ) → C n → C (n + 1)) : Nat.rec h0 h 0 = h0 :=
  rfl

@[simp] theorem rec_add_one {C : ℕ → Sort u} (h0 : C 0) (h : (n : ℕ) → C n → C (n + 1)) (n : ℕ) : Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) :=
  rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. -/
def le_rec_on {C : ℕ → Sort u} {n : ℕ} {m : ℕ} : n ≤ m → ({k : ℕ} → C k → C (k + 1)) → C n → C m :=
  sorry

theorem le_rec_on_self {C : ℕ → Sort u} {n : ℕ} {h : n ≤ n} {next : {k : ℕ} → C k → C (k + 1)} (x : C n) : le_rec_on h next x = x := sorry

theorem le_rec_on_succ {C : ℕ → Sort u} {n : ℕ} {m : ℕ} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next : {k : ℕ} → C k → C (k + 1)} (x : C n) : le_rec_on h2 next x = next (le_rec_on h1 next x) := sorry

theorem le_rec_on_succ' {C : ℕ → Sort u} {n : ℕ} {h : n ≤ n + 1} {next : {k : ℕ} → C k → C (k + 1)} (x : C n) : le_rec_on h next x = next x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (le_rec_on h next x = next x)) (le_rec_on_succ (le_refl n) x)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (next (le_rec_on (le_refl n) next x) = next x)) (le_rec_on_self x)))
      (Eq.refl (next x)))

theorem le_rec_on_trans {C : ℕ → Sort u} {n : ℕ} {m : ℕ} {k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) {next : {k : ℕ} → C k → C (k + 1)} (x : C n) : le_rec_on (le_trans hnm hmk) next x = le_rec_on hmk next (le_rec_on hnm next x) := sorry

theorem le_rec_on_succ_left {C : ℕ → Sort u} {n : ℕ} {m : ℕ} (h1 : n ≤ m) (h2 : n + 1 ≤ m) {next : {k : ℕ} → C k → C (k + 1)} (x : C n) : le_rec_on h2 next (next x) = le_rec_on h1 next x := sorry

theorem le_rec_on_injective {C : ℕ → Sort u} {n : ℕ} {m : ℕ} (hnm : n ≤ m) (next : (n : ℕ) → C n → C (n + 1)) (Hnext : ∀ (n : ℕ), function.injective (next n)) : function.injective (le_rec_on hnm next) := sorry

theorem le_rec_on_surjective {C : ℕ → Sort u} {n : ℕ} {m : ℕ} (hnm : n ≤ m) (next : (n : ℕ) → C n → C (n + 1)) (Hnext : ∀ (n : ℕ), function.surjective (next n)) : function.surjective (le_rec_on hnm next) := sorry

/-- Recursion principle based on `<`. -/
protected def strong_rec' {p : ℕ → Sort u} (H : (n : ℕ) → ((m : ℕ) → m < n → p m) → p n) (n : ℕ) : p n :=
  sorry

/-- Recursion principle based on `<` applied to some natural number. -/
def strong_rec_on' {P : ℕ → Sort u_1} (n : ℕ) (h : (n : ℕ) → ((m : ℕ) → m < n → P m) → P n) : P n :=
  nat.strong_rec' h n

theorem strong_rec_on_beta' {P : ℕ → Sort u_1} {h : (n : ℕ) → ((m : ℕ) → m < n → P m) → P n} {n : ℕ} : strong_rec_on' n h = h n fun (m : ℕ) (hmn : m < n) => strong_rec_on' m h := sorry

/-- Induction principle starting at a non-zero number. For maps to a `Sort*` see `le_rec_on`. -/
theorem le_induction {P : ℕ → Prop} {m : ℕ} (h0 : P m) (h1 : ∀ (n : ℕ), m ≤ n → P n → P (n + 1)) (n : ℕ) : m ≤ n → P n :=
  less_than_or_equal._oldrec h0 h1

/-- Decreasing induction: if `P (k+1)` implies `P k`, then `P n` implies `P m` for all `m ≤ n`.
Also works for functions to `Sort*`. -/
def decreasing_induction {P : ℕ → Sort u_1} (h : (n : ℕ) → P (n + 1) → P n) {m : ℕ} {n : ℕ} (mn : m ≤ n) (hP : P n) : P m :=
  le_rec_on mn (fun (k : ℕ) (ih : P k → P m) (hsk : P (k + 1)) => ih (h k hsk)) (fun (h : P m) => h) hP

@[simp] theorem decreasing_induction_self {P : ℕ → Sort u_1} (h : (n : ℕ) → P (n + 1) → P n) {n : ℕ} (nn : n ≤ n) (hP : P n) : decreasing_induction h nn hP = hP := sorry

theorem decreasing_induction_succ {P : ℕ → Sort u_1} (h : (n : ℕ) → P (n + 1) → P n) {m : ℕ} {n : ℕ} (mn : m ≤ n) (msn : m ≤ n + 1) (hP : P (n + 1)) : decreasing_induction h msn hP = decreasing_induction h mn (h n hP) := sorry

@[simp] theorem decreasing_induction_succ' {P : ℕ → Sort u_1} (h : (n : ℕ) → P (n + 1) → P n) {m : ℕ} (msm : m ≤ m + 1) (hP : P (m + 1)) : decreasing_induction h msm hP = h m hP := sorry

theorem decreasing_induction_trans {P : ℕ → Sort u_1} (h : (n : ℕ) → P (n + 1) → P n) {m : ℕ} {n : ℕ} {k : ℕ} (mn : m ≤ n) (nk : n ≤ k) (hP : P k) : decreasing_induction h (le_trans mn nk) hP = decreasing_induction h mn (decreasing_induction h nk hP) := sorry

theorem decreasing_induction_succ_left {P : ℕ → Sort u_1} (h : (n : ℕ) → P (n + 1) → P n) {m : ℕ} {n : ℕ} (smn : m + 1 ≤ n) (mn : m ≤ n) (hP : P n) : decreasing_induction h mn hP = h m (decreasing_induction h smn hP) := sorry

/-! ### `div` -/

protected theorem div_le_of_le_mul' {m : ℕ} {n : ℕ} {k : ℕ} (h : m ≤ k * n) : m / k ≤ n := sorry

protected theorem div_le_self' (m : ℕ) (n : ℕ) : m / n ≤ m := sorry

/-- A version of `nat.div_lt_self` using successors, rather than additional hypotheses. -/
theorem div_lt_self' (n : ℕ) (b : ℕ) : (n + 1) / (b + bit0 1) < n + 1 :=
  div_lt_self (succ_pos n) (succ_lt_succ (succ_pos b))

theorem le_div_iff_mul_le' {x : ℕ} {y : ℕ} {k : ℕ} (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y :=
  le_div_iff_mul_le x y k0

theorem div_lt_iff_lt_mul' {x : ℕ} {y : ℕ} {k : ℕ} (k0 : 0 < k) : x / k < y ↔ x < y * k :=
  lt_iff_lt_of_le_iff_le (le_div_iff_mul_le' k0)

protected theorem div_le_div_right {n : ℕ} {m : ℕ} (h : n ≤ m) {k : ℕ} : n / k ≤ m / k := sorry

theorem lt_of_div_lt_div {m : ℕ} {n : ℕ} {k : ℕ} (h : m / k < n / k) : m < n :=
  by_contradiction fun (h₁ : ¬m < n) => absurd h (not_lt_of_ge (nat.div_le_div_right (iff.mp not_lt h₁)))

protected theorem div_pos {a : ℕ} {b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b := sorry

protected theorem div_lt_of_lt_mul {m : ℕ} {n : ℕ} {k : ℕ} (h : m < n * k) : m / n < k :=
  lt_of_mul_lt_mul_left (lt_of_le_of_lt (trans_rel_left LessEq (le_add_left (n * (m / n)) (m % n)) (mod_add_div m n)) h)
    (zero_le n)

theorem lt_mul_of_div_lt {a : ℕ} {b : ℕ} {c : ℕ} (h : a / c < b) (w : 0 < c) : a < b * c :=
  lt_of_not_ge (not_le_of_gt h ∘ iff.mpr (le_div_iff_mul_le b a w))

protected theorem div_eq_zero_iff {a : ℕ} {b : ℕ} (hb : 0 < b) : a / b = 0 ↔ a < b := sorry

protected theorem div_eq_zero {a : ℕ} {b : ℕ} (hb : a < b) : a / b = 0 :=
  iff.mpr (nat.div_eq_zero_iff (has_le.le.trans_lt (zero_le a) hb)) hb

theorem eq_zero_of_le_div {a : ℕ} {b : ℕ} (hb : bit0 1 ≤ b) (h : a ≤ a / b) : a = 0 :=
  eq_zero_of_mul_le hb
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * a ≤ a)) (mul_comm b a)))
      (iff.mp (le_div_iff_mul_le' (lt_of_lt_of_le (of_as_true trivial) hb)) h))

theorem mul_div_le_mul_div_assoc (a : ℕ) (b : ℕ) (c : ℕ) : a * (b / c) ≤ a * b / c := sorry

theorem div_mul_div_le_div (a : ℕ) (b : ℕ) (c : ℕ) : a / c * b / a ≤ b / c := sorry

theorem eq_zero_of_le_half {a : ℕ} (h : a ≤ a / bit0 1) : a = 0 :=
  eq_zero_of_le_div (le_refl (bit0 1)) h

protected theorem eq_mul_of_div_eq_right {a : ℕ} {b : ℕ} {c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : a = b * c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b * c)) (Eq.symm H2)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b * (a / b))) (nat.mul_div_cancel' H1))) (Eq.refl a))

protected theorem div_eq_iff_eq_mul_right {a : ℕ} {b : ℕ} {c : ℕ} (H : 0 < b) (H' : b ∣ a) : a / b = c ↔ a = b * c :=
  { mp := nat.eq_mul_of_div_eq_right H', mpr := nat.div_eq_of_eq_mul_right H }

protected theorem div_eq_iff_eq_mul_left {a : ℕ} {b : ℕ} {c : ℕ} (H : 0 < b) (H' : b ∣ a) : a / b = c ↔ a = c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a / b = c ↔ a = c * b)) (mul_comm c b))) (nat.div_eq_iff_eq_mul_right H H')

protected theorem eq_mul_of_div_eq_left {a : ℕ} {b : ℕ} {c : ℕ} (H1 : b ∣ a) (H2 : a / b = c) : a = c * b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = c * b)) (mul_comm c b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b * c)) (nat.eq_mul_of_div_eq_right H1 H2))) (Eq.refl (b * c)))

protected theorem mul_div_cancel_left' {a : ℕ} {b : ℕ} (Hd : a ∣ b) : a * (b / a) = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a * (b / a) = b)) (mul_comm a (b / a))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / a * a = b)) (nat.div_mul_cancel Hd))) (Eq.refl b))

/-! ### `mod`, `dvd` -/

protected theorem div_mod_unique {n : ℕ} {k : ℕ} {m : ℕ} {d : ℕ} (h : 0 < k) : n / k = d ∧ n % k = m ↔ m + k * d = n ∧ m < k := sorry

theorem two_mul_odd_div_two {n : ℕ} (hn : n % bit0 1 = 1) : bit0 1 * (n / bit0 1) = n - 1 := sorry

theorem div_dvd_of_dvd {a : ℕ} {b : ℕ} (h : b ∣ a) : a / b ∣ a :=
  Exists.intro b (Eq.symm (nat.div_mul_cancel h))

protected theorem div_div_self {a : ℕ} {b : ℕ} : b ∣ a → 0 < a → a / (a / b) = b := sorry

theorem mod_mul_right_div_self (a : ℕ) (b : ℕ) (c : ℕ) : a % (b * c) / b = a / b % c := sorry

theorem mod_mul_left_div_self (a : ℕ) (b : ℕ) (c : ℕ) : a % (c * b) / b = a / b % c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a % (c * b) / b = a / b % c)) (mul_comm c b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a % (b * c) / b = a / b % c)) (mod_mul_right_div_self a b c)))
      (Eq.refl (a / b % c)))

@[simp] protected theorem dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 :=
  { mp := eq_one_of_dvd_one, mpr := fun (e : n = 1) => Eq.symm e ▸ dvd_refl 1 }

protected theorem dvd_add_left {k : ℕ} {m : ℕ} {n : ℕ} (h : k ∣ n) : k ∣ m + n ↔ k ∣ m :=
  iff.symm (nat.dvd_add_iff_left h)

protected theorem dvd_add_right {k : ℕ} {m : ℕ} {n : ℕ} (h : k ∣ m) : k ∣ m + n ↔ k ∣ n :=
  iff.symm (nat.dvd_add_iff_right h)

@[simp] protected theorem not_two_dvd_bit1 (n : ℕ) : ¬bit0 1 ∣ bit1 n :=
  mt (iff.mp (nat.dvd_add_right two_dvd_bit0)) (of_as_true trivial)

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp] protected theorem dvd_add_self_left {m : ℕ} {n : ℕ} : m ∣ m + n ↔ m ∣ n :=
  nat.dvd_add_right (dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp] protected theorem dvd_add_self_right {m : ℕ} {n : ℕ} : m ∣ n + m ↔ m ∣ n :=
  nat.dvd_add_left (dvd_refl m)

theorem not_dvd_of_pos_of_lt {a : ℕ} {b : ℕ} (h1 : 0 < b) (h2 : b < a) : ¬a ∣ b := sorry

protected theorem mul_dvd_mul_iff_left {a : ℕ} {b : ℕ} {c : ℕ} (ha : 0 < a) : a * b ∣ a * c ↔ b ∣ c := sorry

protected theorem mul_dvd_mul_iff_right {a : ℕ} {b : ℕ} {c : ℕ} (hc : 0 < c) : a * c ∣ b * c ↔ a ∣ b := sorry

theorem succ_div (a : ℕ) (b : ℕ) : (a + 1) / b = a / b + ite (b ∣ a + 1) 1 0 := sorry

theorem succ_div_of_dvd {a : ℕ} {b : ℕ} (hba : b ∣ a + 1) : (a + 1) / b = a / b + 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + 1) / b = a / b + 1)) (succ_div a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b + ite (b ∣ a + 1) 1 0 = a / b + 1)) (if_pos hba))) (Eq.refl (a / b + 1)))

theorem succ_div_of_not_dvd {a : ℕ} {b : ℕ} (hba : ¬b ∣ a + 1) : (a + 1) / b = a / b :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + 1) / b = a / b)) (succ_div a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a / b + ite (b ∣ a + 1) 1 0 = a / b)) (if_neg hba)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a / b + 0 = a / b)) (add_zero (a / b)))) (Eq.refl (a / b))))

@[simp] theorem mod_mod_of_dvd (n : ℕ) {m : ℕ} {k : ℕ} (h : m ∣ k) : n % k % m = n % m := sorry

@[simp] theorem mod_mod (a : ℕ) (n : ℕ) : a % n % n = a % n := sorry

/--  If `a` and `b` are equal mod `c`, `a - b` is zero mod `c`. -/
theorem sub_mod_eq_zero_of_mod_eq {a : ℕ} {b : ℕ} {c : ℕ} (h : a % c = b % c) : (a - b) % c = 0 := sorry

@[simp] theorem one_mod (n : ℕ) : 1 % (n + bit0 1) = 1 :=
  mod_eq_of_lt (add_lt_add_right (succ_pos n) 1)

theorem dvd_sub_mod {n : ℕ} (k : ℕ) : n ∣ k - k % n :=
  Exists.intro (k / n) (nat.sub_eq_of_eq_add (Eq.symm (mod_add_div k n)))

@[simp] theorem mod_add_mod (m : ℕ) (n : ℕ) (k : ℕ) : (m % n + k) % n = (m + k) % n := sorry

@[simp] theorem add_mod_mod (m : ℕ) (n : ℕ) (k : ℕ) : (m + n % k) % k = (m + n) % k :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((m + n % k) % k = (m + n) % k)) (add_comm m (n % k))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((n % k + m) % k = (m + n) % k)) (mod_add_mod n k m)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((n + m) % k = (m + n) % k)) (add_comm n m))) (Eq.refl ((m + n) % k))))

theorem add_mod (a : ℕ) (b : ℕ) (n : ℕ) : (a + b) % n = (a % n + b % n) % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % n = (a % n + b % n) % n)) (add_mod_mod (a % n) b n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((a + b) % n = (a % n + b) % n)) (mod_add_mod a n b))) (Eq.refl ((a + b) % n)))

theorem add_mod_eq_add_mod_right {m : ℕ} {n : ℕ} {k : ℕ} (i : ℕ) (H : m % n = k % n) : (m + i) % n = (k + i) % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((m + i) % n = (k + i) % n)) (Eq.symm (mod_add_mod m n i))))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((m % n + i) % n = (k + i) % n)) (Eq.symm (mod_add_mod k n i))))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((m % n + i) % n = (k % n + i) % n)) H)) (Eq.refl ((k % n + i) % n))))

theorem add_mod_eq_add_mod_left {m : ℕ} {n : ℕ} {k : ℕ} (i : ℕ) (H : m % n = k % n) : (i + m) % n = (i + k) % n :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((i + m) % n = (i + k) % n)) (add_comm i m)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((m + i) % n = (i + k) % n)) (add_mod_eq_add_mod_right i H)))
      (eq.mpr (id (Eq._oldrec (Eq.refl ((k + i) % n = (i + k) % n)) (add_comm k i))) (Eq.refl ((i + k) % n))))

theorem mul_mod (a : ℕ) (b : ℕ) (n : ℕ) : a * b % n = a % n * (b % n) % n := sorry

theorem dvd_div_of_mul_dvd {a : ℕ} {b : ℕ} {c : ℕ} (h : a * b ∣ c) : b ∣ c / a := sorry

theorem mul_dvd_of_dvd_div {a : ℕ} {b : ℕ} {c : ℕ} (hab : c ∣ b) (h : a ∣ b / c) : c * a ∣ b := sorry

theorem div_mul_div {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (hab : b ∣ a) (hcd : d ∣ c) : a / b * (c / d) = a * c / (b * d) := sorry

@[simp] theorem div_div_div_eq_div {a : ℕ} {b : ℕ} {c : ℕ} (dvd : b ∣ a) (dvd2 : a ∣ c) : c / (a / b) / b = c / a := sorry

theorem eq_of_dvd_of_div_eq_one {a : ℕ} {b : ℕ} (w : a ∣ b) (h : b / a = 1) : a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (Eq.symm (nat.div_mul_cancel w))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a = b / a * a)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a = 1 * a)) (one_mul a))) (Eq.refl a)))

theorem eq_zero_of_dvd_of_div_eq_zero {a : ℕ} {b : ℕ} (w : a ∣ b) (h : b / a = 0) : b = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (b = 0)) (Eq.symm (nat.div_mul_cancel w))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b / a * a = 0)) h))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 * a = 0)) (zero_mul a))) (Eq.refl 0)))

/-- If a small natural number is divisible by a larger natural number,
the small number is zero. -/
theorem eq_zero_of_dvd_of_lt {a : ℕ} {b : ℕ} (w : a ∣ b) (h : b < a) : b = 0 :=
  eq_zero_of_dvd_of_div_eq_zero w (iff.elim_right (nat.div_eq_zero_iff (lt_of_le_of_lt (zero_le b) h)) h)

theorem div_le_div_left {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : c ≤ b) (h₂ : 0 < c) : a / b ≤ a / c :=
  iff.mpr (le_div_iff_mul_le (a / b) a h₂) (le_trans (mul_le_mul_left (a / b) h₁) (div_mul_le_self a b))

theorem div_eq_self {a : ℕ} {b : ℕ} : a / b = a ↔ a = 0 ∨ b = 1 := sorry

/-! ### `pow` -/

-- This is redundant with `canonically_ordered_semiring.pow_le_pow_of_le_left`,

-- but `canonically_ordered_semiring` is not such an obvious abstraction, and also quite long.

-- So, we leave a version in the `nat` namespace as well.

-- (The global `pow_le_pow_of_le_left` needs an extra hypothesis `0 ≤ x`.)

protected theorem pow_le_pow_of_le_left {x : ℕ} {y : ℕ} (H : x ≤ y) (i : ℕ) : x ^ i ≤ y ^ i :=
  canonically_ordered_semiring.pow_le_pow_of_le_left H

theorem pow_le_pow_of_le_right {x : ℕ} (H : x > 0) {i : ℕ} {j : ℕ} : i ≤ j → x ^ i ≤ x ^ j := sorry

theorem pow_lt_pow_of_lt_left {x : ℕ} {y : ℕ} (H : x < y) {i : ℕ} (h : 0 < i) : x ^ i < y ^ i := sorry

theorem pow_lt_pow_of_lt_right {x : ℕ} (H : x > 1) {i : ℕ} {j : ℕ} (h : i < j) : x ^ i < x ^ j := sorry

-- TODO: Generalize?

theorem pow_lt_pow_succ {p : ℕ} (h : 1 < p) (n : ℕ) : p ^ n < p ^ (n + 1) := sorry

theorem lt_pow_self {p : ℕ} (h : 1 < p) (n : ℕ) : n < p ^ n := sorry

theorem lt_two_pow (n : ℕ) : n < bit0 1 ^ n :=
  lt_pow_self (of_as_true trivial) n

theorem one_le_pow (n : ℕ) (m : ℕ) (h : 0 < m) : 1 ≤ m ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ m ^ n)) (Eq.symm (one_pow n)))) (nat.pow_le_pow_of_le_left h n)

theorem one_le_pow' (n : ℕ) (m : ℕ) : 1 ≤ (m + 1) ^ n :=
  one_le_pow n (m + 1) (succ_pos m)

theorem one_le_two_pow (n : ℕ) : 1 ≤ bit0 1 ^ n :=
  one_le_pow n (bit0 1) (of_as_true trivial)

theorem one_lt_pow (n : ℕ) (m : ℕ) (h₀ : 0 < n) (h₁ : 1 < m) : 1 < m ^ n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 < m ^ n)) (Eq.symm (one_pow n)))) (pow_lt_pow_of_lt_left h₁ h₀)

theorem one_lt_pow' (n : ℕ) (m : ℕ) : 1 < (m + bit0 1) ^ (n + 1) :=
  one_lt_pow (n + 1) (m + bit0 1) (succ_pos n) (nat.lt_of_sub_eq_succ rfl)

theorem one_lt_two_pow (n : ℕ) (h₀ : 0 < n) : 1 < bit0 1 ^ n :=
  one_lt_pow n (bit0 1) h₀ (of_as_true trivial)

theorem one_lt_two_pow' (n : ℕ) : 1 < bit0 1 ^ (n + 1) :=
  one_lt_pow (n + 1) (bit0 1) (succ_pos n) (of_as_true trivial)

theorem pow_right_strict_mono {x : ℕ} (k : bit0 1 ≤ x) : strict_mono fun (n : ℕ) => x ^ n :=
  fun (_x _x_1 : ℕ) => pow_lt_pow_of_lt_right k

theorem pow_le_iff_le_right {x : ℕ} {m : ℕ} {n : ℕ} (k : bit0 1 ≤ x) : x ^ m ≤ x ^ n ↔ m ≤ n :=
  strict_mono.le_iff_le (pow_right_strict_mono k)

theorem pow_lt_iff_lt_right {x : ℕ} {m : ℕ} {n : ℕ} (k : bit0 1 ≤ x) : x ^ m < x ^ n ↔ m < n :=
  strict_mono.lt_iff_lt (pow_right_strict_mono k)

theorem pow_right_injective {x : ℕ} (k : bit0 1 ≤ x) : function.injective fun (n : ℕ) => x ^ n :=
  strict_mono.injective (pow_right_strict_mono k)

theorem pow_left_strict_mono {m : ℕ} (k : 1 ≤ m) : strict_mono fun (x : ℕ) => x ^ m :=
  fun (_x _x_1 : ℕ) (h : _x < _x_1) => pow_lt_pow_of_lt_left h k

end nat


theorem strict_mono.nat_pow {n : ℕ} (hn : 1 ≤ n) {f : ℕ → ℕ} (hf : strict_mono f) : strict_mono fun (m : ℕ) => f m ^ n :=
  strict_mono.comp (nat.pow_left_strict_mono hn) hf

namespace nat


theorem pow_le_iff_le_left {m : ℕ} {x : ℕ} {y : ℕ} (k : 1 ≤ m) : x ^ m ≤ y ^ m ↔ x ≤ y :=
  strict_mono.le_iff_le (pow_left_strict_mono k)

theorem pow_lt_iff_lt_left {m : ℕ} {x : ℕ} {y : ℕ} (k : 1 ≤ m) : x ^ m < y ^ m ↔ x < y :=
  strict_mono.lt_iff_lt (pow_left_strict_mono k)

theorem pow_left_injective {m : ℕ} (k : 1 ≤ m) : function.injective fun (x : ℕ) => x ^ m :=
  strict_mono.injective (pow_left_strict_mono k)

/-! ### `pow` and `mod` / `dvd` -/

theorem mod_pow_succ {b : ℕ} (b_pos : 0 < b) (w : ℕ) (m : ℕ) : m % b ^ Nat.succ w = b * (m / b % b ^ w) + m % b := sorry

theorem pow_dvd_pow_iff_pow_le_pow {k : ℕ} {l : ℕ} {x : ℕ} (w : 0 < x) : x ^ k ∣ x ^ l ↔ x ^ k ≤ x ^ l := sorry

/-- If `1 < x`, then `x^k` divides `x^l` if and only if `k` is at most `l`. -/
theorem pow_dvd_pow_iff_le_right {x : ℕ} {k : ℕ} {l : ℕ} (w : 1 < x) : x ^ k ∣ x ^ l ↔ k ≤ l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ^ k ∣ x ^ l ↔ k ≤ l)) (propext (pow_dvd_pow_iff_pow_le_pow (lt_of_succ_lt w)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ^ k ≤ x ^ l ↔ k ≤ l)) (propext (pow_le_iff_le_right w)))) (iff.refl (k ≤ l)))

theorem pow_dvd_pow_iff_le_right' {b : ℕ} {k : ℕ} {l : ℕ} : (b + bit0 1) ^ k ∣ (b + bit0 1) ^ l ↔ k ≤ l :=
  pow_dvd_pow_iff_le_right (nat.lt_of_sub_eq_succ rfl)

theorem not_pos_pow_dvd {p : ℕ} {k : ℕ} (hp : 1 < p) (hk : 1 < k) : ¬p ^ k ∣ p := sorry

theorem pow_dvd_of_le_of_pow_dvd {p : ℕ} {m : ℕ} {n : ℕ} {k : ℕ} (hmn : m ≤ n) (hdiv : p ^ n ∣ k) : p ^ m ∣ k :=
  (fun (this : p ^ m ∣ p ^ n) => dvd_trans this hdiv) (pow_dvd_pow p hmn)

theorem dvd_of_pow_dvd {p : ℕ} {k : ℕ} {m : ℕ} (hk : 1 ≤ k) (hpk : p ^ k ∣ m) : p ∣ m :=
  eq.mpr (id (Eq._oldrec (Eq.refl (p ∣ m)) (Eq.symm (pow_one p)))) (pow_dvd_of_le_of_pow_dvd hk hpk)

/-- `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)` for some `k`. -/
theorem exists_lt_and_lt_iff_not_dvd (m : ℕ) {n : ℕ} (hn : 0 < n) : (∃ (k : ℕ), n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := sorry

/-! ### `find` -/

theorem find_eq_iff {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) {m : ℕ} : nat.find h = m ↔ p m ∧ ∀ (n : ℕ), n < m → ¬p n := sorry

@[simp] theorem find_eq_zero {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) : nat.find h = 0 ↔ p 0 := sorry

@[simp] theorem find_pos {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) : 0 < nat.find h ↔ ¬p 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < nat.find h ↔ ¬p 0)) (propext pos_iff_ne_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat.find h ≠ 0 ↔ ¬p 0)) (propext not_iff_not)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (nat.find h = 0 ↔ p 0)) (propext (find_eq_zero h)))) (iff.refl (p 0))))

/-! ### `find_greatest` -/

/-- `find_greatest P b` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
protected def find_greatest (P : ℕ → Prop) [decidable_pred P] : ℕ → ℕ :=
  sorry

@[simp] theorem find_greatest_zero {P : ℕ → Prop} [decidable_pred P] : nat.find_greatest P 0 = 0 :=
  rfl

@[simp] theorem find_greatest_eq {P : ℕ → Prop} [decidable_pred P] {b : ℕ} : P b → nat.find_greatest P b = b := sorry

@[simp] theorem find_greatest_of_not {P : ℕ → Prop} [decidable_pred P] {b : ℕ} (h : ¬P (b + 1)) : nat.find_greatest P (b + 1) = nat.find_greatest P b := sorry

theorem find_greatest_eq_iff {P : ℕ → Prop} [decidable_pred P] {b : ℕ} {m : ℕ} : nat.find_greatest P b = m ↔ m ≤ b ∧ (m ≠ 0 → P m) ∧ ∀ {n : ℕ}, m < n → n ≤ b → ¬P n := sorry

theorem find_greatest_eq_zero_iff {P : ℕ → Prop} [decidable_pred P] {b : ℕ} : nat.find_greatest P b = 0 ↔ ∀ {n : ℕ}, 0 < n → n ≤ b → ¬P n := sorry

theorem find_greatest_spec {P : ℕ → Prop} [decidable_pred P] {b : ℕ} (h : ∃ (m : ℕ), m ≤ b ∧ P m) : P (nat.find_greatest P b) := sorry

theorem find_greatest_le {P : ℕ → Prop} [decidable_pred P] {b : ℕ} : nat.find_greatest P b ≤ b :=
  and.left (iff.mp find_greatest_eq_iff rfl)

theorem le_find_greatest {P : ℕ → Prop} [decidable_pred P] {b : ℕ} {m : ℕ} (hmb : m ≤ b) (hm : P m) : m ≤ nat.find_greatest P b :=
  le_of_not_lt
    fun (hlt : nat.find_greatest P b < m) => and.right (and.right (iff.mp find_greatest_eq_iff rfl)) m hlt hmb hm

theorem find_greatest_is_greatest {P : ℕ → Prop} [decidable_pred P] {b : ℕ} {k : ℕ} (hk : nat.find_greatest P b < k) (hkb : k ≤ b) : ¬P k :=
  and.right (and.right (iff.mp find_greatest_eq_iff rfl)) k hk hkb

theorem find_greatest_of_ne_zero {P : ℕ → Prop} [decidable_pred P] {b : ℕ} {m : ℕ} (h : nat.find_greatest P b = m) (h0 : m ≠ 0) : P m :=
  and.left (and.right (iff.mp find_greatest_eq_iff h)) h0

/-! ### `bodd_div2` and `bodd` -/

@[simp] theorem bodd_div2_eq (n : ℕ) : bodd_div2 n = (bodd n, div2 n) := sorry

@[simp] theorem bodd_bit0 (n : ℕ) : bodd (bit0 n) = false :=
  bodd_bit false n

@[simp] theorem bodd_bit1 (n : ℕ) : bodd (bit1 n) = tt :=
  bodd_bit tt n

@[simp] theorem div2_bit0 (n : ℕ) : div2 (bit0 n) = n :=
  div2_bit false n

@[simp] theorem div2_bit1 (n : ℕ) : div2 (bit1 n) = n :=
  div2_bit tt n

/-! ### `bit0` and `bit1` -/

protected theorem bit0_le {n : ℕ} {m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m :=
  add_le_add h h

protected theorem bit1_le {n : ℕ} {m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
  succ_le_succ (add_le_add h h)

theorem bit_le (b : Bool) {n : ℕ} {m : ℕ} : n ≤ m → bit b n ≤ bit b m :=
  fun (ᾰ : n ≤ m) => bool.cases_on b (idRhs (bit0 n ≤ bit0 m) (nat.bit0_le ᾰ)) (idRhs (bit1 n ≤ bit1 m) (nat.bit1_le ᾰ))

theorem bit_ne_zero (b : Bool) {n : ℕ} (h : n ≠ 0) : bit b n ≠ 0 :=
  bool.cases_on b (nat.bit0_ne_zero h) (nat.bit1_ne_zero n)

theorem bit0_le_bit (b : Bool) {m : ℕ} {n : ℕ} : m ≤ n → bit0 m ≤ bit b n :=
  fun (ᾰ : m ≤ n) =>
    bool.cases_on b (idRhs (bit0 m ≤ bit0 n) (nat.bit0_le ᾰ)) (idRhs (bit0 m ≤ bit tt n) (le_of_lt (nat.bit0_lt_bit1 ᾰ)))

theorem bit_le_bit1 (b : Bool) {m : ℕ} {n : ℕ} : m ≤ n → bit b m ≤ bit1 n :=
  fun (ᾰ : m ≤ n) =>
    bool.cases_on b (idRhs (bit false m ≤ bit1 n) (le_of_lt (nat.bit0_lt_bit1 ᾰ)))
      (idRhs (bit1 m ≤ bit1 n) (nat.bit1_le ᾰ))

theorem bit_lt_bit0 (b : Bool) {n : ℕ} {m : ℕ} : n < m → bit b n < bit0 m :=
  fun (ᾰ : n < m) =>
    bool.cases_on b (idRhs (bit0 n < bit0 m) (nat.bit0_lt ᾰ)) (idRhs (bit1 n < bit0 m) (nat.bit1_lt_bit0 ᾰ))

theorem bit_lt_bit (a : Bool) (b : Bool) {n : ℕ} {m : ℕ} (h : n < m) : bit a n < bit b m :=
  lt_of_lt_of_le (bit_lt_bit0 a h) (bit0_le_bit b (le_refl m))

@[simp] theorem bit0_le_bit1_iff {n : ℕ} {k : ℕ} : bit0 k ≤ bit1 n ↔ k ≤ n := sorry

@[simp] theorem bit0_lt_bit1_iff {n : ℕ} {k : ℕ} : bit0 k < bit1 n ↔ k ≤ n :=
  { mp := fun (h : bit0 k < bit1 n) => iff.mp bit0_le_bit1_iff (le_of_lt h), mpr := nat.bit0_lt_bit1 }

@[simp] theorem bit1_le_bit0_iff {n : ℕ} {k : ℕ} : bit1 k ≤ bit0 n ↔ k < n := sorry

@[simp] theorem bit1_lt_bit0_iff {n : ℕ} {k : ℕ} : bit1 k < bit0 n ↔ k < n :=
  { mp := fun (h : bit1 k < bit0 n) => iff.mp bit1_le_bit0_iff (le_of_lt h), mpr := nat.bit1_lt_bit0 }

@[simp] theorem one_le_bit0_iff {n : ℕ} : 1 ≤ bit0 n ↔ 0 < n := sorry

@[simp] theorem one_lt_bit0_iff {n : ℕ} : 1 < bit0 n ↔ 1 ≤ n := sorry

@[simp] theorem bit_le_bit_iff {n : ℕ} {k : ℕ} {b : Bool} : bit b k ≤ bit b n ↔ k ≤ n :=
  bool.cases_on b (idRhs (bit0 k ≤ bit0 n ↔ k ≤ n) bit0_le_bit0) (idRhs (bit1 k ≤ bit1 n ↔ k ≤ n) bit1_le_bit1)

@[simp] theorem bit_lt_bit_iff {n : ℕ} {k : ℕ} {b : Bool} : bit b k < bit b n ↔ k < n :=
  bool.cases_on b (idRhs (bit0 k < bit0 n ↔ k < n) bit0_lt_bit0) (idRhs (bit1 k < bit1 n ↔ k < n) bit1_lt_bit1)

@[simp] theorem bit_le_bit1_iff {n : ℕ} {k : ℕ} {b : Bool} : bit b k ≤ bit1 n ↔ k ≤ n :=
  bool.cases_on b (idRhs (bit0 k ≤ bit1 n ↔ k ≤ n) bit0_le_bit1_iff) (idRhs (bit1 k ≤ bit1 n ↔ k ≤ n) bit1_le_bit1)

@[simp] theorem bit0_mod_two {n : ℕ} : bit0 n % bit0 1 = 0 := sorry

@[simp] theorem bit1_mod_two {n : ℕ} : bit1 n % bit0 1 = 1 := sorry

theorem pos_of_bit0_pos {n : ℕ} (h : 0 < bit0 n) : 0 < n := sorry

/-- Define a function on `ℕ` depending on parity of the argument. -/
def bit_cases {C : ℕ → Sort u} (H : (b : Bool) → (n : ℕ) → C (bit b n)) (n : ℕ) : C n :=
  eq.rec_on (bit_decomp n) (H (bodd n) (div2 n))

/-! ### `shiftl` and `shiftr` -/

theorem shiftl_eq_mul_pow (m : ℕ) (n : ℕ) : shiftl m n = m * bit0 1 ^ n := sorry

theorem shiftl'_tt_eq_mul_pow (m : ℕ) (n : ℕ) : shiftl' tt m n + 1 = (m + 1) * bit0 1 ^ n := sorry

theorem one_shiftl (n : ℕ) : shiftl 1 n = bit0 1 ^ n :=
  Eq.trans (shiftl_eq_mul_pow 1 n) (nat.one_mul (bit0 1 ^ n))

@[simp] theorem zero_shiftl (n : ℕ) : shiftl 0 n = 0 :=
  Eq.trans (shiftl_eq_mul_pow 0 n) (nat.zero_mul (bit0 1 ^ n))

theorem shiftr_eq_div_pow (m : ℕ) (n : ℕ) : shiftr m n = m / bit0 1 ^ n := sorry

@[simp] theorem zero_shiftr (n : ℕ) : shiftr 0 n = 0 :=
  Eq.trans (shiftr_eq_div_pow 0 n) (nat.zero_div (bit0 1 ^ n))

theorem shiftl'_ne_zero_left (b : Bool) {m : ℕ} (h : m ≠ 0) (n : ℕ) : shiftl' b m n ≠ 0 := sorry

theorem shiftl'_tt_ne_zero (m : ℕ) {n : ℕ} (h : n ≠ 0) : shiftl' tt m n ≠ 0 :=
  nat.cases_on n (fun (h : 0 ≠ 0) => idRhs (shiftl' tt m 0 ≠ 0) (absurd rfl h))
    (fun (n : ℕ) (h : Nat.succ n ≠ 0) => idRhs (bit1 (shiftl' tt m n) ≠ 0) (nat.bit1_ne_zero (shiftl' tt m n))) h

/-! ### `size` -/

@[simp] theorem size_zero : size 0 = 0 :=
  rfl

@[simp] theorem size_bit {b : Bool} {n : ℕ} (h : bit b n ≠ 0) : size (bit b n) = Nat.succ (size n) := sorry

@[simp] theorem size_bit0 {n : ℕ} (h : n ≠ 0) : size (bit0 n) = Nat.succ (size n) :=
  size_bit (nat.bit0_ne_zero h)

@[simp] theorem size_bit1 (n : ℕ) : size (bit1 n) = Nat.succ (size n) :=
  size_bit (nat.bit1_ne_zero n)

@[simp] theorem size_one : size 1 = 1 :=
  size_bit1 0

@[simp] theorem size_shiftl' {b : Bool} {m : ℕ} {n : ℕ} (h : shiftl' b m n ≠ 0) : size (shiftl' b m n) = size m + n := sorry

@[simp] theorem size_shiftl {m : ℕ} (h : m ≠ 0) (n : ℕ) : size (shiftl m n) = size m + n :=
  size_shiftl' (shiftl'_ne_zero_left false h n)

theorem lt_size_self (n : ℕ) : n < bit0 1 ^ size n := sorry

theorem size_le {m : ℕ} {n : ℕ} : size m ≤ n ↔ m < bit0 1 ^ n := sorry

theorem lt_size {m : ℕ} {n : ℕ} : m < size n ↔ bit0 1 ^ m ≤ n := sorry

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < size n ↔ 0 < n)) (propext lt_size))) (iff.refl (bit0 1 ^ 0 ≤ n))

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 := sorry

theorem size_pow {n : ℕ} : size (bit0 1 ^ n) = n + 1 :=
  le_antisymm (iff.mpr size_le (pow_lt_pow_of_lt_right (of_as_true trivial) (lt_succ_self n)))
    (iff.mpr lt_size (le_refl (bit0 1 ^ n)))

theorem size_le_size {m : ℕ} {n : ℕ} (h : m ≤ n) : size m ≤ size n :=
  iff.mpr size_le (lt_of_le_of_lt h (lt_size_self n))

/-! ### decidability of predicates -/

protected instance decidable_ball_lt (n : ℕ) (P : (k : ℕ) → k < n → Prop) [H : (n_1 : ℕ) → (h : n_1 < n) → Decidable (P n_1 h)] : Decidable (∀ (n_1 : ℕ) (h : n_1 < n), P n_1 h) :=
  Nat.rec (fun (P : (k : ℕ) → k < 0 → Prop) (H : (n : ℕ) → (h : n < 0) → Decidable (P n h)) => is_true sorry)
    (fun (n : ℕ)
      (IH :
      (P : (k : ℕ) → k < n → Prop) →
        [H : (n_1 : ℕ) → (h : n_1 < n) → Decidable (P n_1 h)] → Decidable (∀ (n_1 : ℕ) (h : n_1 < n), P n_1 h))
      (P : (k : ℕ) → k < Nat.succ n → Prop) (H : (n_1 : ℕ) → (h : n_1 < Nat.succ n) → Decidable (P n_1 h)) =>
      decidable.cases_on (IH fun (k : ℕ) (h : k < n) => P k (lt_succ_of_lt h))
        (fun (h : ¬∀ (n_1 : ℕ) (h : n_1 < n), (fun (k : ℕ) (h : k < n) => P k (lt_succ_of_lt h)) n_1 h) => isFalse sorry)
        fun (h : ∀ (n_1 : ℕ) (h : n_1 < n), (fun (k : ℕ) (h : k < n) => P k (lt_succ_of_lt h)) n_1 h) =>
          dite (P n (lt_succ_self n)) (fun (p : P n (lt_succ_self n)) => is_true sorry)
            fun (p : ¬P n (lt_succ_self n)) => isFalse sorry)
    n P

protected instance decidable_forall_fin {n : ℕ} (P : fin n → Prop) [H : decidable_pred P] : Decidable (∀ (i : fin n), P i) :=
  decidable_of_iff (∀ (k : ℕ) (h : k < n), P { val := k, property := h }) sorry

protected instance decidable_ball_le (n : ℕ) (P : (k : ℕ) → k ≤ n → Prop) [H : (n_1 : ℕ) → (h : n_1 ≤ n) → Decidable (P n_1 h)] : Decidable (∀ (n_1 : ℕ) (h : n_1 ≤ n), P n_1 h) :=
  decidable_of_iff (∀ (k : ℕ) (h : k < Nat.succ n), P k (le_of_lt_succ h)) sorry

protected instance decidable_lo_hi (lo : ℕ) (hi : ℕ) (P : ℕ → Prop) [H : decidable_pred P] : Decidable (∀ (x : ℕ), lo ≤ x → x < hi → P x) :=
  decidable_of_iff (∀ (x : ℕ), x < hi - lo → P (lo + x)) sorry

protected instance decidable_lo_hi_le (lo : ℕ) (hi : ℕ) (P : ℕ → Prop) [H : decidable_pred P] : Decidable (∀ (x : ℕ), lo ≤ x → x ≤ hi → P x) :=
  decidable_of_iff (∀ (x : ℕ), lo ≤ x → x < hi + 1 → P x) sorry

protected instance decidable_exists_lt {P : ℕ → Prop} [h : decidable_pred P] : decidable_pred fun (n : ℕ) => ∃ (m : ℕ), m < n ∧ P m :=
  sorry

/-! ### find -/

theorem find_le {p : ℕ → Prop} {q : ℕ → Prop} [decidable_pred p] [decidable_pred q] (h : ∀ (n : ℕ), q n → p n) (hp : ∃ (n : ℕ), p n) (hq : ∃ (n : ℕ), q n) : nat.find hp ≤ nat.find hq :=
  nat.find_min' hp (h (nat.find hq) (nat.find_spec hq))

