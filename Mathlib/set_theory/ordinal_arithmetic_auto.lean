/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.set_theory.ordinal
import PostPort

universes u_1 u_2 u u_3 v 

namespace Mathlib

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limit_rec_on`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We also define the power function and the logarithm function on ordinals, and discuss the properties
of casts of natural numbers of and of `omega` with respect to these operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `is_limit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limit_rec_on` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.

* `is_normal`: a function `f : ordinal → ordinal` satisfies `is_normal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `nfp f a`: the next fixed point of a function `f` on ordinals, above `a`. It behaves well
  for normal functions.

* `CNF b o` is the Cantor normal form of the ordinal `o` in base `b`.

* `sup`: the supremum of an indexed family of ordinals in `Type u`, as an ordinal in `Type u`.
* `bsup`: the supremum of a set of ordinals indexed by ordinals less than a given ordinal `o`.
-/

namespace ordinal


/-! ### Further properties of addition on ordinals -/

@[simp] theorem lift_add (a : ordinal) (b : ordinal) : lift (a + b) = lift a + lift b := sorry

@[simp] theorem lift_succ (a : ordinal) : lift (succ a) = succ (lift a) := sorry

theorem add_le_add_iff_left (a : ordinal) {b : ordinal} {c : ordinal} : a + b ≤ a + c ↔ b ≤ c := sorry

theorem add_succ (o₁ : ordinal) (o₂ : ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  Eq.symm (add_assoc o₁ o₂ 1)

@[simp] theorem succ_zero : succ 0 = 1 :=
  zero_add 1

theorem one_le_iff_pos {o : ordinal} : 1 ≤ o ↔ 0 < o :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ o ↔ 0 < o)) (Eq.symm succ_zero)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (succ 0 ≤ o ↔ 0 < o)) (propext succ_le))) (iff.refl (0 < o)))

theorem one_le_iff_ne_zero {o : ordinal} : 1 ≤ o ↔ o ≠ 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ o ↔ o ≠ 0)) (propext one_le_iff_pos)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (0 < o ↔ o ≠ 0)) (propext ordinal.pos_iff_ne_zero))) (iff.refl (o ≠ 0)))

theorem succ_pos (o : ordinal) : 0 < succ o :=
  lt_of_le_of_lt (ordinal.zero_le o) (lt_succ_self o)

theorem succ_ne_zero (o : ordinal) : succ o ≠ 0 :=
  ne_of_gt (succ_pos o)

@[simp] theorem card_succ (o : ordinal) : card (succ o) = card o + 1 := sorry

theorem nat_cast_succ (n : ℕ) : succ ↑n = ↑(Nat.succ n) :=
  rfl

theorem add_left_cancel (a : ordinal) {b : ordinal} {c : ordinal} : a + b = a + c ↔ b = c := sorry

theorem lt_succ {a : ordinal} {b : ordinal} : a < succ b ↔ a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < succ b ↔ a ≤ b)) (Eq.symm (propext not_le))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (¬succ b ≤ a ↔ a ≤ b)) (propext succ_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (¬b < a ↔ a ≤ b)) (propext not_lt))) (iff.refl (a ≤ b))))

theorem add_lt_add_iff_left (a : ordinal) {b : ordinal} {c : ordinal} : a + b < a + c ↔ b < c := sorry

theorem lt_of_add_lt_add_right {a : ordinal} {b : ordinal} {c : ordinal} : a + b < c + b → a < c :=
  lt_imp_lt_of_le_imp_le fun (h : c ≤ a) => add_le_add_right h b

@[simp] theorem succ_lt_succ {a : ordinal} {b : ordinal} : succ a < succ b ↔ a < b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (succ a < succ b ↔ a < b)) (propext lt_succ)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (succ a ≤ b ↔ a < b)) (propext succ_le))) (iff.refl (a < b)))

@[simp] theorem succ_le_succ {a : ordinal} {b : ordinal} : succ a ≤ succ b ↔ a ≤ b :=
  iff.mpr le_iff_le_iff_lt_iff_lt succ_lt_succ

theorem succ_inj {a : ordinal} {b : ordinal} : succ a = succ b ↔ a = b := sorry

theorem add_le_add_iff_right {a : ordinal} {b : ordinal} (n : ℕ) : a + ↑n ≤ b + ↑n ↔ a ≤ b := sorry

theorem add_right_cancel {a : ordinal} {b : ordinal} (n : ℕ) : a + ↑n = b + ↑n ↔ a = b := sorry

/-! ### The zero ordinal -/

@[simp] theorem card_eq_zero {o : ordinal} : card o = 0 ↔ o = 0 := sorry

theorem type_ne_zero_iff_nonempty {α : Type u_1} {r : α → α → Prop} [is_well_order α r] : type r ≠ 0 ↔ Nonempty α :=
  iff.trans (iff.symm (not_congr card_eq_zero)) cardinal.ne_zero_iff_nonempty

@[simp] theorem type_eq_zero_iff_empty {α : Type u_1} {r : α → α → Prop} [is_well_order α r] : type r = 0 ↔ ¬Nonempty α :=
  iff.symm (iff.mp not_iff_comm type_ne_zero_iff_nonempty)

protected theorem one_ne_zero : 1 ≠ 0 :=
  iff.mpr type_ne_zero_iff_nonempty (Nonempty.intro PUnit.unit)

protected instance nontrivial : nontrivial ordinal :=
  nontrivial.mk (Exists.intro 1 (Exists.intro 0 ordinal.one_ne_zero))

theorem zero_lt_one : 0 < 1 :=
  iff.mpr lt_iff_le_and_ne { left := ordinal.zero_le 1, right := ne.symm ordinal.one_ne_zero }

/-! ### The predecessor of an ordinal -/

/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : ordinal) : ordinal :=
  dite (∃ (a : ordinal), o = succ a) (fun (h : ∃ (a : ordinal), o = succ a) => classical.some h)
    fun (h : ¬∃ (a : ordinal), o = succ a) => o

@[simp] theorem pred_succ (o : ordinal) : pred (succ o) = o := sorry

theorem pred_le_self (o : ordinal) : pred o ≤ o := sorry

theorem pred_eq_iff_not_succ {o : ordinal} : pred o = o ↔ ¬∃ (a : ordinal), o = succ a := sorry

theorem pred_lt_iff_is_succ {o : ordinal} : pred o < o ↔ ∃ (a : ordinal), o = succ a := sorry

theorem succ_pred_iff_is_succ {o : ordinal} : succ (pred o) = o ↔ ∃ (a : ordinal), o = succ a := sorry

theorem succ_lt_of_not_succ {o : ordinal} (h : ¬∃ (a : ordinal), o = succ a) {b : ordinal} : succ b < o ↔ b < o :=
  { mp := lt_trans (lt_succ_self b),
    mpr := fun (l : b < o) => lt_of_le_of_ne (iff.mpr succ_le l) fun (e : succ b = o) => h (Exists.intro b (Eq.symm e)) }

theorem lt_pred {a : ordinal} {b : ordinal} : a < pred b ↔ succ a < b := sorry

theorem pred_le {a : ordinal} {b : ordinal} : pred a ≤ b ↔ a ≤ succ b :=
  iff.mpr le_iff_le_iff_lt_iff_lt lt_pred

@[simp] theorem lift_is_succ {o : ordinal} : (∃ (a : ordinal), lift o = succ a) ↔ ∃ (a : ordinal), o = succ a := sorry

@[simp] theorem lift_pred (o : ordinal) : lift (pred o) = pred (lift o) := sorry

/-! ### Limit ordinals -/

/-- A limit ordinal is an ordinal which is not zero and not a successor. -/
def is_limit (o : ordinal)  :=
  o ≠ 0 ∧ ∀ (a : ordinal), a < o → succ a < o

theorem not_zero_is_limit : ¬is_limit 0 :=
  fun (ᾰ : is_limit 0) =>
    and.dcases_on ᾰ fun (ᾰ_left : 0 ≠ 0) (ᾰ_right : ∀ (a : ordinal), a < 0 → succ a < 0) => idRhs False (ᾰ_left rfl)

theorem not_succ_is_limit (o : ordinal) : ¬is_limit (succ o) := sorry

theorem not_succ_of_is_limit {o : ordinal} (h : is_limit o) : ¬∃ (a : ordinal), o = succ a :=
  fun (ᾰ : ∃ (a : ordinal), o = succ a) =>
    Exists.dcases_on ᾰ fun (ᾰ_w : ordinal) (ᾰ_h : o = succ ᾰ_w) => idRhs False (not_succ_is_limit ᾰ_w (ᾰ_h ▸ h))

theorem succ_lt_of_is_limit {o : ordinal} (h : is_limit o) {a : ordinal} : succ a < o ↔ a < o :=
  { mp := lt_trans (lt_succ_self a), mpr := and.right h a }

theorem le_succ_of_is_limit {o : ordinal} (h : is_limit o) {a : ordinal} : o ≤ succ a ↔ o ≤ a :=
  iff.mpr le_iff_le_iff_lt_iff_lt (succ_lt_of_is_limit h)

theorem limit_le {o : ordinal} (h : is_limit o) {a : ordinal} : o ≤ a ↔ ∀ (x : ordinal), x < o → x ≤ a := sorry

theorem lt_limit {o : ordinal} (h : is_limit o) {a : ordinal} : a < o ↔ ∃ (x : ordinal), ∃ (H : x < o), a < x := sorry

@[simp] theorem lift_is_limit (o : ordinal) : is_limit (lift o) ↔ is_limit o := sorry

theorem is_limit.pos {o : ordinal} (h : is_limit o) : 0 < o :=
  lt_of_le_of_ne (ordinal.zero_le o) (ne.symm (and.left h))

theorem is_limit.one_lt {o : ordinal} (h : is_limit o) : 1 < o := sorry

theorem is_limit.nat_lt {o : ordinal} (h : is_limit o) (n : ℕ) : ↑n < o := sorry

theorem zero_or_succ_or_limit (o : ordinal) : o = 0 ∨ (∃ (a : ordinal), o = succ a) ∨ is_limit o := sorry

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
def limit_rec_on {C : ordinal → Sort u_2} (o : ordinal) (H₁ : C 0) (H₂ : (o : ordinal) → C o → C (succ o)) (H₃ : (o : ordinal) → is_limit o → ((o' : ordinal) → o' < o → C o') → C o) : C o :=
  well_founded.fix wf
    (fun (o : ordinal) (IH : (y : ordinal) → y < o → C y) =>
      dite (o = 0) (fun (o0 : o = 0) => eq.mpr sorry H₁)
        fun (o0 : ¬o = 0) =>
          dite (∃ (a : ordinal), o = succ a)
            (fun (h : ∃ (a : ordinal), o = succ a) => eq.mpr sorry (H₂ (pred o) (IH (pred o) sorry)))
            fun (h : ¬∃ (a : ordinal), o = succ a) => H₃ o sorry IH)
    o

@[simp] theorem limit_rec_on_zero {C : ordinal → Sort u_2} (H₁ : C 0) (H₂ : (o : ordinal) → C o → C (succ o)) (H₃ : (o : ordinal) → is_limit o → ((o' : ordinal) → o' < o → C o') → C o) : limit_rec_on 0 H₁ H₂ H₃ = H₁ := sorry

@[simp] theorem limit_rec_on_succ {C : ordinal → Sort u_2} (o : ordinal) (H₁ : C 0) (H₂ : (o : ordinal) → C o → C (succ o)) (H₃ : (o : ordinal) → is_limit o → ((o' : ordinal) → o' < o → C o') → C o) : limit_rec_on (succ o) H₁ H₂ H₃ = H₂ o (limit_rec_on o H₁ H₂ H₃) := sorry

@[simp] theorem limit_rec_on_limit {C : ordinal → Sort u_2} (o : ordinal) (H₁ : C 0) (H₂ : (o : ordinal) → C o → C (succ o)) (H₃ : (o : ordinal) → is_limit o → ((o' : ordinal) → o' < o → C o') → C o) (h : is_limit o) : limit_rec_on o H₁ H₂ H₃ = H₃ o h fun (x : ordinal) (h : x < o) => limit_rec_on x H₁ H₂ H₃ := sorry

theorem has_succ_of_is_limit {α : Type u_1} {r : α → α → Prop} [wo : is_well_order α r] (h : is_limit (type r)) (x : α) : ∃ (y : α), r x y := sorry

theorem type_subrel_lt (o : ordinal) : type (subrel Less (set_of fun (o' : ordinal) => o' < o)) = lift o := sorry

theorem mk_initial_seg (o : ordinal) : cardinal.mk ↥(set_of fun (o' : ordinal) => o' < o) = cardinal.lift (card o) := sorry

/-! ### Normal ordinal functions -/

/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.  -/
def is_normal (f : ordinal → ordinal)  :=
  (∀ (o : ordinal), f o < f (succ o)) ∧
    ∀ (o : ordinal), is_limit o → ∀ (a : ordinal), f o ≤ a ↔ ∀ (b : ordinal), b < o → f b ≤ a

theorem is_normal.limit_le {f : ordinal → ordinal} (H : is_normal f) {o : ordinal} : is_limit o → ∀ {a : ordinal}, f o ≤ a ↔ ∀ (b : ordinal), b < o → f b ≤ a :=
  and.right H

theorem is_normal.limit_lt {f : ordinal → ordinal} (H : is_normal f) {o : ordinal} (h : is_limit o) {a : ordinal} : a < f o ↔ ∃ (b : ordinal), ∃ (H : b < o), a < f b := sorry

theorem is_normal.lt_iff {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} : f a < f b ↔ a < b := sorry

theorem is_normal.le_iff {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} : f a ≤ f b ↔ a ≤ b :=
  iff.mpr le_iff_le_iff_lt_iff_lt (is_normal.lt_iff H)

theorem is_normal.inj {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} : f a = f b ↔ a = b := sorry

theorem is_normal.le_self {f : ordinal → ordinal} (H : is_normal f) (a : ordinal) : a ≤ f a := sorry

theorem is_normal.le_set {f : ordinal → ordinal} (H : is_normal f) (p : ordinal → Prop) (p0 : ∃ (x : ordinal), p x) (S : ordinal) (H₂ : ∀ (o : ordinal), S ≤ o ↔ ∀ (a : ordinal), p a → a ≤ o) {o : ordinal} : f S ≤ o ↔ ∀ (a : ordinal), p a → f a ≤ o := sorry

theorem is_normal.le_set' {α : Type u_1} {f : ordinal → ordinal} (H : is_normal f) (p : α → Prop) (g : α → ordinal) (p0 : ∃ (x : α), p x) (S : ordinal) (H₂ : ∀ (o : ordinal), S ≤ o ↔ ∀ (a : α), p a → g a ≤ o) {o : ordinal} : f S ≤ o ↔ ∀ (a : α), p a → f (g a) ≤ o := sorry

theorem is_normal.refl : is_normal id :=
  { left := fun (x : ordinal) => lt_succ_self (id x),
    right := fun (o : ordinal) (l : is_limit o) (a : ordinal) => limit_le l }

theorem is_normal.trans {f : ordinal → ordinal} {g : ordinal → ordinal} (H₁ : is_normal f) (H₂ : is_normal g) : is_normal fun (x : ordinal) => f (g x) := sorry

theorem is_normal.is_limit {f : ordinal → ordinal} (H : is_normal f) {o : ordinal} (l : is_limit o) : is_limit (f o) := sorry

theorem add_le_of_limit {a : ordinal} {b : ordinal} {c : ordinal} (h : is_limit b) : a + b ≤ c ↔ ∀ (b' : ordinal), b' < b → a + b' ≤ c := sorry

theorem add_is_normal (a : ordinal) : is_normal (Add.add a) :=
  { left := fun (b : ordinal) => iff.mpr (add_lt_add_iff_left a) (lt_succ_self b),
    right := fun (b : ordinal) (l : is_limit b) (c : ordinal) => add_le_of_limit l }

theorem add_is_limit (a : ordinal) {b : ordinal} : is_limit b → is_limit (a + b) :=
  is_normal.is_limit (add_is_normal a)

/-! ### Subtraction on ordinals-/

/-- `a - b` is the unique ordinal satisfying
  `b + (a - b) = a` when `b ≤ a`. -/
def sub (a : ordinal) (b : ordinal) : ordinal :=
  omin (set_of fun (o : ordinal) => a ≤ b + o) sorry

protected instance has_sub : Sub ordinal :=
  { sub := sub }

theorem le_add_sub (a : ordinal) (b : ordinal) : a ≤ b + (a - b) :=
  omin_mem (set_of fun (o : ordinal) => a ≤ b + o) (sub._proof_1 a b)

theorem sub_le {a : ordinal} {b : ordinal} {c : ordinal} : a - b ≤ c ↔ a ≤ b + c :=
  { mp := fun (h : a - b ≤ c) => le_trans (le_add_sub a b) (add_le_add_left h b),
    mpr := fun (h : a ≤ b + c) => omin_le h }

theorem lt_sub {a : ordinal} {b : ordinal} {c : ordinal} : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a : ordinal) (b : ordinal) : a + b - a = b :=
  le_antisymm (iff.mpr sub_le (le_refl (a + b))) (iff.mp (add_le_add_iff_left a) (le_add_sub (a + b) a))

theorem sub_eq_of_add_eq {a : ordinal} {b : ordinal} {c : ordinal} (h : a + b = c) : c - a = b :=
  h ▸ add_sub_cancel a b

theorem sub_le_self (a : ordinal) (b : ordinal) : a - b ≤ a :=
  iff.mpr sub_le (le_add_left a b)

theorem add_sub_cancel_of_le {a : ordinal} {b : ordinal} (h : b ≤ a) : b + (a - b) = a := sorry

@[simp] theorem sub_zero (a : ordinal) : a - 0 = a := sorry

@[simp] theorem zero_sub (a : ordinal) : 0 - a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 - a = 0)) (Eq.symm (propext ordinal.le_zero)))) (sub_le_self 0 a)

@[simp] theorem sub_self (a : ordinal) : a - a = 0 := sorry

theorem sub_eq_zero_iff_le {a : ordinal} {b : ordinal} : a - b = 0 ↔ a ≤ b := sorry

theorem sub_sub (a : ordinal) (b : ordinal) (c : ordinal) : a - b - c = a - (b + c) := sorry

theorem add_sub_add_cancel (a : ordinal) (b : ordinal) (c : ordinal) : a + b - (a + c) = b - c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b - (a + c) = b - c)) (Eq.symm (sub_sub (a + b) a c))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b - a - c = b - c)) (add_sub_cancel a b))) (Eq.refl (b - c)))

theorem sub_is_limit {a : ordinal} {b : ordinal} (l : is_limit a) (h : b < a) : is_limit (a - b) := sorry

@[simp] theorem one_add_omega : 1 + omega = omega := sorry

@[simp] theorem one_add_of_omega_le {o : ordinal} (h : omega ≤ o) : 1 + o = o := sorry

/-! ### Multiplication of ordinals-/

/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
protected instance monoid : monoid ordinal :=
  monoid.mk (fun (a b : ordinal) => quotient.lift_on₂ a b (fun (_x : Well_order) => sorry) sorry) sorry 1 sorry sorry

@[simp] theorem type_mul {α : Type u} {β : Type u} (r : α → α → Prop) (s : β → β → Prop) [is_well_order α r] [is_well_order β s] : type r * type s = type (prod.lex s r) :=
  rfl

@[simp] theorem lift_mul (a : ordinal) (b : ordinal) : lift (a * b) = lift a * lift b := sorry

@[simp] theorem card_mul (a : ordinal) (b : ordinal) : card (a * b) = card a * card b := sorry

@[simp] theorem mul_zero (a : ordinal) : a * 0 = 0 := sorry

@[simp] theorem zero_mul (a : ordinal) : 0 * a = 0 := sorry

theorem mul_add (a : ordinal) (b : ordinal) (c : ordinal) : a * (b + c) = a * b + a * c := sorry

@[simp] theorem mul_add_one (a : ordinal) (b : ordinal) : a * (b + 1) = a * b + a := sorry

@[simp] theorem mul_succ (a : ordinal) (b : ordinal) : a * succ b = a * b + a :=
  mul_add_one a b

theorem mul_le_mul_left {a : ordinal} {b : ordinal} (c : ordinal) : a ≤ b → c * a ≤ c * b := sorry

theorem mul_le_mul_right {a : ordinal} {b : ordinal} (c : ordinal) : a ≤ b → a * c ≤ b * c := sorry

theorem mul_le_mul {a : ordinal} {b : ordinal} {c : ordinal} {d : ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) : a * b ≤ c * d :=
  le_trans (mul_le_mul_left a h₂) (mul_le_mul_right d h₁)

theorem mul_le_of_limit {a : ordinal} {b : ordinal} {c : ordinal} (h : is_limit b) : a * b ≤ c ↔ ∀ (b' : ordinal), b' < b → a * b' ≤ c := sorry

theorem mul_is_normal {a : ordinal} (h : 0 < a) : is_normal (Mul.mul a) := sorry

theorem lt_mul_of_limit {a : ordinal} {b : ordinal} {c : ordinal} (h : is_limit c) : a < b * c ↔ ∃ (c' : ordinal), ∃ (H : c' < c), a < b * c' := sorry

theorem mul_lt_mul_iff_left {a : ordinal} {b : ordinal} {c : ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
  is_normal.lt_iff (mul_is_normal a0)

theorem mul_le_mul_iff_left {a : ordinal} {b : ordinal} {c : ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  is_normal.le_iff (mul_is_normal a0)

theorem mul_lt_mul_of_pos_left {a : ordinal} {b : ordinal} {c : ordinal} (h : a < b) (c0 : 0 < c) : c * a < c * b :=
  iff.mpr (mul_lt_mul_iff_left c0) h

theorem mul_pos {a : ordinal} {b : ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := sorry

theorem mul_ne_zero {a : ordinal} {b : ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := sorry

theorem le_of_mul_le_mul_left {a : ordinal} {b : ordinal} {c : ordinal} (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
  le_imp_le_of_lt_imp_lt (fun (h' : b < a) => mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_inj {a : ordinal} {b : ordinal} {c : ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  is_normal.inj (mul_is_normal a0)

theorem mul_is_limit {a : ordinal} {b : ordinal} (a0 : 0 < a) : is_limit b → is_limit (a * b) :=
  is_normal.is_limit (mul_is_normal a0)

theorem mul_is_limit_left {a : ordinal} {b : ordinal} (l : is_limit a) (b0 : 0 < b) : is_limit (a * b) := sorry

/-! ### Division on ordinals -/

protected theorem div_aux (a : ordinal) (b : ordinal) (h : b ≠ 0) : set.nonempty (set_of fun (o : ordinal) => a < b * succ o) := sorry

/-- `a / b` is the unique ordinal `o` satisfying
  `a = b * o + o'` with `o' < b`. -/
protected def div (a : ordinal) (b : ordinal) : ordinal :=
  dite (b = 0) (fun (h : b = 0) => 0)
    fun (h : ¬b = 0) => omin (set_of fun (o : ordinal) => a < b * succ o) (ordinal.div_aux a b h)

protected instance has_div : Div ordinal :=
  { div := ordinal.div }

@[simp] theorem div_zero (a : ordinal) : a / 0 = 0 :=
  dif_pos rfl

theorem div_def (a : ordinal) {b : ordinal} (h : b ≠ 0) : a / b = omin (set_of fun (o : ordinal) => a < b * succ o) (ordinal.div_aux a b h) :=
  dif_neg h

theorem lt_mul_succ_div (a : ordinal) {b : ordinal} (h : b ≠ 0) : a < b * succ (a / b) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a < b * succ (a / b))) (div_def a h)))
    (omin_mem (set_of fun (o : ordinal) => a < b * succ o) (ordinal.div_aux a b h))

theorem lt_mul_div_add (a : ordinal) {b : ordinal} (h : b ≠ 0) : a < b * (a / b) + b := sorry

theorem div_le {a : ordinal} {b : ordinal} {c : ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
  { mp := fun (h : a / b ≤ c) => lt_of_lt_of_le (lt_mul_succ_div a b0) (mul_le_mul_left b (iff.mpr succ_le_succ h)),
    mpr := fun (h : a < b * succ c) => eq.mpr (id (Eq._oldrec (Eq.refl (a / b ≤ c)) (div_def a b0))) (omin_le h) }

theorem lt_div {a : ordinal} {b : ordinal} {c : ordinal} (c0 : c ≠ 0) : a < b / c ↔ c * succ a ≤ b := sorry

theorem le_div {a : ordinal} {b : ordinal} {c : ordinal} (c0 : c ≠ 0) : a ≤ b / c ↔ c * a ≤ b := sorry

theorem div_lt {a : ordinal} {b : ordinal} {c : ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b * c :=
  lt_iff_lt_of_le_iff_le (le_div b0)

theorem div_le_of_le_mul {a : ordinal} {b : ordinal} {c : ordinal} (h : a ≤ b * c) : a / b ≤ c := sorry

theorem mul_lt_of_lt_div {a : ordinal} {b : ordinal} {c : ordinal} : a < b / c → c * a < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp] theorem zero_div (a : ordinal) : 0 / a = 0 :=
  iff.mp ordinal.le_zero (div_le_of_le_mul (ordinal.zero_le (a * 0)))

theorem mul_div_le (a : ordinal) (b : ordinal) : b * (a / b) ≤ a := sorry

theorem mul_add_div (a : ordinal) {b : ordinal} (b0 : b ≠ 0) (c : ordinal) : (b * a + c) / b = a + c / b := sorry

theorem div_eq_zero_of_lt {a : ordinal} {b : ordinal} (h : a < b) : a / b = 0 := sorry

@[simp] theorem mul_div_cancel (a : ordinal) {b : ordinal} (b0 : b ≠ 0) : b * a / b = a := sorry

@[simp] theorem div_one (a : ordinal) : a / 1 = a := sorry

@[simp] theorem div_self {a : ordinal} (h : a ≠ 0) : a / a = 1 := sorry

theorem mul_sub (a : ordinal) (b : ordinal) (c : ordinal) : a * (b - c) = a * b - a * c := sorry

theorem is_limit_add_iff {a : ordinal} {b : ordinal} : is_limit (a + b) ↔ is_limit b ∨ b = 0 ∧ is_limit a := sorry

theorem dvd_add_iff {a : ordinal} {b : ordinal} {c : ordinal} : a ∣ b → (a ∣ b + c ↔ a ∣ c) := sorry

theorem dvd_add {a : ordinal} {b : ordinal} {c : ordinal} (h₁ : a ∣ b) : a ∣ c → a ∣ b + c :=
  iff.mpr (dvd_add_iff h₁)

theorem dvd_zero (a : ordinal) : a ∣ 0 :=
  Exists.intro 0 (Eq.symm (mul_zero a))

theorem zero_dvd {a : ordinal} : 0 ∣ a ↔ a = 0 := sorry

theorem one_dvd (a : ordinal) : 1 ∣ a :=
  Exists.intro a (Eq.symm (one_mul a))

theorem div_mul_cancel {a : ordinal} {b : ordinal} : a ≠ 0 → a ∣ b → a * (b / a) = b := sorry

theorem le_of_dvd {a : ordinal} {b : ordinal} : b ≠ 0 → a ∣ b → a ≤ b := sorry

theorem dvd_antisymm {a : ordinal} {b : ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b := sorry

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
protected instance has_mod : Mod ordinal :=
  { mod := fun (a b : ordinal) => a - b * (a / b) }

theorem mod_def (a : ordinal) (b : ordinal) : a % b = a - b * (a / b) :=
  rfl

@[simp] theorem mod_zero (a : ordinal) : a % 0 = a := sorry

theorem mod_eq_of_lt {a : ordinal} {b : ordinal} (h : a < b) : a % b = a := sorry

@[simp] theorem zero_mod (b : ordinal) : 0 % b = 0 := sorry

theorem div_add_mod (a : ordinal) (b : ordinal) : b * (a / b) + a % b = a :=
  add_sub_cancel_of_le (mul_div_le a b)

theorem mod_lt (a : ordinal) {b : ordinal} (h : b ≠ 0) : a % b < b :=
  iff.mp (add_lt_add_iff_left (b * (a / b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (b * (a / b) + a % b < b * (a / b) + b)) (div_add_mod a b))) (lt_mul_div_add a h))

@[simp] theorem mod_self (a : ordinal) : a % a = 0 := sorry

@[simp] theorem mod_one (a : ordinal) : a % 1 = 0 := sorry

/-! ### Supremum of a family of ordinals -/

/-- The supremum of a family of ordinals -/
def sup {ι : Type u_1} (f : ι → ordinal) : ordinal :=
  omin (set_of fun (c : ordinal) => ∀ (i : ι), f i ≤ c) sorry

theorem le_sup {ι : Type u_1} (f : ι → ordinal) (i : ι) : f i ≤ sup f :=
  omin_mem (set_of fun (c : ordinal) => ∀ (i : ι), f i ≤ c) (sup._proof_1 f)

theorem sup_le {ι : Type u_1} {f : ι → ordinal} {a : ordinal} : sup f ≤ a ↔ ∀ (i : ι), f i ≤ a :=
  { mp := fun (h : sup f ≤ a) (i : ι) => le_trans (le_sup f i) h, mpr := fun (h : ∀ (i : ι), f i ≤ a) => omin_le h }

theorem lt_sup {ι : Type u_1} {f : ι → ordinal} {a : ordinal} : a < sup f ↔ ∃ (i : ι), a < f i := sorry

theorem is_normal.sup {f : ordinal → ordinal} (H : is_normal f) {ι : Type u_1} {g : ι → ordinal} (h : Nonempty ι) : f (sup g) = sup (f ∘ g) := sorry

theorem sup_ord {ι : Type u_1} (f : ι → cardinal) : (sup fun (i : ι) => cardinal.ord (f i)) = cardinal.ord (cardinal.sup f) := sorry

theorem sup_succ {ι : Type u_1} (f : ι → ordinal) : (sup fun (i : ι) => succ (f i)) ≤ succ (sup f) :=
  eq.mpr (id (Eq._oldrec (Eq.refl ((sup fun (i : ι) => succ (f i)) ≤ succ (sup f))) (propext sup_le)))
    fun (i : ι) => eq.mpr (id (Eq._oldrec (Eq.refl (succ (f i) ≤ succ (sup f))) (propext succ_le_succ))) (le_sup f i)

theorem unbounded_range_of_sup_ge {α : Type u} {β : Type u} (r : α → α → Prop) [is_well_order α r] (f : β → α) (h : type r ≤ sup (typein r ∘ f)) : unbounded r (set.range f) := sorry

/-- The supremum of a family of ordinals indexed by the set
  of ordinals less than some `o : ordinal.{u}`.
  (This is not a special case of `sup` over the subtype,
  because `{a // a < o} : Type (u+1)` and `sup` only works over
  families in `Type u`.) -/
def bsup (o : ordinal) : ((a : ordinal) → a < o → ordinal) → ordinal :=
  sorry

theorem bsup_le {o : ordinal} {f : (a : ordinal) → a < o → ordinal} {a : ordinal} : bsup o f ≤ a ↔ ∀ (i : ordinal) (h : i < o), f i h ≤ a := sorry

theorem bsup_type {α : Type u_1} (r : α → α → Prop) [is_well_order α r] (f : (a : ordinal) → a < type r → ordinal) : bsup (type r) f = sup fun (a : α) => f (typein r a) (typein_lt_type r a) := sorry

theorem le_bsup {o : ordinal} (f : (a : ordinal) → a < o → ordinal) (i : ordinal) (h : i < o) : f i h ≤ bsup o f :=
  iff.mp bsup_le (le_refl (bsup o f)) i h

theorem lt_bsup {o : ordinal} {f : (a : ordinal) → a < o → ordinal} (hf : ∀ {a a' : ordinal} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha') (ho : is_limit o) (i : ordinal) (h : i < o) : f i h < bsup o f :=
  lt_of_lt_of_le (hf h (and.right ho i h) (lt_succ_self i)) (le_bsup f (succ i) (and.right ho i h))

theorem bsup_id {o : ordinal} (ho : is_limit o) : (bsup o fun (x : ordinal) (_x : x < o) => x) = o := sorry

theorem is_normal.bsup {f : ordinal → ordinal} (H : is_normal f) {o : ordinal} (g : (a : ordinal) → a < o → ordinal) (h : o ≠ 0) : f (bsup o g) = bsup o fun (a : ordinal) (h : a < o) => f (g a h) := sorry

theorem is_normal.bsup_eq {f : ordinal → ordinal} (H : is_normal f) {o : ordinal} (h : is_limit o) : (bsup o fun (x : ordinal) (_x : x < o) => f x) = f o := sorry

/-! ### Ordinal exponential -/

/-- The ordinal exponential, defined by transfinite recursion. -/
def power (a : ordinal) (b : ordinal) : ordinal :=
  ite (a = 0) (1 - b) (limit_rec_on b 1 (fun (_x IH : ordinal) => IH * a) fun (b : ordinal) (_x : is_limit b) => bsup b)

protected instance has_pow : has_pow ordinal ordinal :=
  has_pow.mk power

theorem zero_power' (a : ordinal) : 0 ^ a = 1 - a := sorry

@[simp] theorem zero_power {a : ordinal} (a0 : a ≠ 0) : 0 ^ a = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 ^ a = 0)) (zero_power' a)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (1 - a = 0)) (propext sub_eq_zero_iff_le)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (1 ≤ a)) (propext one_le_iff_ne_zero))) a0))

@[simp] theorem power_zero (a : ordinal) : a ^ 0 = 1 := sorry

@[simp] theorem power_succ (a : ordinal) (b : ordinal) : a ^ succ b = a ^ b * a := sorry

theorem power_limit {a : ordinal} {b : ordinal} (a0 : a ≠ 0) (h : is_limit b) : a ^ b = bsup b fun (c : ordinal) (_x : c < b) => a ^ c := sorry

theorem power_le_of_limit {a : ordinal} {b : ordinal} {c : ordinal} (a0 : a ≠ 0) (h : is_limit b) : a ^ b ≤ c ↔ ∀ (b' : ordinal), b' < b → a ^ b' ≤ c := sorry

theorem lt_power_of_limit {a : ordinal} {b : ordinal} {c : ordinal} (b0 : b ≠ 0) (h : is_limit c) : a < b ^ c ↔ ∃ (c' : ordinal), ∃ (H : c' < c), a < b ^ c' := sorry

@[simp] theorem power_one (a : ordinal) : a ^ 1 = a := sorry

@[simp] theorem one_power (a : ordinal) : 1 ^ a = 1 := sorry

theorem power_pos {a : ordinal} (b : ordinal) (a0 : 0 < a) : 0 < a ^ b := sorry

theorem power_ne_zero {a : ordinal} (b : ordinal) (a0 : a ≠ 0) : a ^ b ≠ 0 :=
  iff.mp ordinal.pos_iff_ne_zero (power_pos b (iff.mpr ordinal.pos_iff_ne_zero a0))

theorem power_is_normal {a : ordinal} (h : 1 < a) : is_normal fun (_y : ordinal) => a ^ _y := sorry

theorem power_lt_power_iff_right {a : ordinal} {b : ordinal} {c : ordinal} (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
  is_normal.lt_iff (power_is_normal a1)

theorem power_le_power_iff_right {a : ordinal} {b : ordinal} {c : ordinal} (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
  is_normal.le_iff (power_is_normal a1)

theorem power_right_inj {a : ordinal} {b : ordinal} {c : ordinal} (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
  is_normal.inj (power_is_normal a1)

theorem power_is_limit {a : ordinal} {b : ordinal} (a1 : 1 < a) : is_limit b → is_limit (a ^ b) :=
  is_normal.is_limit (power_is_normal a1)

theorem power_is_limit_left {a : ordinal} {b : ordinal} (l : is_limit a) (hb : b ≠ 0) : is_limit (a ^ b) := sorry

theorem power_le_power_right {a : ordinal} {b : ordinal} {c : ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c := sorry

theorem power_le_power_left {a : ordinal} {b : ordinal} (c : ordinal) (ab : a ≤ b) : a ^ c ≤ b ^ c := sorry

theorem le_power_self {a : ordinal} (b : ordinal) (a1 : 1 < a) : b ≤ a ^ b :=
  is_normal.le_self (power_is_normal a1) b

theorem power_lt_power_left_of_succ {a : ordinal} {b : ordinal} {c : ordinal} (ab : a < b) : a ^ succ c < b ^ succ c := sorry

theorem power_add (a : ordinal) (b : ordinal) (c : ordinal) : a ^ (b + c) = a ^ b * a ^ c := sorry

theorem power_dvd_power (a : ordinal) {b : ordinal} {c : ordinal} (h : b ≤ c) : a ^ b ∣ a ^ c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ^ b ∣ a ^ c)) (Eq.symm (add_sub_cancel_of_le h))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ^ b ∣ a ^ (b + (c - b)))) (power_add a b (c - b))))
      (dvd_mul_right (a ^ b) (a ^ (c - b))))

theorem power_dvd_power_iff {a : ordinal} {b : ordinal} {c : ordinal} (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c := sorry

theorem power_mul (a : ordinal) (b : ordinal) (c : ordinal) : a ^ (b * c) = (a ^ b) ^ c := sorry

/-! ### Ordinal logarithm -/

/-- The ordinal logarithm is the solution `u` to the equation
  `x = b ^ u * v + w` where `v < b` and `w < b`. -/
def log (b : ordinal) (x : ordinal) : ordinal :=
  dite (1 < b) (fun (h : 1 < b) => pred (omin (set_of fun (o : ordinal) => x < b ^ o) sorry)) fun (h : ¬1 < b) => 0

@[simp] theorem log_not_one_lt {b : ordinal} (b1 : ¬1 < b) (x : ordinal) : log b x = 0 := sorry

theorem log_def {b : ordinal} (b1 : 1 < b) (x : ordinal) : log b x = pred (omin (set_of fun (o : ordinal) => x < b ^ o) (log._proof_1 b x b1)) := sorry

@[simp] theorem log_zero (b : ordinal) : log b 0 = 0 := sorry

theorem succ_log_def {b : ordinal} {x : ordinal} (b1 : 1 < b) (x0 : 0 < x) : succ (log b x) = omin (set_of fun (o : ordinal) => x < b ^ o) (log._proof_1 b x b1) := sorry

theorem lt_power_succ_log {b : ordinal} (b1 : 1 < b) (x : ordinal) : x < b ^ succ (log b x) := sorry

theorem power_log_le (b : ordinal) {x : ordinal} (x0 : 0 < x) : b ^ log b x ≤ x := sorry

theorem le_log {b : ordinal} {x : ordinal} {c : ordinal} (b1 : 1 < b) (x0 : 0 < x) : c ≤ log b x ↔ b ^ c ≤ x := sorry

theorem log_lt {b : ordinal} {x : ordinal} {c : ordinal} (b1 : 1 < b) (x0 : 0 < x) : log b x < c ↔ x < b ^ c :=
  lt_iff_lt_of_le_iff_le (le_log b1 x0)

theorem log_le_log (b : ordinal) {x : ordinal} {y : ordinal} (xy : x ≤ y) : log b x ≤ log b y := sorry

theorem log_le_self (b : ordinal) (x : ordinal) : log b x ≤ x := sorry

/-! ### The Cantor normal form -/

theorem CNF_aux {b : ordinal} {o : ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) : o % b ^ log b o < o :=
  lt_of_lt_of_le (mod_lt o (power_ne_zero (log b o) b0)) (power_log_le b (iff.mpr ordinal.pos_iff_ne_zero o0))

/-- Proving properties of ordinals by induction over their Cantor normal form. -/
def CNF_rec {b : ordinal} (b0 : b ≠ 0) {C : ordinal → Sort u_2} (H0 : C 0) (H : (o : ordinal) → o ≠ 0 → o % b ^ log b o < o → C (o % b ^ log b o) → C o) (o : ordinal) : C o :=
  sorry

@[simp] theorem CNF_rec_zero {b : ordinal} (b0 : b ≠ 0) {C : ordinal → Sort u_2} {H0 : C 0} {H : (o : ordinal) → o ≠ 0 → o % b ^ log b o < o → C (o % b ^ log b o) → C o} : CNF_rec b0 H0 H 0 = H0 := sorry

@[simp] theorem CNF_rec_ne_zero {b : ordinal} (b0 : b ≠ 0) {C : ordinal → Sort u_2} {H0 : C 0} {H : (o : ordinal) → o ≠ 0 → o % b ^ log b o < o → C (o % b ^ log b o) → C o} {o : ordinal} (o0 : o ≠ 0) : CNF_rec b0 H0 H o = H o o0 (CNF_aux b0 o0) (CNF_rec b0 H0 H (o % b ^ log b o)) := sorry

/-- The Cantor normal form of an ordinal is the list of coefficients
  in the base-`b` expansion of `o`.

    CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)] -/
def CNF (b : optParam ordinal omega) (o : ordinal) : List (ordinal × ordinal) :=
  dite (b = 0) (fun (b0 : b = 0) => [])
    fun (b0 : ¬b = 0) =>
      CNF_rec b0 []
        (fun (o : ordinal) (o0 : o ≠ 0) (h : o % b ^ log b o < o) (IH : List (ordinal × ordinal)) =>
          (log b o, o / b ^ log b o) :: IH)
        o

@[simp] theorem zero_CNF (o : ordinal) : CNF 0 o = [] :=
  dif_pos rfl

@[simp] theorem CNF_zero (b : optParam ordinal omega) : CNF b 0 = [] :=
  dite (b = 0) (fun (b0 : b = 0) => dif_pos b0) fun (b0 : ¬b = 0) => Eq.trans (dif_neg b0) (CNF_rec_zero b0)

theorem CNF_ne_zero {b : ordinal} {o : ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) : CNF b o = (log b o, o / b ^ log b o) :: CNF b (o % b ^ log b o) := sorry

theorem one_CNF {o : ordinal} (o0 : o ≠ 0) : CNF 1 o = [(0, o)] := sorry

theorem CNF_foldr {b : ordinal} (b0 : b ≠ 0) (o : ordinal) : list.foldr (fun (p : ordinal × ordinal) (r : ordinal) => b ^ prod.fst p * prod.snd p + r) 0 (CNF b o) = o := sorry

theorem CNF_pairwise_aux (b : optParam ordinal omega) (o : ordinal) : (∀ (p : ordinal × ordinal), p ∈ CNF b o → prod.fst p ≤ log b o) ∧
  list.pairwise (fun (p q : ordinal × ordinal) => prod.fst q < prod.fst p) (CNF b o) := sorry

theorem CNF_pairwise (b : optParam ordinal omega) (o : ordinal) : list.pairwise (fun (p q : ordinal × ordinal) => prod.fst q < prod.fst p) (CNF b o) :=
  and.right (CNF_pairwise_aux b o)

theorem CNF_fst_le_log (b : optParam ordinal omega) (o : ordinal) (p : ordinal × ordinal) (H : p ∈ CNF b o) : prod.fst p ≤ log b o :=
  and.left (CNF_pairwise_aux b o)

theorem CNF_fst_le (b : optParam ordinal omega) (o : ordinal) (p : ordinal × ordinal) (H : p ∈ CNF b o) : prod.fst p ≤ o :=
  le_trans (CNF_fst_le_log b o p H) (log_le_self b o)

theorem CNF_snd_lt {b : ordinal} (b1 : 1 < b) (o : ordinal) (p : ordinal × ordinal) (H : p ∈ CNF b o) : prod.snd p < b := sorry

theorem CNF_sorted (b : optParam ordinal omega) (o : ordinal) : list.sorted gt (list.map prod.fst (CNF b o)) := sorry

/-! ### Casting naturals into ordinals, compatibility with operations -/

@[simp] theorem nat_cast_mul {m : ℕ} {n : ℕ} : ↑(m * n) = ↑m * ↑n := sorry

@[simp] theorem nat_cast_power {m : ℕ} {n : ℕ} : ↑(m ^ n) = ↑m ^ ↑n := sorry

@[simp] theorem nat_cast_le {m : ℕ} {n : ℕ} : ↑m ≤ ↑n ↔ m ≤ n := sorry

@[simp] theorem nat_cast_lt {m : ℕ} {n : ℕ} : ↑m < ↑n ↔ m < n := sorry

@[simp] theorem nat_cast_inj {m : ℕ} {n : ℕ} : ↑m = ↑n ↔ m = n := sorry

@[simp] theorem nat_cast_eq_zero {n : ℕ} : ↑n = 0 ↔ n = 0 :=
  nat_cast_inj

theorem nat_cast_ne_zero {n : ℕ} : ↑n ≠ 0 ↔ n ≠ 0 :=
  not_congr nat_cast_eq_zero

@[simp] theorem nat_cast_pos {n : ℕ} : 0 < ↑n ↔ 0 < n :=
  nat_cast_lt

@[simp] theorem nat_cast_sub {m : ℕ} {n : ℕ} : ↑(m - n) = ↑m - ↑n := sorry

@[simp] theorem nat_cast_div {m : ℕ} {n : ℕ} : ↑(m / n) = ↑m / ↑n := sorry

@[simp] theorem nat_cast_mod {m : ℕ} {n : ℕ} : ↑(m % n) = ↑m % ↑n := sorry

@[simp] theorem nat_le_card {o : ordinal} {n : ℕ} : ↑n ≤ card o ↔ ↑n ≤ o := sorry

@[simp] theorem nat_lt_card {o : ordinal} {n : ℕ} : ↑n < card o ↔ ↑n < o := sorry

@[simp] theorem card_lt_nat {o : ordinal} {n : ℕ} : card o < ↑n ↔ o < ↑n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp] theorem card_le_nat {o : ordinal} {n : ℕ} : card o ≤ ↑n ↔ o ≤ ↑n :=
  iff.mpr le_iff_le_iff_lt_iff_lt nat_lt_card

@[simp] theorem card_eq_nat {o : ordinal} {n : ℕ} : card o = ↑n ↔ o = ↑n := sorry

@[simp] theorem type_fin (n : ℕ) : type Less = ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (type Less = ↑n)) (Eq.symm (propext card_eq_nat))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (card (type Less) = ↑n)) (card_type Less)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (cardinal.mk (fin n) = ↑n)) (cardinal.mk_fin n))) (Eq.refl ↑n)))

@[simp] theorem lift_nat_cast (n : ℕ) : lift ↑n = ↑n := sorry

theorem lift_type_fin (n : ℕ) : lift (type Less) = ↑n := sorry

theorem fintype_card {α : Type u_1} (r : α → α → Prop) [is_well_order α r] [fintype α] : type r = ↑(fintype.card α) := sorry

end ordinal


/-! ### Properties of `omega` -/

namespace cardinal


@[simp] theorem ord_omega : ord omega = ordinal.omega := sorry

@[simp] theorem add_one_of_omega_le {c : cardinal} (h : omega ≤ c) : c + 1 = c := sorry

end cardinal


namespace ordinal


theorem lt_omega {o : ordinal} : o < omega ↔ ∃ (n : ℕ), o = ↑n := sorry

theorem nat_lt_omega (n : ℕ) : ↑n < omega :=
  iff.mpr lt_omega (Exists.intro n rfl)

theorem omega_pos : 0 < omega :=
  nat_lt_omega 0

theorem omega_ne_zero : omega ≠ 0 :=
  ne_of_gt omega_pos

theorem one_lt_omega : 1 < omega := sorry

theorem omega_is_limit : is_limit omega := sorry

theorem omega_le {o : ordinal} : omega ≤ o ↔ ∀ (n : ℕ), ↑n ≤ o := sorry

theorem nat_lt_limit {o : ordinal} (h : is_limit o) (n : ℕ) : ↑n < o := sorry

theorem omega_le_of_is_limit {o : ordinal} (h : is_limit o) : omega ≤ o :=
  iff.mpr omega_le fun (n : ℕ) => le_of_lt (nat_lt_limit h n)

theorem add_omega {a : ordinal} (h : a < omega) : a + omega = omega := sorry

theorem add_lt_omega {a : ordinal} {b : ordinal} (ha : a < omega) (hb : b < omega) : a + b < omega := sorry

theorem mul_lt_omega {a : ordinal} {b : ordinal} (ha : a < omega) (hb : b < omega) : a * b < omega := sorry

theorem is_limit_iff_omega_dvd {a : ordinal} : is_limit a ↔ a ≠ 0 ∧ omega ∣ a := sorry

theorem power_lt_omega {a : ordinal} {b : ordinal} (ha : a < omega) (hb : b < omega) : a ^ b < omega := sorry

theorem add_omega_power {a : ordinal} {b : ordinal} (h : a < omega ^ b) : a + omega ^ b = omega ^ b := sorry

theorem add_lt_omega_power {a : ordinal} {b : ordinal} {c : ordinal} (h₁ : a < omega ^ c) (h₂ : b < omega ^ c) : a + b < omega ^ c :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a + b < omega ^ c)) (Eq.symm (add_omega_power h₁))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a + b < a + omega ^ c)) (propext (add_lt_add_iff_left a)))) h₂)

theorem add_absorp {a : ordinal} {b : ordinal} {c : ordinal} (h₁ : a < omega ^ b) (h₂ : omega ^ b ≤ c) : a + c = c := sorry

theorem add_absorp_iff {o : ordinal} (o0 : 0 < o) : (∀ (a : ordinal), a < o → a + o = o) ↔ ∃ (a : ordinal), o = omega ^ a := sorry

theorem add_mul_limit_aux {a : ordinal} {b : ordinal} {c : ordinal} (ba : b + a = a) (l : is_limit c) (IH : ∀ (c' : ordinal), c' < c → (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c := sorry

theorem add_mul_succ {a : ordinal} {b : ordinal} (c : ordinal) (ba : b + a = a) : (a + b) * succ c = a * succ c + b := sorry

theorem add_mul_limit {a : ordinal} {b : ordinal} {c : ordinal} (ba : b + a = a) (l : is_limit c) : (a + b) * c = a * c :=
  add_mul_limit_aux ba l fun (c' : ordinal) (_x : c' < c) => add_mul_succ c' ba

theorem mul_omega {a : ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega := sorry

theorem mul_lt_omega_power {a : ordinal} {b : ordinal} {c : ordinal} (c0 : 0 < c) (ha : a < omega ^ c) (hb : b < omega) : a * b < omega ^ c := sorry

theorem mul_omega_dvd {a : ordinal} (a0 : 0 < a) (ha : a < omega) {b : ordinal} : omega ∣ b → a * b = b := sorry

theorem mul_omega_power_power {a : ordinal} {b : ordinal} (a0 : 0 < a) (h : a < omega ^ omega ^ b) : a * omega ^ omega ^ b = omega ^ omega ^ b := sorry

theorem power_omega {a : ordinal} (a1 : 1 < a) (h : a < omega) : a ^ omega = omega := sorry

/-! ### Fixed points of normal functions -/

/-- The next fixed point function, the least fixed point of the
  normal function `f` above `a`. -/
def nfp (f : ordinal → ordinal) (a : ordinal) : ordinal :=
  sup fun (n : ℕ) => nat.iterate f n a

theorem iterate_le_nfp (f : ordinal → ordinal) (a : ordinal) (n : ℕ) : nat.iterate f n a ≤ nfp f a :=
  le_sup (fun (n : ℕ) => nat.iterate f n a) n

theorem le_nfp_self (f : ordinal → ordinal) (a : ordinal) : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem is_normal.lt_nfp {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} : f b < nfp f a ↔ b < nfp f a := sorry

theorem is_normal.nfp_le {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  iff.mpr le_iff_le_iff_lt_iff_lt (is_normal.lt_nfp H)

theorem is_normal.nfp_le_fp {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b := sorry

theorem is_normal.nfp_fp {f : ordinal → ordinal} (H : is_normal f) (a : ordinal) : f (nfp f a) = nfp f a := sorry

theorem is_normal.le_nfp {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} {b : ordinal} : f b ≤ nfp f a ↔ b ≤ nfp f a := sorry

theorem nfp_eq_self {f : ordinal → ordinal} {a : ordinal} (h : f a = a) : nfp f a = a := sorry

/-- The derivative of a normal function `f` is
  the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) (o : ordinal) : ordinal :=
  limit_rec_on o (nfp f 0) (fun (a IH : ordinal) => nfp f (succ IH)) fun (a : ordinal) (l : is_limit a) => bsup a

@[simp] theorem deriv_zero (f : ordinal → ordinal) : deriv f 0 = nfp f 0 :=
  limit_rec_on_zero (nfp f 0) (fun (a IH : ordinal) => nfp f (succ IH)) fun (a : ordinal) (l : is_limit a) => bsup a

@[simp] theorem deriv_succ (f : ordinal → ordinal) (o : ordinal) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  limit_rec_on_succ o (nfp f 0) (fun (a IH : ordinal) => nfp f (succ IH)) fun (a : ordinal) (l : is_limit a) => bsup a

theorem deriv_limit (f : ordinal → ordinal) {o : ordinal} : is_limit o → deriv f o = bsup o fun (a : ordinal) (_x : a < o) => deriv f a :=
  limit_rec_on_limit o (nfp f 0) (fun (a IH : ordinal) => nfp f (succ IH)) fun (a : ordinal) (l : is_limit a) => bsup a

theorem deriv_is_normal (f : ordinal → ordinal) : is_normal (deriv f) := sorry

theorem is_normal.deriv_fp {f : ordinal → ordinal} (H : is_normal f) (o : ordinal) : f (deriv f o) = deriv f o := sorry

theorem is_normal.fp_iff_deriv {f : ordinal → ordinal} (H : is_normal f) {a : ordinal} : f a ≤ a ↔ ∃ (o : ordinal), a = deriv f o := sorry

