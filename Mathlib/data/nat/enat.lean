/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.pfun
import Mathlib.tactic.norm_num
import Mathlib.data.equiv.mul_add
import Mathlib.PostPort

namespace Mathlib

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`.

## Main definitions

The following instances are defined:

* `ordered_add_comm_monoid enat`
* `canonically_ordered_add_monoid enat`

There is no additive analogue of `monoid_with_zero`; if there were then `enat` could
be an `add_monoid_with_top`.

* `to_with_top` : the map from `enat` to `with_top ℕ`, with theorems that it plays well
with `+` and `≤`.

* `with_top_add_equiv : enat ≃+ with_top ℕ`
* `with_top_order_iso : enat ≃o with_top ℕ`

## Implementation details

`enat` is defined to be `roption ℕ`.

`+` and `≤` are defined on `enat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `enat`.

Before the `open_locale classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `to_with_top_zero` proved by `rfl`,
followed by `@[simp] lemma to_with_top_zero'` whose proof uses `convert`.


## Tags

enat, with_top ℕ
-/

/-- Type of natural numbers with infinity (`⊤`) -/
def enat  :=
  roption ℕ

namespace enat


protected instance has_zero : HasZero enat :=
  { zero := roption.some 0 }

protected instance inhabited : Inhabited enat :=
  { default := 0 }

protected instance has_one : HasOne enat :=
  { one := roption.some 1 }

protected instance has_add : Add enat :=
  { add :=
      fun (x y : enat) =>
        roption.mk (roption.dom x ∧ roption.dom y)
          fun (h : roption.dom x ∧ roption.dom y) => roption.get x sorry + roption.get y sorry }

protected instance has_coe : has_coe ℕ enat :=
  has_coe.mk roption.some

protected instance dom.decidable (n : ℕ) : Decidable (roption.dom ↑n) :=
  is_true trivial

@[simp] theorem coe_inj {x : ℕ} {y : ℕ} : ↑x = ↑y ↔ x = y :=
  roption.some_inj

@[simp] theorem dom_coe (x : ℕ) : roption.dom ↑x :=
  trivial

protected instance add_comm_monoid : add_comm_monoid enat :=
  add_comm_monoid.mk Add.add sorry 0 sorry sorry sorry

protected instance has_le : HasLessEq enat :=
  { LessEq :=
      fun (x y : enat) =>
        ∃ (h : roption.dom y → roption.dom x), ∀ (hy : roption.dom y), roption.get x (h hy) ≤ roption.get y hy }

protected instance has_top : has_top enat :=
  has_top.mk roption.none

protected instance has_bot : has_bot enat :=
  has_bot.mk 0

protected instance has_sup : has_sup enat :=
  has_sup.mk
    fun (x y : enat) =>
      roption.mk (roption.dom x ∧ roption.dom y)
        fun (h : roption.dom x ∧ roption.dom y) => roption.get x sorry ⊔ roption.get y sorry

theorem le_def (x : enat) (y : enat) : x ≤ y ↔ ∃ (h : roption.dom y → roption.dom x), ∀ (hy : roption.dom y), roption.get x (h hy) ≤ roption.get y hy :=
  iff.rfl

protected theorem cases_on {P : enat → Prop} (a : enat) : P ⊤ → (∀ (n : ℕ), P ↑n) → P a :=
  roption.induction_on

@[simp] theorem top_add (x : enat) : ⊤ + x = ⊤ :=
  roption.ext' (false_and (roption.dom x)) fun (h : roption.dom (⊤ + x)) => false.elim (and.left h)

@[simp] theorem add_top (x : enat) : x + ⊤ = ⊤ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x + ⊤ = ⊤)) (add_comm x ⊤)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⊤ + x = ⊤)) (top_add x))) (Eq.refl ⊤))

@[simp] theorem coe_zero : ↑0 = 0 :=
  rfl

@[simp] theorem coe_one : ↑1 = 1 :=
  rfl

@[simp] theorem coe_add (x : ℕ) (y : ℕ) : ↑(x + y) = ↑x + ↑y :=
  roption.ext' (iff.symm (and_true (roption.dom ↑(x + y))))
    fun (_x : roption.dom ↑(x + y)) (_x_1 : roption.dom (↑x + ↑y)) => rfl

theorem get_coe {x : ℕ} : roption.get (↑x) True.intro = x :=
  rfl

@[simp] theorem get_coe' (x : ℕ) (h : roption.dom ↑x) : roption.get (↑x) h = x :=
  rfl

theorem coe_add_get {x : ℕ} {y : enat} (h : roption.dom (↑x + y)) : roption.get (↑x + y) h = x + roption.get y (and.right h) :=
  rfl

@[simp] theorem get_add {x : enat} {y : enat} (h : roption.dom (x + y)) : roption.get (x + y) h = roption.get x (and.left h) + roption.get y (and.right h) :=
  rfl

@[simp] theorem coe_get {x : enat} (h : roption.dom x) : ↑(roption.get x h) = x :=
  roption.ext' (iff_of_true trivial h) fun (_x : roption.dom ↑(roption.get x h)) (_x_1 : roption.dom x) => rfl

@[simp] theorem get_zero (h : roption.dom 0) : roption.get 0 h = 0 :=
  rfl

@[simp] theorem get_one (h : roption.dom 1) : roption.get 1 h = 1 :=
  rfl

theorem dom_of_le_of_dom {x : enat} {y : enat} : x ≤ y → roption.dom y → roption.dom x := sorry

theorem dom_of_le_some {x : enat} {y : ℕ} (h : x ≤ ↑y) : roption.dom x :=
  dom_of_le_of_dom h trivial

protected instance decidable_le (x : enat) (y : enat) [Decidable (roption.dom x)] [Decidable (roption.dom y)] : Decidable (x ≤ y) :=
  dite (roption.dom x)
    (fun (hx : roption.dom x) =>
      decidable_of_decidable_of_iff
        ((fun (this : Decidable (∀ (hy : roption.dom y), roption.get x hx ≤ roption.get y hy)) => this)
          (Mathlib.forall_prop_decidable fun (hy : roption.dom y) => roption.get x hx ≤ roption.get y hy))
        sorry)
    fun (hx : ¬roption.dom x) =>
      dite (roption.dom y) (fun (hy : roption.dom y) => isFalse sorry) fun (hy : ¬roption.dom y) => is_true sorry

/-- The coercion `ℕ → enat` preserves `0` and addition. -/
def coe_hom : ℕ →+ enat :=
  add_monoid_hom.mk coe coe_zero coe_add

protected instance partial_order : partial_order enat :=
  partial_order.mk LessEq (preorder.lt._default LessEq) sorry sorry sorry

theorem lt_def (x : enat) (y : enat) : x < y ↔ ∃ (hx : roption.dom x), ∀ (hy : roption.dom y), roption.get x hx < roption.get y hy := sorry

@[simp] theorem coe_le_coe {x : ℕ} {y : ℕ} : ↑x ≤ ↑y ↔ x ≤ y := sorry

@[simp] theorem coe_lt_coe {x : ℕ} {y : ℕ} : ↑x < ↑y ↔ x < y := sorry

@[simp] theorem get_le_get {x : enat} {y : enat} {hx : roption.dom x} {hy : roption.dom y} : roption.get x hx ≤ roption.get y hy ↔ x ≤ y := sorry

theorem le_coe_iff (x : enat) (n : ℕ) : x ≤ ↑n ↔ ∃ (h : roption.dom x), roption.get x h ≤ n := sorry

theorem lt_coe_iff (x : enat) (n : ℕ) : x < ↑n ↔ ∃ (h : roption.dom x), roption.get x h < n := sorry

theorem coe_le_iff (n : ℕ) (x : enat) : ↑n ≤ x ↔ ∀ (h : roption.dom x), n ≤ roption.get x h := sorry

theorem coe_lt_iff (n : ℕ) (x : enat) : ↑n < x ↔ ∀ (h : roption.dom x), n < roption.get x h := sorry

protected theorem zero_lt_one : 0 < 1 := sorry

protected instance semilattice_sup_bot : semilattice_sup_bot enat :=
  semilattice_sup_bot.mk ⊥ partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans
    partial_order.le_antisymm sorry has_sup.sup sorry sorry sorry

protected instance order_top : order_top enat :=
  order_top.mk ⊤ semilattice_sup_bot.le semilattice_sup_bot.lt semilattice_sup_bot.le_refl semilattice_sup_bot.le_trans
    semilattice_sup_bot.le_antisymm sorry

theorem dom_of_lt {x : enat} {y : enat} : x < y → roption.dom x :=
  enat.cases_on x not_top_lt fun (_x : ℕ) (_x : ↑_x < y) => trivial

theorem top_eq_none : ⊤ = roption.none :=
  rfl

@[simp] theorem coe_lt_top (x : ℕ) : ↑x < ⊤ :=
  lt_of_le_of_ne le_top fun (h : ↑x = ⊤) => absurd (congr_arg roption.dom h) true_ne_false

@[simp] theorem coe_ne_top (x : ℕ) : ↑x ≠ ⊤ :=
  ne_of_lt (coe_lt_top x)

theorem ne_top_iff {x : enat} : x ≠ ⊤ ↔ ∃ (n : ℕ), x = ↑n :=
  roption.ne_none_iff

theorem ne_top_iff_dom {x : enat} : x ≠ ⊤ ↔ roption.dom x :=
  iff.mp not_iff_comm (iff.symm roption.eq_none_iff')

theorem ne_top_of_lt {x : enat} {y : enat} (h : x < y) : x ≠ ⊤ :=
  ne_of_lt (lt_of_lt_of_le h le_top)

theorem eq_top_iff_forall_lt (x : enat) : x = ⊤ ↔ ∀ (n : ℕ), ↑n < x := sorry

theorem eq_top_iff_forall_le (x : enat) : x = ⊤ ↔ ∀ (n : ℕ), ↑n ≤ x :=
  iff.trans (eq_top_iff_forall_lt x)
    { mp := fun (h : ∀ (n : ℕ), ↑n < x) (n : ℕ) => has_lt.lt.le (h n),
      mpr := fun (h : ∀ (n : ℕ), ↑n ≤ x) (n : ℕ) => lt_of_lt_of_le (iff.mpr coe_lt_coe (nat.lt_succ_self n)) (h (n + 1)) }

theorem pos_iff_one_le {x : enat} : 0 < x ↔ 1 ≤ x := sorry

protected instance linear_order : linear_order enat :=
  linear_order.mk partial_order.le partial_order.lt partial_order.le_refl partial_order.le_trans partial_order.le_antisymm
    sorry (classical.dec_rel LessEq) Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

protected instance bounded_lattice : bounded_lattice enat :=
  bounded_lattice.mk semilattice_sup_bot.sup order_top.le order_top.lt order_top.le_refl order_top.le_trans
    order_top.le_antisymm semilattice_sup_bot.le_sup_left semilattice_sup_bot.le_sup_right semilattice_sup_bot.sup_le min
    min_le_left min_le_right sorry order_top.top order_top.le_top semilattice_sup_bot.bot semilattice_sup_bot.bot_le

theorem sup_eq_max {a : enat} {b : enat} : a ⊔ b = max a b :=
  le_antisymm (sup_le (le_max_left a b) (le_max_right a b)) (max_le le_sup_left le_sup_right)

theorem inf_eq_min {a : enat} {b : enat} : a ⊓ b = min a b :=
  rfl

protected instance ordered_add_comm_monoid : ordered_add_comm_monoid enat :=
  ordered_add_comm_monoid.mk add_comm_monoid.add add_comm_monoid.add_assoc add_comm_monoid.zero add_comm_monoid.zero_add
    add_comm_monoid.add_zero add_comm_monoid.add_comm linear_order.le linear_order.lt linear_order.le_refl
    linear_order.le_trans linear_order.le_antisymm sorry sorry

protected instance canonically_ordered_add_monoid : canonically_ordered_add_monoid enat :=
  canonically_ordered_add_monoid.mk ordered_add_comm_monoid.add ordered_add_comm_monoid.add_assoc
    ordered_add_comm_monoid.zero ordered_add_comm_monoid.zero_add ordered_add_comm_monoid.add_zero
    ordered_add_comm_monoid.add_comm semilattice_sup_bot.le semilattice_sup_bot.lt semilattice_sup_bot.le_refl
    semilattice_sup_bot.le_trans semilattice_sup_bot.le_antisymm ordered_add_comm_monoid.add_le_add_left
    ordered_add_comm_monoid.lt_of_add_lt_add_left semilattice_sup_bot.bot semilattice_sup_bot.bot_le sorry

protected theorem add_lt_add_right {x : enat} {y : enat} {z : enat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z := sorry

protected theorem add_lt_add_iff_right {x : enat} {y : enat} {z : enat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
  { mp := lt_of_add_lt_add_right, mpr := fun (h : x < y) => enat.add_lt_add_right h hz }

protected theorem add_lt_add_iff_left {x : enat} {y : enat} {z : enat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y := sorry

protected theorem lt_add_iff_pos_right {x : enat} {y : enat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y := sorry

theorem lt_add_one {x : enat} (hx : x ≠ ⊤) : x < x + 1 := sorry

theorem le_of_lt_add_one {x : enat} {y : enat} (h : x < y + 1) : x ≤ y := sorry

theorem add_one_le_of_lt {x : enat} {y : enat} (h : x < y) : x + 1 ≤ y := sorry

theorem add_one_le_iff_lt {x : enat} {y : enat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y := sorry

theorem lt_add_one_iff_lt {x : enat} {y : enat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y := sorry

theorem add_eq_top_iff {a : enat} {b : enat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := sorry

protected theorem add_right_cancel_iff {a : enat} {b : enat} {c : enat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b := sorry

protected theorem add_left_cancel_iff {a : enat} {b : enat} {c : enat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := sorry

/-- Computably converts an `enat` to a `with_top ℕ`. -/
def to_with_top (x : enat) [Decidable (roption.dom x)] : with_top ℕ :=
  roption.to_option x

theorem to_with_top_top : to_with_top ⊤ = ⊤ :=
  rfl

@[simp] theorem to_with_top_top' {h : Decidable (roption.dom ⊤)} : to_with_top ⊤ = ⊤ := sorry

theorem to_with_top_zero : to_with_top 0 = 0 :=
  rfl

@[simp] theorem to_with_top_zero' {h : Decidable (roption.dom 0)} : to_with_top 0 = 0 := sorry

theorem to_with_top_coe (n : ℕ) : to_with_top ↑n = ↑n :=
  rfl

@[simp] theorem to_with_top_coe' (n : ℕ) {h : Decidable (roption.dom ↑n)} : to_with_top ↑n = ↑n := sorry

@[simp] theorem to_with_top_le {x : enat} {y : enat} [Decidable (roption.dom x)] [Decidable (roption.dom y)] : to_with_top x ≤ to_with_top y ↔ x ≤ y := sorry

@[simp] theorem to_with_top_lt {x : enat} {y : enat} [Decidable (roption.dom x)] [Decidable (roption.dom y)] : to_with_top x < to_with_top y ↔ x < y :=
  lt_iff_lt_of_le_iff_le to_with_top_le

@[simp] theorem to_with_top_add {x : enat} {y : enat} : to_with_top (x + y) = to_with_top x + to_with_top y := sorry

/-- `equiv` between `enat` and `with_top ℕ` (for the order isomorphism see `with_top_order_iso`). -/
def with_top_equiv : enat ≃ with_top ℕ :=
  equiv.mk (fun (x : enat) => to_with_top x) (fun (x : with_top ℕ) => sorry) sorry sorry

@[simp] theorem with_top_equiv_top : coe_fn with_top_equiv ⊤ = ⊤ :=
  to_with_top_top'

@[simp] theorem with_top_equiv_coe (n : ℕ) : coe_fn with_top_equiv ↑n = ↑n :=
  to_with_top_coe' n

@[simp] theorem with_top_equiv_zero : coe_fn with_top_equiv 0 = 0 :=
  with_top_equiv_coe 0

@[simp] theorem with_top_equiv_le {x : enat} {y : enat} : coe_fn with_top_equiv x ≤ coe_fn with_top_equiv y ↔ x ≤ y :=
  to_with_top_le

@[simp] theorem with_top_equiv_lt {x : enat} {y : enat} : coe_fn with_top_equiv x < coe_fn with_top_equiv y ↔ x < y :=
  to_with_top_lt

/-- `to_with_top` induces an order isomorphism between `enat` and `with_top ℕ`. -/
def with_top_order_iso : enat ≃o with_top ℕ :=
  rel_iso.mk (equiv.mk (equiv.to_fun with_top_equiv) (equiv.inv_fun with_top_equiv) sorry sorry) sorry

@[simp] theorem with_top_equiv_symm_top : coe_fn (equiv.symm with_top_equiv) ⊤ = ⊤ :=
  rfl

@[simp] theorem with_top_equiv_symm_coe (n : ℕ) : coe_fn (equiv.symm with_top_equiv) ↑n = ↑n :=
  rfl

@[simp] theorem with_top_equiv_symm_zero : coe_fn (equiv.symm with_top_equiv) 0 = 0 :=
  rfl

@[simp] theorem with_top_equiv_symm_le {x : with_top ℕ} {y : with_top ℕ} : coe_fn (equiv.symm with_top_equiv) x ≤ coe_fn (equiv.symm with_top_equiv) y ↔ x ≤ y := sorry

@[simp] theorem with_top_equiv_symm_lt {x : with_top ℕ} {y : with_top ℕ} : coe_fn (equiv.symm with_top_equiv) x < coe_fn (equiv.symm with_top_equiv) y ↔ x < y := sorry

/-- `to_with_top` induces an additive monoid isomorphism between `enat` and `with_top ℕ`. -/
def with_top_add_equiv : enat ≃+ with_top ℕ :=
  add_equiv.mk (equiv.to_fun with_top_equiv) (equiv.inv_fun with_top_equiv) sorry sorry sorry

theorem lt_wf : well_founded Less := sorry

protected instance has_well_founded : has_well_founded enat :=
  has_well_founded.mk Less lt_wf

/-- The smallest `enat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find (P : ℕ → Prop) [decidable_pred P] : enat :=
  roption.mk (∃ (n : ℕ), P n) nat.find

@[simp] theorem find_get (P : ℕ → Prop) [decidable_pred P] (h : roption.dom (find P)) : roption.get (find P) h = nat.find h :=
  rfl

theorem find_dom (P : ℕ → Prop) [decidable_pred P] (h : ∃ (n : ℕ), P n) : roption.dom (find P) :=
  h

theorem lt_find (P : ℕ → Prop) [decidable_pred P] (n : ℕ) (h : ∀ (m : ℕ), m ≤ n → ¬P m) : ↑n < find P := sorry

theorem lt_find_iff (P : ℕ → Prop) [decidable_pred P] (n : ℕ) : ↑n < find P ↔ ∀ (m : ℕ), m ≤ n → ¬P m := sorry

theorem find_le (P : ℕ → Prop) [decidable_pred P] (n : ℕ) (h : P n) : find P ≤ ↑n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (find P ≤ ↑n)) (propext (le_coe_iff (find P) n))))
    (Exists.intro (Exists.intro n h) (nat.find_min' (Exists.intro n h) h))

theorem find_eq_top_iff (P : ℕ → Prop) [decidable_pred P] : find P = ⊤ ↔ ∀ (n : ℕ), ¬P n :=
  iff.trans (eq_top_iff_forall_lt (find P))
    { mp := fun (h : ∀ (n : ℕ), ↑n < find P) (n : ℕ) => iff.mp (lt_find_iff P n) (h n) n le_rfl,
      mpr := fun (h : ∀ (n : ℕ), ¬P n) (n : ℕ) => lt_find P n fun (_x : ℕ) (_x_1 : _x ≤ n) => h _x }

