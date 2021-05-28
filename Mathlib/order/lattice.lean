/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines the inf/sup (semi)-lattice with optionally top/bot type class hierarchy.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.rel_classes
import Mathlib.PostPort

universes u l u_1 v 

namespace Mathlib

-- TODO: move this eventually, if we decide to use them

-- TODO: this seems crazy, but it also seems to work reasonably well

theorem le_antisymm' {α : Type u} [partial_order α] {a : α} {b : α} : a ≤ b → b ≤ a → a = b :=
  le_antisymm

/- TODO: automatic construction of dual definitions / theorems -/

/-- Typeclass for the `⊔` (`\lub`) notation -/
/-- Typeclass for the `⊓` (`\glb`) notation -/
class has_sup (α : Type u) 
where
  sup : α → α → α

class has_inf (α : Type u) 
where
  inf : α → α → α

infixl:65 " ⊔ " => Mathlib.has_sup.sup

infixl:70 " ⊓ " => Mathlib.has_inf.inf

/-- A `semilattice_sup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class semilattice_sup (α : Type u) 
extends has_sup α, partial_order α
where
  le_sup_left : ∀ (a b : α), a ≤ a ⊔ b
  le_sup_right : ∀ (a b : α), b ≤ a ⊔ b
  sup_le : ∀ (a b c : α), a ≤ c → b ≤ c → a ⊔ b ≤ c

protected instance order_dual.has_sup (α : Type u_1) [has_inf α] : has_sup (order_dual α) :=
  has_sup.mk has_inf.inf

protected instance order_dual.has_inf (α : Type u_1) [has_sup α] : has_inf (order_dual α) :=
  has_inf.mk has_sup.sup

@[simp] theorem le_sup_left {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ≤ a ⊔ b :=
  semilattice_sup.le_sup_left a b

theorem le_sup_left' {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ≤ a ⊔ b :=
  le_sup_left

@[simp] theorem le_sup_right {α : Type u} [semilattice_sup α] {a : α} {b : α} : b ≤ a ⊔ b :=
  semilattice_sup.le_sup_right a b

theorem le_sup_right' {α : Type u} [semilattice_sup α] {a : α} {b : α} : b ≤ a ⊔ b :=
  le_sup_right

theorem le_sup_left_of_le {α : Type u} [semilattice_sup α] {a : α} {b : α} {c : α} (h : c ≤ a) : c ≤ a ⊔ b :=
  le_trans h le_sup_left

theorem le_sup_right_of_le {α : Type u} [semilattice_sup α] {a : α} {b : α} {c : α} (h : c ≤ b) : c ≤ a ⊔ b :=
  le_trans h le_sup_right

theorem sup_le {α : Type u} [semilattice_sup α] {a : α} {b : α} {c : α} : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  semilattice_sup.sup_le a b c

@[simp] theorem sup_le_iff {α : Type u} [semilattice_sup α] {a : α} {b : α} {c : α} : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c := sorry

@[simp] theorem sup_eq_left {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ⊔ b = a ↔ b ≤ a := sorry

theorem sup_of_le_left {α : Type u} [semilattice_sup α] {a : α} {b : α} (h : b ≤ a) : a ⊔ b = a :=
  iff.mpr sup_eq_left h

@[simp] theorem left_eq_sup {α : Type u} [semilattice_sup α] {a : α} {b : α} : a = a ⊔ b ↔ b ≤ a :=
  iff.trans eq_comm sup_eq_left

@[simp] theorem sup_eq_right {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ⊔ b = b ↔ a ≤ b := sorry

theorem sup_of_le_right {α : Type u} [semilattice_sup α] {a : α} {b : α} (h : a ≤ b) : a ⊔ b = b :=
  iff.mpr sup_eq_right h

@[simp] theorem right_eq_sup {α : Type u} [semilattice_sup α] {a : α} {b : α} : b = a ⊔ b ↔ a ≤ b :=
  iff.trans eq_comm sup_eq_right

theorem sup_le_sup {α : Type u} [semilattice_sup α] {a : α} {b : α} {c : α} {d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
  sup_le (le_sup_left_of_le h₁) (le_sup_right_of_le h₂)

theorem sup_le_sup_left {α : Type u} [semilattice_sup α] {a : α} {b : α} (h₁ : a ≤ b) (c : α) : c ⊔ a ≤ c ⊔ b :=
  sup_le_sup (le_refl c) h₁

theorem sup_le_sup_right {α : Type u} [semilattice_sup α] {a : α} {b : α} (h₁ : a ≤ b) (c : α) : a ⊔ c ≤ b ⊔ c :=
  sup_le_sup h₁ (le_refl c)

theorem le_of_sup_eq {α : Type u} [semilattice_sup α] {a : α} {b : α} (h : a ⊔ b = b) : a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b)) (Eq.symm h))) (eq.mpr (id (propext (iff_true_intro le_sup_left))) trivial)

theorem sup_ind {α : Type u} [semilattice_sup α] [is_total α LessEq] (a : α) (b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
  or.elim (is_total.total a b)
    (fun (h : a ≤ b) => eq.mpr (id (Eq._oldrec (Eq.refl (p (a ⊔ b))) (iff.mpr sup_eq_right h))) hb)
    fun (h : b ≤ a) => eq.mpr (id (Eq._oldrec (Eq.refl (p (a ⊔ b))) (iff.mpr sup_eq_left h))) ha

@[simp] theorem sup_lt_iff {α : Type u} [semilattice_sup α] [is_total α LessEq] {a : α} {b : α} {c : α} : b ⊔ c < a ↔ b < a ∧ c < a :=
  { mp := fun (h : b ⊔ c < a) => { left := has_le.le.trans_lt le_sup_left h, right := has_le.le.trans_lt le_sup_right h },
    mpr := fun (h : b < a ∧ c < a) => sup_ind b c (and.left h) (and.right h) }

@[simp] theorem le_sup_iff {α : Type u} [semilattice_sup α] [is_total α LessEq] {a : α} {b : α} {c : α} : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c := sorry

@[simp] theorem lt_sup_iff {α : Type u} [semilattice_sup α] [is_total α LessEq] {a : α} {b : α} {c : α} : a < b ⊔ c ↔ a < b ∨ a < c := sorry

@[simp] theorem sup_idem {α : Type u} [semilattice_sup α] {a : α} : a ⊔ a = a :=
  le_antisymm (eq.mpr (id (Eq.trans (propext sup_le_iff) (propext (and_self (a ≤ a))))) (le_refl a))
    (eq.mpr (id (propext (iff_true_intro le_sup_right))) trivial)

protected instance sup_is_idempotent {α : Type u} [semilattice_sup α] : is_idempotent α has_sup.sup :=
  is_idempotent.mk sup_idem

theorem sup_comm {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ⊔ b = b ⊔ a := sorry

protected instance sup_is_commutative {α : Type u} [semilattice_sup α] : is_commutative α has_sup.sup :=
  is_commutative.mk sup_comm

theorem sup_assoc {α : Type u} [semilattice_sup α] {a : α} {b : α} {c : α} : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
  le_antisymm (sup_le (sup_le le_sup_left (le_sup_right_of_le le_sup_left)) (le_sup_right_of_le le_sup_right))
    (sup_le (le_sup_left_of_le le_sup_left) (sup_le (le_sup_left_of_le le_sup_right) le_sup_right))

protected instance sup_is_associative {α : Type u} [semilattice_sup α] : is_associative α has_sup.sup :=
  is_associative.mk sup_assoc

@[simp] theorem sup_left_idem {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ⊔ (a ⊔ b) = a ⊔ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ (a ⊔ b) = a ⊔ b)) (Eq.symm sup_assoc)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ a ⊔ b = a ⊔ b)) sup_idem)) (Eq.refl (a ⊔ b)))

@[simp] theorem sup_right_idem {α : Type u} [semilattice_sup α] {a : α} {b : α} : a ⊔ b ⊔ b = a ⊔ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ b ⊔ b = a ⊔ b)) sup_assoc))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ (b ⊔ b) = a ⊔ b)) sup_idem)) (Eq.refl (a ⊔ b)))

theorem sup_left_comm {α : Type u} [semilattice_sup α] (a : α) (b : α) (c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c))) (Eq.symm sup_assoc)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ b ⊔ c = b ⊔ (a ⊔ c))) (Eq.symm sup_assoc)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ⊔ b ⊔ c = b ⊔ a ⊔ c)) sup_comm)) (Eq.refl (b ⊔ a ⊔ c))))

theorem forall_le_or_exists_lt_sup {α : Type u} [semilattice_sup α] (a : α) : (∀ (b : α), b ≤ a) ∨ ∃ (b : α), a < b := sorry

/-- If `f` is a monotonically increasing sequence, `g` is a monotonically decreasing
sequence, and `f n ≤ g n` for all `n`, then for all `m`, `n` we have `f m ≤ g n`. -/
theorem forall_le_of_monotone_of_mono_decr {α : Type u} [semilattice_sup α] {β : Type u_1} [preorder β] {f : α → β} {g : α → β} (hf : monotone f) (hg : ∀ {m n : α}, m ≤ n → g n ≤ g m) (h : ∀ (n : α), f n ≤ g n) (m : α) (n : α) : f m ≤ g n :=
  le_trans (le_trans (hf le_sup_left) (h (m ⊔ n))) (hg le_sup_right)

theorem semilattice_sup.ext_sup {α : Type u_1} {A : semilattice_sup α} {B : semilattice_sup α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) (x : α) (y : α) : x ⊔ y = x ⊔ y := sorry

theorem semilattice_sup.ext {α : Type u_1} {A : semilattice_sup α} {B : semilattice_sup α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-- A `semilattice_inf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
class semilattice_inf (α : Type u) 
extends partial_order α, has_inf α
where
  inf_le_left : ∀ (a b : α), a ⊓ b ≤ a
  inf_le_right : ∀ (a b : α), a ⊓ b ≤ b
  le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ b ⊓ c

protected instance order_dual.semilattice_sup (α : Type u_1) [semilattice_inf α] : semilattice_sup (order_dual α) :=
  semilattice_sup.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance order_dual.semilattice_inf (α : Type u_1) [semilattice_sup α] : semilattice_inf (order_dual α) :=
  semilattice_inf.mk has_inf.inf partial_order.le partial_order.lt sorry sorry sorry le_sup_left le_sup_right sorry

@[simp] theorem inf_le_left {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b ≤ a :=
  semilattice_inf.inf_le_left a b

theorem inf_le_left' {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b ≤ a :=
  semilattice_inf.inf_le_left a b

@[simp] theorem inf_le_right {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b ≤ b :=
  semilattice_inf.inf_le_right a b

theorem inf_le_right' {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b ≤ b :=
  semilattice_inf.inf_le_right a b

theorem le_inf {α : Type u} [semilattice_inf α] {a : α} {b : α} {c : α} : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
  semilattice_inf.le_inf a b c

theorem inf_le_left_of_le {α : Type u} [semilattice_inf α] {a : α} {b : α} {c : α} (h : a ≤ c) : a ⊓ b ≤ c :=
  le_trans inf_le_left h

theorem inf_le_right_of_le {α : Type u} [semilattice_inf α] {a : α} {b : α} {c : α} (h : b ≤ c) : a ⊓ b ≤ c :=
  le_trans inf_le_right h

@[simp] theorem le_inf_iff {α : Type u} [semilattice_inf α] {a : α} {b : α} {c : α} : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  sup_le_iff

@[simp] theorem inf_eq_left {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b = a ↔ a ≤ b := sorry

theorem inf_of_le_left {α : Type u} [semilattice_inf α] {a : α} {b : α} (h : a ≤ b) : a ⊓ b = a :=
  iff.mpr inf_eq_left h

@[simp] theorem left_eq_inf {α : Type u} [semilattice_inf α] {a : α} {b : α} : a = a ⊓ b ↔ a ≤ b :=
  iff.trans eq_comm inf_eq_left

@[simp] theorem inf_eq_right {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b = b ↔ b ≤ a := sorry

theorem inf_of_le_right {α : Type u} [semilattice_inf α] {a : α} {b : α} (h : b ≤ a) : a ⊓ b = b :=
  iff.mpr inf_eq_right h

@[simp] theorem right_eq_inf {α : Type u} [semilattice_inf α] {a : α} {b : α} : b = a ⊓ b ↔ b ≤ a :=
  iff.trans eq_comm inf_eq_right

theorem inf_le_inf {α : Type u} [semilattice_inf α] {a : α} {b : α} {c : α} {d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
  le_inf (inf_le_left_of_le h₁) (inf_le_right_of_le h₂)

theorem inf_le_inf_right {α : Type u} [semilattice_inf α] (a : α) {b : α} {c : α} (h : b ≤ c) : b ⊓ a ≤ c ⊓ a :=
  inf_le_inf h (le_refl a)

theorem inf_le_inf_left {α : Type u} [semilattice_inf α] (a : α) {b : α} {c : α} (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
  inf_le_inf (le_refl a) h

theorem le_of_inf_eq {α : Type u} [semilattice_inf α] {a : α} {b : α} (h : a ⊓ b = a) : a ≤ b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ≤ b)) (Eq.symm h))) (eq.mpr (id (propext (iff_true_intro inf_le_right))) trivial)

theorem inf_ind {α : Type u} [semilattice_inf α] [is_total α LessEq] (a : α) (b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊓ b) :=
  sup_ind a b ha hb

@[simp] theorem lt_inf_iff {α : Type u} [semilattice_inf α] [is_total α LessEq] {a : α} {b : α} {c : α} : a < b ⊓ c ↔ a < b ∧ a < c :=
  sup_lt_iff

@[simp] theorem inf_le_iff {α : Type u} [semilattice_inf α] [is_total α LessEq] {a : α} {b : α} {c : α} : b ⊓ c ≤ a ↔ b ≤ a ∨ c ≤ a :=
  le_sup_iff

@[simp] theorem inf_idem {α : Type u} [semilattice_inf α] {a : α} : a ⊓ a = a :=
  sup_idem

protected instance inf_is_idempotent {α : Type u} [semilattice_inf α] : is_idempotent α has_inf.inf :=
  is_idempotent.mk inf_idem

theorem inf_comm {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b = b ⊓ a :=
  sup_comm

protected instance inf_is_commutative {α : Type u} [semilattice_inf α] : is_commutative α has_inf.inf :=
  is_commutative.mk inf_comm

theorem inf_assoc {α : Type u} [semilattice_inf α] {a : α} {b : α} {c : α} : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  sup_assoc

protected instance inf_is_associative {α : Type u} [semilattice_inf α] : is_associative α has_inf.inf :=
  is_associative.mk inf_assoc

@[simp] theorem inf_left_idem {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ (a ⊓ b) = a ⊓ b :=
  sup_left_idem

@[simp] theorem inf_right_idem {α : Type u} [semilattice_inf α] {a : α} {b : α} : a ⊓ b ⊓ b = a ⊓ b :=
  sup_right_idem

theorem inf_left_comm {α : Type u} [semilattice_inf α] (a : α) (b : α) (c : α) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) :=
  sup_left_comm a b c

theorem forall_le_or_exists_lt_inf {α : Type u} [semilattice_inf α] (a : α) : (∀ (b : α), a ≤ b) ∨ ∃ (b : α), b < a :=
  forall_le_or_exists_lt_sup a

theorem semilattice_inf.ext_inf {α : Type u_1} {A : semilattice_inf α} {B : semilattice_inf α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) (x : α) (y : α) : x ⊓ y = x ⊓ y := sorry

theorem semilattice_inf.ext {α : Type u_1} {A : semilattice_inf α} {B : semilattice_inf α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-! ### Lattices -/

/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
class lattice (α : Type u) 
extends semilattice_sup α, semilattice_inf α
where

protected instance order_dual.lattice (α : Type u_1) [lattice α] : lattice (order_dual α) :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

/- Distributivity laws -/

/- TODO: better names? -/

theorem sup_inf_le {α : Type u} [lattice α] {a : α} {b : α} {c : α} : a ⊔ b ⊓ c ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
  le_inf (sup_le_sup_left inf_le_left a) (sup_le_sup_left inf_le_right a)

theorem le_inf_sup {α : Type u} [lattice α] {a : α} {b : α} {c : α} : a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c) :=
  sup_le (inf_le_inf_left a le_sup_left) (inf_le_inf_left a le_sup_right)

theorem inf_sup_self {α : Type u} [lattice α] {a : α} {b : α} : a ⊓ (a ⊔ b) = a :=
  eq.mpr (id (Eq.trans (propext inf_eq_left) (propext (iff_true_intro le_sup_left)))) trivial

theorem sup_inf_self {α : Type u} [lattice α] {a : α} {b : α} : a ⊔ a ⊓ b = a :=
  eq.mpr (id (Eq.trans (propext sup_eq_left) (propext (iff_true_intro inf_le_left)))) trivial

theorem lattice.ext {α : Type u_1} {A : lattice α} {B : lattice α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-- A distributive lattice is a lattice that satisfies any of four
  equivalent distribution properties (of sup over inf or inf over sup,
  on the left or right). A classic example of a distributive lattice
  is the lattice of subsets of a set, and in fact this example is
  generic in the sense that every distributive lattice is realizable
  as a sublattice of a powerset lattice. -/
class distrib_lattice (α : Type u_1) 
extends lattice α
where
  le_sup_inf : ∀ (x y z : α), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

theorem le_sup_inf {α : Type u} [distrib_lattice α] {x : α} {y : α} {z : α} : (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  distrib_lattice.le_sup_inf

theorem sup_inf_left {α : Type u} [distrib_lattice α] {x : α} {y : α} {z : α} : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z) :=
  le_antisymm sup_inf_le le_sup_inf

theorem sup_inf_right {α : Type u} [distrib_lattice α] {x : α} {y : α} {z : α} : y ⊓ z ⊔ x = (y ⊔ x) ⊓ (z ⊔ x) := sorry

theorem inf_sup_left {α : Type u} [distrib_lattice α] {x : α} {y : α} {z : α} : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z := sorry

protected instance order_dual.distrib_lattice (α : Type u_1) [distrib_lattice α] : distrib_lattice (order_dual α) :=
  distrib_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    sorry

theorem inf_sup_right {α : Type u} [distrib_lattice α] {x : α} {y : α} {z : α} : (y ⊔ z) ⊓ x = y ⊓ x ⊔ z ⊓ x := sorry

theorem le_of_inf_le_sup_le {α : Type u} [distrib_lattice α] {x : α} {y : α} {z : α} (h₁ : x ⊓ z ≤ y ⊓ z) (h₂ : x ⊔ z ≤ y ⊔ z) : x ≤ y := sorry

theorem eq_of_inf_eq_sup_eq {α : Type u} [distrib_lattice α] {a : α} {b : α} {c : α} (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
  le_antisymm (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
    (le_of_inf_le_sup_le (le_of_eq (Eq.symm h₁)) (le_of_eq (Eq.symm h₂)))

/-!
### Lattices derived from linear orders
-/

protected instance lattice_of_linear_order {α : Type u} [o : linear_order α] : lattice α :=
  lattice.mk max linear_order.le linear_order.lt linear_order.le_refl linear_order.le_trans linear_order.le_antisymm
    le_max_left le_max_right sorry min min_le_left min_le_right sorry

theorem sup_eq_max {α : Type u} [linear_order α] {x : α} {y : α} : x ⊔ y = max x y :=
  rfl

theorem inf_eq_min {α : Type u} [linear_order α] {x : α} {y : α} : x ⊓ y = min x y :=
  rfl

protected instance distrib_lattice_of_linear_order {α : Type u} [o : linear_order α] : distrib_lattice α :=
  distrib_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    sorry

protected instance nat.distrib_lattice : distrib_lattice ℕ :=
  Mathlib.distrib_lattice_of_linear_order

namespace monotone


theorem le_map_sup {α : Type u} {β : Type v} [semilattice_sup α] [semilattice_sup β] {f : α → β} (h : monotone f) (x : α) (y : α) : f x ⊔ f y ≤ f (x ⊔ y) :=
  sup_le (h le_sup_left) (h le_sup_right)

theorem map_sup {α : Type u} {β : Type v} [semilattice_sup α] [is_total α LessEq] [semilattice_sup β] {f : α → β} (hf : monotone f) (x : α) (y : α) : f (x ⊔ y) = f x ⊔ f y := sorry

theorem map_inf_le {α : Type u} {β : Type v} [semilattice_inf α] [semilattice_inf β] {f : α → β} (h : monotone f) (x : α) (y : α) : f (x ⊓ y) ≤ f x ⊓ f y :=
  le_inf (h inf_le_left) (h inf_le_right)

theorem map_inf {α : Type u} {β : Type v} [semilattice_inf α] [is_total α LessEq] [semilattice_inf β] {f : α → β} (hf : monotone f) (x : α) (y : α) : f (x ⊓ y) = f x ⊓ f y :=
  map_sup (monotone.order_dual hf) x y

end monotone


namespace prod


protected instance has_sup (α : Type u) (β : Type v) [has_sup α] [has_sup β] : has_sup (α × β) :=
  has_sup.mk fun (p q : α × β) => (fst p ⊔ fst q, snd p ⊔ snd q)

protected instance has_inf (α : Type u) (β : Type v) [has_inf α] [has_inf β] : has_inf (α × β) :=
  has_inf.mk fun (p q : α × β) => (fst p ⊓ fst q, snd p ⊓ snd q)

protected instance semilattice_sup (α : Type u) (β : Type v) [semilattice_sup α] [semilattice_sup β] : semilattice_sup (α × β) :=
  semilattice_sup.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance semilattice_inf (α : Type u) (β : Type v) [semilattice_inf α] [semilattice_inf β] : semilattice_inf (α × β) :=
  semilattice_inf.mk has_inf.inf partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance lattice (α : Type u) (β : Type v) [lattice α] [lattice β] : lattice (α × β) :=
  lattice.mk semilattice_sup.sup semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance distrib_lattice (α : Type u) (β : Type v) [distrib_lattice α] [distrib_lattice β] : distrib_lattice (α × β) :=
  distrib_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    sorry

end prod


namespace subtype


/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property. -/
protected def semilattice_sup {α : Type u} [semilattice_sup α] {P : α → Prop} (Psup : ∀ {x y : α}, P x → P y → P (x ⊔ y)) : semilattice_sup (Subtype fun (x : α) => P x) :=
  semilattice_sup.mk (fun (x y : Subtype fun (x : α) => P x) => { val := val x ⊔ val y, property := sorry })
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property. -/
protected def semilattice_inf {α : Type u} [semilattice_inf α] {P : α → Prop} (Pinf : ∀ {x y : α}, P x → P y → P (x ⊓ y)) : semilattice_inf (Subtype fun (x : α) => P x) :=
  semilattice_inf.mk (fun (x y : Subtype fun (x : α) => P x) => { val := val x ⊓ val y, property := sorry })
    partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

/-- A subtype forms a lattice if `⊔` and `⊓` preserve the property. -/
protected def lattice {α : Type u} [lattice α] {P : α → Prop} (Psup : ∀ {x y : α}, P x → P y → P (x ⊔ y)) (Pinf : ∀ {x y : α}, P x → P y → P (x ⊓ y)) : lattice (Subtype fun (x : α) => P x) :=
  lattice.mk semilattice_sup.sup semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

