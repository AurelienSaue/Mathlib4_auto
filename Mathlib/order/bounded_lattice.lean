/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines bounded lattice type class hierarchy.

Includes the Prop and fun instances.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.lattice
import Mathlib.data.option.basic
import Mathlib.tactic.pi_instances
import Mathlib.logic.nontrivial
import Mathlib.PostPort

universes u l v u_1 u_2 

namespace Mathlib

/-- Typeclass for the `⊤` (`\top`) notation -/
/-- Typeclass for the `⊥` (`\bot`) notation -/
class has_top (α : Type u) 
where
  top : α

class has_bot (α : Type u) 
where
  bot : α

notation:1024 "⊤" => Mathlib.has_top.top

notation:1024 "⊥" => Mathlib.has_bot.bot

/-- An `order_top` is a partial order with a maximal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_top (α : Type u) 
extends has_top α, partial_order α
where
  le_top : ∀ (a : α), a ≤ ⊤

@[simp] theorem le_top {α : Type u} [order_top α] {a : α} : a ≤ ⊤ :=
  order_top.le_top a

theorem top_unique {α : Type u} [order_top α] {a : α} (h : ⊤ ≤ a) : a = ⊤ :=
  le_antisymm le_top h

-- TODO: delete in favor of the next?

theorem eq_top_iff {α : Type u} [order_top α] {a : α} : a = ⊤ ↔ ⊤ ≤ a :=
  { mp := fun (eq : a = ⊤) => Eq.symm eq ▸ le_refl ⊤, mpr := top_unique }

@[simp] theorem top_le_iff {α : Type u} [order_top α] {a : α} : ⊤ ≤ a ↔ a = ⊤ :=
  { mp := top_unique, mpr := fun (h : a = ⊤) => Eq.symm h ▸ le_refl ⊤ }

@[simp] theorem not_top_lt {α : Type u} [order_top α] {a : α} : ¬⊤ < a :=
  fun (h : ⊤ < a) => lt_irrefl a (lt_of_le_of_lt le_top h)

theorem eq_top_mono {α : Type u} [order_top α] {a : α} {b : α} (h : a ≤ b) (h₂ : a = ⊤) : b = ⊤ :=
  iff.mp top_le_iff (h₂ ▸ h)

theorem lt_top_iff_ne_top {α : Type u} [order_top α] {a : α} : a < ⊤ ↔ a ≠ ⊤ := sorry

theorem ne_top_of_lt {α : Type u} [order_top α] {a : α} {b : α} (h : a < b) : a ≠ ⊤ :=
  iff.mp lt_top_iff_ne_top (lt_of_lt_of_le h le_top)

theorem ne_top_of_le_ne_top {α : Type u} [order_top α] {a : α} {b : α} (hb : b ≠ ⊤) (hab : a ≤ b) : a ≠ ⊤ :=
  fun (ha : a = ⊤) => hb (top_unique (ha ▸ hab))

theorem strict_mono.top_preimage_top' {α : Type u} {β : Type v} [linear_order α] [order_top β] {f : α → β} (H : strict_mono f) {a : α} (h_top : f a = ⊤) (x : α) : x ≤ a :=
  strict_mono.top_preimage_top H (fun (p : β) => eq.mpr (id (Eq._oldrec (Eq.refl (p ≤ f a)) h_top)) le_top) x

theorem order_top.ext_top {α : Type u_1} {A : order_top α} {B : order_top α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : ⊤ = ⊤ :=
  top_unique (eq.mpr (id (Eq._oldrec (Eq.refl (⊤ ≤ ⊤)) (Eq.symm (propext (H ⊤ ⊤))))) le_top)

theorem order_top.ext {α : Type u_1} {A : order_top α} {B : order_top α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-- An `order_bot` is a partial order with a minimal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_bot (α : Type u) 
extends has_bot α, partial_order α
where
  bot_le : ∀ (a : α), ⊥ ≤ a

@[simp] theorem bot_le {α : Type u} [order_bot α] {a : α} : ⊥ ≤ a :=
  order_bot.bot_le a

theorem bot_unique {α : Type u} [order_bot α] {a : α} (h : a ≤ ⊥) : a = ⊥ :=
  le_antisymm h bot_le

-- TODO: delete?

theorem eq_bot_iff {α : Type u} [order_bot α] {a : α} : a = ⊥ ↔ a ≤ ⊥ :=
  { mp := fun (eq : a = ⊥) => Eq.symm eq ▸ le_refl ⊥, mpr := bot_unique }

@[simp] theorem le_bot_iff {α : Type u} [order_bot α] {a : α} : a ≤ ⊥ ↔ a = ⊥ :=
  { mp := bot_unique, mpr := fun (h : a = ⊥) => Eq.symm h ▸ le_refl ⊥ }

@[simp] theorem not_lt_bot {α : Type u} [order_bot α] {a : α} : ¬a < ⊥ :=
  fun (h : a < ⊥) => lt_irrefl a (lt_of_lt_of_le h bot_le)

theorem ne_bot_of_le_ne_bot {α : Type u} [order_bot α] {a : α} {b : α} (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
  fun (ha : a = ⊥) => hb (bot_unique (ha ▸ hab))

theorem eq_bot_mono {α : Type u} [order_bot α] {a : α} {b : α} (h : a ≤ b) (h₂ : b = ⊥) : a = ⊥ :=
  iff.mp le_bot_iff (h₂ ▸ h)

theorem bot_lt_iff_ne_bot {α : Type u} [order_bot α] {a : α} : ⊥ < a ↔ a ≠ ⊥ := sorry

theorem ne_bot_of_gt {α : Type u} [order_bot α] {a : α} {b : α} (h : a < b) : b ≠ ⊥ :=
  iff.mp bot_lt_iff_ne_bot (lt_of_le_of_lt bot_le h)

theorem strict_mono.bot_preimage_bot' {α : Type u} {β : Type v} [linear_order α] [order_bot β] {f : α → β} (H : strict_mono f) {a : α} (h_bot : f a = ⊥) (x : α) : a ≤ x :=
  strict_mono.bot_preimage_bot H (fun (p : β) => eq.mpr (id (Eq._oldrec (Eq.refl (f a ≤ p)) h_bot)) bot_le) x

theorem order_bot.ext_bot {α : Type u_1} {A : order_bot α} {B : order_bot α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : ⊥ = ⊥ :=
  bot_unique (eq.mpr (id (Eq._oldrec (Eq.refl (⊥ ≤ ⊥)) (Eq.symm (propext (H ⊥ ⊥))))) bot_le)

theorem order_bot.ext {α : Type u_1} {A : order_bot α} {B : order_bot α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-- A `semilattice_sup_top` is a semilattice with top and join. -/
class semilattice_sup_top (α : Type u) 
extends semilattice_sup α, order_top α
where

@[simp] theorem top_sup_eq {α : Type u} [semilattice_sup_top α] {a : α} : ⊤ ⊔ a = ⊤ :=
  sup_of_le_left le_top

@[simp] theorem sup_top_eq {α : Type u} [semilattice_sup_top α] {a : α} : a ⊔ ⊤ = ⊤ :=
  sup_of_le_right le_top

/-- A `semilattice_sup_bot` is a semilattice with bottom and join. -/
class semilattice_sup_bot (α : Type u) 
extends order_bot α, semilattice_sup α
where

@[simp] theorem bot_sup_eq {α : Type u} [semilattice_sup_bot α] {a : α} : ⊥ ⊔ a = a :=
  sup_of_le_right bot_le

@[simp] theorem sup_bot_eq {α : Type u} [semilattice_sup_bot α] {a : α} : a ⊔ ⊥ = a :=
  sup_of_le_left bot_le

@[simp] theorem sup_eq_bot_iff {α : Type u} [semilattice_sup_bot α] {a : α} {b : α} : a ⊔ b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := sorry

protected instance nat.semilattice_sup_bot : semilattice_sup_bot ℕ :=
  semilattice_sup_bot.mk 0 distrib_lattice.le distrib_lattice.lt distrib_lattice.le_refl distrib_lattice.le_trans
    distrib_lattice.le_antisymm nat.zero_le distrib_lattice.sup distrib_lattice.le_sup_left distrib_lattice.le_sup_right
    distrib_lattice.sup_le

/-- A `semilattice_inf_top` is a semilattice with top and meet. -/
class semilattice_inf_top (α : Type u) 
extends semilattice_inf α, order_top α
where

@[simp] theorem top_inf_eq {α : Type u} [semilattice_inf_top α] {a : α} : ⊤ ⊓ a = a :=
  inf_of_le_right le_top

@[simp] theorem inf_top_eq {α : Type u} [semilattice_inf_top α] {a : α} : a ⊓ ⊤ = a :=
  inf_of_le_left le_top

@[simp] theorem inf_eq_top_iff {α : Type u} [semilattice_inf_top α] {a : α} {b : α} : a ⊓ b = ⊤ ↔ a = ⊤ ∧ b = ⊤ := sorry

/-- A `semilattice_inf_bot` is a semilattice with bottom and meet. -/
class semilattice_inf_bot (α : Type u) 
extends order_bot α, semilattice_inf α
where

@[simp] theorem bot_inf_eq {α : Type u} [semilattice_inf_bot α] {a : α} : ⊥ ⊓ a = ⊥ :=
  inf_of_le_left bot_le

@[simp] theorem inf_bot_eq {α : Type u} [semilattice_inf_bot α] {a : α} : a ⊓ ⊥ = ⊥ :=
  inf_of_le_right bot_le

/- Bounded lattices -/

/-- A bounded lattice is a lattice with a top and bottom element,
  denoted `⊤` and `⊥` respectively. This allows for the interpretation
  of all finite suprema and infima, taking `inf ∅ = ⊤` and `sup ∅ = ⊥`. -/
class bounded_lattice (α : Type u) 
extends order_bot α, order_top α, lattice α
where

protected instance semilattice_inf_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_top α :=
  semilattice_inf_top.mk bounded_lattice.top bounded_lattice.le bounded_lattice.lt bounded_lattice.le_refl
    bounded_lattice.le_trans bounded_lattice.le_antisymm sorry bounded_lattice.inf bounded_lattice.inf_le_left
    bounded_lattice.inf_le_right bounded_lattice.le_inf

protected instance semilattice_inf_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_bot α :=
  semilattice_inf_bot.mk bounded_lattice.bot bounded_lattice.le bounded_lattice.lt bounded_lattice.le_refl
    bounded_lattice.le_trans bounded_lattice.le_antisymm sorry bounded_lattice.inf bounded_lattice.inf_le_left
    bounded_lattice.inf_le_right bounded_lattice.le_inf

protected instance semilattice_sup_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_top α :=
  semilattice_sup_top.mk bounded_lattice.top bounded_lattice.le bounded_lattice.lt bounded_lattice.le_refl
    bounded_lattice.le_trans bounded_lattice.le_antisymm sorry bounded_lattice.sup bounded_lattice.le_sup_left
    bounded_lattice.le_sup_right bounded_lattice.sup_le

protected instance semilattice_sup_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_bot α :=
  semilattice_sup_bot.mk bounded_lattice.bot bounded_lattice.le bounded_lattice.lt bounded_lattice.le_refl
    bounded_lattice.le_trans bounded_lattice.le_antisymm sorry bounded_lattice.sup bounded_lattice.le_sup_left
    bounded_lattice.le_sup_right bounded_lattice.sup_le

theorem bounded_lattice.ext {α : Type u_1} {A : bounded_lattice α} {B : bounded_lattice α} (H : ∀ (x y : α), x ≤ y ↔ x ≤ y) : A = B := sorry

/-- A bounded distributive lattice is exactly what it sounds like. -/
class bounded_distrib_lattice (α : Type u_1) 
extends distrib_lattice α, bounded_lattice α
where

theorem inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c := sorry

/- Prop instance -/

protected instance bounded_distrib_lattice_Prop : bounded_distrib_lattice Prop :=
  bounded_distrib_lattice.mk Or (fun (a b : Prop) => a → b) (distrib_lattice.lt._default fun (a b : Prop) => a → b) sorry
    sorry sorry Or.inl Or.inr sorry And and.left and.right sorry sorry True sorry False false.elim

protected instance Prop.linear_order : linear_order Prop :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry (classical.dec_rel LessEq)
    Mathlib.decidable_eq_of_decidable_le Mathlib.decidable_lt_of_decidable_le

@[simp] theorem le_iff_imp {p : Prop} {q : Prop} : p ≤ q ↔ p → q :=
  iff.rfl

theorem monotone_and {α : Type u} [preorder α] {p : α → Prop} {q : α → Prop} (m_p : monotone p) (m_q : monotone q) : monotone fun (x : α) => p x ∧ q x :=
  fun (a b : α) (h : a ≤ b) => and.imp (m_p h) (m_q h)

-- Note: by finish [monotone] doesn't work

theorem monotone_or {α : Type u} [preorder α] {p : α → Prop} {q : α → Prop} (m_p : monotone p) (m_q : monotone q) : monotone fun (x : α) => p x ∨ q x :=
  fun (a b : α) (h : a ≤ b) => or.imp (m_p h) (m_q h)

protected instance pi.order_bot {α : Type u_1} {β : α → Type u_2} [(a : α) → order_bot (β a)] : order_bot ((a : α) → β a) :=
  order_bot.mk (fun (_x : α) => ⊥) partial_order.le partial_order.lt sorry sorry sorry sorry

/- Function lattices -/

protected instance pi.has_sup {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_sup (α i)] : has_sup ((i : ι) → α i) :=
  has_sup.mk fun (f g : (i : ι) → α i) (i : ι) => f i ⊔ g i

@[simp] theorem sup_apply {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_sup (α i)] (f : (i : ι) → α i) (g : (i : ι) → α i) (i : ι) : has_sup.sup f g i = f i ⊔ g i :=
  rfl

protected instance pi.has_inf {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_inf (α i)] : has_inf ((i : ι) → α i) :=
  has_inf.mk fun (f g : (i : ι) → α i) (i : ι) => f i ⊓ g i

@[simp] theorem inf_apply {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_inf (α i)] (f : (i : ι) → α i) (g : (i : ι) → α i) (i : ι) : has_inf.inf f g i = f i ⊓ g i :=
  rfl

protected instance pi.has_bot {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_bot (α i)] : has_bot ((i : ι) → α i) :=
  has_bot.mk fun (i : ι) => ⊥

@[simp] theorem bot_apply {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_bot (α i)] (i : ι) : ⊥ = ⊥ :=
  rfl

protected instance pi.has_top {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_top (α i)] : has_top ((i : ι) → α i) :=
  has_top.mk fun (i : ι) => ⊤

@[simp] theorem top_apply {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → has_top (α i)] (i : ι) : ⊤ = ⊤ :=
  rfl

protected instance pi.semilattice_sup {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → semilattice_sup (α i)] : semilattice_sup ((i : ι) → α i) :=
  semilattice_sup.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance pi.semilattice_inf {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → semilattice_inf (α i)] : semilattice_inf ((i : ι) → α i) :=
  semilattice_inf.mk has_inf.inf partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry

protected instance pi.semilattice_inf_bot {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → semilattice_inf_bot (α i)] : semilattice_inf_bot ((i : ι) → α i) :=
  semilattice_inf_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry has_inf.inf sorry sorry sorry

protected instance pi.semilattice_inf_top {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → semilattice_inf_top (α i)] : semilattice_inf_top ((i : ι) → α i) :=
  semilattice_inf_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry has_inf.inf sorry sorry sorry

protected instance pi.semilattice_sup_bot {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → semilattice_sup_bot (α i)] : semilattice_sup_bot ((i : ι) → α i) :=
  semilattice_sup_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry has_sup.sup sorry sorry sorry

protected instance pi.semilattice_sup_top {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → semilattice_sup_top (α i)] : semilattice_sup_top ((i : ι) → α i) :=
  semilattice_sup_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry has_sup.sup sorry sorry sorry

protected instance pi.lattice {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → lattice (α i)] : lattice ((i : ι) → α i) :=
  lattice.mk semilattice_sup.sup semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

protected instance pi.bounded_lattice {ι : Type u_1} {α : ι → Type u_2} [(i : ι) → bounded_lattice (α i)] : bounded_lattice ((i : ι) → α i) :=
  bounded_lattice.mk semilattice_sup_top.sup semilattice_sup_top.le semilattice_sup_top.lt sorry sorry sorry sorry sorry
    sorry semilattice_inf_bot.inf sorry sorry sorry semilattice_sup_top.top sorry semilattice_inf_bot.bot sorry

theorem eq_bot_of_bot_eq_top {α : Type u_1} [bounded_lattice α] (hα : ⊥ = ⊤) (x : α) : x = ⊥ :=
  eq_bot_mono le_top (Eq.symm hα)

theorem eq_top_of_bot_eq_top {α : Type u_1} [bounded_lattice α] (hα : ⊥ = ⊤) (x : α) : x = ⊤ :=
  eq_top_mono bot_le hα

theorem subsingleton_of_top_le_bot {α : Type u_1} [bounded_lattice α] (h : ⊤ ≤ ⊥) : subsingleton α :=
  subsingleton.intro
    fun (a b : α) => le_antisymm (le_trans le_top (le_trans h bot_le)) (le_trans le_top (le_trans h bot_le))

theorem subsingleton_of_bot_eq_top {α : Type u_1} [bounded_lattice α] (hα : ⊥ = ⊤) : subsingleton α :=
  subsingleton_of_top_le_bot (ge_of_eq hα)

theorem subsingleton_iff_bot_eq_top {α : Type u_1} [bounded_lattice α] : ⊥ = ⊤ ↔ subsingleton α :=
  { mp := subsingleton_of_bot_eq_top, mpr := fun (h : subsingleton α) => subsingleton.elim ⊥ ⊤ }

/-- Attach `⊥` to a type. -/
def with_bot (α : Type u_1) :=
  Option α

namespace with_bot


protected instance has_coe_t {α : Type u} : has_coe_t α (with_bot α) :=
  has_coe_t.mk some

protected instance has_bot {α : Type u} : has_bot (with_bot α) :=
  has_bot.mk none

protected instance inhabited {α : Type u} : Inhabited (with_bot α) :=
  { default := ⊥ }

theorem none_eq_bot {α : Type u} : none = ⊥ :=
  rfl

theorem some_eq_coe {α : Type u} (a : α) : some a = ↑a :=
  rfl

/-- Recursor for `with_bot` using the preferred forms `⊥` and `↑a`. -/
def rec_bot_coe {α : Type u} {C : with_bot α → Sort u_1} (h₁ : C ⊥) (h₂ : (a : α) → C ↑a) (n : with_bot α) : C n :=
  Option.rec h₁ h₂

theorem coe_eq_coe {α : Type u} {a : α} {b : α} : ↑a = ↑b ↔ a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑a = ↑b ↔ a = b)) (Eq.symm (option.some.inj_eq a b)))) (iff.refl (↑a = ↑b))

protected instance has_lt {α : Type u} [HasLess α] : HasLess (with_bot α) :=
  { Less := fun (o₁ o₂ : Option α) => ∃ (b : α), ∃ (H : b ∈ o₂), ∀ (a : α), a ∈ o₁ → a < b }

@[simp] theorem some_lt_some {α : Type u} [HasLess α] {a : α} {b : α} : some a < some b ↔ a < b := sorry

theorem bot_lt_some {α : Type u} [HasLess α] (a : α) : ⊥ < some a :=
  Exists.intro a (Exists.intro rfl fun (b : α) (hb : b ∈ ⊥) => false.elim (option.not_mem_none b hb))

theorem bot_lt_coe {α : Type u} [HasLess α] (a : α) : ⊥ < ↑a :=
  bot_lt_some a

protected instance preorder {α : Type u} [preorder α] : preorder (with_bot α) :=
  preorder.mk (fun (o₁ o₂ : Option α) => ∀ (a : α) (H : a ∈ o₁), ∃ (b : α), ∃ (H : b ∈ o₂), a ≤ b) Less sorry sorry

protected instance partial_order {α : Type u} [partial_order α] : partial_order (with_bot α) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

protected instance order_bot {α : Type u} [partial_order α] : order_bot (with_bot α) :=
  order_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry

@[simp] theorem coe_le_coe {α : Type u} [preorder α] {a : α} {b : α} : ↑a ≤ ↑b ↔ a ≤ b := sorry

@[simp] theorem some_le_some {α : Type u} [preorder α] {a : α} {b : α} : some a ≤ some b ↔ a ≤ b :=
  coe_le_coe

theorem coe_le {α : Type u} [partial_order α] {a : α} {b : α} {o : Option α} : b ∈ o → (↑a ≤ o ↔ a ≤ b) := sorry

theorem coe_lt_coe {α : Type u} [partial_order α] {a : α} {b : α} : ↑a < ↑b ↔ a < b :=
  some_lt_some

theorem le_coe_get_or_else {α : Type u} [preorder α] (a : with_bot α) (b : α) : a ≤ ↑(option.get_or_else a b) := sorry

@[simp] theorem get_or_else_bot {α : Type u} (a : α) : option.get_or_else ⊥ a = a :=
  rfl

theorem get_or_else_bot_le_iff {α : Type u} [order_bot α] {a : with_bot α} {b : α} : option.get_or_else a ⊥ ≤ b ↔ a ≤ ↑b := sorry

protected instance decidable_le {α : Type u} [preorder α] [DecidableRel LessEq] : DecidableRel LessEq :=
  sorry

protected instance decidable_lt {α : Type u} [HasLess α] [DecidableRel Less] : DecidableRel Less :=
  sorry

protected instance linear_order {α : Type u} [linear_order α] : linear_order (with_bot α) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry with_bot.decidable_le
    Mathlib.decidable_eq_of_decidable_le with_bot.decidable_lt

protected instance semilattice_sup {α : Type u} [semilattice_sup α] : semilattice_sup_bot (with_bot α) :=
  semilattice_sup_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry (option.lift_or_get has_sup.sup)
    sorry sorry sorry

protected instance semilattice_inf {α : Type u} [semilattice_inf α] : semilattice_inf_bot (with_bot α) :=
  semilattice_inf_bot.mk order_bot.bot order_bot.le order_bot.lt sorry sorry sorry sorry
    (fun (o₁ o₂ : with_bot α) => option.bind o₁ fun (a : α) => option.map (fun (b : α) => a ⊓ b) o₂) sorry sorry sorry

protected instance lattice {α : Type u} [lattice α] : lattice (with_bot α) :=
  lattice.mk semilattice_sup_bot.sup semilattice_sup_bot.le semilattice_sup_bot.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf_bot.inf sorry sorry sorry

theorem lattice_eq_DLO {α : Type u} [linear_order α] : Mathlib.lattice_of_linear_order = with_bot.lattice :=
  lattice.ext fun (x y : with_bot α) => iff.rfl

theorem sup_eq_max {α : Type u} [linear_order α] (x : with_bot α) (y : with_bot α) : x ⊔ y = max x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ⊔ y = max x y)) (Eq.symm sup_eq_max)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊔ y = x ⊔ y)) lattice_eq_DLO)) (Eq.refl (x ⊔ y)))

theorem inf_eq_min {α : Type u} [linear_order α] (x : with_bot α) (y : with_bot α) : x ⊓ y = min x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ⊓ y = min x y)) (Eq.symm inf_eq_min)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊓ y = x ⊓ y)) lattice_eq_DLO)) (Eq.refl (x ⊓ y)))

protected instance order_top {α : Type u} [order_top α] : order_top (with_bot α) :=
  order_top.mk (some ⊤) partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance bounded_lattice {α : Type u} [bounded_lattice α] : bounded_lattice (with_bot α) :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

theorem well_founded_lt {α : Type u} [partial_order α] (h : well_founded Less) : well_founded Less := sorry

protected instance densely_ordered {α : Type u} [partial_order α] [densely_ordered α] [no_bot_order α] : densely_ordered (with_bot α) :=
  densely_ordered.mk fun (a b : with_bot α) => sorry

end with_bot


--TODO(Mario): Construct using order dual on with_bot

/-- Attach `⊤` to a type. -/
def with_top (α : Type u_1) :=
  Option α

namespace with_top


protected instance has_coe_t {α : Type u} : has_coe_t α (with_top α) :=
  has_coe_t.mk some

protected instance has_top {α : Type u} : has_top (with_top α) :=
  has_top.mk none

protected instance inhabited {α : Type u} : Inhabited (with_top α) :=
  { default := ⊤ }

theorem none_eq_top {α : Type u} : none = ⊤ :=
  rfl

theorem some_eq_coe {α : Type u} (a : α) : some a = ↑a :=
  rfl

/-- Recursor for `with_top` using the preferred forms `⊤` and `↑a`. -/
def rec_top_coe {α : Type u} {C : with_top α → Sort u_1} (h₁ : C ⊤) (h₂ : (a : α) → C ↑a) (n : with_top α) : C n :=
  Option.rec h₁ h₂

theorem coe_eq_coe {α : Type u} {a : α} {b : α} : ↑a = ↑b ↔ a = b :=
  eq.mpr (id (Eq._oldrec (Eq.refl (↑a = ↑b ↔ a = b)) (Eq.symm (option.some.inj_eq a b)))) (iff.refl (↑a = ↑b))

@[simp] theorem top_ne_coe {α : Type u} {a : α} : ⊤ ≠ ↑a :=
  fun (ᾰ : ⊤ = ↑a) => eq.dcases_on ᾰ (fun (a_1 : some a = none) => option.no_confusion a_1) (Eq.refl ↑a) (HEq.refl ᾰ)

@[simp] theorem coe_ne_top {α : Type u} {a : α} : ↑a ≠ ⊤ :=
  fun (ᾰ : ↑a = ⊤) => eq.dcases_on ᾰ (fun (a_1 : none = some a) => option.no_confusion a_1) (Eq.refl ⊤) (HEq.refl ᾰ)

protected instance has_lt {α : Type u} [HasLess α] : HasLess (with_top α) :=
  { Less := fun (o₁ o₂ : Option α) => ∃ (b : α), ∃ (H : b ∈ o₁), ∀ (a : α), a ∈ o₂ → b < a }

protected instance has_le {α : Type u} [HasLessEq α] : HasLessEq (with_top α) :=
  { LessEq := fun (o₁ o₂ : Option α) => ∀ (a : α) (H : a ∈ o₂), ∃ (b : α), ∃ (H : b ∈ o₁), b ≤ a }

@[simp] theorem some_lt_some {α : Type u} [HasLess α] {a : α} {b : α} : some a < some b ↔ a < b := sorry

@[simp] theorem some_le_some {α : Type u} [HasLessEq α] {a : α} {b : α} : some a ≤ some b ↔ a ≤ b := sorry

@[simp] theorem le_none {α : Type u} [HasLessEq α] {a : with_top α} : a ≤ none := sorry

@[simp] theorem some_lt_none {α : Type u} [HasLess α] {a : α} : some a < none := sorry

protected instance can_lift {α : Type u} : can_lift (with_top α) α :=
  can_lift.mk coe (fun (r : with_top α) => r ≠ ⊤) sorry

protected instance preorder {α : Type u} [preorder α] : preorder (with_top α) :=
  preorder.mk (fun (o₁ o₂ : Option α) => ∀ (a : α) (H : a ∈ o₂), ∃ (b : α), ∃ (H : b ∈ o₁), b ≤ a) Less sorry sorry

protected instance partial_order {α : Type u} [partial_order α] : partial_order (with_top α) :=
  partial_order.mk preorder.le preorder.lt sorry sorry sorry

protected instance order_top {α : Type u} [partial_order α] : order_top (with_top α) :=
  order_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry

@[simp] theorem coe_le_coe {α : Type u} [partial_order α] {a : α} {b : α} : ↑a ≤ ↑b ↔ a ≤ b := sorry

theorem le_coe {α : Type u} [partial_order α] {a : α} {b : α} {o : Option α} : a ∈ o → (o ≤ ↑b ↔ a ≤ b) := sorry

theorem le_coe_iff {α : Type u} [partial_order α] {b : α} {x : with_top α} : x ≤ ↑b ↔ ∃ (a : α), x = ↑a ∧ a ≤ b := sorry

theorem coe_le_iff {α : Type u} [partial_order α] {a : α} {x : with_top α} : ↑a ≤ x ↔ ∀ (b : α), x = ↑b → a ≤ b := sorry

theorem lt_iff_exists_coe {α : Type u} [partial_order α] {a : with_top α} {b : with_top α} : a < b ↔ ∃ (p : α), a = ↑p ∧ ↑p < b := sorry

theorem coe_lt_coe {α : Type u} [partial_order α] {a : α} {b : α} : ↑a < ↑b ↔ a < b :=
  some_lt_some

theorem coe_lt_top {α : Type u} [partial_order α] (a : α) : ↑a < ⊤ :=
  some_lt_none

theorem coe_lt_iff {α : Type u} [partial_order α] {a : α} {x : with_top α} : ↑a < x ↔ ∀ (b : α), x = ↑b → a < b := sorry

theorem not_top_le_coe {α : Type u} [partial_order α] (a : α) : ¬⊤ ≤ ↑a :=
  fun (h : ⊤ ≤ ↑a) => false.elim (lt_irrefl ⊤ (lt_of_le_of_lt h (coe_lt_top a)))

protected instance decidable_le {α : Type u} [preorder α] [DecidableRel LessEq] : DecidableRel LessEq :=
  fun (x y : with_top α) => with_bot.decidable_le y x

protected instance decidable_lt {α : Type u} [HasLess α] [DecidableRel Less] : DecidableRel Less :=
  fun (x y : with_top α) => with_bot.decidable_lt y x

protected instance linear_order {α : Type u} [linear_order α] : linear_order (with_top α) :=
  linear_order.mk partial_order.le partial_order.lt sorry sorry sorry sorry with_top.decidable_le
    Mathlib.decidable_eq_of_decidable_le with_top.decidable_lt

protected instance semilattice_inf {α : Type u} [semilattice_inf α] : semilattice_inf_top (with_top α) :=
  semilattice_inf_top.mk order_top.top order_top.le order_top.lt sorry sorry sorry sorry (option.lift_or_get has_inf.inf)
    sorry sorry sorry

theorem coe_inf {α : Type u} [semilattice_inf α] (a : α) (b : α) : ↑(a ⊓ b) = ↑a ⊓ ↑b :=
  rfl

protected instance semilattice_sup {α : Type u} [semilattice_sup α] : semilattice_sup_top (with_top α) :=
  semilattice_sup_top.mk order_top.top order_top.le order_top.lt sorry sorry sorry sorry
    (fun (o₁ o₂ : with_top α) => option.bind o₁ fun (a : α) => option.map (fun (b : α) => a ⊔ b) o₂) sorry sorry sorry

theorem coe_sup {α : Type u} [semilattice_sup α] (a : α) (b : α) : ↑(a ⊔ b) = ↑a ⊔ ↑b :=
  rfl

protected instance lattice {α : Type u} [lattice α] : lattice (with_top α) :=
  lattice.mk semilattice_sup_top.sup semilattice_sup_top.le semilattice_sup_top.lt sorry sorry sorry sorry sorry sorry
    semilattice_inf_top.inf sorry sorry sorry

theorem lattice_eq_DLO {α : Type u} [linear_order α] : Mathlib.lattice_of_linear_order = with_top.lattice :=
  lattice.ext fun (x y : with_top α) => iff.rfl

theorem sup_eq_max {α : Type u} [linear_order α] (x : with_top α) (y : with_top α) : x ⊔ y = max x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ⊔ y = max x y)) (Eq.symm sup_eq_max)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊔ y = x ⊔ y)) lattice_eq_DLO)) (Eq.refl (x ⊔ y)))

theorem inf_eq_min {α : Type u} [linear_order α] (x : with_top α) (y : with_top α) : x ⊓ y = min x y :=
  eq.mpr (id (Eq._oldrec (Eq.refl (x ⊓ y = min x y)) (Eq.symm inf_eq_min)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (x ⊓ y = x ⊓ y)) lattice_eq_DLO)) (Eq.refl (x ⊓ y)))

protected instance order_bot {α : Type u} [order_bot α] : order_bot (with_top α) :=
  order_bot.mk (some ⊥) partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance bounded_lattice {α : Type u} [bounded_lattice α] : bounded_lattice (with_top α) :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

theorem well_founded_lt {α : Type u_1} [partial_order α] (h : well_founded Less) : well_founded Less := sorry

protected instance densely_ordered {α : Type u} [partial_order α] [densely_ordered α] [no_top_order α] : densely_ordered (with_top α) :=
  densely_ordered.mk fun (a b : with_top α) => sorry

theorem lt_iff_exists_coe_btwn {α : Type u} [partial_order α] [densely_ordered α] [no_top_order α] {a : with_top α} {b : with_top α} : a < b ↔ ∃ (x : α), a < ↑x ∧ ↑x < b := sorry

end with_top


namespace subtype


/-- A subtype forms a `⊔`-`⊥`-semilattice if `⊥` and `⊔` preserve the property. -/
protected def semilattice_sup_bot {α : Type u} [semilattice_sup_bot α] {P : α → Prop} (Pbot : P ⊥) (Psup : ∀ {x y : α}, P x → P y → P (x ⊔ y)) : semilattice_sup_bot (Subtype fun (x : α) => P x) :=
  semilattice_sup_bot.mk { val := ⊥, property := Pbot } semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry
    semilattice_sup.sup sorry sorry sorry

/-- A subtype forms a `⊓`-`⊥`-semilattice if `⊥` and `⊓` preserve the property. -/
protected def semilattice_inf_bot {α : Type u} [semilattice_inf_bot α] {P : α → Prop} (Pbot : P ⊥) (Pinf : ∀ {x y : α}, P x → P y → P (x ⊓ y)) : semilattice_inf_bot (Subtype fun (x : α) => P x) :=
  semilattice_inf_bot.mk { val := ⊥, property := Pbot } semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

/-- A subtype forms a `⊓`-`⊤`-semilattice if `⊤` and `⊓` preserve the property. -/
protected def semilattice_inf_top {α : Type u} [semilattice_inf_top α] {P : α → Prop} (Ptop : P ⊤) (Pinf : ∀ {x y : α}, P x → P y → P (x ⊓ y)) : semilattice_inf_top (Subtype fun (x : α) => P x) :=
  semilattice_inf_top.mk { val := ⊤, property := Ptop } semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry
    semilattice_inf.inf sorry sorry sorry

end subtype


namespace order_dual


protected instance has_top (α : Type u) [has_bot α] : has_top (order_dual α) :=
  has_top.mk ⊥

protected instance has_bot (α : Type u) [has_top α] : has_bot (order_dual α) :=
  has_bot.mk ⊤

protected instance order_top (α : Type u) [order_bot α] : order_top (order_dual α) :=
  order_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry bot_le

protected instance order_bot (α : Type u) [order_top α] : order_bot (order_dual α) :=
  order_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry le_top

protected instance semilattice_sup_top (α : Type u) [semilattice_inf_bot α] : semilattice_sup_top (order_dual α) :=
  semilattice_sup_top.mk order_top.top semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry semilattice_sup.sup
    sorry sorry sorry

protected instance semilattice_sup_bot (α : Type u) [semilattice_inf_top α] : semilattice_sup_bot (order_dual α) :=
  semilattice_sup_bot.mk order_bot.bot semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry semilattice_sup.sup
    sorry sorry sorry

protected instance semilattice_inf_top (α : Type u) [semilattice_sup_bot α] : semilattice_inf_top (order_dual α) :=
  semilattice_inf_top.mk order_top.top semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry semilattice_inf.inf
    sorry sorry sorry

protected instance semilattice_inf_bot (α : Type u) [semilattice_sup_top α] : semilattice_inf_bot (order_dual α) :=
  semilattice_inf_bot.mk order_bot.bot semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry semilattice_inf.inf
    sorry sorry sorry

protected instance bounded_lattice (α : Type u) [bounded_lattice α] : bounded_lattice (order_dual α) :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

protected instance bounded_distrib_lattice (α : Type u) [bounded_distrib_lattice α] : bounded_distrib_lattice (order_dual α) :=
  bounded_distrib_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry

end order_dual


namespace prod


protected instance has_top (α : Type u) (β : Type v) [has_top α] [has_top β] : has_top (α × β) :=
  has_top.mk (⊤, ⊤)

protected instance has_bot (α : Type u) (β : Type v) [has_bot α] [has_bot β] : has_bot (α × β) :=
  has_bot.mk (⊥, ⊥)

protected instance order_top (α : Type u) (β : Type v) [order_top α] [order_top β] : order_top (α × β) :=
  order_top.mk ⊤ partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance order_bot (α : Type u) (β : Type v) [order_bot α] [order_bot β] : order_bot (α × β) :=
  order_bot.mk ⊥ partial_order.le partial_order.lt sorry sorry sorry sorry

protected instance semilattice_sup_top (α : Type u) (β : Type v) [semilattice_sup_top α] [semilattice_sup_top β] : semilattice_sup_top (α × β) :=
  semilattice_sup_top.mk order_top.top semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry semilattice_sup.sup
    sorry sorry sorry

protected instance semilattice_inf_top (α : Type u) (β : Type v) [semilattice_inf_top α] [semilattice_inf_top β] : semilattice_inf_top (α × β) :=
  semilattice_inf_top.mk order_top.top semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry semilattice_inf.inf
    sorry sorry sorry

protected instance semilattice_sup_bot (α : Type u) (β : Type v) [semilattice_sup_bot α] [semilattice_sup_bot β] : semilattice_sup_bot (α × β) :=
  semilattice_sup_bot.mk order_bot.bot semilattice_sup.le semilattice_sup.lt sorry sorry sorry sorry semilattice_sup.sup
    sorry sorry sorry

protected instance semilattice_inf_bot (α : Type u) (β : Type v) [semilattice_inf_bot α] [semilattice_inf_bot β] : semilattice_inf_bot (α × β) :=
  semilattice_inf_bot.mk order_bot.bot semilattice_inf.le semilattice_inf.lt sorry sorry sorry sorry semilattice_inf.inf
    sorry sorry sorry

protected instance bounded_lattice (α : Type u) (β : Type v) [bounded_lattice α] [bounded_lattice β] : bounded_lattice (α × β) :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    order_top.top sorry order_bot.bot sorry

protected instance bounded_distrib_lattice (α : Type u) (β : Type v) [bounded_distrib_lattice α] [bounded_distrib_lattice β] : bounded_distrib_lattice (α × β) :=
  bounded_distrib_lattice.mk bounded_lattice.sup bounded_lattice.le bounded_lattice.lt sorry sorry sorry sorry sorry sorry
    bounded_lattice.inf sorry sorry sorry sorry bounded_lattice.top sorry bounded_lattice.bot sorry

end prod


/-- Two elements of a lattice are disjoint if their inf is the bottom element.
  (This generalizes disjoint sets, viewed as members of the subset lattice.) -/
def disjoint {α : Type u} [semilattice_inf_bot α] (a : α) (b : α) :=
  a ⊓ b ≤ ⊥

theorem disjoint.eq_bot {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} (h : disjoint a b) : a ⊓ b = ⊥ :=
  iff.mpr eq_bot_iff h

theorem disjoint_iff {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} : disjoint a b ↔ a ⊓ b = ⊥ :=
  iff.symm eq_bot_iff

theorem disjoint.comm {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} : disjoint a b ↔ disjoint b a :=
  eq.mpr (id (Eq._oldrec (Eq.refl (disjoint a b ↔ disjoint b a)) (disjoint.equations._eqn_1 a b)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ⊓ b ≤ ⊥ ↔ disjoint b a)) (disjoint.equations._eqn_1 b a)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ⊓ b ≤ ⊥ ↔ b ⊓ a ≤ ⊥)) inf_comm)) (iff.refl (b ⊓ a ≤ ⊥))))

theorem disjoint.symm {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} : disjoint a b → disjoint b a :=
  iff.mp disjoint.comm

@[simp] theorem disjoint_bot_left {α : Type u} [semilattice_inf_bot α] {a : α} : disjoint ⊥ a :=
  inf_le_left

@[simp] theorem disjoint_bot_right {α : Type u} [semilattice_inf_bot α] {a : α} : disjoint a ⊥ :=
  inf_le_right

theorem disjoint.mono {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} {c : α} {d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : disjoint b d → disjoint a c :=
  le_trans (inf_le_inf h₁ h₂)

theorem disjoint.mono_left {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} {c : α} (h : a ≤ b) : disjoint b c → disjoint a c :=
  disjoint.mono h (le_refl c)

theorem disjoint.mono_right {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} {c : α} (h : b ≤ c) : disjoint a c → disjoint a b :=
  disjoint.mono (le_refl a) h

@[simp] theorem disjoint_self {α : Type u} [semilattice_inf_bot α] {a : α} : disjoint a a ↔ a = ⊥ := sorry

theorem disjoint.ne {α : Type u} [semilattice_inf_bot α] {a : α} {b : α} (ha : a ≠ ⊥) (hab : disjoint a b) : a ≠ b := sorry

@[simp] theorem disjoint_top {α : Type u} [bounded_lattice α] {a : α} : disjoint a ⊤ ↔ a = ⊥ := sorry

@[simp] theorem top_disjoint {α : Type u} [bounded_lattice α] {a : α} : disjoint ⊤ a ↔ a = ⊥ := sorry

@[simp] theorem disjoint_sup_left {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} : disjoint (a ⊔ b) c ↔ disjoint a c ∧ disjoint b c := sorry

@[simp] theorem disjoint_sup_right {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} : disjoint a (b ⊔ c) ↔ disjoint a b ∧ disjoint a c := sorry

theorem disjoint.sup_left {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} (ha : disjoint a c) (hb : disjoint b c) : disjoint (a ⊔ b) c :=
  iff.mpr disjoint_sup_left { left := ha, right := hb }

theorem disjoint.sup_right {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} (hb : disjoint a b) (hc : disjoint a c) : disjoint a (b ⊔ c) :=
  iff.mpr disjoint_sup_right { left := hb, right := hc }

theorem disjoint.left_le_of_le_sup_right {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} (h : a ≤ b ⊔ c) (hd : disjoint a c) : a ≤ b :=
  (fun (x : a ⊓ c ≤ b ⊓ c) => le_of_inf_le_sup_le x (sup_le h le_sup_right)) (Eq.symm (iff.mp disjoint_iff hd) ▸ bot_le)

theorem disjoint.left_le_of_le_sup_left {α : Type u} [bounded_distrib_lattice α] {a : α} {b : α} {c : α} (h : a ≤ c ⊔ b) (hd : disjoint a c) : a ≤ b :=
  le_of_inf_le_sup_le (Eq.symm (iff.mp disjoint_iff hd) ▸ bot_le) (sup_comm ▸ sup_le h le_sup_left)

/-!
### `is_compl` predicate
-/

/-- Two elements `x` and `y` are complements of each other if
`x ⊔ y = ⊤` and `x ⊓ y = ⊥`. -/
structure is_compl {α : Type u} [bounded_lattice α] (x : α) (y : α) 
where
  inf_le_bot : x ⊓ y ≤ ⊥
  top_le_sup : ⊤ ≤ x ⊔ y

namespace is_compl


protected theorem disjoint {α : Type u} [bounded_lattice α] {x : α} {y : α} (h : is_compl x y) : disjoint x y :=
  inf_le_bot h

protected theorem symm {α : Type u} [bounded_lattice α] {x : α} {y : α} (h : is_compl x y) : is_compl y x :=
  mk (eq.mpr (id (Eq._oldrec (Eq.refl (y ⊓ x ≤ ⊥)) inf_comm)) (inf_le_bot h))
    (eq.mpr (id (Eq._oldrec (Eq.refl (⊤ ≤ y ⊔ x)) sup_comm)) (top_le_sup h))

theorem of_eq {α : Type u} [bounded_lattice α] {x : α} {y : α} (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : is_compl x y :=
  mk (le_of_eq h₁) (le_of_eq (Eq.symm h₂))

theorem inf_eq_bot {α : Type u} [bounded_lattice α] {x : α} {y : α} (h : is_compl x y) : x ⊓ y = ⊥ :=
  disjoint.eq_bot (is_compl.disjoint h)

theorem sup_eq_top {α : Type u} [bounded_lattice α] {x : α} {y : α} (h : is_compl x y) : x ⊔ y = ⊤ :=
  top_unique (top_le_sup h)

theorem to_order_dual {α : Type u} [bounded_lattice α] {x : α} {y : α} (h : is_compl x y) : is_compl x y :=
  mk (top_le_sup h) (inf_le_bot h)

theorem le_left_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl x y) : z ≤ x ↔ disjoint z y :=
  { mp := fun (hz : z ≤ x) => disjoint.mono_left hz (is_compl.disjoint h),
    mpr := fun (hz : disjoint z y) => le_of_inf_le_sup_le (le_trans hz bot_le) (le_trans le_top (top_le_sup h)) }

theorem le_right_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl x y) : z ≤ y ↔ disjoint z x :=
  le_left_iff (is_compl.symm h)

theorem left_le_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl x y) : x ≤ z ↔ ⊤ ≤ z ⊔ y :=
  le_left_iff (to_order_dual h)

theorem right_le_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl x y) : y ≤ z ↔ ⊤ ≤ z ⊔ x :=
  left_le_iff (is_compl.symm h)

theorem antimono {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {x' : α} {y' : α} (h : is_compl x y) (h' : is_compl x' y') (hx : x ≤ x') : y' ≤ y :=
  iff.mpr (right_le_iff h') (le_trans (top_le_sup (is_compl.symm h)) (sup_le_sup_left hx y))

theorem right_unique {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (hxy : is_compl x y) (hxz : is_compl x z) : y = z :=
  le_antisymm (antimono hxz hxy (le_refl x)) (antimono hxy hxz (le_refl x))

theorem left_unique {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (hxz : is_compl x z) (hyz : is_compl y z) : x = y :=
  right_unique (is_compl.symm hxz) (is_compl.symm hyz)

theorem sup_inf {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {x' : α} {y' : α} (h : is_compl x y) (h' : is_compl x' y') : is_compl (x ⊔ x') (y ⊓ y') := sorry

theorem inf_sup {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {x' : α} {y' : α} (h : is_compl x y) (h' : is_compl x' y') : is_compl (x ⊓ x') (y ⊔ y') :=
  is_compl.symm (sup_inf (is_compl.symm h) (is_compl.symm h'))

theorem inf_left_eq_bot_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl y z) : x ⊓ y = ⊥ ↔ x ≤ z :=
  inf_eq_bot_iff_le_compl (sup_eq_top h) (inf_eq_bot h)

theorem inf_right_eq_bot_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl y z) : x ⊓ z = ⊥ ↔ x ≤ y :=
  inf_left_eq_bot_iff (is_compl.symm h)

theorem disjoint_left_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl y z) : disjoint x y ↔ x ≤ z :=
  iff.trans disjoint_iff (inf_left_eq_bot_iff h)

theorem disjoint_right_iff {α : Type u} [bounded_distrib_lattice α] {x : α} {y : α} {z : α} (h : is_compl y z) : disjoint x z ↔ x ≤ y :=
  disjoint_left_iff (is_compl.symm h)

end is_compl


theorem is_compl_bot_top {α : Type u} [bounded_lattice α] : is_compl ⊥ ⊤ :=
  is_compl.of_eq bot_inf_eq sup_top_eq

theorem is_compl_top_bot {α : Type u} [bounded_lattice α] : is_compl ⊤ ⊥ :=
  is_compl.of_eq inf_bot_eq top_sup_eq

theorem bot_ne_top {α : Type u} [bounded_lattice α] [nontrivial α] : ⊥ ≠ ⊤ :=
  fun (H : ⊥ = ⊤) => iff.mpr not_nontrivial_iff_subsingleton (subsingleton_of_bot_eq_top H) _inst_2

theorem top_ne_bot {α : Type u} [bounded_lattice α] [nontrivial α] : ⊤ ≠ ⊥ :=
  ne.symm bot_ne_top

namespace bool


protected instance bounded_lattice : bounded_lattice Bool :=
  bounded_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    tt sorry false sorry

end bool


@[simp] theorem top_eq_tt : ⊤ = tt :=
  rfl

@[simp] theorem bot_eq_ff : ⊥ = false :=
  rfl

