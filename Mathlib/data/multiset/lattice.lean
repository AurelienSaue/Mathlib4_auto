/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.finset_ops
import Mathlib.data.multiset.fold
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# Lattice operations on multisets
-/

namespace multiset


/-! ### sup -/

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
def sup {α : Type u_1} [semilattice_sup_bot α] (s : multiset α) : α :=
  fold has_sup.sup ⊥ s

@[simp] theorem sup_zero {α : Type u_1} [semilattice_sup_bot α] : sup 0 = ⊥ :=
  fold_zero has_sup.sup ⊥

@[simp] theorem sup_cons {α : Type u_1} [semilattice_sup_bot α] (a : α) (s : multiset α) : sup (a ::ₘ s) = a ⊔ sup s :=
  fold_cons_left has_sup.sup ⊥ a s

@[simp] theorem sup_singleton {α : Type u_1} [semilattice_sup_bot α] {a : α} : sup (a ::ₘ 0) = a := sorry

@[simp] theorem sup_add {α : Type u_1} [semilattice_sup_bot α] (s₁ : multiset α) (s₂ : multiset α) : sup (s₁ + s₂) = sup s₁ ⊔ sup s₂ := sorry

theorem sup_le {α : Type u_1} [semilattice_sup_bot α] {s : multiset α} {a : α} : sup s ≤ a ↔ ∀ (b : α), b ∈ s → b ≤ a := sorry

theorem le_sup {α : Type u_1} [semilattice_sup_bot α] {s : multiset α} {a : α} (h : a ∈ s) : a ≤ sup s :=
  iff.mp sup_le (le_refl (sup s)) a h

theorem sup_mono {α : Type u_1} [semilattice_sup_bot α] {s₁ : multiset α} {s₂ : multiset α} (h : s₁ ⊆ s₂) : sup s₁ ≤ sup s₂ :=
  iff.mpr sup_le fun (b : α) (hb : b ∈ s₁) => le_sup (h hb)

@[simp] theorem sup_erase_dup {α : Type u_1} [semilattice_sup_bot α] [DecidableEq α] (s : multiset α) : sup (erase_dup s) = sup s :=
  fold_erase_dup_idem has_sup.sup s ⊥

@[simp] theorem sup_ndunion {α : Type u_1} [semilattice_sup_bot α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : sup (ndunion s₁ s₂) = sup s₁ ⊔ sup s₂ := sorry

@[simp] theorem sup_union {α : Type u_1} [semilattice_sup_bot α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : sup (s₁ ∪ s₂) = sup s₁ ⊔ sup s₂ := sorry

@[simp] theorem sup_ndinsert {α : Type u_1} [semilattice_sup_bot α] [DecidableEq α] (a : α) (s : multiset α) : sup (ndinsert a s) = a ⊔ sup s := sorry

/-! ### inf -/

/-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/
def inf {α : Type u_1} [semilattice_inf_top α] (s : multiset α) : α :=
  fold has_inf.inf ⊤ s

@[simp] theorem inf_zero {α : Type u_1} [semilattice_inf_top α] : inf 0 = ⊤ :=
  fold_zero has_inf.inf ⊤

@[simp] theorem inf_cons {α : Type u_1} [semilattice_inf_top α] (a : α) (s : multiset α) : inf (a ::ₘ s) = a ⊓ inf s :=
  fold_cons_left has_inf.inf ⊤ a s

@[simp] theorem inf_singleton {α : Type u_1} [semilattice_inf_top α] {a : α} : inf (a ::ₘ 0) = a := sorry

@[simp] theorem inf_add {α : Type u_1} [semilattice_inf_top α] (s₁ : multiset α) (s₂ : multiset α) : inf (s₁ + s₂) = inf s₁ ⊓ inf s₂ := sorry

theorem le_inf {α : Type u_1} [semilattice_inf_top α] {s : multiset α} {a : α} : a ≤ inf s ↔ ∀ (b : α), b ∈ s → a ≤ b := sorry

theorem inf_le {α : Type u_1} [semilattice_inf_top α] {s : multiset α} {a : α} (h : a ∈ s) : inf s ≤ a :=
  iff.mp le_inf (le_refl (inf s)) a h

theorem inf_mono {α : Type u_1} [semilattice_inf_top α] {s₁ : multiset α} {s₂ : multiset α} (h : s₁ ⊆ s₂) : inf s₂ ≤ inf s₁ :=
  iff.mpr le_inf fun (b : α) (hb : b ∈ s₁) => inf_le (h hb)

@[simp] theorem inf_erase_dup {α : Type u_1} [semilattice_inf_top α] [DecidableEq α] (s : multiset α) : inf (erase_dup s) = inf s :=
  fold_erase_dup_idem has_inf.inf s ⊤

@[simp] theorem inf_ndunion {α : Type u_1} [semilattice_inf_top α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : inf (ndunion s₁ s₂) = inf s₁ ⊓ inf s₂ := sorry

@[simp] theorem inf_union {α : Type u_1} [semilattice_inf_top α] [DecidableEq α] (s₁ : multiset α) (s₂ : multiset α) : inf (s₁ ∪ s₂) = inf s₁ ⊓ inf s₂ := sorry

@[simp] theorem inf_ndinsert {α : Type u_1} [semilattice_inf_top α] [DecidableEq α] (a : α) (s : multiset α) : inf (ndinsert a s) = a ⊓ inf s := sorry

