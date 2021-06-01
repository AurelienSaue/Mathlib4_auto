/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.basic
import Mathlib.PostPort

namespace Mathlib

namespace list


/--
tfae: The Following (propositions) Are Equivalent.

The `tfae_have` and `tfae_finish` tactics can be useful in proofs with `tfae` goals.
-/
def tfae (l : List Prop) :=
  ∀ (x : Prop), x ∈ l → ∀ (y : Prop), y ∈ l → (x ↔ y)

theorem tfae_nil : tfae [] :=
  forall_mem_nil fun (x : Prop) => ∀ (y : Prop), y ∈ [] → (x ↔ y)

theorem tfae_singleton (p : Prop) : tfae [p] := sorry

theorem tfae_cons_of_mem {a : Prop} {b : Prop} {l : List Prop} (h : b ∈ l) : tfae (a :: l) ↔ (a ↔ b) ∧ tfae l := sorry

theorem tfae_cons_cons {a : Prop} {b : Prop} {l : List Prop} : tfae (a :: b :: l) ↔ (a ↔ b) ∧ tfae (b :: l) :=
  tfae_cons_of_mem (Or.inl rfl)

theorem tfae_of_forall (b : Prop) (l : List Prop) (h : ∀ (a : Prop), a ∈ l → (a ↔ b)) : tfae l :=
  fun (a₁ : Prop) (h₁ : a₁ ∈ l) (a₂ : Prop) (h₂ : a₂ ∈ l) => iff.trans (h a₁ h₁) (iff.symm (h a₂ h₂))

theorem tfae_of_cycle {a : Prop} {b : Prop} {l : List Prop} : chain (fun (_x _y : Prop) => _x → _y) a (b :: l) → (ilast' b l → a) → tfae (a :: b :: l) := sorry

theorem tfae.out {l : List Prop} (h : tfae l) (n₁ : ℕ) (n₂ : ℕ) {a : Prop} {b : Prop} (h₁ : autoParam (nth l n₁ = some a)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.refl")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive") "refl")
    [])) (h₂ : autoParam (nth l n₂ = some b)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.refl")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive") "refl")
    [])) : a ↔ b :=
  h a (nth_mem h₁) b (nth_mem h₂)

