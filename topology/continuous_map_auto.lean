/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.topology.subset_properties
import Mathlib.topology.tactic
import PostPort

universes u_1 u_2 l u_3 

namespace Mathlib

/-!
# Continuous bundled map

In this file we define the type `continuous_map` of continuous bundled maps.
-/

/-- Bundled continuous maps. -/
structure continuous_map (α : Type u_1) (β : Type u_2) [topological_space α] [topological_space β] 
where
  to_fun : α → β
  continuous_to_fun : autoParam (continuous to_fun)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.tactic.interactive.continuity'")
    (Lean.Name.mkStr
      (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "tactic") "interactive")
      "continuity'")
    [])

namespace continuous_map


protected instance has_coe_to_fun {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] : has_coe_to_fun (continuous_map α β) :=
  has_coe_to_fun.mk (fun (x : continuous_map α β) => α → β) continuous_map.to_fun

protected theorem continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (f : continuous_map α β) : continuous ⇑f :=
  continuous_map.continuous_to_fun f

theorem coe_continuous {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : continuous_map α β} : continuous ⇑f :=
  continuous_map.continuous_to_fun f

theorem ext {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : continuous_map α β} {g : continuous_map α β} (H : ∀ (x : α), coe_fn f x = coe_fn g x) : f = g := sorry

protected instance inhabited {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] [Inhabited β] : Inhabited (continuous_map α β) :=
  { default := mk fun (_x : α) => Inhabited.default }

theorem coe_inj {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {f : continuous_map α β} {g : continuous_map α β} (h : ⇑f = ⇑g) : f = g := sorry

/-- The identity as a continuous map. -/
def id {α : Type u_1} [topological_space α] : continuous_map α α :=
  mk id

/-- The composition of continuous maps, as a continuous map. -/
def comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β] [topological_space γ] (f : continuous_map β γ) (g : continuous_map α β) : continuous_map α γ :=
  mk (⇑f ∘ ⇑g)

/-- Constant map as a continuous map -/
def const {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] (b : β) : continuous_map α β :=
  mk fun (x : α) => b

