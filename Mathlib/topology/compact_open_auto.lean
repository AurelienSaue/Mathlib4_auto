/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Type of continuous maps and the compact-open topology on them.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.subset_properties
import Mathlib.topology.continuous_map
import Mathlib.tactic.tidy
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

namespace continuous_map


def compact_open.gen {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    (s : set α) (u : set β) : set (continuous_map α β) :=
  set_of fun (f : continuous_map α β) => ⇑f '' s ⊆ u

-- The compact-open topology on the space of continuous maps α → β.

protected instance compact_open {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] : topological_space (continuous_map α β) :=
  topological_space.generate_from
    (set_of
      fun (m : set (continuous_map α β)) =>
        ∃ (s : set α), ∃ (hs : is_compact s), ∃ (u : set β), ∃ (hu : is_open u), m = sorry)

def induced {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α] [topological_space β]
    [topological_space γ] {g : β → γ} (hg : continuous g) (f : continuous_map α β) :
    continuous_map α γ :=
  mk (g ∘ ⇑f)

/-- C(α, -) is a functor. -/
theorem continuous_induced {α : Type u_1} {β : Type u_2} {γ : Type u_3} [topological_space α]
    [topological_space β] [topological_space γ] {g : β → γ} (hg : continuous g) :
    continuous (induced hg) :=
  sorry

def ev (α : Type u_1) (β : Type u_2) [topological_space α] [topological_space β]
    (p : continuous_map α β × α) : β :=
  coe_fn (prod.fst p) (prod.snd p)

-- The evaluation map C(α, β) × α → β is continuous if α is locally compact.

theorem continuous_ev {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [locally_compact_space α] : continuous (ev α β) :=
  sorry

def coev (α : Type u_1) (β : Type u_2) [topological_space α] [topological_space β] (b : β) :
    continuous_map α (β × α) :=
  mk fun (a : α) => (b, a)

theorem image_coev {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] {y : β}
    (s : set α) : ⇑(coev α β y) '' s = set.prod (singleton y) s :=
  sorry

-- The coevaluation map β → C(α, β × α) is continuous (always).

theorem continuous_coev {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β] :
    continuous (coev α β) :=
  sorry

end Mathlib