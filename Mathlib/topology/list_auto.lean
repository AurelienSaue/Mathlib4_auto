/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.constructions
import Mathlib.topology.algebra.group
import Mathlib.PostPort

universes u_1 u_2 

namespace Mathlib

/-!
# Topology on lists and vectors

-/

protected instance list.topological_space {α : Type u_1} [topological_space α] :
    topological_space (List α) :=
  topological_space.mk_of_nhds (traverse nhds)

theorem nhds_list {α : Type u_1} [topological_space α] (as : List α) : nhds as = traverse nhds as :=
  sorry

@[simp] theorem nhds_nil {α : Type u_1} [topological_space α] : nhds [] = pure [] :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nhds [] = pure [])) (nhds_list [])))
    (eq.mpr (id (Eq._oldrec (Eq.refl (traverse nhds [] = pure [])) (list.traverse_nil nhds)))
      (Eq.refl (pure [])))

theorem nhds_cons {α : Type u_1} [topological_space α] (a : α) (l : List α) :
    nhds (a :: l) = List.cons <$> nhds a <*> nhds l :=
  sorry

theorem list.tendsto_cons {α : Type u_1} [topological_space α] {a : α} {l : List α} :
    filter.tendsto (fun (p : α × List α) => prod.fst p :: prod.snd p)
        (filter.prod (nhds a) (nhds l)) (nhds (a :: l)) :=
  sorry

theorem filter.tendsto.cons {β : Type u_2} [topological_space β] {α : Type u_1} {f : α → β}
    {g : α → List β} {a : filter α} {b : β} {l : List β} (hf : filter.tendsto f a (nhds b))
    (hg : filter.tendsto g a (nhds l)) :
    filter.tendsto (fun (a : α) => f a :: g a) a (nhds (b :: l)) :=
  filter.tendsto.comp list.tendsto_cons (filter.tendsto.prod_mk hf hg)

namespace list


theorem tendsto_cons_iff {α : Type u_1} [topological_space α] {β : Type u_2} {f : List α → β}
    {b : filter β} {a : α} {l : List α} :
    filter.tendsto f (nhds (a :: l)) b ↔
        filter.tendsto (fun (p : α × List α) => f (prod.fst p :: prod.snd p))
          (filter.prod (nhds a) (nhds l)) b :=
  sorry

theorem continuous_cons {α : Type u_1} [topological_space α] :
    continuous fun (x : α × List α) => prod.fst x :: prod.snd x :=
  sorry

theorem tendsto_nhds {α : Type u_1} [topological_space α] {β : Type u_2} {f : List α → β}
    {r : List α → filter β} (h_nil : filter.tendsto f (pure []) (r []))
    (h_cons :
      ∀ (l : List α) (a : α),
        filter.tendsto f (nhds l) (r l) →
          filter.tendsto (fun (p : α × List α) => f (prod.fst p :: prod.snd p))
            (filter.prod (nhds a) (nhds l)) (r (a :: l)))
    (l : List α) : filter.tendsto f (nhds l) (r l) :=
  sorry

theorem continuous_at_length {α : Type u_1} [topological_space α] (l : List α) :
    continuous_at length l :=
  sorry

theorem tendsto_insert_nth' {α : Type u_1} [topological_space α] {a : α} {n : ℕ} {l : List α} :
    filter.tendsto (fun (p : α × List α) => insert_nth n (prod.fst p) (prod.snd p))
        (filter.prod (nhds a) (nhds l)) (nhds (insert_nth n a l)) :=
  sorry

theorem tendsto_insert_nth {α : Type u_1} [topological_space α] {β : Type u_2} {n : ℕ} {a : α}
    {l : List α} {f : β → α} {g : β → List α} {b : filter β} (hf : filter.tendsto f b (nhds a))
    (hg : filter.tendsto g b (nhds l)) :
    filter.tendsto (fun (b : β) => insert_nth n (f b) (g b)) b (nhds (insert_nth n a l)) :=
  filter.tendsto.comp tendsto_insert_nth' (filter.tendsto.prod_mk hf hg)

theorem continuous_insert_nth {α : Type u_1} [topological_space α] {n : ℕ} :
    continuous fun (p : α × List α) => insert_nth n (prod.fst p) (prod.snd p) :=
  sorry

theorem tendsto_remove_nth {α : Type u_1} [topological_space α] {n : ℕ} {l : List α} :
    filter.tendsto (fun (l : List α) => remove_nth l n) (nhds l) (nhds (remove_nth l n)) :=
  sorry

theorem continuous_remove_nth {α : Type u_1} [topological_space α] {n : ℕ} :
    continuous fun (l : List α) => remove_nth l n :=
  iff.mpr continuous_iff_continuous_at fun (a : List α) => tendsto_remove_nth

theorem tendsto_sum {α : Type u_1} [topological_space α] [add_monoid α] [has_continuous_add α]
    {l : List α} : filter.tendsto sum (nhds l) (nhds (sum l)) :=
  sorry

theorem continuous_sum {α : Type u_1} [topological_space α] [add_monoid α] [has_continuous_add α] :
    continuous sum :=
  iff.mpr continuous_iff_continuous_at fun (l : List α) => tendsto_sum

end list


namespace vector


protected instance topological_space {α : Type u_1} [topological_space α] (n : ℕ) :
    topological_space (vector α n) :=
  eq.mpr sorry subtype.topological_space

theorem tendsto_cons {α : Type u_1} [topological_space α] {n : ℕ} {a : α} {l : vector α n} :
    filter.tendsto (fun (p : α × vector α n) => prod.fst p::ᵥprod.snd p)
        (filter.prod (nhds a) (nhds l)) (nhds (a::ᵥl)) :=
  sorry

theorem tendsto_insert_nth {α : Type u_1} [topological_space α] {n : ℕ} {i : fin (n + 1)} {a : α}
    {l : vector α n} :
    filter.tendsto (fun (p : α × vector α n) => insert_nth (prod.fst p) i (prod.snd p))
        (filter.prod (nhds a) (nhds l)) (nhds (insert_nth a i l)) :=
  sorry

theorem continuous_insert_nth' {α : Type u_1} [topological_space α] {n : ℕ} {i : fin (n + 1)} :
    continuous fun (p : α × vector α n) => insert_nth (prod.fst p) i (prod.snd p) :=
  sorry

theorem continuous_insert_nth {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] {n : ℕ} {i : fin (n + 1)} {f : β → α} {g : β → vector α n}
    (hf : continuous f) (hg : continuous g) : continuous fun (b : β) => insert_nth (f b) i (g b) :=
  continuous.comp continuous_insert_nth' (continuous.prod_mk hf hg)

theorem continuous_at_remove_nth {α : Type u_1} [topological_space α] {n : ℕ} {i : fin (n + 1)}
    {l : vector α (n + 1)} : continuous_at (remove_nth i) l :=
  sorry

--  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (𝓝 l) (𝓝 (remove_nth i l))

--| ⟨l, hl⟩ :=

theorem continuous_remove_nth {α : Type u_1} [topological_space α] {n : ℕ} {i : fin (n + 1)} :
    continuous (remove_nth i) :=
  sorry

end Mathlib