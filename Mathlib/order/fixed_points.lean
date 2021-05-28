/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.complete_lattice
import Mathlib.dynamics.fixed_points.basic
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# Fixed point construction on complete lattices
-/

/-- Least fixed point of a monotone function -/
/-- Greatest fixed point of a monotone function -/
def lfp {α : Type u} [complete_lattice α] (f : α → α) : α :=
  Inf (set_of fun (a : α) => f a ≤ a)

def gfp {α : Type u} [complete_lattice α] (f : α → α) : α :=
  Sup (set_of fun (a : α) => a ≤ f a)

theorem lfp_le {α : Type u} [complete_lattice α] {f : α → α} {a : α} (h : f a ≤ a) : lfp f ≤ a :=
  Inf_le h

theorem le_lfp {α : Type u} [complete_lattice α] {f : α → α} {a : α} (h : ∀ (b : α), f b ≤ b → a ≤ b) : a ≤ lfp f :=
  le_Inf h

theorem lfp_eq {α : Type u} [complete_lattice α] {f : α → α} (m : monotone f) : lfp f = f (lfp f) :=
  (fun (this : f (lfp f) ≤ lfp f) => le_antisymm (lfp_le (m this)) this)
    (le_lfp fun (b : α) (h : f b ≤ b) => le_trans (m (lfp_le h)) h)

theorem lfp_induct {α : Type u} [complete_lattice α] {f : α → α} {p : α → Prop} (m : monotone f) (step : ∀ (a : α), p a → a ≤ lfp f → p (f a)) (sup : ∀ (s : set α), (∀ (a : α), a ∈ s → p a) → p (Sup s)) : p (lfp f) := sorry

theorem monotone_lfp {α : Type u} [complete_lattice α] : monotone lfp :=
  fun (f g : α → α) (this : f ≤ g) => le_lfp fun (a : α) (this_1 : g a ≤ a) => lfp_le (le_trans (this a) this_1)

theorem le_gfp {α : Type u} [complete_lattice α] {f : α → α} {a : α} (h : a ≤ f a) : a ≤ gfp f :=
  le_Sup h

theorem gfp_le {α : Type u} [complete_lattice α] {f : α → α} {a : α} (h : ∀ (b : α), b ≤ f b → b ≤ a) : gfp f ≤ a :=
  Sup_le h

theorem gfp_eq {α : Type u} [complete_lattice α] {f : α → α} (m : monotone f) : gfp f = f (gfp f) :=
  (fun (this : gfp f ≤ f (gfp f)) => le_antisymm this (le_gfp (m this)))
    (gfp_le fun (b : α) (h : b ≤ f b) => le_trans h (m (le_gfp h)))

theorem gfp_induct {α : Type u} [complete_lattice α] {f : α → α} {p : α → Prop} (m : monotone f) (step : ∀ (a : α), p a → gfp f ≤ a → p (f a)) (inf : ∀ (s : set α), (∀ (a : α), a ∈ s → p a) → p (Inf s)) : p (gfp f) := sorry

theorem monotone_gfp {α : Type u} [complete_lattice α] : monotone gfp :=
  fun (f g : α → α) (this : f ≤ g) => gfp_le fun (a : α) (this_1 : a ≤ f a) => le_gfp (le_trans this_1 (this a))

-- Rolling rule

theorem lfp_comp {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {f : β → α} {g : α → β} (m_f : monotone f) (m_g : monotone g) : lfp (f ∘ g) = f (lfp (g ∘ f)) := sorry

theorem gfp_comp {α : Type u} {β : Type v} [complete_lattice α] [complete_lattice β] {f : β → α} {g : α → β} (m_f : monotone f) (m_g : monotone g) : gfp (f ∘ g) = f (gfp (g ∘ f)) := sorry

-- Diagonal rule

theorem lfp_lfp {α : Type u} [complete_lattice α] {h : α → α → α} (m : ∀ {a b c d : α}, a ≤ b → c ≤ d → h a c ≤ h b d) : lfp (lfp ∘ h) = lfp fun (x : α) => h x x := sorry

theorem gfp_gfp {α : Type u} [complete_lattice α] {h : α → α → α} (m : ∀ {a b c d : α}, a ≤ b → c ≤ d → h a c ≤ h b d) : gfp (gfp ∘ h) = gfp fun (x : α) => h x x := sorry

/- The complete lattice of fixed points of a function f -/

namespace fixed_points


def prev {α : Type u} [complete_lattice α] (f : α → α) (x : α) : α :=
  gfp fun (z : α) => x ⊓ f z

def next {α : Type u} [complete_lattice α] (f : α → α) (x : α) : α :=
  lfp fun (z : α) => x ⊔ f z

theorem prev_le {α : Type u} [complete_lattice α] {f : α → α} {x : α} : prev f x ≤ x :=
  gfp_le fun (z : α) (hz : z ≤ x ⊓ f z) => le_trans hz inf_le_left

theorem prev_eq {α : Type u} [complete_lattice α] {f : α → α} (hf : monotone f) {a : α} (h : f a ≤ a) : prev f a = f (prev f a) := sorry

def prev_fixed {α : Type u} [complete_lattice α] {f : α → α} (hf : monotone f) (a : α) (h : f a ≤ a) : ↥(function.fixed_points f) :=
  { val := prev f a, property := sorry }

theorem next_le {α : Type u} [complete_lattice α] {f : α → α} {x : α} : x ≤ next f x :=
  le_lfp fun (z : α) (hz : x ⊔ f z ≤ z) => le_trans le_sup_left hz

theorem next_eq {α : Type u} [complete_lattice α] {f : α → α} (hf : monotone f) {a : α} (h : a ≤ f a) : next f a = f (next f a) := sorry

def next_fixed {α : Type u} [complete_lattice α] {f : α → α} (hf : monotone f) (a : α) (h : a ≤ f a) : ↥(function.fixed_points f) :=
  { val := next f a, property := sorry }

theorem sup_le_f_of_fixed_points {α : Type u} [complete_lattice α] (f : α → α) (hf : monotone f) (x : ↥(function.fixed_points f)) (y : ↥(function.fixed_points f)) : subtype.val x ⊔ subtype.val y ≤ f (subtype.val x ⊔ subtype.val y) := sorry

theorem f_le_inf_of_fixed_points {α : Type u} [complete_lattice α] (f : α → α) (hf : monotone f) (x : ↥(function.fixed_points f)) (y : ↥(function.fixed_points f)) : f (subtype.val x ⊓ subtype.val y) ≤ subtype.val x ⊓ subtype.val y := sorry

theorem Sup_le_f_of_fixed_points {α : Type u} [complete_lattice α] (f : α → α) (hf : monotone f) (A : set α) (HA : A ⊆ function.fixed_points f) : Sup A ≤ f (Sup A) :=
  Sup_le fun (x : α) (hxA : x ∈ A) => HA hxA ▸ hf (le_Sup hxA)

theorem f_le_Inf_of_fixed_points {α : Type u} [complete_lattice α] (f : α → α) (hf : monotone f) (A : set α) (HA : A ⊆ function.fixed_points f) : f (Inf A) ≤ Inf A :=
  le_Inf fun (x : α) (hxA : x ∈ A) => HA hxA ▸ hf (Inf_le hxA)

/-- The fixed points of `f` form a complete lattice.
This cannot be an instance, since it depends on the monotonicity of `f`. -/
protected def complete_lattice {α : Type u} [complete_lattice α] (f : α → α) (hf : monotone f) : complete_lattice ↥(function.fixed_points f) :=
  complete_lattice.mk
    (fun (x y : ↥(function.fixed_points f)) =>
      next_fixed hf (subtype.val x ⊔ subtype.val y) (sup_le_f_of_fixed_points f hf x y))
    (fun (x y : ↥(function.fixed_points f)) => subtype.val x ≤ subtype.val y)
    (bounded_lattice.lt._default fun (x y : ↥(function.fixed_points f)) => subtype.val x ≤ subtype.val y) sorry sorry
    sorry sorry sorry sorry
    (fun (x y : ↥(function.fixed_points f)) =>
      prev_fixed hf (subtype.val x ⊓ subtype.val y) (f_le_inf_of_fixed_points f hf x y))
    sorry sorry sorry (prev_fixed hf ⊤ sorry) sorry (next_fixed hf ⊥ sorry) sorry
    (fun (A : set ↥(function.fixed_points f)) => next_fixed hf (Sup (subtype.val '' A)) sorry)
    (fun (A : set ↥(function.fixed_points f)) => prev_fixed hf (Inf (subtype.val '' A)) sorry) sorry sorry sorry sorry

