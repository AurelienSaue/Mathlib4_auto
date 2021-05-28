/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of complete Boolean algebras.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.order.complete_lattice
import Mathlib.PostPort

universes u_1 l u w 

namespace Mathlib

/-- A complete distributive lattice is a bit stronger than the name might
  suggest; perhaps completely distributive lattice is more descriptive,
  as this class includes a requirement that the lattice join
  distribute over *arbitrary* infima, and similarly for the dual. -/
class complete_distrib_lattice (α : Type u_1) 
extends complete_lattice α
where
  infi_sup_le_sup_Inf : ∀ (a : α) (s : set α), (infi fun (b : α) => infi fun (H : b ∈ s) => a ⊔ b) ≤ a ⊔ Inf s
  inf_Sup_le_supr_inf : ∀ (a : α) (s : set α), a ⊓ Sup s ≤ supr fun (b : α) => supr fun (H : b ∈ s) => a ⊓ b

theorem sup_Inf_eq {α : Type u} [complete_distrib_lattice α] {a : α} {s : set α} : a ⊔ Inf s = infi fun (b : α) => infi fun (H : b ∈ s) => a ⊔ b :=
  le_antisymm (le_infi fun (i : α) => le_infi fun (h : i ∈ s) => sup_le_sup_left (Inf_le h) a)
    (complete_distrib_lattice.infi_sup_le_sup_Inf a s)

theorem Inf_sup_eq {α : Type u} [complete_distrib_lattice α] {b : α} {s : set α} : Inf s ⊔ b = infi fun (a : α) => infi fun (H : a ∈ s) => a ⊔ b := sorry

theorem inf_Sup_eq {α : Type u} [complete_distrib_lattice α] {a : α} {s : set α} : a ⊓ Sup s = supr fun (b : α) => supr fun (H : b ∈ s) => a ⊓ b :=
  le_antisymm (complete_distrib_lattice.inf_Sup_le_supr_inf a s)
    (supr_le fun (i : α) => supr_le fun (h : i ∈ s) => inf_le_inf_left a (le_Sup h))

theorem Sup_inf_eq {α : Type u} [complete_distrib_lattice α] {b : α} {s : set α} : Sup s ⊓ b = supr fun (a : α) => supr fun (H : a ∈ s) => a ⊓ b := sorry

theorem Inf_sup_Inf {α : Type u} [complete_distrib_lattice α] {s : set α} {t : set α} : Inf s ⊔ Inf t = infi fun (p : α × α) => infi fun (H : p ∈ set.prod s t) => prod.fst p ⊔ prod.snd p := sorry

theorem Sup_inf_Sup {α : Type u} [complete_distrib_lattice α] {s : set α} {t : set α} : Sup s ⊓ Sup t = supr fun (p : α × α) => supr fun (H : p ∈ set.prod s t) => prod.fst p ⊓ prod.snd p := sorry

protected instance complete_distrib_lattice.bounded_distrib_lattice {α : Type u} [d : complete_distrib_lattice α] : bounded_distrib_lattice α :=
  bounded_distrib_lattice.mk complete_distrib_lattice.sup complete_distrib_lattice.le complete_distrib_lattice.lt
    complete_distrib_lattice.le_refl complete_distrib_lattice.le_trans complete_distrib_lattice.le_antisymm
    complete_distrib_lattice.le_sup_left complete_distrib_lattice.le_sup_right complete_distrib_lattice.sup_le
    complete_distrib_lattice.inf complete_distrib_lattice.inf_le_left complete_distrib_lattice.inf_le_right
    complete_distrib_lattice.le_inf sorry complete_distrib_lattice.top complete_distrib_lattice.le_top
    complete_distrib_lattice.bot complete_distrib_lattice.bot_le

/-- A complete boolean algebra is a completely distributive boolean algebra. -/
class complete_boolean_algebra (α : Type u_1) 
extends boolean_algebra α, complete_distrib_lattice α
where

theorem compl_infi {α : Type u} {ι : Sort w} [complete_boolean_algebra α] {f : ι → α} : infi fᶜ = supr fun (i : ι) => f iᶜ :=
  le_antisymm (compl_le_of_compl_le (le_infi fun (i : ι) => compl_le_of_compl_le (le_supr (compl ∘ f) i)))
    (supr_le fun (i : ι) => compl_le_compl (infi_le f i))

theorem compl_supr {α : Type u} {ι : Sort w} [complete_boolean_algebra α] {f : ι → α} : supr fᶜ = infi fun (i : ι) => f iᶜ := sorry

theorem compl_Inf {α : Type u} [complete_boolean_algebra α] {s : set α} : Inf sᶜ = supr fun (i : α) => supr fun (H : i ∈ s) => iᶜ := sorry

theorem compl_Sup {α : Type u} [complete_boolean_algebra α] {s : set α} : Sup sᶜ = infi fun (i : α) => infi fun (H : i ∈ s) => iᶜ := sorry

