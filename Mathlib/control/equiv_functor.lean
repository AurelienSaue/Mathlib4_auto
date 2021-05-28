/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.category.default
import Mathlib.data.equiv.functor
import Mathlib.PostPort

universes u₀ u₁ l 

namespace Mathlib

/-!
# Functions functorial with respect to equivalences

An `equiv_functor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/

/--
An `equiv_functor` is only functorial with respect to equivalences.

To construct an `equiv_functor`, it suffices to supply just the function `f α → f β` from
an equivalence `α ≃ β`, and then prove the functor laws. It's then a consequence that
this function is part of an equivalence, provided by `equiv_functor.map_equiv`.
-/
class equiv_functor (f : Type u₀ → Type u₁) 
where
  map : {α β : Type u₀} → α ≃ β → f α → f β
  map_refl' : autoParam (∀ (α : Type u₀), map (equiv.refl α) = id)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  map_trans' : autoParam (∀ {α β γ : Type u₀} (k : α ≃ β) (h : β ≃ γ), map (equiv.trans k h) = map h ∘ map k)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem equiv_functor.map_refl {f : Type u₀ → Type u₁} [c : equiv_functor f] (α : Type u₀) : equiv_functor.map (equiv.refl α) = id := sorry

theorem equiv_functor.map_trans {f : Type u₀ → Type u₁} [c : equiv_functor f] {α : Type u₀} {β : Type u₀} {γ : Type u₀} (k : α ≃ β) (h : β ≃ γ) : equiv_functor.map (equiv.trans k h) = equiv_functor.map h ∘ equiv_functor.map k := sorry

namespace equiv_functor


/-- An `equiv_functor` in fact takes every equiv to an equiv. -/
def map_equiv (f : Type u₀ → Type u₁) [equiv_functor f] {α : Type u₀} {β : Type u₀} (e : α ≃ β) : f α ≃ f β :=
  equiv.mk (map e) (map (equiv.symm e)) sorry sorry

@[simp] theorem map_equiv_apply (f : Type u₀ → Type u₁) [equiv_functor f] {α : Type u₀} {β : Type u₀} (e : α ≃ β) (x : f α) : coe_fn (map_equiv f e) x = map e x :=
  rfl

theorem map_equiv_symm_apply (f : Type u₀ → Type u₁) [equiv_functor f] {α : Type u₀} {β : Type u₀} (e : α ≃ β) (y : f β) : coe_fn (equiv.symm (map_equiv f e)) y = map (equiv.symm e) y :=
  rfl

@[simp] theorem map_equiv_refl (f : Type u₀ → Type u₁) [equiv_functor f] (α : Type u₀) : map_equiv f (equiv.refl α) = equiv.refl (f α) := sorry

@[simp] theorem map_equiv_symm (f : Type u₀ → Type u₁) [equiv_functor f] {α : Type u₀} {β : Type u₀} (e : α ≃ β) : equiv.symm (map_equiv f e) = map_equiv f (equiv.symm e) :=
  equiv.ext (map_equiv_symm_apply f e)

/--
The composition of `map_equiv`s is carried over the `equiv_functor`.
For plain `functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp] theorem map_equiv_trans (f : Type u₀ → Type u₁) [equiv_functor f] {α : Type u₀} {β : Type u₀} {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) : equiv.trans (map_equiv f ab) (map_equiv f bc) = map_equiv f (equiv.trans ab bc) := sorry

protected instance of_is_lawful_functor (f : Type u₀ → Type u₁) [Functor f] [is_lawful_functor f] : equiv_functor f :=
  mk fun (α β : Type u₀) (e : α ≃ β) => Functor.map ⇑e

theorem map_equiv.injective (f : Type u₀ → Type u₁) [Applicative f] [is_lawful_applicative f] {α : Type u₀} {β : Type u₀} (h : Type u₀ → function.injective pure) : function.injective (map_equiv f) := sorry

