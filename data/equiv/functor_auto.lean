/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.control.bifunctor
import PostPort

universes u v w 

namespace Mathlib

/-!
# Functor and bifunctors can be applied to `equiv`s.

We define
```lean
def functor.map_equiv (f : Type u → Type v) [functor f] [is_lawful_functor f] :
  α ≃ β → f α ≃ f β
```
and
```lean
def bifunctor.map_equiv (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] :
  α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/

namespace functor


/-- Apply a functor to an `equiv`. -/
def map_equiv {α : Type u} {β : Type u} (f : Type u → Type v) [Functor f] [is_lawful_functor f] (h : α ≃ β) : f α ≃ f β :=
  equiv.mk (Functor.map ⇑h) (Functor.map ⇑(equiv.symm h)) sorry sorry

@[simp] theorem map_equiv_apply {α : Type u} {β : Type u} (f : Type u → Type v) [Functor f] [is_lawful_functor f] (h : α ≃ β) (x : f α) : coe_fn (map_equiv f h) x = ⇑h <$> x :=
  rfl

@[simp] theorem map_equiv_symm_apply {α : Type u} {β : Type u} (f : Type u → Type v) [Functor f] [is_lawful_functor f] (h : α ≃ β) (y : f β) : coe_fn (equiv.symm (map_equiv f h)) y = ⇑(equiv.symm h) <$> y :=
  rfl

@[simp] theorem map_equiv_refl {α : Type u} (f : Type u → Type v) [Functor f] [is_lawful_functor f] : map_equiv f (equiv.refl α) = equiv.refl (f α) := sorry

end functor


namespace bifunctor


/-- Apply a bifunctor to a pair of `equiv`s. -/
def map_equiv {α : Type u} {β : Type u} {α' : Type v} {β' : Type v} (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' :=
  equiv.mk (bimap ⇑h ⇑h') (bimap ⇑(equiv.symm h) ⇑(equiv.symm h')) sorry sorry

@[simp] theorem map_equiv_apply {α : Type u} {β : Type u} {α' : Type v} {β' : Type v} (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] (h : α ≃ β) (h' : α' ≃ β') (x : F α α') : coe_fn (map_equiv F h h') x = bimap (⇑h) (⇑h') x :=
  rfl

@[simp] theorem map_equiv_symm_apply {α : Type u} {β : Type u} {α' : Type v} {β' : Type v} (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] (h : α ≃ β) (h' : α' ≃ β') (y : F β β') : coe_fn (equiv.symm (map_equiv F h h')) y = bimap (⇑(equiv.symm h)) (⇑(equiv.symm h')) y :=
  rfl

@[simp] theorem map_equiv_refl_refl {α : Type u} {α' : Type v} (F : Type u → Type v → Type w) [bifunctor F] [is_lawful_bifunctor F] : map_equiv F (equiv.refl α) (equiv.refl α') = equiv.refl (F α α') := sorry

