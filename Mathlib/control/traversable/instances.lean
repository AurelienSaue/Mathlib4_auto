/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances of `traversable` for types from the core library
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.forall2
import Mathlib.data.set.lattice
import Mathlib.control.traversable.lemmas
import Mathlib.PostPort

universes u_1 u 

namespace Mathlib

theorem option.id_traverse {α : Type u_1} (x : Option α) : option.traverse id.mk x = x :=
  option.cases_on x (Eq.refl (option.traverse id.mk none)) fun (x : α) => Eq.refl (option.traverse id.mk (some x))

theorem option.comp_traverse {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type u_1} {β : Type u} {γ : Type u} (f : β → F γ) (g : α → G β) (x : Option α) : option.traverse (functor.comp.mk ∘ Functor.map f ∘ g) x = functor.comp.mk (option.traverse f <$> option.traverse g x) := sorry

theorem option.traverse_eq_map_id {α : Type u_1} {β : Type u_1} (f : α → β) (x : Option α) : traverse (id.mk ∘ f) x = id.mk (f <$> x) :=
  option.cases_on x (Eq.refl (traverse (id.mk ∘ f) none)) fun (x : α) => Eq.refl (traverse (id.mk ∘ f) (some x))

theorem option.naturality {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u_1} {β : Type u} (f : α → F β) (x : Option α) : coe_fn η (Option β) (option.traverse f x) = option.traverse (coe_fn η β ∘ f) x := sorry

protected instance option.is_lawful_traversable : is_lawful_traversable Option :=
  is_lawful_traversable.mk option.id_traverse option.comp_traverse option.traverse_eq_map_id option.naturality

namespace list


protected theorem id_traverse {α : Type u_1} (xs : List α) : list.traverse id.mk xs = xs := sorry

protected theorem comp_traverse {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type u_1} {β : Type u} {γ : Type u} (f : β → F γ) (g : α → G β) (x : List α) : list.traverse (functor.comp.mk ∘ Functor.map f ∘ g) x = functor.comp.mk (list.traverse f <$> list.traverse g x) := sorry

protected theorem traverse_eq_map_id {α : Type u_1} {β : Type u_1} (f : α → β) (x : List α) : list.traverse (id.mk ∘ f) x = id.mk (f <$> x) := sorry

protected theorem naturality {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u_1} {β : Type u} (f : α → F β) (x : List α) : coe_fn η (List β) (list.traverse f x) = list.traverse (coe_fn η β ∘ f) x := sorry

protected instance is_lawful_traversable : is_lawful_traversable List :=
  is_lawful_traversable.mk list.id_traverse list.comp_traverse list.traverse_eq_map_id list.naturality

@[simp] theorem traverse_nil {F : Type u → Type u} [Applicative F] {α' : Type u} {β' : Type u} (f : α' → F β') : traverse f [] = pure [] :=
  rfl

@[simp] theorem traverse_cons {F : Type u → Type u} [Applicative F] {α' : Type u} {β' : Type u} (f : α' → F β') (a : α') (l : List α') : traverse f (a :: l) = (fun (_x : β') (_y : List β') => _x :: _y) <$> f a <*> traverse f l :=
  rfl

@[simp] theorem traverse_append {F : Type u → Type u} [Applicative F] {α' : Type u} {β' : Type u} (f : α' → F β') [is_lawful_applicative F] (as : List α') (bs : List α') : traverse f (as ++ bs) = append <$> traverse f as <*> traverse f bs := sorry

theorem mem_traverse {α' : Type u} {β' : Type u} {f : α' → set β'} (l : List α') (n : List β') : n ∈ traverse f l ↔ forall₂ (fun (b : β') (a : α') => b ∈ f a) n l := sorry

end list


namespace sum


protected theorem traverse_map {σ : Type u} {G : Type u → Type u} [Applicative G] {α : Type u} {β : Type u} {γ : Type u} (g : α → β) (f : β → G γ) (x : σ ⊕ α) : sum.traverse f (g <$> x) = sum.traverse (f ∘ g) x := sorry

protected theorem id_traverse {σ : Type u_1} {α : Type u_1} (x : σ ⊕ α) : sum.traverse id.mk x = x :=
  sum.cases_on x (fun (x : σ) => Eq.refl (sum.traverse id.mk (inl x))) fun (x : α) => Eq.refl (sum.traverse id.mk (inr x))

protected theorem comp_traverse {σ : Type u} {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type u_1} {β : Type u} {γ : Type u} (f : β → F γ) (g : α → G β) (x : σ ⊕ α) : sum.traverse (functor.comp.mk ∘ Functor.map f ∘ g) x = functor.comp.mk (sum.traverse f <$> sum.traverse g x) := sorry

protected theorem traverse_eq_map_id {σ : Type u} {α : Type u} {β : Type u} (f : α → β) (x : σ ⊕ α) : sum.traverse (id.mk ∘ f) x = id.mk (f <$> x) := sorry

protected theorem map_traverse {σ : Type u} {G : Type u → Type u} [Applicative G] [is_lawful_applicative G] {α : Type u_1} {β : Type u} {γ : Type u} (g : α → G β) (f : β → γ) (x : σ ⊕ α) : Functor.map f <$> sum.traverse g x = sum.traverse (Functor.map f ∘ g) x := sorry

protected theorem naturality {σ : Type u} {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u_1} {β : Type u} (f : α → F β) (x : σ ⊕ α) : coe_fn η (σ ⊕ β) (sum.traverse f x) = sum.traverse (coe_fn η β ∘ f) x := sorry

protected instance is_lawful_traversable {σ : Type u} : is_lawful_traversable (sum σ) :=
  is_lawful_traversable.mk sum.id_traverse sum.comp_traverse sum.traverse_eq_map_id sum.naturality

