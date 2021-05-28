/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Lemmas about traversing collections.

Inspired by:

    The Essence of the Iterator Pattern
    Jeremy Gibbons and Bruno César dos Santos Oliveira
    In Journal of Functional Programming. Vol. 19. No. 3&4. Pages 377−402. 2009.
    <http://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf>
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.traversable.basic
import Mathlib.control.applicative
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace traversable


/-- The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`. -/
def pure_transformation (F : Type u → Type u) [Applicative F] [is_lawful_applicative F] : applicative_transformation id F :=
  applicative_transformation.mk pure sorry sorry

@[simp] theorem pure_transformation_apply (F : Type u → Type u) [Applicative F] [is_lawful_applicative F] {α : Type u} (x : id α) : coe_fn (pure_transformation F) α x = pure x :=
  rfl

theorem map_eq_traverse_id {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {β : Type u} {γ : Type u} (f : β → γ) : Functor.map f = traverse (id.mk ∘ f) :=
  funext fun (y : t β) => Eq.symm (is_lawful_traversable.traverse_eq_map_id f y)

theorem map_traverse {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} [Applicative F] [is_lawful_applicative F] {α : Type u} {β : Type u} {γ : Type u} (g : α → F β) (f : β → γ) (x : t α) : Functor.map f <$> traverse g x = traverse (Functor.map f ∘ g) x := sorry

theorem traverse_map {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} [Applicative F] [is_lawful_applicative F] {α : Type u} {β : Type u} {γ : Type u} (f : β → F γ) (g : α → β) (x : t α) : traverse f (g <$> x) = traverse (f ∘ g) x := sorry

theorem pure_traverse {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} [Applicative F] [is_lawful_applicative F] {α : Type u} (x : t α) : traverse pure x = pure x :=
  eq.mp (Eq._oldrec (Eq.refl (traverse pure x = pure (traverse id.mk x))) (is_lawful_traversable.id_traverse x))
    (Eq.symm (is_lawful_traversable.naturality (pure_transformation F) id.mk x))

theorem id_sequence {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {α : Type u} (x : t α) : sequence (id.mk <$> x) = id.mk x := sorry

theorem comp_sequence {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [is_lawful_applicative F] [Applicative G] [is_lawful_applicative G] {α : Type u} (x : t (F (G α))) : sequence (functor.comp.mk <$> x) = functor.comp.mk (sequence <$> sequence x) := sorry

theorem naturality' {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [is_lawful_applicative F] [Applicative G] [is_lawful_applicative G] {α : Type u} (η : applicative_transformation F G) (x : t (F α)) : coe_fn η (t α) (sequence x) = sequence (coe_fn η α <$> x) := sorry

theorem traverse_id {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {α : Type u} : traverse id.mk = id.mk := sorry

theorem traverse_comp {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [is_lawful_applicative F] [Applicative G] [is_lawful_applicative G] {α : Type u} {β : Type u} {γ : Type u} (g : α → F β) (h : β → G γ) : traverse (functor.comp.mk ∘ Functor.map h ∘ g) = functor.comp.mk ∘ Functor.map (traverse h) ∘ traverse g := sorry

theorem traverse_eq_map_id' {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {β : Type u} {γ : Type u} (f : β → γ) : traverse (id.mk ∘ f) = id.mk ∘ Functor.map f := sorry

-- @[functor_norm]

theorem traverse_map' {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {G : Type u → Type u} [Applicative G] [is_lawful_applicative G] {α : Type u} {β : Type u} {γ : Type u} (g : α → β) (h : β → G γ) : traverse (h ∘ g) = traverse h ∘ Functor.map g := sorry

theorem map_traverse' {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {G : Type u → Type u} [Applicative G] [is_lawful_applicative G] {α : Type u} {β : Type u} {γ : Type u} (g : α → G β) (h : β → γ) : traverse (Functor.map h ∘ g) = Functor.map (Functor.map h) ∘ traverse g := sorry

theorem naturality_pf {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [is_lawful_applicative F] [Applicative G] [is_lawful_applicative G] {α : Type u} {β : Type u} (η : applicative_transformation F G) (f : α → F β) : traverse (coe_fn η β ∘ f) = coe_fn η (t β) ∘ traverse f := sorry

