/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.control.bitraversable.basic
import PostPort

universes u l_1 u_1 

namespace Mathlib

/-!
# Bitraversable Lemmas

## Main definitions
  * tfst - traverse on first functor argument
  * tsnd - traverse on second functor argument

## Lemmas

Combination of
  * bitraverse
  * tfst
  * tsnd

with the applicatives `id` and `comp`

## References

 * Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative


-/

namespace bitraversable


/-- traverse on the first functor argument -/
def tfst {t : Type u → Type u → Type u} [bitraversable t] {β : Type u} {F : Type u → Type u} [Applicative F] {α : Type u} {α' : Type u} (f : α → F α') : t α β → F (t α' β) :=
  bitraverse f pure

/-- traverse on the second functor argument -/
def tsnd {t : Type u → Type u → Type u} [bitraversable t] {β : Type u} {F : Type u → Type u} [Applicative F] {α : Type u} {α' : Type u} (f : α → F α') : t β α → F (t β α') :=
  bitraverse pure f

theorem id_tfst {t : Type u → Type u → Type u} [bitraversable t] [is_lawful_bitraversable t] {α : Type u} {β : Type u} (x : t α β) : tfst id.mk x = id.mk x :=
  id_bitraverse

theorem id_tsnd {t : Type u → Type u → Type u} [bitraversable t] [is_lawful_bitraversable t] {α : Type u} {β : Type u} (x : t α β) : tsnd id.mk x = id.mk x :=
  id_bitraverse

theorem tfst_comp_tfst {t : Type l_1 → Type l_1 → Type l_1} [bitraversable t] {F : Type l_1 → Type l_1} {G : Type l_1 → Type l_1} [Applicative F] [Applicative G] [is_lawful_bitraversable t] [is_lawful_applicative F] [is_lawful_applicative G] {α₀ : Type l_1} {α₁ : Type l_1} {α₂ : Type l_1} {β : Type l_1} (f : α₀ → F α₁) (f' : α₁ → G α₂) : functor.comp.mk ∘ Functor.map (tfst f') ∘ tfst f = tfst (functor.comp.mk ∘ Functor.map f' ∘ f) :=
  funext fun (x : t α₀ β) => comp_tfst f f' x

theorem tfst_tsnd {t : Type u → Type u → Type u} [bitraversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_bitraversable t] [is_lawful_applicative F] [is_lawful_applicative G] {α₀ : Type u} {α₁ : Type u} {β₀ : Type u} {β₁ : Type u} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) : functor.comp.mk (tfst f <$> tsnd f' x) =
  bitraverse (functor.comp.mk ∘ pure ∘ f) (functor.comp.mk ∘ Functor.map pure ∘ f') x := sorry

theorem tsnd_tfst {t : Type u → Type u → Type u} [bitraversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_bitraversable t] [is_lawful_applicative F] [is_lawful_applicative G] {α₀ : Type u} {α₁ : Type u} {β₀ : Type u} {β₁ : Type u} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) : functor.comp.mk (tsnd f' <$> tfst f x) =
  bitraverse (functor.comp.mk ∘ Functor.map pure ∘ f) (functor.comp.mk ∘ pure ∘ f') x := sorry

theorem comp_tsnd {t : Type u → Type u → Type u} [bitraversable t] {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G] [is_lawful_bitraversable t] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type u} {β₀ : Type u} {β₁ : Type u} {β₂ : Type u} (g : β₀ → F β₁) (g' : β₁ → G β₂) (x : t α β₀) : functor.comp.mk (tsnd g' <$> tsnd g x) = tsnd (functor.comp.mk ∘ Functor.map g' ∘ g) x := sorry

theorem tfst_eq_fst_id {t : Type u → Type u → Type u} [bitraversable t] [is_lawful_bitraversable t] {α : Type u} {α' : Type u} {β : Type u} (f : α → α') (x : t α β) : tfst (id.mk ∘ f) x = id.mk (bifunctor.fst f x) := sorry

theorem tsnd_eq_snd_id {t : Type u → Type u → Type u} [bitraversable t] [is_lawful_bitraversable t] {α : Type u} {β : Type u} {β' : Type u} (f : β → β') (x : t α β) : tsnd (id.mk ∘ f) x = id.mk (bifunctor.snd f x) := sorry

