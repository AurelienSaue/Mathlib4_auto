/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.bitraversable.lemmas
import Mathlib.control.traversable.lemmas
import Mathlib.PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
# bitraversable instances

## Instances

 * prod
 * sum
 * const
 * flip
 * bicompl
 * bicompr

## References

 * Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative

-/

def prod.bitraverse {F : Type u → Type u} [Applicative F] {α : Type u_1} {α' : Type u} {β : Type u_2} {β' : Type u} (f : α → F α') (f' : β → F β') : α × β → F (α' × β') :=
  sorry

protected instance prod.bitraversable : bitraversable Prod :=
  bitraversable.mk prod.bitraverse

protected instance prod.is_lawful_bitraversable : is_lawful_bitraversable Prod :=
  is_lawful_bitraversable.mk sorry sorry sorry sorry

def sum.bitraverse {F : Type u → Type u} [Applicative F] {α : Type u_1} {α' : Type u} {β : Type u_2} {β' : Type u} (f : α → F α') (f' : β → F β') : α ⊕ β → F (α' ⊕ β') :=
  sorry

protected instance sum.bitraversable : bitraversable sum :=
  bitraversable.mk sum.bitraverse

protected instance sum.is_lawful_bitraversable : is_lawful_bitraversable sum :=
  is_lawful_bitraversable.mk sorry sorry sorry sorry

def const.bitraverse {F : Type u → Type u} [Applicative F] {α : Type u_1} {α' : Type u} {β : Type u_2} {β' : Type u} (f : α → F α') (f' : β → F β') : functor.const α β → F (functor.const α' β') :=
  f

protected instance bitraversable.const : bitraversable functor.const :=
  bitraversable.mk const.bitraverse

protected instance is_lawful_bitraversable.const : is_lawful_bitraversable functor.const :=
  is_lawful_bitraversable.mk sorry sorry sorry sorry

def flip.bitraverse {t : Type u → Type u → Type u} [bitraversable t] {F : Type u → Type u} [Applicative F] {α : Type u} {α' : Type u} {β : Type u} {β' : Type u} (f : α → F α') (f' : β → F β') : flip t α β → F (flip t α' β') :=
  bitraverse f' f

protected instance bitraversable.flip {t : Type u → Type u → Type u} [bitraversable t] : bitraversable (flip t) :=
  bitraversable.mk flip.bitraverse

protected instance is_lawful_bitraversable.flip {t : Type u → Type u → Type u} [bitraversable t] [is_lawful_bitraversable t] : is_lawful_bitraversable (flip t) :=
  is_lawful_bitraversable.mk sorry sorry sorry sorry

protected instance bitraversable.traversable {t : Type u → Type u → Type u} [bitraversable t] {α : Type u} : traversable (t α) :=
  traversable.mk bitraversable.tsnd

protected instance bitraversable.is_lawful_traversable {t : Type u → Type u → Type u} [bitraversable t] [is_lawful_bitraversable t] {α : Type u} : is_lawful_traversable (t α) :=
  is_lawful_traversable.mk sorry sorry sorry sorry

def bicompl.bitraverse {t : Type u → Type u → Type u} [bitraversable t] (F : Type u → Type u) (G : Type u → Type u) [traversable F] [traversable G] {m : Type u → Type u} [Applicative m] {α : Type u} {β : Type u} {α' : Type u} {β' : Type u} (f : α → m β) (f' : α' → m β') : function.bicompl t F G α α' → m (function.bicompl t F G β β') :=
  bitraverse (traverse f) (traverse f')

protected instance function.bicompl.bitraversable {t : Type u → Type u → Type u} [bitraversable t] (F : Type u → Type u) (G : Type u → Type u) [traversable F] [traversable G] : bitraversable (function.bicompl t F G) :=
  bitraversable.mk (bicompl.bitraverse F G)

protected instance function.bicompl.is_lawful_bitraversable {t : Type u → Type u → Type u} [bitraversable t] (F : Type u → Type u) (G : Type u → Type u) [traversable F] [traversable G] [is_lawful_traversable F] [is_lawful_traversable G] [is_lawful_bitraversable t] : is_lawful_bitraversable (function.bicompl t F G) :=
  is_lawful_bitraversable.mk sorry sorry sorry sorry

def bicompr.bitraverse {t : Type u → Type u → Type u} [bitraversable t] (F : Type u → Type u) [traversable F] {m : Type u → Type u} [Applicative m] {α : Type u} {β : Type u} {α' : Type u} {β' : Type u} (f : α → m β) (f' : α' → m β') : function.bicompr F t α α' → m (function.bicompr F t β β') :=
  traverse (bitraverse f f')

protected instance function.bicompr.bitraversable {t : Type u → Type u → Type u} [bitraversable t] (F : Type u → Type u) [traversable F] : bitraversable (function.bicompr F t) :=
  bitraversable.mk (bicompr.bitraverse F)

protected instance function.bicompr.is_lawful_bitraversable {t : Type u → Type u → Type u} [bitraversable t] (F : Type u → Type u) [traversable F] [is_lawful_traversable F] [is_lawful_bitraversable t] : is_lawful_bitraversable (function.bicompr F t) :=
  is_lawful_bitraversable.mk sorry sorry sorry sorry

