/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.control.bifunctor
import Mathlib.control.traversable.basic
import PostPort

universes u l u_1 l_1 

namespace Mathlib

/-!
# Bitraversable type class

Type class for traversing bifunctors. The concepts and laws are taken from
<https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

Simple examples of `bitraversable` are `prod` and `sum`. A more elaborate example is
to define an a-list as:

```
def alist (key val : Type) := list (key × val)
```

Then we can use `f : key → io key'` and `g : val → io val'` to manipulate the `alist`'s key
and value respectively with `bitraverse f g : alist key val → io (alist key' val')`

## Main definitions
  * bitraversable - exposes the `bitraverse` function
  * is_lawful_bitraversable - laws similar to is_lawful_traversable

## Tags

traversable bitraversable iterator functor bifunctor applicative

-/

class bitraversable (t : Type u → Type u → Type u) 
extends bifunctor t
where
  bitraverse : {m : Type u → Type u} → [_inst_1 : Applicative m] → {α α' β β' : Type u} → (α → m α') → (β → m β') → t α β → m (t α' β')

def bisequence {t : Type u_1 → Type u_1 → Type u_1} {m : Type u_1 → Type u_1} [bitraversable t] [Applicative m] {α : Type u_1} {β : Type u_1} : t (m α) (m β) → m (t α β) :=
  bitraverse id id

class is_lawful_bitraversable (t : Type u → Type u → Type u) [bitraversable t] 
extends is_lawful_bifunctor t
where
  id_bitraverse : ∀ {α β : Type u} (x : t α β), bitraverse id.mk id.mk x = id.mk x
  comp_bitraverse : ∀ {F G : Type u → Type u} [_inst_1_1 : Applicative F] [_inst_2 : Applicative G] [_inst_3 : is_lawful_applicative F]
  [_inst_4 : is_lawful_applicative G] {α α' β β' γ γ' : Type u} (f : β → F γ) (f' : β' → F γ') (g : α → G β)
  (g' : α' → G β') (x : t α α'),
  bitraverse (functor.comp.mk ∘ Functor.map f ∘ g) (functor.comp.mk ∘ Functor.map f' ∘ g') x =
    functor.comp.mk (bitraverse f f' <$> bitraverse g g' x)
  bitraverse_eq_bimap_id : ∀ {α α' β β' : Type u} (f : α → β) (f' : α' → β') (x : t α α'),
  bitraverse (id.mk ∘ f) (id.mk ∘ f') x = id.mk (bimap f f' x)
  binaturality : ∀ {F G : Type u → Type u} [_inst_1_1 : Applicative F] [_inst_2 : Applicative G] [_inst_3 : is_lawful_applicative F]
  [_inst_4 : is_lawful_applicative G] (η : applicative_transformation F G) {α α' β β' : Type u} (f : α → F β)
  (f' : α' → F β') (x : t α α'),
  coe_fn η (t β β') (bitraverse f f' x) = bitraverse (coe_fn η β ∘ f) (coe_fn η β' ∘ f') x

theorem is_lawful_bitraversable.bitraverse_id_id {t : Type l_1 → Type l_1 → Type l_1} [bitraversable t] [c : is_lawful_bitraversable t] {α : Type l_1} {β : Type l_1} : bitraverse id.mk id.mk = id.mk :=
  funext fun (x : t α β) => id_bitraverse x

theorem is_lawful_bitraversable.bitraverse_comp {t : Type l_1 → Type l_1 → Type l_1} [bitraversable t] [c : is_lawful_bitraversable t] {F : Type l_1 → Type l_1} {G : Type l_1 → Type l_1} : ∀ [_inst_1_1 : Applicative F] [_inst_2 : Applicative G] [_inst_3 : is_lawful_applicative F]
  [_inst_4 : is_lawful_applicative G] {α α' β β' γ γ' : Type l_1} (f : β → F γ) (f' : β' → F γ') (g : α → G β)
  (g' : α' → G β'),
  bitraverse (functor.comp.mk ∘ Functor.map f ∘ g) (functor.comp.mk ∘ Functor.map f' ∘ g') =
    functor.comp.mk ∘ Functor.map (bitraverse f f') ∘ bitraverse g g' :=
  fun (_inst_1_1 : Applicative F) (_inst_2 : Applicative G) (_inst_3 : is_lawful_applicative F)
    (_inst_4 : is_lawful_applicative G) (α α' β β' γ γ' : Type l_1) (f : β → F γ) (f' : β' → F γ') (g : α → G β)
    (g' : α' → G β') => funext fun (x : t α α') => comp_bitraverse f f' g g' x

theorem is_lawful_bitraversable.bitraverse_eq_bimap_id' {t : Type l_1 → Type l_1 → Type l_1} [bitraversable t] [c : is_lawful_bitraversable t] {α : Type l_1} {α' : Type l_1} {β : Type l_1} {β' : Type l_1} (f : α → β) (f' : α' → β') : bitraverse (id.mk ∘ f) (id.mk ∘ f') = id.mk ∘ bimap f f' :=
  funext fun (x : t α α') => bitraverse_eq_bimap_id f f' x

