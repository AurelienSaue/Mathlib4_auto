/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Transferring `traversable` instances using isomorphisms.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.equiv.basic
import Mathlib.control.traversable.lemmas
import Mathlib.PostPort

universes u 

namespace Mathlib

namespace equiv


/-- Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`equiv.functor`). -/
protected def map {t : Type u → Type u} {t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α)
    [Functor t] {α : Type u} {β : Type u} (f : α → β) (x : t' α) : t' β :=
  coe_fn (eqv β) (f <$> coe_fn (equiv.symm (eqv α)) x)

/-- The function `equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`.  -/
protected def functor {t : Type u → Type u} {t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α)
    [Functor t] : Functor t' :=
  { map := equiv.map eqv, mapConst := fun (α β : Type u) => equiv.map eqv ∘ function.const β }

protected theorem id_map {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [Functor t] [is_lawful_functor t] {α : Type u} (x : t' α) :
    equiv.map eqv id x = x :=
  sorry

protected theorem comp_map {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [Functor t] [is_lawful_functor t] {α : Type u} {β : Type u}
    {γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
    equiv.map eqv (h ∘ g) x = equiv.map eqv h (equiv.map eqv g x) :=
  sorry

protected theorem is_lawful_functor {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [Functor t] [is_lawful_functor t] : is_lawful_functor t' :=
  is_lawful_functor.mk (equiv.id_map eqv) (equiv.comp_map eqv)

protected theorem is_lawful_functor' {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [Functor t] [is_lawful_functor t] [F : Functor t']
    (h₀ : ∀ {α β : Type u} (f : α → β), Functor.map f = equiv.map eqv f)
    (h₁ :
      ∀ {α β : Type u} (f : β),
        Functor.mapConst f = function.comp (equiv.map eqv) (function.const α) f) :
    is_lawful_functor t' :=
  sorry

/-- Like `equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α.  See `equiv.traversable`. -/
protected def traverse {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] {m : Type u → Type u} [Applicative m]
    {α : Type u} {β : Type u} (f : α → m β) (x : t' α) : m (t' β) :=
  ⇑(eqv β) <$> traverse f (coe_fn (equiv.symm (eqv α)) x)

/-- The function `equiv.tranverse` transfers a traversable functor
instance across the equivalences `eqv`. -/
protected def traversable {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] : traversable t' :=
  traversable.mk (equiv.traverse eqv)

protected theorem id_traverse {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] [is_lawful_traversable t] {α : Type u}
    (x : t' α) : equiv.traverse eqv id.mk x = x :=
  sorry

protected theorem traverse_eq_map_id {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] [is_lawful_traversable t] {α : Type u}
    {β : Type u} (f : α → β) (x : t' α) :
    equiv.traverse eqv (id.mk ∘ f) x = id.mk (equiv.map eqv f x) :=
  sorry

protected theorem comp_traverse {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] [is_lawful_traversable t]
    {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G] {α : Type u} {β : Type u} {γ : Type u}
    (f : β → F γ) (g : α → G β) (x : t' α) :
    equiv.traverse eqv (functor.comp.mk ∘ Functor.map f ∘ g) x =
        functor.comp.mk (equiv.traverse eqv f <$> equiv.traverse eqv g x) :=
  sorry

protected theorem naturality {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] [is_lawful_traversable t]
    {F : Type u → Type u} {G : Type u → Type u} [Applicative F] [Applicative G]
    [is_lawful_applicative F] [is_lawful_applicative G] (η : applicative_transformation F G)
    {α : Type u} {β : Type u} (f : α → F β) (x : t' α) :
    coe_fn η (t' β) (equiv.traverse eqv f x) = equiv.traverse eqv (coe_fn η β ∘ f) x :=
  sorry

/-- The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`equiv.traversable`. -/
protected def is_lawful_traversable {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] [is_lawful_traversable t] :
    is_lawful_traversable t' :=
  is_lawful_traversable.mk (equiv.id_traverse eqv) (equiv.comp_traverse eqv)
    (equiv.traverse_eq_map_id eqv) (equiv.naturality eqv)

/-- If the `traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the the fact `t` is a lawful traversable functor
carries over as well. -/
protected def is_lawful_traversable' {t : Type u → Type u} {t' : Type u → Type u}
    (eqv : (α : Type u) → t α ≃ t' α) [traversable t] [is_lawful_traversable t] [traversable t']
    (h₀ : ∀ {α β : Type u} (f : α → β), Functor.map f = equiv.map eqv f)
    (h₁ :
      ∀ {α β : Type u} (f : β),
        Functor.mapConst f = function.comp (equiv.map eqv) (function.const α) f)
    (h₂ :
      ∀ {F : Type u → Type u} [_inst_7 : Applicative F] [_inst_8 : is_lawful_applicative F]
        {α β : Type u} (f : α → F β), traverse f = equiv.traverse eqv f) :
    is_lawful_traversable t' :=
  is_lawful_traversable.mk sorry sorry sorry sorry

end Mathlib