/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.control.functor
import PostPort

universes u v w l s t u_1 

namespace Mathlib

/-!
# Traversable type class

Type classes for traversing collections. The concepts and laws are taken from
<http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html>

Traversable collections are a generalization of functors. Whereas
functors (such as `list`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email → io response`
that takes an email address, sends an email and waits for a
response. If we have a list `guests : list email`, using calling
`invite` using `map` gives us the following: `map invite guests : list
(io response)`.  It is not what we need. We need something of type `io
(list response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : io (list response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `io` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
<https://en.wikibooks.org/wiki/Haskell/Traversable>

## Main definitions
  * `traversable` type class - exposes the `traverse` function
  * `sequence` - based on `traverse`, turns a collection of effects into an effect returning a collection
  * `is_lawful_traversable` - laws for a traversable functor
  * `applicative_transformation` - the notion of a natural transformation for applicative functors

## Tags

traversable iterator functor applicative

## References

 * "Applicative Programming with Effects", by Conor McBride and Ross Paterson,
   Journal of Functional Programming 18:1 (2008) 1-13, online at
   <http://www.soi.city.ac.uk/~ross/papers/Applicative.html>
 * "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira,
   in Mathematically-Structured Functional Programming, 2006, online at
   <http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator>
 * "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek,
   in Mathematically-Structured Functional Programming, 2012,
   online at <http://arxiv.org/pdf/1202.2919>
-/

/-- A transformation between applicative functors.  It a natural
transformation such that `app` preserves the `has_pure.pure` and
`functor.map` (`<*>`) operations. See
`applicative_transformation.preserves_map` for naturality. -/
structure applicative_transformation (F : Type u → Type v) [Applicative F] [is_lawful_applicative F] (G : Type u → Type w) [Applicative G] [is_lawful_applicative G] 
where
  app : (α : Type u) → F α → G α
  preserves_pure' : ∀ {α : Type u} (x : α), app α (pure x) = pure x
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app β (x <*> y) = app (α → β) x <*> app α y

namespace applicative_transformation


protected instance has_coe_to_fun (F : Type u → Type v) [Applicative F] [is_lawful_applicative F] (G : Type u → Type w) [Applicative G] [is_lawful_applicative G] : has_coe_to_fun (applicative_transformation F G) :=
  has_coe_to_fun.mk (fun (_x : applicative_transformation F G) => {α : Type u} → F α → G α)
    fun (a : applicative_transformation F G) => app a

@[simp] theorem app_eq_coe {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) : app η = ⇑η :=
  rfl

@[simp] theorem coe_mk {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (f : (α : Type u) → F α → G α) (pp : ∀ {α : Type u} (x : α), f α (pure x) = pure x) (ps : ∀ {α β : Type u} (x : F (α → β)) (y : F α), f β (x <*> y) = f (α → β) x <*> f α y) : ⇑(mk f pp ps) = f :=
  rfl

protected theorem congr_fun {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) (η' : applicative_transformation F G) (h : η = η') {α : Type u} (x : F α) : coe_fn η α x = coe_fn η' α x :=
  congr_arg (fun (η'' : applicative_transformation F G) => coe_fn η'' α x) h

protected theorem congr_arg {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u} {x : F α} {y : F α} (h : x = y) : coe_fn η α x = coe_fn η α y :=
  congr_arg (fun (z : F α) => coe_fn η α z) h

theorem coe_inj {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] {η : applicative_transformation F G} {η' : applicative_transformation F G} (h : ⇑η = ⇑η') : η = η' := sorry

theorem ext {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] {η : applicative_transformation F G} {η' : applicative_transformation F G} (h : ∀ (α : Type u) (x : F α), coe_fn η α x = coe_fn η' α x) : η = η' :=
  coe_inj (funext fun (α : Type u) => funext (h α))

theorem ext_iff {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] {η : applicative_transformation F G} {η' : applicative_transformation F G} : η = η' ↔ ∀ (α : Type u) (x : F α), coe_fn η α x = coe_fn η' α x :=
  { mp := fun (h : η = η') (α : Type u) (x : F α) => h ▸ rfl,
    mpr := fun (h : ∀ (α : Type u) (x : F α), coe_fn η α x = coe_fn η' α x) => ext h }

theorem preserves_pure {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u} (x : α) : coe_fn η α (pure x) = pure x :=
  preserves_pure' η

theorem preserves_seq {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u} {β : Type u} (x : F (α → β)) (y : F α) : coe_fn η β (x <*> y) = coe_fn η (α → β) x <*> coe_fn η α y :=
  preserves_seq' η

theorem preserves_map {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u} {β : Type u} (x : α → β) (y : F α) : coe_fn η β (x <$> y) = x <$> coe_fn η α y := sorry

theorem preserves_map' {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) {α : Type u} {β : Type u} (x : α → β) : coe_fn η β ∘ Functor.map x = Functor.map x ∘ coe_fn η α :=
  funext fun (y : F α) => preserves_map η x y

/-- The identity applicative transformation from an applicative functor to itself. -/
def id_transformation {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] : applicative_transformation F F :=
  mk (fun (α : Type u) => id) sorry sorry

protected instance inhabited {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] : Inhabited (applicative_transformation F F) :=
  { default := id_transformation }

/-- The composition of applicative transformations. -/
def comp {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] {H : Type u → Type s} [Applicative H] [is_lawful_applicative H] (η' : applicative_transformation G H) (η : applicative_transformation F G) : applicative_transformation F H :=
  mk (fun (α : Type u) (x : F α) => coe_fn η' α (coe_fn η α x)) sorry sorry

@[simp] theorem comp_apply {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] {H : Type u → Type s} [Applicative H] [is_lawful_applicative H] (η' : applicative_transformation G H) (η : applicative_transformation F G) {α : Type u} (x : F α) : coe_fn (comp η' η) α x = coe_fn η' α (coe_fn η α x) :=
  rfl

theorem comp_assoc {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] {H : Type u → Type s} [Applicative H] [is_lawful_applicative H] {I : Type u → Type t} [Applicative I] [is_lawful_applicative I] (η'' : applicative_transformation H I) (η' : applicative_transformation G H) (η : applicative_transformation F G) : comp (comp η'' η') η = comp η'' (comp η' η) :=
  rfl

@[simp] theorem comp_id {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) : comp η id_transformation = η :=
  ext fun (α : Type u) (x : F α) => rfl

@[simp] theorem id_comp {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {G : Type u → Type w} [Applicative G] [is_lawful_applicative G] (η : applicative_transformation F G) : comp id_transformation η = η :=
  ext fun (α : Type u) (x : F α) => rfl

end applicative_transformation


/-- A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `list` and `m` is the applicative functor
`io`, then given a function `f : α → io β`, the function `functor.map f` is
`list α → list (io β)`, but `traverse f` is `list α → io (list β)`. -/
class traversable (t : Type u → Type u) 
extends Functor t
where
  traverse : {m : Type u → Type u} → [_inst_1 : Applicative m] → {α β : Type u} → (α → m β) → t α → m (t β)

/-- A traversable functor commutes with all applicative functors. -/
def sequence {t : Type u → Type u} {α : Type u} {f : Type u → Type u} [Applicative f] [traversable t] : t (f α) → f (t α) :=
  traverse id

/-- A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `id.mk` to `id.mk`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `λ x, f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations. -/
class is_lawful_traversable (t : Type u → Type u) [traversable t] 
extends is_lawful_functor t
where
  id_traverse : ∀ {α : Type u} (x : t α), traverse id.mk x = x
  comp_traverse : ∀ {F G : Type u → Type u} [_inst_1_1 : Applicative F] [_inst_2 : Applicative G] [_inst_3 : is_lawful_applicative F]
  [_inst_4 : is_lawful_applicative G] {α β γ : Type u} (f : β → F γ) (g : α → G β) (x : t α),
  traverse (functor.comp.mk ∘ Functor.map f ∘ g) x = functor.comp.mk (traverse f <$> traverse g x)
  traverse_eq_map_id : ∀ {α β : Type u} (f : α → β) (x : t α), traverse (id.mk ∘ f) x = id.mk (f <$> x)
  naturality : ∀ {F G : Type u → Type u} [_inst_1_1 : Applicative F] [_inst_2 : Applicative G] [_inst_3 : is_lawful_applicative F]
  [_inst_4 : is_lawful_applicative G] (η : applicative_transformation F G) {α β : Type u} (f : α → F β) (x : t α),
  coe_fn η (t β) (traverse f x) = traverse (coe_fn η β ∘ f) x

protected instance id.traversable : traversable id :=
  traversable.mk fun (_x : Type u_1 → Type u_1) (_x_1 : Applicative _x) (_x_2 _x_3 : Type u_1) => id

protected instance id.is_lawful_traversable : is_lawful_traversable id :=
  is_lawful_traversable.mk sorry sorry sorry sorry

protected instance option.traversable : traversable Option :=
  traversable.mk option.traverse

protected instance list.traversable : traversable List :=
  traversable.mk list.traverse

namespace sum


/-- Defines a `traverse` function on the second component of a sum type.
This is used to give a `traversable` instance for the functor `σ ⊕ -`. -/
protected def traverse {σ : Type u} {F : Type u → Type u} [Applicative F] {α : Type u_1} {β : Type u} (f : α → F β) : σ ⊕ α → F (σ ⊕ β) :=
  sorry

end sum


protected instance sum.traversable {σ : Type u} : traversable (sum σ) :=
  traversable.mk sum.traverse

