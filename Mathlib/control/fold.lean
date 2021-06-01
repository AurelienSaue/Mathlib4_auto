/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.free_monoid
import Mathlib.algebra.opposites
import Mathlib.control.traversable.instances
import Mathlib.control.traversable.lemmas
import Mathlib.category_theory.category.default
import Mathlib.category_theory.endomorphism
import Mathlib.category_theory.types
import Mathlib.category_theory.category.Kleisli
import Mathlib.PostPort

universes u u_1 

namespace Mathlib

/-!

# List folds generalized to `traversable`

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `fold_map` as a
primitive and `fold_map_hom` as a defining property.

```
def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω := ...

lemma fold_map_hom (α β)
  [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
...
```

`fold_map` uses a monoid ω to accumulate a value for every element of
a data structure and `fold_map_hom` uses a monoid homomorphism to
substitute the monoid used by `fold_map`. The two are sufficient to
define `foldl`, `foldr` and `to_list`. `to_list` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `to_list` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`traversable`.
-/

namespace monoid


/--
For a list, foldl f x [y₀,y₁] reduces as follows
  calc  foldl f x [y₀,y₁]
      = foldl f (f x y₀) [y₁]      : rfl
  ... = foldl f (f (f x y₀) y₁) [] : rfl
  ... = f (f x y₀) y₁              : rfl

with f : α → β → α
     x : α
     [y₀,y₁] : list β

We can view the above as a composition of functions:

  ... = f (f x y₀) y₁              : rfl
  ... = flip f y₁ (flip f y₀ x)    : rfl
  ... = (flip f y₁ ∘ flip f y₀) x  : rfl

We can use traverse and const to construct this composition:

  calc   const.run (traverse (λ y, const.mk' (flip f y)) [y₀,y₁]) x
       = const.run ((::) <$> const.mk' (flip f y₀) <*> traverse (λ y, const.mk' (flip f y)) [y₁]) x
  ...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
           ( (::) <$> const.mk' (flip f y₁) <*> traverse (λ y, const.mk' (flip f y)) [] )) x
  ...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
           ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
  ...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
           ((::) <$> const.mk' (flip f y₀)) ) x
  ...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
  ...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
  ...  = f (f x y₀) y₁

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `foldl`.
-/
def foldl (α : Type u) :=
  category_theory.End αᵒᵖ

def foldl.mk {α : Type u} (f : α → α) : foldl α :=
  opposite.op f

def foldl.get {α : Type u} (x : foldl α) : α → α :=
  opposite.unop x

def foldl.of_free_monoid {α : Type u} {β : Type u} (f : β → α → β) (xs : free_monoid α) : foldl β :=
  opposite.op (flip (list.foldl f) xs)

def foldr (α : Type u) :=
  category_theory.End α

def foldr.mk {α : Type u} (f : α → α) : foldr α :=
  f

def foldr.get {α : Type u} (x : foldr α) : α → α :=
  x

def foldr.of_free_monoid {α : Type u} {β : Type u} (f : α → β → β) (xs : free_monoid α) : foldr β :=
  flip (list.foldr f) xs

def mfoldl (m : Type u → Type u) [Monad m] (α : Type u) :=
  category_theory.End (category_theory.Kleisli.mk m α)ᵒᵖ

def mfoldl.mk {m : Type u → Type u} [Monad m] {α : Type u} (f : α → m α) : mfoldl m α :=
  opposite.op f

def mfoldl.get {m : Type u → Type u} [Monad m] {α : Type u} (x : mfoldl m α) : α → m α :=
  opposite.unop x

def mfoldl.of_free_monoid {m : Type u → Type u} [Monad m] {α : Type u} {β : Type u} (f : β → α → m β) (xs : free_monoid α) : mfoldl m β :=
  opposite.op (flip (mfoldl f) xs)

def mfoldr (m : Type u → Type u) [Monad m] (α : Type u) :=
  category_theory.End (category_theory.Kleisli.mk m α)

def mfoldr.mk {m : Type u → Type u} [Monad m] {α : Type u} (f : α → m α) : mfoldr m α :=
  f

def mfoldr.get {m : Type u → Type u} [Monad m] {α : Type u} (x : mfoldr m α) : α → m α :=
  x

def mfoldr.of_free_monoid {m : Type u → Type u} [Monad m] {α : Type u} {β : Type u} (f : α → β → m β) (xs : free_monoid α) : mfoldr m β :=
  flip (list.mfoldr f) xs

end monoid


namespace traversable


def fold_map {t : Type u → Type u} [traversable t] {α : Type u} {ω : Type u} [HasOne ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (functor.const.mk' ∘ f)

def foldl {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] (f : α → β → α) (x : α) (xs : t β) : α :=
  monoid.foldl.get (fold_map (monoid.foldl.mk ∘ flip f) xs) x

def foldr {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] (f : α → β → β) (x : β) (xs : t α) : β :=
  monoid.foldr.get (fold_map (monoid.foldr.mk ∘ f) xs) x

/--
Conceptually, `to_list` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma to_list_spec (x : t α) : to_list x = fold_map free_monoid.mk x`.

The definition of `to_list` is based on `foldl` and `list.cons` for
speed. It is faster than using `fold_map free_monoid.mk` because, by
using `foldl` and `list.cons`, each insertion is done in constant
time. As a consequence, `to_list` performs in linear.

On the other hand, `fold_map free_monoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
def to_list {α : Type u} {t : Type u → Type u} [traversable t] : t α → List α :=
  list.reverse ∘ foldl (flip List.cons) []

def length {α : Type u} {t : Type u → Type u} [traversable t] (xs : t α) : ℕ :=
  ulift.down (foldl (fun (l : ulift ℕ) (_x : α) => ulift.up (ulift.down l + 1)) (ulift.up 0) xs)

def mfoldl {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] {m : Type u → Type u} [Monad m] (f : α → β → m α) (x : α) (xs : t β) : m α :=
  monoid.mfoldl.get (fold_map (monoid.mfoldl.mk ∘ flip f) xs) x

def mfoldr {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] {m : Type u → Type u} [Monad m] (f : α → β → m β) (x : β) (xs : t α) : m β :=
  monoid.mfoldr.get (fold_map (monoid.mfoldr.mk ∘ f) xs) x

def map_fold {α : Type u} {β : Type u} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] : applicative_transformation (functor.const α) (functor.const β) :=
  applicative_transformation.mk (fun (x : Type u_1) => f) sorry sorry

def free.mk {α : Type u} : α → free_monoid α :=
  list.ret

def free.map {α : Type u} {β : Type u} (f : α → β) : free_monoid α → free_monoid β :=
  list.map f

theorem free.map_eq_map {α : Type u} {β : Type u} (f : α → β) (xs : List α) : f <$> xs = free.map f xs :=
  rfl

protected instance free.map.is_monoid_hom {α : Type u} {β : Type u} (f : α → β) : is_monoid_hom (free.map f) :=
  is_monoid_hom.mk
    (eq.mpr
      (id
        ((fun (a a_1 : free_monoid β) (e_1 : a = a_1) (ᾰ ᾰ_1 : free_monoid β) (e_2 : ᾰ = ᾰ_1) =>
            congr (congr_arg Eq e_1) e_2)
          (free.map f 1) []
          (Eq.trans
            (Eq.trans
              ((fun (f f_1 : α → β) (e_1 : f = f_1) (ᾰ ᾰ_1 : free_monoid α) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg free.map e_1) e_2)
                f f (Eq.refl f) 1 [] free_monoid.one_def)
              (congr_fun (free.map.equations._eqn_1 f) []))
            (list.map.equations._eqn_1 f))
          1 [] free_monoid.one_def))
      (Eq.refl []))

protected instance fold_foldl {α : Type u} {β : Type u} (f : β → α → β) : is_monoid_hom (monoid.foldl.of_free_monoid f) :=
  is_monoid_hom.mk rfl

theorem foldl.unop_of_free_monoid {α : Type u} {β : Type u} (f : β → α → β) (xs : free_monoid α) (a : β) : opposite.unop (monoid.foldl.of_free_monoid f xs) a = list.foldl f a xs :=
  rfl

protected instance fold_foldr {α : Type u} {β : Type u} (f : α → β → β) : is_monoid_hom (monoid.foldr.of_free_monoid f) :=
  is_monoid_hom.mk rfl

@[simp] theorem mfoldl.unop_of_free_monoid {α : Type u} {β : Type u} (m : Type u → Type u) [Monad m] [is_lawful_monad m] (f : β → α → m β) (xs : free_monoid α) (a : β) : opposite.unop (monoid.mfoldl.of_free_monoid f xs) a = mfoldl f a xs :=
  rfl

protected instance fold_mfoldl {α : Type u} {β : Type u} (m : Type u → Type u) [Monad m] [is_lawful_monad m] (f : β → α → m β) : is_monoid_hom (monoid.mfoldl.of_free_monoid f) :=
  is_monoid_hom.mk rfl

protected instance fold_mfoldr {α : Type u} {β : Type u} (m : Type u → Type u) [Monad m] [is_lawful_monad m] (f : α → β → m β) : is_monoid_hom (monoid.mfoldr.of_free_monoid f) :=
  is_monoid_hom.mk rfl

theorem fold_map_hom {α : Type u} {β : Type u} {γ : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] (g : γ → α) (x : t γ) : f (fold_map g x) = fold_map (f ∘ g) x :=
  Eq.trans (Eq.trans (Eq.trans rfl rfl) (is_lawful_traversable.naturality (map_fold f) (functor.const.mk' ∘ g) x)) rfl

theorem fold_map_hom_free {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] [monoid β] (f : free_monoid α → β) [is_monoid_hom f] (x : t α) : f (fold_map free.mk x) = fold_map (f ∘ free.mk) x :=
  fold_map_hom f free.mk x

theorem fold_mfoldl_cons {α : Type u} {β : Type u} {m : Type u → Type u} [Monad m] [is_lawful_monad m] (f : α → β → m α) (x : β) (y : α) : mfoldl f y (free.mk x) = f y x := sorry

theorem fold_mfoldr_cons {α : Type u} {β : Type u} {m : Type u → Type u} [Monad m] [is_lawful_monad m] (f : β → α → m α) (x : β) (y : α) : list.mfoldr f y (free.mk x) = f x y := sorry

@[simp] theorem foldl.of_free_monoid_comp_free_mk {α : Type u} {β : Type u} (f : α → β → α) : monoid.foldl.of_free_monoid f ∘ free.mk = monoid.foldl.mk ∘ flip f :=
  rfl

@[simp] theorem foldr.of_free_monoid_comp_free_mk {α : Type u} {β : Type u} (f : β → α → α) : monoid.foldr.of_free_monoid f ∘ free.mk = monoid.foldr.mk ∘ f :=
  rfl

@[simp] theorem mfoldl.of_free_monoid_comp_free_mk {α : Type u} {β : Type u} {m : Type u → Type u} [Monad m] [is_lawful_monad m] (f : α → β → m α) : monoid.mfoldl.of_free_monoid f ∘ free.mk = monoid.mfoldl.mk ∘ flip f := sorry

@[simp] theorem mfoldr.of_free_monoid_comp_free_mk {α : Type u} {β : Type u} {m : Type u → Type u} [Monad m] [is_lawful_monad m] (f : β → α → m α) : monoid.mfoldr.of_free_monoid f ∘ free.mk = monoid.mfoldr.mk ∘ f := sorry

theorem to_list_spec {α : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] (xs : t α) : to_list xs = fold_map free.mk xs := sorry

theorem fold_map_map {α : Type u} {β : Type u} {γ : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] [monoid γ] (f : α → β) (g : β → γ) (xs : t α) : fold_map g (f <$> xs) = fold_map (g ∘ f) xs := sorry

theorem foldl_to_list {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] (f : α → β → α) (xs : t β) (x : α) : foldl f x xs = list.foldl f x (to_list xs) := sorry

theorem foldr_to_list {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] (f : α → β → β) (xs : t α) (x : β) : foldr f x xs = list.foldr f x (to_list xs) := sorry

theorem to_list_map {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] (f : α → β) (xs : t α) : to_list (f <$> xs) = f <$> to_list xs := sorry

@[simp] theorem foldl_map {α : Type u} {β : Type u} {γ : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] (g : β → γ) (f : α → γ → α) (a : α) (l : t β) : foldl f a (g <$> l) = foldl (fun (x : α) (y : β) => f x (g y)) a l := sorry

@[simp] theorem foldr_map {α : Type u} {β : Type u} {γ : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] (g : β → γ) (f : γ → α → α) (a : α) (l : t β) : foldr f a (g <$> l) = foldr (f ∘ g) a l := sorry

@[simp] theorem to_list_eq_self {α : Type u} {xs : List α} : to_list xs = xs := sorry

theorem length_to_list {α : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {xs : t α} : length xs = list.length (to_list xs) := sorry

theorem mfoldl_to_list {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {m : Type u → Type u} [Monad m] [is_lawful_monad m] {f : α → β → m α} {x : α} {xs : t β} : mfoldl f x xs = mfoldl f x (to_list xs) := sorry

theorem mfoldr_to_list {α : Type u} {β : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {m : Type u → Type u} [Monad m] [is_lawful_monad m] (f : α → β → m β) (x : β) (xs : t α) : mfoldr f x xs = list.mfoldr f x (to_list xs) := sorry

@[simp] theorem mfoldl_map {α : Type u} {β : Type u} {γ : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {m : Type u → Type u} [Monad m] [is_lawful_monad m] (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) : mfoldl f a (g <$> l) = mfoldl (fun (x : α) (y : β) => f x (g y)) a l := sorry

@[simp] theorem mfoldr_map {α : Type u} {β : Type u} {γ : Type u} {t : Type u → Type u} [traversable t] [is_lawful_traversable t] {m : Type u → Type u} [Monad m] [is_lawful_monad m] (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) : mfoldr f a (g <$> l) = mfoldr (f ∘ g) a l := sorry

