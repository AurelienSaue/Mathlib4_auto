/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.ext
import Mathlib.tactic.lint.default
import Mathlib.PostPort

universes u v u_1 u_2 u_3 w 

namespace Mathlib

/-!
# Functors

This module provides additional lemmas, definitions, and instances for `functor`s.

## Main definitions

* `const α` is the functor that sends all types to `α`.
* `add_const α` is `const α` but for when `α` has an additive structure.
* `comp F G` for functors `F` and `G` is the functor composition of `F` and `G`.
* `liftp` and `liftr` respectively lift predicates and relations on a type `α`
  to `F α`.  Terms of `F α` are considered to, in some sense, contain values of type `α`.

## Tags

functor, applicative
-/

theorem functor.map_id {F : Type u → Type v} {α : Type u} [Functor F] [is_lawful_functor F] :
    Functor.map id = id :=
  funext id_map

theorem functor.map_comp_map {F : Type u → Type v} {α : Type u} {β : Type u} {γ : Type u}
    [Functor F] [is_lawful_functor F] (f : α → β) (g : β → γ) :
    Functor.map g ∘ Functor.map f = Functor.map (g ∘ f) :=
  sorry

theorem functor.ext {F : Type u_1 → Type u_2} {F1 : Functor F} {F2 : Functor F}
    [is_lawful_functor F] [is_lawful_functor F]
    (H : ∀ (α β : Type u_1) (f : α → β) (x : F α), f <$> x = f <$> x) : F1 = F2 :=
  sorry

/-- Introduce the `id` functor. Incidentally, this is `pure` for
`id` as a `monad` and as an `applicative` functor. -/
def id.mk {α : Sort u} : α → id α := id

namespace functor


/-- `const α` is the constant functor, mapping every type to `α`. When
`α` has a monoid structure, `const α` has an `applicative` instance.
(If `α` has an additive monoid structure, see `functor.add_const`.) -/
def const (α : Type u_1) (β : Type u_2) := α

/-- `const.mk` is the canonical map `α → const α β` (the identity), and
it can be used as a pattern to extract this value. -/
def const.mk {α : Type u_1} {β : Type u_2} (x : α) : const α β := x

/-- `const.mk'` is `const.mk` but specialized to map `α` to
`const α punit`, where `punit` is the terminal object in `Type*`. -/
def const.mk' {α : Type u_1} (x : α) : const α PUnit := x

/-- Extract the element of `α` from the `const` functor. -/
def const.run {α : Type u_1} {β : Type u_2} (x : const α β) : α := x

namespace const


protected theorem ext {α : Type u_1} {β : Type u_2} {x : const α β} {y : const α β}
    (h : run x = run y) : x = y :=
  h

/-- The map operation of the `const γ` functor. -/
protected def map {γ : Type u_1} {α : Type u_2} {β : Type u_3} (f : α → β) (x : const γ β) :
    const γ α :=
  x

protected instance functor {γ : Type u_1} : Functor (const γ) :=
  { map := const.map, mapConst := fun (α β : Type u_2) => const.map ∘ function.const β }

protected instance is_lawful_functor {γ : Type u_1} : is_lawful_functor (const γ) :=
  is_lawful_functor.mk (fun (α : Type u_2) (x : const γ α) => Eq.refl (id <$> x))
    fun (α β γ_1 : Type u_2) (g : α → β) (h : β → γ_1) (x : const γ α) => Eq.refl ((h ∘ g) <$> x)

protected instance inhabited {α : Type u_1} {β : Type u_2} [Inhabited α] : Inhabited (const α β) :=
  { default := Inhabited.default }

end const


/-- `add_const α` is a synonym for constant functor `const α`, mapping
every type to `α`. When `α` has a additive monoid structure,
`add_const α` has an `applicative` instance. (If `α` has a
multiplicative monoid structure, see `functor.const`.) -/
def add_const (α : Type u_1) (β : Type u_2) := const α

/-- `add_const.mk` is the canonical map `α → add_const α β`, which is the identity,
where `add_const α β = const α β`. It can be used as a pattern to extract this value. -/
def add_const.mk {α : Type u_1} {β : Type u_2} (x : α) : add_const α β := x

/-- Extract the element of `α` from the constant functor. -/
def add_const.run {α : Type u_1} {β : Type u_2} : add_const α β → α := id

protected instance add_const.functor {γ : Type u_1} : Functor (add_const γ) := const.functor

protected instance add_const.is_lawful_functor {γ : Type u_1} : is_lawful_functor (add_const γ) :=
  const.is_lawful_functor

protected instance add_const.inhabited {α : Type u_1} {β : Type u_2} [Inhabited α] :
    Inhabited (add_const α β) :=
  { default := Inhabited.default }

/-- `functor.comp` is a wrapper around `function.comp` for types.
    It prevents Lean's type class resolution mechanism from trying
    a `functor (comp F id)` when `functor F` would do. -/
def comp (F : Type u → Type w) (G : Type v → Type u) (α : Type v) := F (G α)

/-- Construct a term of `comp F G α` from a term of `F (G α)`, which is the same type.
Can be used as a pattern to extract a term of `F (G α)`. -/
def comp.mk {F : Type u → Type w} {G : Type v → Type u} {α : Type v} (x : F (G α)) : comp F G α := x

/-- Extract a term of `F (G α)` from a term of `comp F G α`, which is the same type. -/
def comp.run {F : Type u → Type w} {G : Type v → Type u} {α : Type v} (x : comp F G α) : F (G α) :=
  x

namespace comp


protected theorem ext {F : Type u → Type w} {G : Type v → Type u} {α : Type v} {x : comp F G α}
    {y : comp F G α} : run x = run y → x = y :=
  id

protected instance inhabited {F : Type u → Type w} {G : Type v → Type u} {α : Type v}
    [Inhabited (F (G α))] : Inhabited (comp F G α) :=
  { default := Inhabited.default }

/-- The map operation for the composition `comp F G` of functors `F` and `G`. -/
protected def map {F : Type u → Type w} {G : Type v → Type u} [Functor F] [Functor G] {α : Type v}
    {β : Type v} (h : α → β) : comp F G α → comp F G β :=
  sorry

protected instance functor {F : Type u → Type w} {G : Type v → Type u} [Functor F] [Functor G] :
    Functor (comp F G) :=
  { map := comp.map, mapConst := fun (α β : Type v) => comp.map ∘ function.const β }

theorem map_mk {F : Type u → Type w} {G : Type v → Type u} [Functor F] [Functor G] {α : Type v}
    {β : Type v} (h : α → β) (x : F (G α)) : h <$> mk x = mk (Functor.map h <$> x) :=
  rfl

@[simp] protected theorem run_map {F : Type u → Type w} {G : Type v → Type u} [Functor F]
    [Functor G] {α : Type v} {β : Type v} (h : α → β) (x : comp F G α) :
    run (h <$> x) = Functor.map h <$> run x :=
  rfl

protected theorem id_map {F : Type u → Type w} {G : Type v → Type u} [Functor F] [Functor G]
    [is_lawful_functor F] [is_lawful_functor G] {α : Type v} (x : comp F G α) : comp.map id x = x :=
  sorry

protected theorem comp_map {F : Type u → Type w} {G : Type v → Type u} [Functor F] [Functor G]
    [is_lawful_functor F] [is_lawful_functor G] {α : Type v} {β : Type v} {γ : Type v} (g' : α → β)
    (h : β → γ) (x : comp F G α) : comp.map (h ∘ g') x = comp.map h (comp.map g' x) :=
  sorry

protected instance is_lawful_functor {F : Type u → Type w} {G : Type v → Type u} [Functor F]
    [Functor G] [is_lawful_functor F] [is_lawful_functor G] : is_lawful_functor (comp F G) :=
  is_lawful_functor.mk comp.id_map comp.comp_map

theorem functor_comp_id {F : Type u_1 → Type u_2} [AF : Functor F] [is_lawful_functor F] :
    comp.functor = AF :=
  ext fun (α β : Type u_1) (f : α → β) (x : F α) => rfl

theorem functor_id_comp {F : Type u_1 → Type u_2} [AF : Functor F] [is_lawful_functor F] :
    comp.functor = AF :=
  ext fun (α β : Type u_1) (f : α → β) (x : F α) => rfl

end comp


namespace comp


/-- The `<*>` operation for the composition of applicative functors. -/
protected def seq {F : Type u → Type w} {G : Type v → Type u} [Applicative F] [Applicative G]
    {α : Type v} {β : Type v} : comp F G (α → β) → comp F G α → comp F G β :=
  sorry

protected instance has_pure {F : Type u → Type w} {G : Type v → Type u} [Applicative F]
    [Applicative G] : Pure (comp F G) :=
  { pure := fun (_x : Type v) (x : _x) => mk (pure (pure x)) }

protected instance has_seq {F : Type u → Type w} {G : Type v → Type u} [Applicative F]
    [Applicative G] : Seq (comp F G) :=
  { seq := fun (_x _x_1 : Type v) (f : comp F G (_x → _x_1)) (x : comp F G _x) => comp.seq f x }

@[simp] protected theorem run_pure {F : Type u → Type w} {G : Type v → Type u} [Applicative F]
    [Applicative G] {α : Type v} (x : α) : run (pure x) = pure (pure x) :=
  idRhs (run (pure x) = run (pure x)) rfl

@[simp] protected theorem run_seq {F : Type u → Type w} {G : Type v → Type u} [Applicative F]
    [Applicative G] {α : Type v} {β : Type v} (f : comp F G (α → β)) (x : comp F G α) :
    run (f <*> x) = Seq.seq <$> run f <*> run x :=
  rfl

protected instance applicative {F : Type u → Type w} {G : Type v → Type u} [Applicative F]
    [Applicative G] : Applicative (comp F G) :=
  { toFunctor := { map := comp.map, mapConst := fun (α β : Type v) => comp.map ∘ function.const β },
    toPure := { pure := pure }, toSeq := { seq := comp.seq },
    toSeqLeft :=
      { seqLeft :=
          fun (α β : Type v) (a : comp F G α) (b : comp F G β) =>
            comp.seq (comp.map (function.const β) a) b },
    toSeqRight :=
      { seqRight :=
          fun (α β : Type v) (a : comp F G α) (b : comp F G β) =>
            comp.seq (comp.map (function.const α id) a) b } }

end comp


/-- If we consider `x : F α` to, in some sense, contain values of type `α`, 
predicate `liftp p x` holds iff every value contained by `x` satisfies `p`. -/
def liftp {F : Type u → Type u} [Functor F] {α : Type u} (p : α → Prop) (x : F α) :=
  ∃ (u : F (Subtype p)), subtype.val <$> u = x

/-- If we consider `x : F α` to, in some sense, contain values of type `α`, then
`liftr r x y` relates `x` and `y` iff (1) `x` and `y` have the same shape and
(2) we can pair values `a` from `x` and `b` from `y` so that `r a b` holds. -/
def liftr {F : Type u → Type u} [Functor F] {α : Type u} (r : α → α → Prop) (x : F α) (y : F α) :=
  ∃ (u : F (Subtype fun (p : α × α) => r (prod.fst p) (prod.snd p))),
    (fun (t : Subtype fun (p : α × α) => r (prod.fst p) (prod.snd p)) =>
            prod.fst (subtype.val t)) <$>
          u =
        x ∧
      (fun (t : Subtype fun (p : α × α) => r (prod.fst p) (prod.snd p)) =>
            prod.snd (subtype.val t)) <$>
          u =
        y

/-- If we consider `x : F α` to, in some sense, contain values of type `α`, then
`supp x` is the set of values of type `α` that `x` contains. -/
def supp {F : Type u → Type u} [Functor F] {α : Type u} (x : F α) : set α :=
  set_of fun (y : α) => ∀ {p : α → Prop}, liftp p x → p y

theorem of_mem_supp {F : Type u → Type u} [Functor F] {α : Type u} {x : F α} {p : α → Prop}
    (h : liftp p x) (y : α) (H : y ∈ supp x) : p y :=
  hy h

end functor


namespace ulift


protected instance functor : Functor ulift :=
  { map := fun (α β : Type u_1) (f : α → β) => up ∘ f ∘ down,
    mapConst := fun (α β : Type u_1) => (fun (f : β → α) => up ∘ f ∘ down) ∘ function.const β }

end Mathlib