/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u l v 

namespace Mathlib

/-!
# Types with a unique term

In this file we define a typeclass `unique`,
which expresses that a type has a unique term.
In other words, a type that is `inhabited` and a `subsingleton`.

## Main declaration

* `unique`: a typeclass that expresses that a type has a unique term.

## Main statements

* `unique.mk'`: an inhabited subsingleton type is `unique`. This can not be an instance because it
  would lead to loops in typeclass inference.

* `function.surjective.unique`: if the domain of a surjective function is `unique`, then its
  codomain is `unique` as well.

* `function.injective.subsingleton`: if the codomain of an injective function is `subsingleton`,
  then its domain is `subsingleton` as well.

* `function.injective.unique`: if the codomain of an injective function is `subsingleton` and its
  domain is `inhabited`, then its domain is `unique`.

## Implementation details

The typeclass `unique α` is implemented as a type,
rather than a `Prop`-valued predicate,
for good definitional properties of the default term.

-/

/-- `unique α` expresses that `α` is a type with a unique term `default α`.

This is implemented as a type, rather than a `Prop`-valued predicate,
for good definitional properties of the default term. -/
class unique (α : Sort u) extends Inhabited α where
  uniq : ∀ (a : α), a = Inhabited.default

protected instance punit.unique : unique PUnit := unique.mk { default := PUnit.unit } sorry

theorem fin.eq_zero (n : fin 1) : n = 0 := sorry

protected instance fin.inhabited {n : ℕ} : Inhabited (fin (Nat.succ n)) := { default := 0 }

@[simp] theorem fin.default_eq_zero (n : ℕ) : Inhabited.default = 0 := rfl

protected instance fin.unique : unique (fin 1) :=
  unique.mk { default := Inhabited.default } fin.eq_zero

namespace unique


protected instance inhabited {α : Sort u} [unique α] : Inhabited α := to_inhabited _inst_1

theorem eq_default {α : Sort u} [unique α] (a : α) : a = Inhabited.default := uniq _inst_1 a

theorem default_eq {α : Sort u} [unique α] (a : α) : Inhabited.default = a :=
  Eq.symm (uniq _inst_1 a)

protected instance subsingleton {α : Sort u} [unique α] : subsingleton α :=
  subsingleton.intro
    fun (a b : α) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (a = b)) (eq_default a)))
        (eq.mpr (id (Eq._oldrec (Eq.refl (Inhabited.default = b)) (eq_default b)))
          (Eq.refl Inhabited.default))

theorem forall_iff {α : Sort u} [unique α] {p : α → Prop} :
    (∀ (a : α), p a) ↔ p Inhabited.default :=
  { mp := fun (h : ∀ (a : α), p a) => h Inhabited.default,
    mpr :=
      fun (h : p Inhabited.default) (x : α) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (p x)) (eq_default x))) h }

theorem exists_iff {α : Sort u} [unique α] {p : α → Prop} : Exists p ↔ p Inhabited.default := sorry

protected theorem subsingleton_unique' {α : Sort u} (h₁ : unique α) (h₂ : unique α) : h₁ = h₂ :=
  sorry

protected instance subsingleton_unique {α : Sort u} : subsingleton (unique α) :=
  subsingleton.intro unique.subsingleton_unique'

/-- Construct `unique` from `inhabited` and `subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
def mk' (α : Sort u) [h₁ : Inhabited α] [subsingleton α] : unique α :=
  mk { default := Inhabited.default } sorry

end unique


@[simp] theorem pi.default_def {α : Sort u} {β : α → Sort v} [(a : α) → Inhabited (β a)] :
    Inhabited.default = fun (a : α) => Inhabited.default :=
  rfl

theorem pi.default_apply {α : Sort u} {β : α → Sort v} [(a : α) → Inhabited (β a)] (a : α) :
    Inhabited.default a = Inhabited.default :=
  rfl

protected instance pi.unique {α : Sort u} {β : α → Sort v} [(a : α) → unique (β a)] :
    unique ((a : α) → β a) :=
  unique.mk { default := Inhabited.default } sorry

/-- There is a unique function on an empty domain. -/
def pi.unique_of_empty {α : Sort u} (h : α → False) (β : α → Sort v) : unique ((a : α) → β a) :=
  unique.mk { default := fun (a : α) => false.elim (h a) } sorry

namespace function


/-- If the domain of a surjective function is a singleton,
then the codomain is a singleton as well. -/
protected def surjective.unique {α : Sort u} {β : Sort v} {f : α → β} (hf : surjective f)
    [unique α] : unique β :=
  unique.mk { default := f Inhabited.default } sorry

/-- If the codomain of an injective function is a subsingleton, then the domain
is a subsingleton as well. -/
protected theorem injective.subsingleton {α : Sort u} {β : Sort v} {f : α → β} (hf : injective f)
    [subsingleton β] : subsingleton α :=
  subsingleton.intro fun (x y : α) => hf (subsingleton.elim (f x) (f y))

/-- If `α` is inhabited and admits an injective map to a subsingleton type, then `α` is `unique`. -/
protected def injective.unique {α : Sort u} {β : Sort v} {f : α → β} [Inhabited α] [subsingleton β]
    (hf : injective f) : unique α :=
  unique.mk' α

end Mathlib