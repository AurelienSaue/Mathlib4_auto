/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Traversable instance for lazy_lists.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.traversable.equiv
import Mathlib.control.traversable.instances
import Mathlib.Lean3Lib.data.lazy_list
import Mathlib.PostPort

universes u_1 u u_2 u_3 

namespace Mathlib

/-!
## Definitions on lazy lists

This file contains various definitions and proofs on lazy lists.

TODO: move the `lazy_list.lean` file from core to mathlib.
-/

namespace thunk


/-- Creates a thunk with a (non-lazy) constant value. -/
def mk {α : Type u_1} (x : α) : thunk α := fun (_x : Unit) => x

protected instance decidable_eq {α : Type u} [DecidableEq α] : DecidableEq (thunk α) := sorry

end thunk


namespace lazy_list


/-- Isomorphism between strict and lazy lists. -/
def list_equiv_lazy_list (α : Type u_1) : List α ≃ lazy_list α :=
  equiv.mk of_list to_list sorry sorry

protected instance inhabited {α : Type u} : Inhabited (lazy_list α) := { default := nil }

protected instance decidable_eq {α : Type u} [DecidableEq α] : DecidableEq (lazy_list α) := sorry

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicative m] {α : Type u} {β : Type u}
    (f : α → m β) : lazy_list α → m (lazy_list β) :=
  sorry

protected instance traversable : traversable lazy_list := traversable.mk lazy_list.traverse

protected instance is_lawful_traversable : is_lawful_traversable lazy_list :=
  equiv.is_lawful_traversable' list_equiv_lazy_list sorry sorry sorry

/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list. -/
def init {α : Type u_1} : lazy_list α → lazy_list α := sorry

/-- Return the first object contained in the list that satisfies
predicate `p` -/
def find {α : Type u_1} (p : α → Prop) [decidable_pred p] : lazy_list α → Option α := sorry

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α : Type u_1} : lazy_list α → lazy_list α → lazy_list α := sorry

/-- `interleave_all (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleave_all {α : Type u_1} : List (lazy_list α) → lazy_list α := sorry

/-- Monadic bind operation for `lazy_list`. -/
protected def bind {α : Type u_1} {β : Type u_2} : lazy_list α → (α → lazy_list β) → lazy_list β :=
  sorry

/-- Reverse the order of a `lazy_list`.
It is done by converting to a `list` first because reversal involves evaluating all
the list and if the list is all evaluated, `list` is a better representation for
it than a series of thunks. -/
def reverse {α : Type u_1} (xs : lazy_list α) : lazy_list α := of_list (list.reverse (to_list xs))

protected instance monad : Monad lazy_list := sorry

theorem append_nil {α : Type u_1} (xs : lazy_list α) : (append xs fun (_ : Unit) => nil) = xs :=
  sorry

theorem append_assoc {α : Type u_1} (xs : lazy_list α) (ys : lazy_list α) (zs : lazy_list α) :
    (append (append xs fun (_ : Unit) => ys) fun (_ : Unit) => zs) =
        append xs fun (_ : Unit) => append ys fun (_ : Unit) => zs :=
  sorry

theorem append_bind {α : Type u_1} {β : Type u_2} (xs : lazy_list α) (ys : thunk (lazy_list α))
    (f : α → lazy_list β) :
    lazy_list.bind (append xs ys) f =
        append (lazy_list.bind xs f) fun (_ : Unit) => lazy_list.bind (ys Unit.unit) f :=
  sorry

protected instance is_lawful_monad : is_lawful_monad lazy_list := sorry

/-- Try applying function `f` to every element of a `lazy_list` and
return the result of the first attempt that succeeds. -/
def mfirst {m : Type u_1 → Type u_2} [alternative m] {α : Type u_3} {β : Type u_1} (f : α → m β) :
    lazy_list α → m β :=
  sorry

/-- Membership in lazy lists -/
protected def mem {α : Type u_1} (x : α) : lazy_list α → Prop := sorry

protected instance has_mem {α : outParam (Type u_1)} : has_mem α (lazy_list α) :=
  has_mem.mk lazy_list.mem

protected instance mem.decidable {α : Type u_1} [DecidableEq α] (x : α) (xs : lazy_list α) :
    Decidable (x ∈ xs) :=
  sorry

@[simp] theorem mem_nil {α : Type u_1} (x : α) : x ∈ nil ↔ False := iff.rfl

@[simp] theorem mem_cons {α : Type u_1} (x : α) (y : α) (ys : thunk (lazy_list α)) :
    x ∈ cons y ys ↔ x = y ∨ x ∈ ys Unit.unit :=
  iff.rfl

theorem forall_mem_cons {α : Type u_1} {p : α → Prop} {a : α} {l : thunk (lazy_list α)} :
    (∀ (x : α), x ∈ cons a l → p x) ↔ p a ∧ ∀ (x : α), x ∈ l Unit.unit → p x :=
  sorry

/-! ### map for partial functions -/

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β)
    (l : lazy_list α) : (∀ (a : α), a ∈ l → p a) → lazy_list β :=
  sorry

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `lazy_list`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α : Type u_1} (l : lazy_list α) : lazy_list (Subtype fun (x : α) => x ∈ l) :=
  pmap Subtype.mk l sorry

protected instance has_repr {α : Type u_1} [has_repr α] : has_repr (lazy_list α) :=
  has_repr.mk fun (xs : lazy_list α) => repr (to_list xs)

end Mathlib