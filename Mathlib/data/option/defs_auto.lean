/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Extra definitions on option.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u_1 u_2 u v w 

namespace Mathlib

namespace option


/-- An elimination principle for `option`. It is a nondependent version of `option.rec_on`. -/
@[simp] protected def elim {α : Type u_1} {β : Type u_2} : Option α → β → (α → β) → β := sorry

protected instance has_mem {α : Type u_1} : has_mem α (Option α) :=
  has_mem.mk fun (a : α) (b : Option α) => b = some a

@[simp] theorem mem_def {α : Type u_1} {a : α} {b : Option α} : a ∈ b ↔ b = some a := iff.rfl

theorem is_none_iff_eq_none {α : Type u_1} {o : Option α} : is_none o = tt ↔ o = none :=
  { mp := eq_none_of_is_none, mpr := fun (e : o = none) => Eq.symm e ▸ rfl }

theorem some_inj {α : Type u_1} {a : α} {b : α} : some a = some b ↔ a = b := sorry

/--
`o = none` is decidable even if the wrapped type does not have decidable equality.

This is not an instance because it is not definitionally equal to `option.decidable_eq`.
Try to use `o.is_none` or `o.is_some` instead.
-/
def decidable_eq_none {α : Type u_1} {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff (bool.decidable_eq (is_none o) tt) is_none_iff_eq_none

protected instance decidable_forall_mem {α : Type u_1} {p : α → Prop} [decidable_pred p]
    (o : Option α) : Decidable (∀ (a : α), a ∈ o → p a) :=
  sorry

protected instance decidable_exists_mem {α : Type u_1} {p : α → Prop} [decidable_pred p]
    (o : Option α) : Decidable (∃ (a : α), ∃ (H : a ∈ o), p a) :=
  sorry

/-- inhabited `get` function. Returns `a` if the input is `some a`,
  otherwise returns `default`. -/
def iget {α : Type u_1} [Inhabited α] : Option α → α := sorry

@[simp] theorem iget_some {α : Type u_1} [Inhabited α] {a : α} : iget (some a) = a := rfl

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard {α : Type u_1} (p : α → Prop) [decidable_pred p] (a : α) : Option α :=
  ite (p a) (some a) none

/-- `filter p o` returns `some a` if `o` is `some a`
  and `p a` holds, otherwise `none`. -/
def filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (o : Option α) : Option α :=
  option.bind o (guard p)

def to_list {α : Type u_1} : Option α → List α := sorry

@[simp] theorem mem_to_list {α : Type u_1} {a : α} {o : Option α} : a ∈ to_list o ↔ a ∈ o := sorry

def lift_or_get {α : Type u_1} (f : α → α → α) : Option α → Option α → Option α := sorry

protected instance lift_or_get_comm {α : Type u_1} (f : α → α → α) [h : is_commutative α f] :
    is_commutative (Option α) (lift_or_get f) :=
  sorry

protected instance lift_or_get_assoc {α : Type u_1} (f : α → α → α) [h : is_associative α f] :
    is_associative (Option α) (lift_or_get f) :=
  sorry

protected instance lift_or_get_idem {α : Type u_1} (f : α → α → α) [h : is_idempotent α f] :
    is_idempotent (Option α) (lift_or_get f) :=
  sorry

protected instance lift_or_get_is_left_id {α : Type u_1} (f : α → α → α) :
    is_left_id (Option α) (lift_or_get f) none :=
  is_left_id.mk
    fun (a : Option α) =>
      option.cases_on a
        (eq.mpr
          (id
            (Eq.trans
              ((fun (a a_1 : Option α) (e_1 : a = a_1) (ᾰ ᾰ_1 : Option α) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg Eq e_1) e_2)
                (lift_or_get f none none) none (lift_or_get.equations._eqn_1 f) none none
                (Eq.refl none))
              (propext (eq_self_iff_true none))))
          trivial)
        fun (a : α) =>
          eq.mpr
            (id
              (Eq.trans
                (Eq.trans
                  ((fun (a a_1 : Option α) (e_1 : a = a_1) (ᾰ ᾰ_1 : Option α) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg Eq e_1) e_2)
                    (lift_or_get f none (some a)) (some a) (lift_or_get.equations._eqn_2 f a)
                    (some a) (some a) (Eq.refl (some a)))
                  (some.inj_eq a a))
                (propext (eq_self_iff_true a))))
            trivial

protected instance lift_or_get_is_right_id {α : Type u_1} (f : α → α → α) :
    is_right_id (Option α) (lift_or_get f) none :=
  is_right_id.mk
    fun (a : Option α) =>
      option.cases_on a
        (eq.mpr
          (id
            (Eq.trans
              ((fun (a a_1 : Option α) (e_1 : a = a_1) (ᾰ ᾰ_1 : Option α) (e_2 : ᾰ = ᾰ_1) =>
                  congr (congr_arg Eq e_1) e_2)
                (lift_or_get f none none) none (lift_or_get.equations._eqn_1 f) none none
                (Eq.refl none))
              (propext (eq_self_iff_true none))))
          trivial)
        fun (a : α) =>
          eq.mpr
            (id
              (Eq.trans
                (Eq.trans
                  ((fun (a a_1 : Option α) (e_1 : a = a_1) (ᾰ ᾰ_1 : Option α) (e_2 : ᾰ = ᾰ_1) =>
                      congr (congr_arg Eq e_1) e_2)
                    (lift_or_get f (some a) none) (some a) (lift_or_get.equations._eqn_3 f a)
                    (some a) (some a) (Eq.refl (some a)))
                  (some.inj_eq a a))
                (propext (eq_self_iff_true a))))
            trivial

inductive rel {α : Type u_1} {β : Type u_2} (r : α → β → Prop) : Option α → Option β → Prop where
| some : ∀ {a : α} {b : β}, r a b → rel r (some a) (some b)
| none : rel r none none

/-- Partial bind. If for some `x : option α`, `f : Π (a : α), a ∈ x → option β` is a
  partial function defined on `a : α` giving an `option β`, where `some a = x`,
  then `pbind x f h` is essentially the same as `bind x f`
  but is defined only when all `x = some a`, using the proof to apply `f`. -/
@[simp] def pbind {α : Type u_1} {β : Type u_2} (x : Option α) :
    ((a : α) → a ∈ x → Option β) → Option β :=
  sorry

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f x h` is essentially the same as `map f x`
  but is defined only when all members of `x` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β)
    (x : Option α) : (∀ (a : α), a ∈ x → p a) → Option β :=
  sorry

/--
Flatten an `option` of `option`, a specialization of `mjoin`.
-/
@[simp] def join {α : Type u_1} : Option (Option α) → Option α :=
  fun (x : Option (Option α)) => x >>= id

protected def traverse {F : Type u → Type v} [Applicative F] {α : Type u_1} {β : Type u}
    (f : α → F β) : Option α → F (Option β) :=
  sorry

/- By analogy with `monad.sequence` in `init/category/combinators.lean`. -/

/-- If you maybe have a monadic computation in a `[monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result. -/
def maybe {m : Type u → Type v} [Monad m] {α : Type u} : Option (m α) → m (Option α) := sorry

/-- Map a monadic function `f : α → m β` over an `o : option α`, maybe producing a result. -/
def mmap {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) (o : Option α) :
    m (Option β) :=
  maybe (option.map f o)

end Mathlib