/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.basic
import PostPort

universes u u_1 u_2 

namespace Mathlib

/-!
# A type for VM-erased data

This file defines a type `erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `erased α` is
represented as `0`, just like types and proofs.
-/

/-- `erased α` is the same as `α`, except that the elements
  of `erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def erased (α : Sort u)  :=
  psigma fun (s : α → Prop) => ∃ (a : α), (fun (b : α) => a = b) = s

namespace erased


/-- Erase a value. -/
def mk {α : Sort u_1} (a : α) : erased α :=
  psigma.mk (fun (b : α) => a = b) sorry

/-- Extracts the erased value, noncomputably. -/
def out {α : Sort u_1} : erased α → α :=
  sorry

/--
Extracts the erased value, if it is a type.

Note: `(mk a).out_type` is not definitionally equal to `a`.
-/
def out_type (a : erased (Sort u))  :=
  out a

/-- Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : erased p) : p :=
  out a

@[simp] theorem out_mk {α : Sort u_1} (a : α) : out (mk a) = a :=
  let h : ∃ (x : α), (fun (b : α) => x = b) = fun (b : α) => a = b := mk._proof_1 a;
  id (cast (Eq.symm (congr_fun (classical.some_spec h) a)) rfl)

@[simp] theorem mk_out {α : Sort u_1} (a : erased α) : mk (out a) = a := sorry

theorem out_inj {α : Sort u_1} (a : erased α) (b : erased α) (h : out a = out b) : a = b := sorry

/-- Equivalence between `erased α` and `α`. -/
def equiv (α : Sort u_1) : erased α ≃ α :=
  equiv.mk out mk mk_out out_mk

protected instance has_repr (α : Type u) : has_repr (erased α) :=
  has_repr.mk
    fun (_x : erased α) =>
      string.str
        (string.str
          (string.str
            (string.str
              (string.str (string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
                (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
              (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
            (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
        (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))))

protected instance has_to_string (α : Type u) : has_to_string (erased α) :=
  has_to_string.mk
    fun (_x : erased α) =>
      string.str
        (string.str
          (string.str
            (string.str
              (string.str (string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
                (char.of_nat (bit0 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
              (char.of_nat (bit1 (bit0 (bit0 (bit0 (bit0 (bit1 1))))))))
            (char.of_nat (bit1 (bit1 (bit0 (bit0 (bit1 (bit1 1))))))))
          (char.of_nat (bit1 (bit0 (bit1 (bit0 (bit0 (bit1 1))))))))
        (char.of_nat (bit0 (bit0 (bit1 (bit0 (bit0 (bit1 1)))))))

/-- Computably produce an erased value from a proof of nonemptiness. -/
def choice {α : Sort u_1} (h : Nonempty α) : erased α :=
  mk (Classical.choice h)

@[simp] theorem nonempty_iff {α : Sort u_1} : Nonempty (erased α) ↔ Nonempty α := sorry

protected instance inhabited {α : Sort u_1} [h : Nonempty α] : Inhabited (erased α) :=
  { default := choice h }

/--
`(>>=)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `monad`).
-/
def bind {α : Sort u_1} {β : Sort u_2} (a : erased α) (f : α → erased β) : erased β :=
  psigma.mk (fun (b : β) => psigma.fst (f (out a)) b) sorry

@[simp] theorem bind_eq_out {α : Sort u_1} {β : Sort u_2} (a : erased α) (f : α → erased β) : bind a f = f (out a) := sorry

/--
Collapses two levels of erasure.
-/
def join {α : Sort u_1} (a : erased (erased α)) : erased α :=
  bind a id

@[simp] theorem join_eq_out {α : Sort u_1} (a : erased (erased α)) : join a = out a :=
  bind_eq_out a id

/--
`(<$>)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `functor`).
-/
def map {α : Sort u_1} {β : Sort u_2} (f : α → β) (a : erased α) : erased β :=
  bind a (mk ∘ f)

@[simp] theorem map_out {α : Sort u_1} {β : Sort u_2} {f : α → β} (a : erased α) : out (map f a) = f (out a) := sorry

protected instance monad : Monad erased :=
  { toApplicative :=
      { toFunctor := { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β }, toPure := { pure := mk },
        toSeq :=
          { seq := fun (α β : Type u_1) (f : erased (α → β)) (x : erased α) => bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : erased α) (b : erased β) =>
                (fun (α β : Type u_1) (f : erased (α → β)) (x : erased α) => bind f fun (_x : α → β) => map _x x) β α
                  (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : erased α) (b : erased β) =>
                (fun (α β : Type u_1) (f : erased (α → β)) (x : erased α) => bind f fun (_x : α → β) => map _x x) β β
                  (map (function.const α id) a) b } },
    toBind := { bind := bind } }

@[simp] theorem pure_def {α : Type u_1} : pure = mk :=
  rfl

@[simp] theorem bind_def {α : Type u_1} {β : Type u_1} : bind = bind :=
  rfl

@[simp] theorem map_def {α : Type u_1} {β : Type u_1} : Functor.map = map :=
  rfl

protected instance is_lawful_monad : is_lawful_monad erased := sorry

