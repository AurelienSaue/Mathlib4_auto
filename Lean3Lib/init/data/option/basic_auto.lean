/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import PrePort
import Lean3Lib.init.logic
import Lean3Lib.init.control.monad
import Lean3Lib.init.control.alternative
import PostPort

universes u v u_1 u_2 

namespace Mathlib

namespace option


def to_monad {m : Type → Type} [Monad m] [alternative m] {A : Type} : Option A → m A :=
  sorry

def get_or_else {α : Type u} : Option α → α → α :=
  sorry

def is_some {α : Type u} : Option α → Bool :=
  sorry

def is_none {α : Type u} : Option α → Bool :=
  sorry

def get {α : Type u} {o : Option α} : ↥(is_some o) → α :=
  sorry

def rhoare {α : Type u} : Bool → α → Option α :=
  sorry

def lhoare {α : Type u} : α → Option α → α :=
  sorry

infixr:1 "|>" => Mathlib.option.rhoare

infixr:1 "<|" => Mathlib.option.lhoare

protected def bind {α : Type u} {β : Type v} : Option α → (α → Option β) → Option β :=
  sorry

protected def map {α : Type u_1} {β : Type u_2} (f : α → β) (o : Option α) : Option β :=
  option.bind o (some ∘ f)

theorem map_id {α : Type u_1} : option.map id = id := sorry

protected instance monad : Monad Option :=
  { toApplicative :=
      { toFunctor := { map := option.map, mapConst := fun (α β : Type u_1) => option.map ∘ function.const β },
        toPure := { pure := some },
        toSeq :=
          { seq :=
              fun (α β : Type u_1) (f : Option (α → β)) (x : Option α) =>
                option.bind f fun (_x : α → β) => option.map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : Option α) (b : Option β) =>
                (fun (α β : Type u_1) (f : Option (α → β)) (x : Option α) =>
                    option.bind f fun (_x : α → β) => option.map _x x)
                  β α (option.map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : Option α) (b : Option β) =>
                (fun (α β : Type u_1) (f : Option (α → β)) (x : Option α) =>
                    option.bind f fun (_x : α → β) => option.map _x x)
                  β β (option.map (function.const α id) a) b } },
    toBind := { bind := option.bind } }

protected def orelse {α : Type u} : Option α → Option α → Option α :=
  sorry

protected instance alternative : alternative Option :=
  alternative.mk none

end option


protected instance option.inhabited (α : Type u) : Inhabited (Option α) :=
  { default := none }

protected instance option.decidable_eq {α : Type u} [d : DecidableEq α] : DecidableEq (Option α) :=
  sorry

