/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.alternative
import Mathlib.Lean3Lib.init.control.lift
import Mathlib.Lean3Lib.init.control.except
import Mathlib.PostPort

universes u v l u_1 u_2 

namespace Mathlib

structure option_t (m : Type u → Type v) (α : Type u) 
where
  run : m (Option α)

namespace option_t


protected def bind_cont {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (f : α → option_t m β) : Option α → m (Option β) :=
  sorry

protected def bind {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (ma : option_t m α) (f : α → option_t m β) : option_t m β :=
  mk (run ma >>= option_t.bind_cont f)

protected def pure {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : option_t m α :=
  mk (pure (some a))

protected instance monad {m : Type u → Type v} [Monad m] : Monad (option_t m) := sorry

protected def orelse {m : Type u → Type v} [Monad m] {α : Type u} (ma : option_t m α) (mb : option_t m α) : option_t m α :=
  mk
    do 
      run ma 
      sorry

protected def fail {m : Type u → Type v} [Monad m] {α : Type u} : option_t m α :=
  mk (pure none)

def of_option {m : Type u → Type v} [Monad m] {α : Type u} : Option α → option_t m α :=
  sorry

protected instance alternative {m : Type u → Type v} [Monad m] : alternative (option_t m) :=
  alternative.mk option_t.fail

protected def lift {m : Type u → Type v} [Monad m] {α : Type u} (ma : m α) : option_t m α :=
  mk (some <$> ma)

protected instance has_monad_lift {m : Type u → Type v} [Monad m] : has_monad_lift m (option_t m) :=
  has_monad_lift.mk option_t.lift

protected def monad_map {m : Type u → Type v} [Monad m] {m' : Type u → Type u_1} [Monad m'] {α : Type u} (f : {α : Type u} → m α → m' α) : option_t m α → option_t m' α :=
  fun (x : option_t m α) => mk (f (run x))

protected instance monad_functor {m : Type u → Type v} [Monad m] (m' : Type u → Type v) [Monad m'] : monad_functor m m' (option_t m) (option_t m') :=
  monad_functor.mk fun (α : Type u) => option_t.monad_map

protected def catch {m : Type u → Type v} [Monad m] {α : Type u} (ma : option_t m α) (handle : Unit → option_t m α) : option_t m α :=
  mk
    do 
      run ma 
      sorry

protected instance monad_except {m : Type u → Type v} [Monad m] : monad_except Unit (option_t m) :=
  monad_except.mk (fun (_x : Type u) (_x_1 : Unit) => option_t.fail) option_t.catch

protected instance monad_run (m : Type u_1 → Type u_2) (out : outParam (Type u_1 → Type u_2)) [monad_run out m] : monad_run (fun (α : Type u_1) => out (Option α)) (option_t m) :=
  monad_run.mk fun (α : Type u_1) => run ∘ run

