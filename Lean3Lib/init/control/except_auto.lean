/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Sebastian Ullrich

The except monad transformer.
-/
import PrePort
import Lean3Lib.init.control.alternative
import Lean3Lib.init.control.lift
import PostPort

universes u v l u_1 w u_2 

namespace Mathlib

inductive except (ε : Type u) (α : Type v) 
where
| error : ε → except ε α
| ok : α → except ε α

namespace except


protected def return {ε : Type u} {α : Type v} (a : α) : except ε α :=
  ok a

protected def map {ε : Type u} {α : Type v} {β : Type v} (f : α → β) : except ε α → except ε β :=
  sorry

protected def map_error {ε : Type u} {ε' : Type u} {α : Type v} (f : ε → ε') : except ε α → except ε' α :=
  sorry

protected def bind {ε : Type u} {α : Type v} {β : Type v} (ma : except ε α) (f : α → except ε β) : except ε β :=
  sorry

protected def to_bool {ε : Type u} {α : Type v} : except ε α → Bool :=
  sorry

protected def to_option {ε : Type u} {α : Type v} : except ε α → Option α :=
  sorry

protected instance monad {ε : Type u} : Monad (except ε) := sorry

end except


structure except_t (ε : Type u) (m : Type u → Type v) (α : Type u) 
where
  run : m (except ε α)

namespace except_t


protected def return {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : except_t ε m α :=
  mk (pure (except.ok a))

protected def bind_cont {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (f : α → except_t ε m β) : except ε α → m (except ε β) :=
  sorry

protected def bind {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (ma : except_t ε m α) (f : α → except_t ε m β) : except_t ε m β :=
  mk (run ma >>= except_t.bind_cont f)

protected def lift {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (t : m α) : except_t ε m α :=
  mk (except.ok <$> t)

protected instance has_monad_lift {ε : Type u} {m : Type u → Type v} [Monad m] : has_monad_lift m (except_t ε m) :=
  has_monad_lift.mk except_t.lift

protected def catch {ε : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (ma : except_t ε m α) (handle : ε → except_t ε m α) : except_t ε m α :=
  mk
    do 
      run ma 
      sorry

protected def monad_map {ε : Type u} {m : Type u → Type v} [Monad m] {m' : Type u → Type u_1} [Monad m'] {α : Type u} (f : {α : Type u} → m α → m' α) : except_t ε m α → except_t ε m' α :=
  fun (x : except_t ε m α) => mk (f (run x))

protected instance monad_functor {ε : Type u} {m : Type u → Type v} [Monad m] (m' : Type u → Type v) [Monad m'] : monad_functor m m' (except_t ε m) (except_t ε m') :=
  monad_functor.mk except_t.monad_map

protected instance monad {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (except_t ε m) := sorry

protected def adapt {ε : Type u} {m : Type u → Type v} [Monad m] {ε' : Type u} {α : Type u} (f : ε → ε') : except_t ε m α → except_t ε' m α :=
  fun (x : except_t ε m α) => mk (except.map_error f <$> run x)

end except_t


/-- An implementation of [MonadError](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Except.html#t:MonadError) -/
class monad_except (ε : outParam (Type u)) (m : Type v → Type w) 
where
  throw : {α : Type v} → ε → m α
  catch : {α : Type v} → m α → (ε → m α) → m α

namespace monad_except


protected def orelse {ε : Type u} {m : Type v → Type w} [monad_except ε m] {α : Type v} (t₁ : m α) (t₂ : m α) : m α :=
  catch t₁ fun (_x : ε) => t₂

/-- Alternative orelse operator that allows to select which exception should be used.
    The default is to use the first exception since the standard `orelse` uses the second. -/
end monad_except


protected instance except_t.monad_except (m : Type u_1 → Type u_2) (ε : outParam (Type u_1)) [Monad m] : monad_except ε (except_t ε m) :=
  monad_except.mk (fun (α : Type u_1) => except_t.mk ∘ pure ∘ except.error) except_t.catch

/-- Adapt a monad stack, changing its top-most error type.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_except_functor (ε ε' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [monad m], except_t ε m α → except_t ε' m α) → n α → n' α)
    ```
    -/
class monad_except_adapter (ε : outParam (Type u)) (ε' : outParam (Type u)) (m : Type u → Type v) (m' : Type u → Type v) 
where
  adapt_except : {α : Type u} → (ε → ε') → m α → m' α

protected instance monad_except_adapter_trans {ε : Type u} {ε' : Type u} {m : Type u → Type v} {m' : Type u → Type v} {n : Type u → Type v} {n' : Type u → Type v} [monad_functor m m' n n'] [monad_except_adapter ε ε' m m'] : monad_except_adapter ε ε' n n' :=
  monad_except_adapter.mk fun (α : Type u) (f : ε → ε') => monad_map fun (α : Type u) => adapt_except f

protected instance except_t.monad_except_adapter {ε : Type u} {ε' : Type u} {m : Type u → Type v} [Monad m] : monad_except_adapter ε ε' (except_t ε m) (except_t ε' m) :=
  monad_except_adapter.mk fun (α : Type u) => except_t.adapt

protected instance except_t.monad_run (ε : Type u_1) (m : Type u_1 → Type u_2) (out : outParam (Type u_1 → Type u_2)) [monad_run out m] : monad_run (fun (α : Type u_1) => out (except ε α)) (except_t ε m) :=
  monad_run.mk fun (α : Type u_1) => run ∘ except_t.run

