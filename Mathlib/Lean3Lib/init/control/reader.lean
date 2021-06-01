/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The reader monad transformer for passing immutable state.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.lift
import Mathlib.Lean3Lib.init.control.id
import Mathlib.Lean3Lib.init.control.alternative
import Mathlib.Lean3Lib.init.control.except
 

universes u v l u_1 u_2 u_3 w 

namespace Mathlib

/-- An implementation of [ReaderT](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Reader.html#t:ReaderT) -/
structure reader_t (ρ : Type u) (m : Type u → Type v) (α : Type u) 
where
  run : ρ → m α

def reader (ρ : Type u) (α : Type u) :=
  reader_t ρ id

namespace reader_t


protected def read {ρ : Type u} {m : Type u → Type v} [Monad m] : reader_t ρ m ρ :=
  mk pure

protected def pure {ρ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : reader_t ρ m α :=
  mk fun (r : ρ) => pure a

protected def bind {ρ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (x : reader_t ρ m α) (f : α → reader_t ρ m β) : reader_t ρ m β :=
  mk
    fun (r : ρ) =>
      do 
        let a ← run x r 
        run (f a) r

protected instance monad {ρ : Type u} {m : Type u → Type v} [Monad m] : Monad (reader_t ρ m) := sorry

protected def lift {ρ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : m α) : reader_t ρ m α :=
  mk fun (r : ρ) => a

protected instance has_monad_lift {ρ : Type u} (m : Type u → Type u_1) [Monad m] : has_monad_lift m (reader_t ρ m) :=
  has_monad_lift.mk reader_t.lift

protected def monad_map {ρ : Type u_1} {m : Type u_1 → Type u_2} {m' : Type u_1 → Type u_3} [Monad m] [Monad m'] {α : Type u_1} (f : {α : Type u_1} → m α → m' α) : reader_t ρ m α → reader_t ρ m' α :=
  fun (x : reader_t ρ m α) => mk fun (r : ρ) => f (run x r)

protected instance monad_functor (ρ : Type u_1) (m : Type u_1 → Type u_2) (m' : Type u_1 → Type u_2) [Monad m] [Monad m'] : monad_functor m m' (reader_t ρ m) (reader_t ρ m') :=
  monad_functor.mk reader_t.monad_map

protected def adapt {ρ : Type u} {m : Type u → Type v} [Monad m] {ρ' : Type u} [Monad m] {α : Type u} (f : ρ' → ρ) : reader_t ρ m α → reader_t ρ' m α :=
  fun (x : reader_t ρ m α) => mk fun (r : ρ') => run x (f r)

protected def orelse {ρ : Type u} {m : Type u → Type v} [Monad m] [alternative m] {α : Type u} (x₁ : reader_t ρ m α) (x₂ : reader_t ρ m α) : reader_t ρ m α :=
  mk fun (s : ρ) => run x₁ s <|> run x₂ s

protected def failure {ρ : Type u} {m : Type u → Type v} [Monad m] [alternative m] {α : Type u} : reader_t ρ m α :=
  mk fun (s : ρ) => failure

protected instance alternative {ρ : Type u} {m : Type u → Type v} [Monad m] [alternative m] : alternative (reader_t ρ m) :=
  alternative.mk reader_t.failure

protected instance monad_except {ρ : Type u} {m : Type u → Type v} [Monad m] (ε : outParam (Type u_1)) [Monad m] [monad_except ε m] : monad_except ε (reader_t ρ m) :=
  monad_except.mk (fun (α : Type u) => reader_t.lift ∘ throw)
    fun (α : Type u) (x : reader_t ρ m α) (c : ε → reader_t ρ m α) =>
      mk fun (r : ρ) => catch (run x r) fun (e : ε) => run (c e) r

end reader_t


/-- An implementation of [MonadReader](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
    It does not contain `local` because this function cannot be lifted using `monad_lift`.
    Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
    ```
    -/
class monad_reader (ρ : outParam (Type u)) (m : Type u → Type v) 
where
  read : m ρ

protected instance monad_reader_trans {ρ : Type u} {m : Type u → Type v} {n : Type u → Type w} [monad_reader ρ m] [has_monad_lift m n] : monad_reader ρ n :=
  monad_reader.mk (monad_lift read)

protected instance reader_t.monad_reader {ρ : Type u} {m : Type u → Type v} [Monad m] : monad_reader ρ (reader_t ρ m) :=
  monad_reader.mk reader_t.read

/-- Adapt a monad stack, changing the type of its top-most environment.

    This class is comparable to [Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify), but does not use lenses (why would it), and is derived automatically for any transformer implementing `monad_functor`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
    ```
    -/
class monad_reader_adapter (ρ : outParam (Type u)) (ρ' : outParam (Type u)) (m : Type u → Type v) (m' : Type u → Type v) 
where
  adapt_reader : {α : Type u} → (ρ' → ρ) → m α → m' α

protected instance monad_reader_adapter_trans {ρ : Type u} {ρ' : Type u} {m : Type u → Type v} {m' : Type u → Type v} {n : Type u → Type v} {n' : Type u → Type v} [monad_functor m m' n n'] [monad_reader_adapter ρ ρ' m m'] : monad_reader_adapter ρ ρ' n n' :=
  monad_reader_adapter.mk fun (α : Type u) (f : ρ' → ρ) => monad_map fun (α : Type u) => adapt_reader f

protected instance reader_t.monad_reader_adapter {ρ : Type u} {ρ' : Type u} {m : Type u → Type v} [Monad m] : monad_reader_adapter ρ ρ' (reader_t ρ m) (reader_t ρ' m) :=
  monad_reader_adapter.mk fun (α : Type u) => reader_t.adapt

protected instance reader_t.monad_run (ρ : Type u) (m : Type u → Type u_1) (out : outParam (Type u → Type u_1)) [monad_run out m] : monad_run (fun (α : Type u) => ρ → out α) (reader_t ρ m) :=
  monad_run.mk fun (α : Type u) (x : reader_t ρ m α) => run ∘ reader_t.run x

