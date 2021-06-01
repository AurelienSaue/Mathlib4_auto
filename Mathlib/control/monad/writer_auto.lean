/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

The writer monad transformer for passing immutable state.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.monad.basic
import Mathlib.algebra.group.basic
import Mathlib.PostPort

universes u v l u_1 u_2 u_3 u₀ u₁ v₀ v₁ 

namespace Mathlib

structure writer_t (ω : Type u) (m : Type u → Type v) (α : Type u) where
  run : m (α × ω)

def writer (ω : Type u) (α : Type u) := writer_t ω id

namespace writer_t


protected theorem ext {ω : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (x : writer_t ω m α)
    (x' : writer_t ω m α) (h : run x = run x') : x = x' :=
  sorry

protected def tell {ω : Type u} {m : Type u → Type v} [Monad m] (w : ω) : writer_t ω m PUnit :=
  mk (pure (PUnit.unit, w))

protected def listen {ω : Type u} {m : Type u → Type v} [Monad m] {α : Type u} :
    writer_t ω m α → writer_t ω m (α × ω) :=
  sorry

protected def pass {ω : Type u} {m : Type u → Type v} [Monad m] {α : Type u} :
    writer_t ω m (α × (ω → ω)) → writer_t ω m α :=
  sorry

protected def pure {ω : Type u} {m : Type u → Type v} [Monad m] {α : Type u} [HasOne ω] (a : α) :
    writer_t ω m α :=
  mk (pure (a, 1))

protected def bind {ω : Type u} {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} [Mul ω]
    (x : writer_t ω m α) (f : α → writer_t ω m β) : writer_t ω m β :=
  mk
    (do 
      let x ← run x 
      let x' ← run (f (prod.fst x))
      pure (prod.fst x', prod.snd x * prod.snd x'))

protected instance monad {ω : Type u} {m : Type u → Type v} [Monad m] [HasOne ω] [Mul ω] :
    Monad (writer_t ω m) :=
  sorry

protected instance is_lawful_monad {ω : Type u} {m : Type u → Type v} [Monad m] [monoid ω]
    [is_lawful_monad m] : is_lawful_monad (writer_t ω m) :=
  sorry

protected def lift {ω : Type u} {m : Type u → Type v} [Monad m] {α : Type u} [HasOne ω] (a : m α) :
    writer_t ω m α :=
  mk (flip Prod.mk 1 <$> a)

protected instance has_monad_lift {ω : Type u} (m : Type u → Type u_1) [Monad m] [HasOne ω] :
    has_monad_lift m (writer_t ω m) :=
  has_monad_lift.mk fun (α : Type u) => writer_t.lift

protected def monad_map {ω : Type u} {m : Type u → Type u_1} {m' : Type u → Type u_2} [Monad m]
    [Monad m'] {α : Type u} (f : {α : Type u} → m α → m' α) : writer_t ω m α → writer_t ω m' α :=
  fun (x : writer_t ω m α) => mk (f (run x))

protected instance monad_functor {ω : Type u} (m : Type u → Type u_1) (m' : Type u → Type u_1)
    [Monad m] [Monad m'] : monad_functor m m' (writer_t ω m) (writer_t ω m') :=
  monad_functor.mk writer_t.monad_map

protected def adapt {ω : Type u} {m : Type u → Type v} [Monad m] {ω' : Type u} {α : Type u}
    (f : ω → ω') : writer_t ω m α → writer_t ω' m α :=
  fun (x : writer_t ω m α) => mk (prod.map id f <$> run x)

protected instance monad_except {ω : Type u} {m : Type u → Type v} [Monad m]
    (ε : outParam (Type u_1)) [HasOne ω] [Monad m] [monad_except ε m] :
    monad_except ε (writer_t ω m) :=
  monad_except.mk (fun (α : Type u) => writer_t.lift ∘ throw)
    fun (α : Type u) (x : writer_t ω m α) (c : ε → writer_t ω m α) =>
      mk (catch (run x) fun (e : ε) => run (c e))

end writer_t


/--
An implementation of [MonadReader](
https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
It does not contain `local` because this function cannot be lifted using `monad_lift`.
Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
(lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
```
-/
class monad_writer (ω : outParam (Type u)) (m : Type u → Type v) where
  tell : ω → m PUnit
  listen : {α : Type u} → m α → m (α × ω)
  pass : {α : Type u} → m (α × (ω → ω)) → m α

protected instance writer_t.monad_writer {ω : Type u} {m : Type u → Type v} [Monad m] :
    monad_writer ω (writer_t ω m) :=
  monad_writer.mk writer_t.tell (fun (α : Type u) => writer_t.listen)
    fun (α : Type u) => writer_t.pass

protected instance reader_t.monad_writer {ω : Type u} {ρ : Type u} {m : Type u → Type v} [Monad m]
    [monad_writer ω m] : monad_writer ω (reader_t ρ m) :=
  monad_writer.mk (fun (x : ω) => monad_lift (monad_writer.tell x))
    (fun (α : Type u) (_x : reader_t ρ m α) => sorry)
    fun (α : Type u) (_x : reader_t ρ m (α × (ω → ω))) => sorry

def swap_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} : (α × β) × γ → (α × γ) × β := sorry

protected instance state_t.monad_writer {ω : Type u} {σ : Type u} {m : Type u → Type v} [Monad m]
    [monad_writer ω m] : monad_writer ω (state_t σ m) :=
  monad_writer.mk (fun (x : ω) => monad_lift (monad_writer.tell x))
    (fun (α : Type u) (_x : state_t σ m α) => sorry)
    fun (α : Type u) (_x : state_t σ m (α × (ω → ω))) => sorry

def except_t.pass_aux {ε : Type u_1} {α : Type u_2} {ω : Type u_3} :
    except ε (α × (ω → ω)) → except ε α × (ω → ω) :=
  sorry

protected instance except_t.monad_writer {ω : Type u} {ε : Type u} {m : Type u → Type v} [Monad m]
    [monad_writer ω m] : monad_writer ω (except_t ε m) :=
  monad_writer.mk (fun (x : ω) => monad_lift (monad_writer.tell x))
    (fun (α : Type u) (_x : except_t ε m α) => sorry)
    fun (α : Type u) (_x : except_t ε m (α × (ω → ω))) => sorry

def option_t.pass_aux {α : Type u_1} {ω : Type u_2} : Option (α × (ω → ω)) → Option α × (ω → ω) :=
  sorry

protected instance option_t.monad_writer {ω : Type u} {m : Type u → Type v} [Monad m]
    [monad_writer ω m] : monad_writer ω (option_t m) :=
  monad_writer.mk (fun (x : ω) => monad_lift (monad_writer.tell x))
    (fun (α : Type u) (_x : option_t m α) => sorry)
    fun (α : Type u) (_x : option_t m (α × (ω → ω))) => sorry

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to
[Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `monad_functor`.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
(map {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
```
-/
class monad_writer_adapter (ω : outParam (Type u)) (ω' : outParam (Type u)) (m : Type u → Type v)
    (m' : Type u → Type v)
    where
  adapt_writer : {α : Type u} → (ω → ω') → m α → m' α

/-- Transitivity.

This instance generates the type-class problem with a metavariable argument (which is why this
is marked as `[nolint dangerous_instance]`).
Currently that is not a problem, as there are almost no instances of `monad_functor` or
`monad_writer_adapter`.

see Note [lower instance priority] -/
protected instance monad_writer_adapter_trans {ω : Type u} {ω' : Type u} {m : Type u → Type v}
    {m' : Type u → Type v} {n : Type u → Type v} {n' : Type u → Type v}
    [monad_writer_adapter ω ω' m m'] [monad_functor m m' n n'] : monad_writer_adapter ω ω' n n' :=
  monad_writer_adapter.mk
    fun (α : Type u) (f : ω → ω') => monad_map fun (α : Type u) => adapt_writer f

protected instance writer_t.monad_writer_adapter {ω : Type u} {ω' : Type u} {m : Type u → Type v}
    [Monad m] : monad_writer_adapter ω ω' (writer_t ω m) (writer_t ω' m) :=
  monad_writer_adapter.mk fun (α : Type u) => writer_t.adapt

protected instance writer_t.monad_run (ω : Type u) (m : Type u → Type (max u u_1))
    (out : outParam (Type u → Type (max u u_1))) [monad_run out m] :
    monad_run (fun (α : Type u) => out (α × ω)) (writer_t ω m) :=
  monad_run.mk fun (α : Type u) (x : writer_t ω m α) => run (writer_t.run x)

/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
def writer_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ : Type u₀} {ω₁ : Type u₀}
    {α₂ : Type u₁} {ω₂ : Type u₁} (F : m₁ (α₁ × ω₁) ≃ m₂ (α₂ × ω₂)) :
    writer_t ω₁ m₁ α₁ ≃ writer_t ω₂ m₂ α₂ :=
  equiv.mk (fun (_x : writer_t ω₁ m₁ α₁) => sorry) (fun (_x : writer_t ω₂ m₂ α₂) => sorry) sorry
    sorry

end Mathlib