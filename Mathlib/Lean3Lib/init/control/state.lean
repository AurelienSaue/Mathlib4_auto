/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

The state monad transformer.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.alternative
import Mathlib.Lean3Lib.init.control.lift
import Mathlib.Lean3Lib.init.control.id
import Mathlib.Lean3Lib.init.control.except
import PostPort

universes u v l u_1 u_2 u_3 w 

namespace Mathlib

structure state_t (σ : Type u) (m : Type u → Type v) (α : Type u) 
where
  run : σ → m (α × σ)

def state (σ : Type u) (α : Type u)  :=
  state_t σ id α

namespace state_t


protected def pure {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (a : α) : state_t σ m α :=
  mk fun (s : σ) => pure (a, s)

protected def bind {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (x : state_t σ m α) (f : α → state_t σ m β) : state_t σ m β :=
  mk
    fun (s : σ) =>
      do 
        run x s 
        sorry

protected instance monad {σ : Type u} {m : Type u → Type v} [Monad m] : Monad (state_t σ m) := sorry

protected def orelse {σ : Type u} {m : Type u → Type v} [Monad m] [alternative m] {α : Type u} (x₁ : state_t σ m α) (x₂ : state_t σ m α) : state_t σ m α :=
  mk fun (s : σ) => run x₁ s <|> run x₂ s

protected def failure {σ : Type u} {m : Type u → Type v} [Monad m] [alternative m] {α : Type u} : state_t σ m α :=
  mk fun (s : σ) => failure

protected instance alternative {σ : Type u} {m : Type u → Type v} [Monad m] [alternative m] : alternative (state_t σ m) :=
  alternative.mk state_t.failure

protected def get {σ : Type u} {m : Type u → Type v} [Monad m] : state_t σ m σ :=
  mk fun (s : σ) => pure (s, s)

protected def put {σ : Type u} {m : Type u → Type v} [Monad m] : σ → state_t σ m PUnit :=
  fun (s' : σ) => mk fun (s : σ) => pure (PUnit.unit, s')

protected def modify {σ : Type u} {m : Type u → Type v} [Monad m] (f : σ → σ) : state_t σ m PUnit :=
  mk fun (s : σ) => pure (PUnit.unit, f s)

protected def lift {σ : Type u} {m : Type u → Type v} [Monad m] {α : Type u} (t : m α) : state_t σ m α :=
  mk
    fun (s : σ) =>
      do 
        let a ← t 
        pure (a, s)

protected instance has_monad_lift {σ : Type u} {m : Type u → Type v} [Monad m] : has_monad_lift m (state_t σ m) :=
  has_monad_lift.mk state_t.lift

protected def monad_map {σ : Type u_1} {m : Type u_1 → Type u_2} {m' : Type u_1 → Type u_3} [Monad m] [Monad m'] {α : Type u_1} (f : {α : Type u_1} → m α → m' α) : state_t σ m α → state_t σ m' α :=
  fun (x : state_t σ m α) => mk fun (st : σ) => f (run x st)

protected instance monad_functor (σ : Type u_1) (m : Type u_1 → Type u_2) (m' : Type u_1 → Type u_2) [Monad m] [Monad m'] : monad_functor m m' (state_t σ m) (state_t σ m') :=
  monad_functor.mk state_t.monad_map

protected def adapt {σ : Type u} {σ' : Type u} {σ'' : Type u} {α : Type u} {m : Type u → Type v} [Monad m] (split : σ → σ' × σ'') (join : σ' → σ'' → σ) (x : state_t σ' m α) : state_t σ m α :=
  mk fun (st : σ) => sorry

protected instance monad_except {σ : Type u} {m : Type u → Type v} [Monad m] (ε : outParam (Type u_1)) [monad_except ε m] : monad_except ε (state_t σ m) :=
  monad_except.mk (fun (α : Type u) => state_t.lift ∘ throw)
    fun (α : Type u) (x : state_t σ m α) (c : ε → state_t σ m α) =>
      mk fun (s : σ) => catch (run x s) fun (e : ε) => run (c e) s

end state_t


/-- An implementation of [MonadState](https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-State-Class.html).
    In contrast to the Haskell implementation, we use overlapping instances to derive instances
    automatically from `monad_lift`.

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_state_lift (σ : out_param (Type u)) (n : Type u → Type u) :=
    (lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], state_t σ m α) → n α)
    ```
    which better describes the intent of "we can lift a `state_t` from anywhere in the monad stack".
    However, by parametricity the types `∀ m [monad m], σ → m (α × σ)` and `σ → α × σ` should be
    equivalent because the only way to obtain an `m` is through `pure`.
    -/
class monad_state (σ : outParam (Type u)) (m : Type u → Type v) 
where
  lift : {α : Type u} → state σ α → m α

-- NOTE: The ordering of the following two instances determines that the top-most `state_t` monad layer

-- will be picked first

protected instance monad_state_trans {σ : Type u} {m : Type u → Type v} {n : Type u → Type w} [monad_state σ m] [has_monad_lift m n] : monad_state σ n :=
  monad_state.mk fun (α : Type u) (x : state σ α) => monad_lift (monad_state.lift x)

protected instance state_t.monad_state {σ : Type u} {m : Type u → Type v} [Monad m] : monad_state σ (state_t σ m) :=
  monad_state.mk fun (α : Type u) (x : state σ α) => state_t.mk fun (s : σ) => pure (state_t.run x s)

/-- Obtain the top-most state of a monad stack. -/
def get {σ : Type u} {m : Type u → Type v} [Monad m] [monad_state σ m] : m σ :=
  monad_state.lift state_t.get

/-- Set the top-most state of a monad stack. -/
def put {σ : Type u} {m : Type u → Type v} [Monad m] [monad_state σ m] (st : σ) : m PUnit :=
  monad_state.lift (state_t.put st)

/-- Map the top-most state of a monad stack.

    Note: `modify f` may be preferable to `f <$> get >>= put` because the latter
    does not use the state linearly (without sufficient inlining). -/
def modify {σ : Type u} {m : Type u → Type v} [Monad m] [monad_state σ m] (f : σ → σ) : m PUnit :=
  monad_state.lift (state_t.modify f)

/-- Adapt a monad stack, changing the type of its top-most state.

    This class is comparable to [Control.Lens.Zoom](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Zoom), but does not use lenses (yet?), and is derived automatically for any transformer implementing `monad_functor`.

    For zooming into a part of the state, the `split` function should split σ into the part σ' and the "context" σ'' so that the potentially modified σ' and the context can be rejoined by `join` in the end.
    In the simplest case, the context can be chosen as the full outer state (ie. `σ'' = σ`), which makes `split` and `join` simpler to define. However, note that the state will not be used linearly in this case.

    Example:
    ```
    def zoom_fst {α σ σ' : Type} : state σ α → state (σ × σ') α :=
    adapt_state id prod.mk
    ```

    The function can also zoom out into a "larger" state, where the new parts are supplied by `split` and discarded by `join` in the end. The state is therefore not used linearly anymore but merely affinely, which is not a practically relevant distinction in Lean.

    Example:
    ```
    def with_snd {α σ σ' : Type} (snd : σ') : state (σ × σ') α → state σ α :=
    adapt_state (λ st, ((st, snd), ())) (λ ⟨st,snd⟩ _, st)
    ```

    Note: This class can be seen as a simplification of the more "principled" definition
    ```
    class monad_state_functor (σ σ' : out_param (Type u)) (n n' : Type u → Type u) :=
    (map {α : Type u} : (∀ {m : Type u → Type u} [monad m], state_t σ m α → state_t σ' m α) → n α → n' α)
    ```
    which better describes the intent of "we can map a `state_t` anywhere in the monad stack".
    If we look at the unfolded type of the first argument `∀ m [monad m], (σ → m (α × σ)) → σ' → m (α × σ')`, we see that it has the lens type `∀ f [functor f], (α → f α) → β → f β` with `f` specialized to `λ σ, m (α × σ)` (exercise: show that this is a lawful functor). We can build all lenses we are insterested in from the functions `split` and `join` as
    ```
    λ f _ st, let (st, ctx) := split st in
              (λ st', join st' ctx) <$> f st
    ```
    -/
class monad_state_adapter (σ : outParam (Type u)) (σ' : outParam (Type u)) (m : Type u → Type v) (m' : Type u → Type v) 
where
  adapt_state : {σ'' α : Type u} → (σ' → σ × σ'') → (σ → σ'' → σ') → m α → m' α

protected instance monad_state_adapter_trans {σ : Type u} {σ' : Type u} {m : Type u → Type v} {m' : Type u → Type v} {n : Type u → Type v} {n' : Type u → Type v} [monad_functor m m' n n'] [monad_state_adapter σ σ' m m'] : monad_state_adapter σ σ' n n' :=
  monad_state_adapter.mk
    fun (σ'' α : Type u) (split : σ' → σ × σ'') (join : σ → σ'' → σ') =>
      monad_map fun (α : Type u) => adapt_state split join

protected instance state_t.monad_state_adapter {σ : Type u} {σ' : Type u} {m : Type u → Type v} [Monad m] : monad_state_adapter σ σ' (state_t σ m) (state_t σ' m) :=
  monad_state_adapter.mk fun (σ'' α : Type u) => state_t.adapt

protected instance state_t.monad_run (σ : Type u_1) (m : Type u_1 → Type u_2) (out : outParam (Type u_1 → Type u_2)) [monad_run out m] : monad_run (fun (α : Type u_1) => σ → out (α × σ)) (state_t σ m) :=
  monad_run.mk fun (α : Type u_1) (x : state_t σ m α) => run ∘ fun (σ_1 : σ) => state_t.run x σ_1

