/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich

Classy functions for lifting monadic actions of different shapes.

This theory is roughly modeled after the Haskell 'layers' package https://hackage.haskell.org/package/layers-0.1.
Please see https://hackage.haskell.org/package/layers-0.1/docs/Documentation-Layers-Overview.html for an exhaustive discussion of the different approaches to lift functions.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.function
import Mathlib.Lean3Lib.init.coe
import Mathlib.Lean3Lib.init.control.monad
 

universes u v w l u_1 u_2 u_3 u_4 

namespace Mathlib

/-- A function for lifting a computation from an inner monad to an outer monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class has_monad_lift (m : Type u → Type v) (n : Type u → Type w) 
where
  monad_lift : {α : Type u} → m α → n α

/-- The reflexive-transitive closure of `has_monad_lift`.
    `monad_lift` is used to transitively lift monadic computations such as `state_t.get` or `state_t.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class has_monad_lift_t (m : Type u → Type v) (n : Type u → Type w) 
where
  monad_lift : {α : Type u} → m α → n α

/-- A coercion that may reduce the need for explicit lifting.
    Because of [limitations of the current coercion resolution](https://github.com/leanprover/lean/issues/1402), this definition is not marked as a global instance and should be marked locally instead. -/
def has_monad_lift_to_has_coe {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} [has_monad_lift_t m n] {α : Type u_1} : has_coe (m α) (n α) :=
  has_coe.mk monad_lift

protected instance has_monad_lift_t_trans (m : Type u_1 → Type u_2) (n : Type u_1 → Type u_3) (o : Type u_1 → Type u_4) [has_monad_lift_t m n] [has_monad_lift n o] : has_monad_lift_t m o :=
  has_monad_lift_t.mk fun (α : Type u_1) (ma : m α) => has_monad_lift.monad_lift (monad_lift ma)

protected instance has_monad_lift_t_refl (m : Type u_1 → Type u_2) : has_monad_lift_t m m :=
  has_monad_lift_t.mk fun (α : Type u_1) => id

@[simp] theorem monad_lift_refl {m : Type u → Type v} {α : Type u} : monad_lift = id :=
  rfl

/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor). -/
class monad_functor (m : Type u → Type v) (m' : Type u → Type v) (n : Type u → Type w) (n' : Type u → Type w) 
where
  monad_map : {α : Type u} → ({α : Type u} → m α → m' α) → n α → n' α

/-- The reflexive-transitive closure of `monad_functor`.
    `monad_map` is used to transitively lift monad morphisms such as `state_t.zoom`.
    A generalization of [MonadLiftFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadLiftFunctor), which can only lift endomorphisms (i.e. m = m', n = n'). -/
class monad_functor_t (m : Type u → Type v) (m' : Type u → Type v) (n : Type u → Type w) (n' : Type u → Type w) 
where
  monad_map : {α : Type u} → ({α : Type u} → m α → m' α) → n α → n' α

protected instance monad_functor_t_trans (m : Type u_1 → Type u_2) (m' : Type u_1 → Type u_2) (n : Type u_1 → Type u_3) (n' : Type u_1 → Type u_3) (o : Type u_1 → Type u_4) (o' : Type u_1 → Type u_4) [monad_functor_t m m' n n'] [monad_functor n n' o o'] : monad_functor_t m m' o o' :=
  monad_functor_t.mk
    fun (α : Type u_1) (f : {α : Type u_1} → m α → m' α) => monad_functor.monad_map fun (α : Type u_1) => monad_map f

protected instance monad_functor_t_refl (m : Type u_1 → Type u_2) (m' : Type u_1 → Type u_2) : monad_functor_t m m' m m' :=
  monad_functor_t.mk fun (α : Type u_1) (f : {α : Type u_1} → m α → m' α) => f

@[simp] theorem monad_map_refl {m : Type u → Type v} {m' : Type u → Type v} (f : {α : Type u} → m α → m' α) {α : Type u} : monad_map f = f :=
  rfl

/-- Run a monad stack to completion.
    `run` should be the composition of the transformers' individual `run` functions.
    This class mostly saves some typing when using highly nested monad stacks:
    ```
    @[reducible] def my_monad := reader_t my_cfg $ state_t my_state $ except_t my_err id
    -- def my_monad.run {α : Type} (x : my_monad α) (cfg : my_cfg) (st : my_state) := ((x.run cfg).run st).run
    def my_monad.run {α : Type} (x : my_monad α) := monad_run.run x
    ```
    -/
class monad_run (out : outParam (Type u → Type v)) (m : Type u → Type v) 
where
  run : {α : Type u} → m α → out α

