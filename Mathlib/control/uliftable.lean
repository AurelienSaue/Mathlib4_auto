/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.monad.basic
import Mathlib.control.monad.cont
import Mathlib.control.monad.writer
import Mathlib.data.equiv.basic
import Mathlib.tactic.interactive
import Mathlib.PostPort

universes u₀ u₁ v₀ v₁ l u_1 u_2 u_3 u_4 u_5 u_6 

namespace Mathlib

/-!
# Universe lifting for type families

Some functors such as `option` and `list` are universe polymorphic. Unlike
type polymorphism where `option α` is a function application and reasoning and
generalizations that apply to functions can be used, `option.{u}` and `option.{v}`
are not one function applied to two universe names but one polymorphic definition
instantiated twice. This means that whatever works on `option.{u}` is hard
to transport over to `option.{v}`. `uliftable` is an attempt at improving the situation.

`uliftable option.{u} option.{v}` gives us a generic and composable way to use
`option.{u}` in a context that requires `option.{v}`. It is often used in tandem with
`ulift` but the two are purposefully decoupled.


## Main definitions
  * `uliftable` class

## Tags

universe polymorphism functor

-/

/-- Given a universe polymorphic type family `M.{u} : Type u₁ → Type
u₂`, this class convert between instantiations, from
`M.{u} : Type u₁ → Type u₂` to `M.{v} : Type v₁ → Type v₂` and back -/
class uliftable (f : Type u₀ → Type u₁) (g : Type v₀ → Type v₁) 
where
  congr : {α : Type u₀} → {β : Type v₀} → α ≃ β → f α ≃ g β

namespace uliftable


/-- The most common practical use `uliftable` (together with `up`), this function takes
`x : M.{u} α` and lifts it to M.{max u v} (ulift.{v} α) -/
def up {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [uliftable f g] {α : Type u₀} : f α → g (ulift α) :=
  equiv.to_fun (congr f g (equiv.symm equiv.ulift))

/-- The most common practical use of `uliftable` (together with `up`), this function takes
`x : M.{max u v} (ulift.{v} α)` and lowers it to `M.{u} α` -/
def down {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [uliftable f g] {α : Type u₀} : g (ulift α) → f α :=
  equiv.inv_fun (congr f g (equiv.symm equiv.ulift))

/-- convenient shortcut to avoid manipulating `ulift` -/
def adapt_up (F : Type v₀ → Type v₁) (G : Type (max v₀ u₀) → Type u₁) [uliftable F G] [Monad G] {α : Type v₀} {β : Type (max v₀ u₀)} (x : F α) (f : α → G β) : G β :=
  up x >>= f ∘ ulift.down

/-- convenient shortcut to avoid manipulating `ulift` -/
def adapt_down {F : Type (max u₀ v₀) → Type u₁} {G : Type v₀ → Type v₁} [L : uliftable G F] [Monad F] {α : Type (max u₀ v₀)} {β : Type v₀} (x : F α) (f : α → G β) : G β :=
  down (x >>= up ∘ f)

/-- map function that moves up universes -/
def up_map {F : Type u₀ → Type u₁} {G : Type (max u₀ v₀) → Type v₁} [inst : uliftable F G] [Functor G] {α : Type u₀} {β : Type (max u₀ v₀)} (f : α → β) (x : F α) : G β :=
  (f ∘ ulift.down) <$> up x

/-- map function that moves down universes -/
def down_map {F : Type (max u₀ v₀) → Type u₁} {G : Type → Type v₁} [inst : uliftable G F] [Functor F] {α : Type (max u₀ v₀)} {β : Type} (f : α → β) (x : F α) : G β :=
  down ((ulift.up ∘ f) <$> x)

@[simp] theorem up_down {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [uliftable f g] {α : Type u₀} (x : g (ulift α)) : up (down x) = x :=
  equiv.right_inv (congr f g (equiv.symm equiv.ulift)) x

@[simp] theorem down_up {f : Type u₀ → Type u₁} {g : Type (max u₀ v₀) → Type v₁} [uliftable f g] {α : Type u₀} (x : f α) : down (up x) = x :=
  equiv.left_inv (congr f g (equiv.symm equiv.ulift)) x

end uliftable


protected instance id.uliftable : uliftable id id :=
  uliftable.mk fun (α : Type u_1) (β : Type u_2) (F : α ≃ β) => F

/-- for specific state types, this function helps to create a uliftable instance -/
def state_t.uliftable' {s : Type u₀} {s' : Type u₁} {m : Type u₀ → Type v₀} {m' : Type u₁ → Type v₁} [uliftable m m'] (F : s ≃ s') : uliftable (state_t s m) (state_t s' m') :=
  uliftable.mk
    fun (α : Type u₀) (β : Type u₁) (G : α ≃ β) =>
      state_t.equiv (equiv.Pi_congr F fun (_x : s) => uliftable.congr m m' (equiv.prod_congr G F))

protected instance state_t.uliftable {s : Type u_1} {m : Type u_1 → Type u_2} {m' : Type (max u_1 u_3) → Type u_4} [uliftable m m'] : uliftable (state_t s m) (state_t (ulift s) m') :=
  state_t.uliftable' (equiv.symm equiv.ulift)

/-- for specific reader monads, this function helps to create a uliftable instance -/
def reader_t.uliftable' {s : Type u_1} {s' : Type u_2} {m : Type u_1 → Type u_3} {m' : Type u_2 → Type u_4} [uliftable m m'] (F : s ≃ s') : uliftable (reader_t s m) (reader_t s' m') :=
  uliftable.mk
    fun (α : Type u_1) (β : Type u_2) (G : α ≃ β) =>
      reader_t.equiv (equiv.Pi_congr F fun (_x : s) => uliftable.congr m m' G)

protected instance reader_t.uliftable {s : Type u_1} {m : Type u_1 → Type u_2} {m' : Type (max u_1 u_3) → Type u_4} [uliftable m m'] : uliftable (reader_t s m) (reader_t (ulift s) m') :=
  reader_t.uliftable' (equiv.symm equiv.ulift)

/-- for specific continuation passing monads, this function helps to create a uliftable instance -/
def cont_t.uliftable' {r : Type u_1} {r' : Type u_2} {m : Type u_1 → Type u_3} {m' : Type u_2 → Type u_4} [uliftable m m'] (F : r ≃ r') : uliftable (cont_t r m) (cont_t r' m') :=
  uliftable.mk fun (α : Type u_1) (β : Type u_2) => cont_t.equiv (uliftable.congr m m' F)

protected instance cont_t.uliftable {s : Type u_1} {m : Type u_1 → Type u_2} {m' : Type (max u_1 u_3) → Type u_4} [uliftable m m'] : uliftable (cont_t s m) (cont_t (ulift s) m') :=
  cont_t.uliftable' (equiv.symm equiv.ulift)

/-- for specific writer monads, this function helps to create a uliftable instance -/
def writer_t.uliftable' {w : Type (max u_1 u_2)} {w' : Type (max u_3 u_4)} {m : Type (max u_1 u_2) → Type u_5} {m' : Type (max u_3 u_4) → Type u_6} [uliftable m m'] (F : w ≃ w') : uliftable (writer_t w m) (writer_t w' m') :=
  uliftable.mk
    fun (α : Type (max u_1 u_2)) (β : Type (max u_3 u_4)) (G : α ≃ β) =>
      writer_t.equiv (uliftable.congr m m' (equiv.prod_congr G F))

protected instance writer_t.uliftable {s : Type (max u_1 u_2)} {m : Type (max u_1 u_2) → Type u_3} {m' : Type (max (max u_1 u_2) u_4) → Type u_5} [uliftable m m'] : uliftable (writer_t s m) (writer_t (ulift s) m') :=
  writer_t.uliftable' (equiv.symm equiv.ulift)

