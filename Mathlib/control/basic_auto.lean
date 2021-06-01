/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

universes u v u_1 u_2 u_3 w l 

namespace Mathlib

theorem functor.map_map {α : Type u} {β : Type u} {γ : Type u} {f : Type u → Type v} [Functor f]
    [is_lawful_functor f] (m : α → β) (g : β → γ) (x : f α) : g <$> m <$> x = (g ∘ m) <$> x :=
  Eq.symm (comp_map m g x)

@[simp] theorem id_map' {α : Type u} {f : Type u → Type v} [Functor f] [is_lawful_functor f]
    (x : f α) : (fun (a : α) => a) <$> x = x :=
  id_map x

def mzip_with {F : Type u → Type v} [Applicative F] {α₁ : Type u} {α₂ : Type u} {φ : Type u}
    (f : α₁ → α₂ → F φ) (ma₁ : List α₁) (ma₂ : List α₂) : F (List φ) :=
  sorry

def mzip_with' {α : Type u} {β : Type u} {γ : Type u} {F : Type u → Type v} [Applicative F]
    (f : α → β → F γ) : List α → List β → F PUnit :=
  sorry

@[simp] theorem pure_id'_seq {α : Type u} {F : Type u → Type v} [Applicative F]
    [is_lawful_applicative F] (x : F α) : (pure fun (x : α) => x) <*> x = x :=
  pure_id_seq x

theorem seq_map_assoc {α : Type u} {β : Type u} {γ : Type u} {F : Type u → Type v} [Applicative F]
    [is_lawful_applicative F] (x : F (α → β)) (f : γ → α) (y : F γ) :
    x <*> f <$> y = (fun (m : α → β) => m ∘ f) <$> x <*> y :=
  sorry

theorem map_seq {α : Type u} {β : Type u} {γ : Type u} {F : Type u → Type v} [Applicative F]
    [is_lawful_applicative F] (f : β → γ) (x : F (α → β)) (y : F α) :
    f <$> (x <*> y) = function.comp f <$> x <*> y :=
  sorry

-- TODO: setup `functor_norm` for `monad` laws

def list.mpartition {f : Type → Type} [Monad f] {α : Type} (p : α → f Bool) :
    List α → f (List α × List α) :=
  sorry

theorem map_bind {α : Type u} {β : Type u} {γ : Type u} {m : Type u → Type v} [Monad m]
    [is_lawful_monad m] (x : m α) {g : α → m β} {f : β → γ} :
    f <$> (x >>= g) =
        do 
          let a ← x 
          f <$> g a :=
  sorry

theorem seq_bind_eq {α : Type u} {β : Type u} {γ : Type u} {m : Type u → Type v} [Monad m]
    [is_lawful_monad m] (x : m α) {g : β → m γ} {f : α → β} : f <$> x >>= g = x >>= g ∘ f :=
  sorry

theorem seq_eq_bind_map {α : Type u} {β : Type u} {m : Type u → Type v} [Monad m]
    [is_lawful_monad m] {x : m α} {f : m (α → β)} :
    f <*> x =
        do 
          let _x ← f 
          _x <$> x :=
  Eq.symm (bind_map_eq_seq f x)

/-- This is the Kleisli composition -/
def fish {m : Type u_1 → Type u_2} [Monad m] {α : Sort u_3} {β : Type u_1} {γ : Type u_1}
    (f : α → m β) (g : β → m γ) (x : α) : m γ :=
  f x >>= g

infixl:55 " >=> " => Mathlib.fish

-- >=> is already defined in the core library but it is unusable

-- because of its precedence (it is defined with precedence 2) and

-- because it is defined as a lambda instead of having a named

-- function

theorem fish_pure {m : Type u → Type v} [Monad m] [is_lawful_monad m] {α : Sort u_1} {β : Type u}
    (f : α → m β) : f >=> pure = f :=
  sorry

theorem fish_pipe {m : Type u → Type v} [Monad m] [is_lawful_monad m] {α : Type u} {β : Type u}
    (f : α → m β) : pure >=> f = f :=
  sorry

theorem fish_assoc {m : Type u → Type v} [Monad m] [is_lawful_monad m] {α : Sort u_1} {β : Type u}
    {γ : Type u} {φ : Type u} (f : α → m β) (g : β → m γ) (h : γ → m φ) :
    f >=> g >=> h = f >=> (g >=> h) :=
  sorry

def list.mmap_accumr {α : Type u} {β' : Type v} {γ' : Type v} {m' : Type v → Type w} [Monad m']
    (f : α → β' → m' (β' × γ')) : β' → List α → m' (β' × List γ') :=
  sorry

def list.mmap_accuml {α : Type u} {β' : Type v} {γ' : Type v} {m' : Type v → Type w} [Monad m']
    (f : β' → α → m' (β' × γ')) : β' → List α → m' (β' × List γ') :=
  sorry

theorem mjoin_map_map {m : Type u → Type u} [Monad m] [is_lawful_monad m] {α : Type u} {β : Type u}
    (f : α → β) (a : m (m α)) : mjoin (Functor.map f <$> a) = f <$> mjoin a :=
  sorry

theorem mjoin_map_mjoin {m : Type u → Type u} [Monad m] [is_lawful_monad m] {α : Type u}
    (a : m (m (m α))) : mjoin (mjoin <$> a) = mjoin (mjoin a) :=
  sorry

@[simp] theorem mjoin_map_pure {m : Type u → Type u} [Monad m] [is_lawful_monad m] {α : Type u}
    (a : m α) : mjoin (pure <$> a) = a :=
  sorry

@[simp] theorem mjoin_pure {m : Type u → Type u} [Monad m] [is_lawful_monad m] {α : Type u}
    (a : m α) : mjoin (pure a) = a :=
  pure_bind a id

def succeeds {F : Type → Type v} [alternative F] {α : Type} (x : F α) : F Bool :=
  x $> tt <|> pure false

def mtry {F : Type → Type v} [alternative F] {α : Type} (x : F α) : F Unit :=
  x $> Unit.unit <|> pure Unit.unit

@[simp] theorem guard_true {F : Type → Type v} [alternative F] {h : Decidable True} :
    guard True = pure Unit.unit :=
  sorry

@[simp] theorem guard_false {F : Type → Type v} [alternative F] {h : Decidable False} :
    guard False = failure :=
  sorry

namespace sum


protected def bind {e : Type v} {α : Type u_1} {β : Type u_2} : e ⊕ α → (α → e ⊕ β) → e ⊕ β := sorry

protected instance monad {e : Type v} : Monad (sum e) := sorry

protected instance is_lawful_functor {e : Type v} : is_lawful_functor (sum e) :=
  is_lawful_functor.mk
    (fun (α : Type u) (x : e ⊕ α) =>
      sum.cases_on x (fun (x : e) => Eq.refl (id <$> inl x)) fun (x : α) => Eq.refl (id <$> inr x))
    fun (α β γ : Type u) (g : α → β) (h : β → γ) (x : e ⊕ α) =>
      sum.cases_on x (fun (x : e) => Eq.refl ((h ∘ g) <$> inl x))
        fun (x : α) => Eq.refl ((h ∘ g) <$> inr x)

protected instance is_lawful_monad {e : Type v} : is_lawful_monad (sum e) :=
  is_lawful_monad.mk (fun (α β : Type u) (x : α) (f : α → e ⊕ β) => Eq.refl (pure x >>= f))
    fun (α β γ : Type u) (x : e ⊕ α) (f : α → e ⊕ β) (g : β → e ⊕ γ) =>
      sum.cases_on x (fun (x : e) => Eq.refl (inl x >>= f >>= g))
        fun (x : α) => Eq.refl (inr x >>= f >>= g)

end sum


class is_comm_applicative (m : Type u_1 → Type u_2) [Applicative m] extends is_lawful_applicative m
    where
  commutative_prod :
    ∀ {α β : Type u_1} (a : m α) (b : m β),
      Prod.mk <$> a <*> b = (fun (b : β) (a : α) => (a, b)) <$> b <*> a

theorem is_comm_applicative.commutative_map {m : Type u_1 → Type u_2} [Applicative m]
    [is_comm_applicative m] {α : Type u_1} {β : Type u_1} {γ : Type u_1} (a : m α) (b : m β)
    {f : α → β → γ} : f <$> a <*> b = flip f <$> b <*> a :=
  sorry

end Mathlib