/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.control.monad.writer
import Mathlib.PostPort

universes u v w l u_1 u_2 u₀ u₁ v₀ v₁ 

namespace Mathlib

structure monad_cont.label (α : Type w) (m : Type u → Type v) (β : Type u) 
where
  apply : α → m β

def monad_cont.goto {α : Type u_1} {β : Type u} {m : Type u → Type v} (f : monad_cont.label α m β) (x : α) : m β :=
  monad_cont.label.apply f x

class monad_cont (m : Type u → Type v) 
where
  call_cc : {α β : Type u} → (monad_cont.label α m β → m α) → m α

class is_lawful_monad_cont (m : Type u → Type v) [Monad m] [monad_cont m] 
extends is_lawful_monad m
where
  call_cc_bind_right : ∀ {α ω γ : Type u} (cmd : m α) (next : monad_cont.label ω m γ → α → m ω),
  (monad_cont.call_cc fun (f : monad_cont.label ω m γ) => cmd >>= next f) =
    do 
      let x ← cmd 
      monad_cont.call_cc fun (f : monad_cont.label ω m γ) => next f x
  call_cc_bind_left : ∀ {α : Type u} (β : Type u) (x : α) (dead : monad_cont.label α m β → β → m α),
  (monad_cont.call_cc fun (f : monad_cont.label α m β) => monad_cont.goto f x >>= dead f) = pure x
  call_cc_dummy : ∀ {α β : Type u} (dummy : m α), (monad_cont.call_cc fun (f : monad_cont.label α m β) => dummy) = dummy

def cont_t (r : Type u) (m : Type u → Type v) (α : Type w)  :=
  (α → m r) → m r

def cont (r : Type u) (α : Type w)  :=
  cont_t r id α

namespace cont_t


def run {r : Type u} {m : Type u → Type v} {α : Type w} : cont_t r m α → (α → m r) → m r :=
  id

def map {r : Type u} {m : Type u → Type v} {α : Type w} (f : m r → m r) (x : cont_t r m α) : cont_t r m α :=
  f ∘ x

theorem run_cont_t_map_cont_t {r : Type u} {m : Type u → Type v} {α : Type w} (f : m r → m r) (x : cont_t r m α) : run (map f x) = f ∘ run x :=
  rfl

def with_cont_t {r : Type u} {m : Type u → Type v} {α : Type w} {β : Type w} (f : (β → m r) → α → m r) (x : cont_t r m α) : cont_t r m β :=
  fun (g : β → m r) => x (f g)

theorem run_with_cont_t {r : Type u} {m : Type u → Type v} {α : Type w} {β : Type w} (f : (β → m r) → α → m r) (x : cont_t r m α) : run (with_cont_t f x) = run x ∘ f :=
  rfl

protected theorem ext {r : Type u} {m : Type u → Type v} {α : Type w} {x : cont_t r m α} {y : cont_t r m α} (h : ∀ (f : α → m r), run x f = run y f) : x = y :=
  funext fun (x_1 : α → m r) => h x_1

protected instance monad {r : Type u} {m : Type u → Type v} : Monad (cont_t r m) := sorry

protected instance is_lawful_monad {r : Type u} {m : Type u → Type v} : is_lawful_monad (cont_t r m) :=
  is_lawful_monad.mk
    (fun (α β : Type u_1) (x : α) (f : α → cont_t r m β) =>
      cont_t.ext fun (f_1 : β → m r) => Eq.refl (run (pure x >>= f) f_1))
    fun (α β γ : Type u_1) (x : cont_t r m α) (f : α → cont_t r m β) (g : β → cont_t r m γ) =>
      cont_t.ext fun (f_1 : γ → m r) => Eq.refl (run (x >>= f >>= g) f_1)

def monad_lift {r : Type u} {m : Type u → Type v} [Monad m] {α : Type u} : m α → cont_t r m α :=
  fun (x : m α) (f : α → m r) => x >>= f

protected instance has_monad_lift {r : Type u} {m : Type u → Type v} [Monad m] : has_monad_lift m (cont_t r m) :=
  has_monad_lift.mk fun (α : Type u) => monad_lift

theorem monad_lift_bind {r : Type u} {m : Type u → Type v} [Monad m] [is_lawful_monad m] {α : Type u} {β : Type u} (x : m α) (f : α → m β) : monad_lift (x >>= f) = monad_lift x >>= monad_lift ∘ f := sorry

protected instance monad_cont {r : Type u} {m : Type u → Type v} : monad_cont (cont_t r m) :=
  monad_cont.mk
    fun (α β : Type u_1) (f : label α (cont_t r m) β → cont_t r m α) (g : α → m r) =>
      f (monad_cont.label.mk fun (x : α) (h : β → m r) => g x) g

protected instance is_lawful_monad_cont {r : Type u} {m : Type u → Type v} : is_lawful_monad_cont (cont_t r m) :=
  is_lawful_monad_cont.mk sorry sorry sorry

protected instance monad_except {r : Type u} {m : Type u → Type v} (ε : outParam (Type u_1)) [monad_except ε m] : monad_except ε (cont_t r m) :=
  monad_except.mk (fun (x : Type u_2) (e : ε) (f : x → m r) => throw e)
    fun (α : Type u_2) (act : cont_t r m α) (h : ε → cont_t r m α) (f : α → m r) => catch (act f) fun (e : ε) => h e f

protected instance monad_run {r : Type u} {m : Type u → Type v} : monad_run (fun (α : Type u) => (α → m r) → ulift (m r)) (cont_t r m) :=
  monad_run.mk fun (α : Type u) (f : cont_t r m α) (x : α → m r) => ulift.up (f x)

end cont_t


def except_t.mk_label {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} {ε : Type u} : label (except ε α) m β → label α (except_t ε m) β :=
  sorry

theorem except_t.goto_mk_label {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} {ε : Type u} (x : label (except ε α) m β) (i : α) : goto (except_t.mk_label x) i = except_t.mk (except.ok <$> goto x (except.ok i)) :=
  monad_cont.label.cases_on x fun (x : except ε α → m β) => Eq.refl (goto (except_t.mk_label (monad_cont.label.mk x)) i)

def except_t.call_cc {m : Type u → Type v} [Monad m] {ε : Type u} [monad_cont m] {α : Type u} {β : Type u} (f : label α (except_t ε m) β → except_t ε m α) : except_t ε m α :=
  except_t.mk (monad_cont.call_cc fun (x : label (except ε α) m β) => except_t.run (f (except_t.mk_label x)))

protected instance except_t.monad_cont {m : Type u → Type v} [Monad m] {ε : Type u} [monad_cont m] : monad_cont (except_t ε m) :=
  monad_cont.mk fun (α β : Type u) => except_t.call_cc

protected instance except_t.is_lawful_monad_cont {m : Type u → Type v} [Monad m] {ε : Type u} [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (except_t ε m) :=
  is_lawful_monad_cont.mk sorry sorry sorry

def option_t.mk_label {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} : label (Option α) m β → label α (option_t m) β :=
  sorry

theorem option_t.goto_mk_label {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} (x : label (Option α) m β) (i : α) : goto (option_t.mk_label x) i = option_t.mk (some <$> goto x (some i)) :=
  monad_cont.label.cases_on x fun (x : Option α → m β) => Eq.refl (goto (option_t.mk_label (monad_cont.label.mk x)) i)

def option_t.call_cc {m : Type u → Type v} [Monad m] [monad_cont m] {α : Type u} {β : Type u} (f : label α (option_t m) β → option_t m α) : option_t m α :=
  option_t.mk (monad_cont.call_cc fun (x : label (Option α) m β) => option_t.run (f (option_t.mk_label x)))

protected instance option_t.monad_cont {m : Type u → Type v} [Monad m] [monad_cont m] : monad_cont (option_t m) :=
  monad_cont.mk fun (α β : Type u) => option_t.call_cc

protected instance option_t.is_lawful_monad_cont {m : Type u → Type v} [Monad m] [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (option_t m) :=
  is_lawful_monad_cont.mk sorry sorry sorry

def writer_t.mk_label {m : Type u → Type v} [Monad m] {α : Type u_1} {β : Type u} {ω : Type u} [HasOne ω] : label (α × ω) m β → label α (writer_t ω m) β :=
  sorry

theorem writer_t.goto_mk_label {m : Type u → Type v} [Monad m] {α : Type u_1} {β : Type u} {ω : Type u} [HasOne ω] (x : label (α × ω) m β) (i : α) : goto (writer_t.mk_label x) i = monad_lift (goto x (i, 1)) :=
  monad_cont.label.cases_on x fun (x : α × ω → m β) => Eq.refl (goto (writer_t.mk_label (monad_cont.label.mk x)) i)

def writer_t.call_cc {m : Type u → Type v} [Monad m] [monad_cont m] {α : Type u} {β : Type u} {ω : Type u} [HasOne ω] (f : label α (writer_t ω m) β → writer_t ω m α) : writer_t ω m α :=
  writer_t.mk (monad_cont.call_cc (writer_t.run ∘ f ∘ writer_t.mk_label))

protected instance writer_t.monad_cont {m : Type u → Type v} [Monad m] (ω : Type u) [Monad m] [HasOne ω] [monad_cont m] : monad_cont (writer_t ω m) :=
  monad_cont.mk fun (α β : Type u) => writer_t.call_cc

def state_t.mk_label {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} {σ : Type u} : label (α × σ) m (β × σ) → label α (state_t σ m) β :=
  sorry

theorem state_t.goto_mk_label {m : Type u → Type v} [Monad m] {α : Type u} {β : Type u} {σ : Type u} (x : label (α × σ) m (β × σ)) (i : α) : goto (state_t.mk_label x) i = state_t.mk fun (s : σ) => goto x (i, s) :=
  monad_cont.label.cases_on x fun (x : α × σ → m (β × σ)) => Eq.refl (goto (state_t.mk_label (monad_cont.label.mk x)) i)

def state_t.call_cc {m : Type u → Type v} [Monad m] {σ : Type u} [monad_cont m] {α : Type u} {β : Type u} (f : label α (state_t σ m) β → state_t σ m α) : state_t σ m α :=
  state_t.mk
    fun (r : σ) => monad_cont.call_cc fun (f' : label (α × σ) m (β × σ)) => state_t.run (f (state_t.mk_label f')) r

protected instance state_t.monad_cont {m : Type u → Type v} [Monad m] {σ : Type u} [monad_cont m] : monad_cont (state_t σ m) :=
  monad_cont.mk fun (α β : Type u) => state_t.call_cc

protected instance state_t.is_lawful_monad_cont {m : Type u → Type v} [Monad m] {σ : Type u} [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (state_t σ m) :=
  is_lawful_monad_cont.mk sorry sorry sorry

def reader_t.mk_label {m : Type u → Type v} [Monad m] {α : Type u_1} {β : Type u} (ρ : Type u) : label α m β → label α (reader_t ρ m) β :=
  sorry

theorem reader_t.goto_mk_label {m : Type u → Type v} [Monad m] {α : Type u_1} {ρ : Type u} {β : Type u} (x : label α m β) (i : α) : goto (reader_t.mk_label ρ x) i = monad_lift (goto x i) :=
  monad_cont.label.cases_on x fun (x : α → m β) => Eq.refl (goto (reader_t.mk_label ρ (monad_cont.label.mk x)) i)

def reader_t.call_cc {m : Type u → Type v} [Monad m] {ε : Type u} [monad_cont m] {α : Type u} {β : Type u} (f : label α (reader_t ε m) β → reader_t ε m α) : reader_t ε m α :=
  reader_t.mk fun (r : ε) => monad_cont.call_cc fun (f' : label α m β) => reader_t.run (f (reader_t.mk_label ε f')) r

protected instance reader_t.monad_cont {m : Type u → Type v} [Monad m] {ρ : Type u} [monad_cont m] : monad_cont (reader_t ρ m) :=
  monad_cont.mk fun (α β : Type u) => reader_t.call_cc

protected instance reader_t.is_lawful_monad_cont {m : Type u → Type v} [Monad m] {ρ : Type u} [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (reader_t ρ m) :=
  is_lawful_monad_cont.mk sorry sorry sorry

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def cont_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁} {α₁ : Type u₀} {r₁ : Type u₀} {α₂ : Type u₁} {r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) : cont_t r₁ m₁ α₁ ≃ cont_t r₂ m₂ α₂ :=
  equiv.mk
    (fun (f : cont_t r₁ m₁ α₁) (r : α₂ → m₂ r₂) => coe_fn F (f fun (x : α₁) => coe_fn (equiv.symm F) (r (coe_fn G x))))
    (fun (f : cont_t r₂ m₂ α₂) (r : α₁ → m₁ r₁) =>
      coe_fn (equiv.symm F) (f fun (x : α₂) => coe_fn F (r (coe_fn (equiv.symm G) x))))
    sorry sorry

