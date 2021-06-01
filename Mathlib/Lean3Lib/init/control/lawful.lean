/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.monad
import Mathlib.Lean3Lib.init.meta.interactive
import Mathlib.Lean3Lib.init.control.state
import Mathlib.Lean3Lib.init.control.except
import Mathlib.Lean3Lib.init.control.reader
import Mathlib.Lean3Lib.init.control.option
 

universes u v l u_1 

namespace Mathlib

class is_lawful_functor (f : Type u → Type v) [Functor f] 
where
  map_const_eq : autoParam (∀ {α β : Type u}, Functor.mapConst = Functor.map ∘ function.const β)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])
  id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x

-- `functor` is indeed a categorical functor

-- `comp_map` does not make a good simp lemma

class is_lawful_applicative (f : Type u → Type v) [Applicative f] 
extends is_lawful_functor f
where
  seq_left_eq : autoParam (∀ {α β : Type u} (a : f α) (b : f β), a <* b = function.const β <$> a <*> b)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])
  seq_right_eq : autoParam (∀ {α β : Type u} (a : f α) (b : f β), a *> b = function.const α id <$> a <*> b)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])
  pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x
  map_pure : ∀ {α β : Type u} (g : α → β) (x : α), g <$> pure x = pure (g x)
  seq_pure : ∀ {α β : Type u} (g : f (α → β)) (x : α), g <*> pure x = (fun (g : α → β) => g x) <$> g
  seq_assoc : ∀ {α β γ : Type u} (x : f α) (g : f (α → β)) (h : f (β → γ)), h <*> (g <*> x) = function.comp <$> h <*> g <*> x

-- applicative laws

-- default functor law

-- applicative "law" derivable from other laws

@[simp] theorem pure_id_seq {α : Type u} {f : Type u → Type v} [Applicative f] [is_lawful_applicative f] (x : f α) : pure id <*> x = x := sorry

class is_lawful_monad (m : Type u → Type v) [Monad m] 
extends is_lawful_applicative m
where
  bind_pure_comp_eq_map : autoParam (∀ {α β : Type u} (f : α → β) (x : m α), x >>= pure ∘ f = f <$> x)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])
  bind_map_eq_seq : autoParam
  (∀ {α β : Type u} (f : m (α → β)) (x : m α),
    (do 
        let _x ← f 
        _x <$> x) =
      f <*> x)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.control_laws_tac")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "control_laws_tac") [])
  pure_bind : ∀ {α β : Type u} (x : α) (f : α → m β), pure x >>= f = f x
  bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ), x >>= f >>= g = x >>= fun (x : α) => f x >>= g

-- monad laws

-- monad "law" derivable from other laws

@[simp] theorem bind_pure {α : Type u} {m : Type u → Type v} [Monad m] [is_lawful_monad m] (x : m α) : x >>= pure = x := sorry

theorem bind_ext_congr {α : Type u} {β : Type u} {m : Type u → Type v} [Bind m] {x : m α} {f : α → m β} {g : α → m β} : (∀ (a : α), f a = g a) → x >>= f = x >>= g := sorry

theorem map_ext_congr {α : Type u} {β : Type u} {m : Type u → Type v} [Functor m] {x : m α} {f : α → β} {g : α → β} : (∀ (a : α), f a = g a) → f <$> x = g <$> x := sorry

-- instances of previously defined monads

namespace id


@[simp] theorem map_eq {α : Type} {β : Type} (x : id α) (f : α → β) : f <$> x = f x :=
  rfl

@[simp] theorem bind_eq {α : Type} {β : Type} (x : id α) (f : α → id β) : x >>= f = f x :=
  rfl

end id


@[simp] theorem id.pure_eq {α : Type} (a : α) : pure a = a :=
  rfl

protected instance id.is_lawful_monad : is_lawful_monad id :=
  is_lawful_monad.mk (fun (α β : Type u_1) (x : α) (f : α → id β) => Eq.refl (pure x >>= f))
    fun (α β γ : Type u_1) (x : id α) (f : α → id β) (g : β → id γ) => Eq.refl (x >>= f >>= g)

namespace state_t


theorem ext {σ : Type u} {m : Type u → Type v} {α : Type u} {x : state_t σ m α} {x' : state_t σ m α} (h : ∀ (st : σ), run x st = run x' st) : x = x' := sorry

@[simp] theorem run_pure {σ : Type u} {m : Type u → Type v} {α : Type u} (st : σ) [Monad m] (a : α) : run (pure a) st = pure (a, st) :=
  rfl

@[simp] theorem run_bind {σ : Type u} {m : Type u → Type v} {α : Type u} {β : Type u} (x : state_t σ m α) (st : σ) [Monad m] (f : α → state_t σ m β) : run (x >>= f) st =
  do 
    let p ← run x st 
    run (f (prod.fst p)) (prod.snd p) := sorry

@[simp] theorem run_map {σ : Type u} {m : Type u → Type v} {α : Type u} {β : Type u} (x : state_t σ m α) (st : σ) [Monad m] (f : α → β) [is_lawful_monad m] : run (f <$> x) st = (fun (p : α × σ) => (f (prod.fst p), prod.snd p)) <$> run x st := sorry

@[simp] theorem run_monad_lift {σ : Type u} {m : Type u → Type v} {α : Type u} (st : σ) [Monad m] {n : Type u → Type u_1} [has_monad_lift_t n m] (x : n α) : run (monad_lift x) st =
  do 
    let a ← monad_lift x 
    pure (a, st) :=
  rfl

@[simp] theorem run_monad_map {σ : Type u} {m : Type u → Type v} {α : Type u} (x : state_t σ m α) (st : σ) [Monad m] {m' : Type u → Type v} {n : Type u → Type u_1} {n' : Type u → Type u_1} [Monad m'] [monad_functor_t n n' m m'] (f : {α : Type u} → n α → n' α) : run (monad_map f x) st = monad_map f (run x st) :=
  rfl

@[simp] theorem run_adapt {σ : Type u} {m : Type u → Type v} {α : Type u} [Monad m] {σ' : Type u} {σ'' : Type u} (st : σ) (split : σ → σ' × σ'') (join : σ' → σ'' → σ) (x : state_t σ' m α) : run (state_t.adapt split join x) st =
  (fun (_a : σ' × σ'') =>
      prod.cases_on _a
        fun (fst : σ') (snd : σ'') =>
          idRhs (m (α × σ))
            (do 
              let _p ← run x fst
              (fun (_a : α × σ') =>
                    prod.cases_on _a fun (fst : α) (snd_1 : σ') => idRhs (m (α × σ)) (pure (fst, join snd_1 snd)))
                  _p))
    (split st) := sorry

@[simp] theorem run_get {σ : Type u} {m : Type u → Type v} (st : σ) [Monad m] : run state_t.get st = pure (st, st) :=
  rfl

@[simp] theorem run_put {σ : Type u} {m : Type u → Type v} (st : σ) [Monad m] (st' : σ) : run (state_t.put st') st = pure (PUnit.unit, st') :=
  rfl

end state_t


protected instance state_t.is_lawful_monad (m : Type u → Type v) [Monad m] [is_lawful_monad m] (σ : Type u) : is_lawful_monad (state_t σ m) := sorry

namespace except_t


theorem ext {α : Type u} {ε : Type u} {m : Type u → Type v} {x : except_t ε m α} {x' : except_t ε m α} (h : run x = run x') : x = x' := sorry

@[simp] theorem run_pure {α : Type u} {ε : Type u} {m : Type u → Type v} [Monad m] (a : α) : run (pure a) = pure (except.ok a) :=
  rfl

@[simp] theorem run_bind {α : Type u} {β : Type u} {ε : Type u} {m : Type u → Type v} (x : except_t ε m α) [Monad m] (f : α → except_t ε m β) : run (x >>= f) = run x >>= except_t.bind_cont f :=
  rfl

@[simp] theorem run_map {α : Type u} {β : Type u} {ε : Type u} {m : Type u → Type v} (x : except_t ε m α) [Monad m] (f : α → β) [is_lawful_monad m] : run (f <$> x) = except.map f <$> run x := sorry

@[simp] theorem run_monad_lift {α : Type u} {ε : Type u} {m : Type u → Type v} [Monad m] {n : Type u → Type u_1} [has_monad_lift_t n m] (x : n α) : run (monad_lift x) = except.ok <$> monad_lift x :=
  rfl

@[simp] theorem run_monad_map {α : Type u} {ε : Type u} {m : Type u → Type v} (x : except_t ε m α) [Monad m] {m' : Type u → Type v} {n : Type u → Type u_1} {n' : Type u → Type u_1} [Monad m'] [monad_functor_t n n' m m'] (f : {α : Type u} → n α → n' α) : run (monad_map f x) = monad_map f (run x) :=
  rfl

end except_t


protected instance except_t.is_lawful_monad (m : Type u → Type v) [Monad m] [is_lawful_monad m] (ε : Type u) : is_lawful_monad (except_t ε m) := sorry

namespace reader_t


theorem ext {ρ : Type u} {m : Type u → Type v} {α : Type u} {x : reader_t ρ m α} {x' : reader_t ρ m α} (h : ∀ (r : ρ), run x r = run x' r) : x = x' := sorry

@[simp] theorem run_pure {ρ : Type u} {m : Type u → Type v} {α : Type u} (r : ρ) [Monad m] (a : α) : run (pure a) r = pure a :=
  rfl

@[simp] theorem run_bind {ρ : Type u} {m : Type u → Type v} {α : Type u} {β : Type u} (x : reader_t ρ m α) (r : ρ) [Monad m] (f : α → reader_t ρ m β) : run (x >>= f) r =
  do 
    let a ← run x r 
    run (f a) r :=
  rfl

@[simp] theorem run_map {ρ : Type u} {m : Type u → Type v} {α : Type u} {β : Type u} (x : reader_t ρ m α) (r : ρ) [Monad m] (f : α → β) [is_lawful_monad m] : run (f <$> x) r = f <$> run x r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (run (f <$> x) r = f <$> run x r)) (Eq.symm (bind_pure_comp_eq_map f (run x r)))))
    (Eq.refl (run (f <$> x) r))

@[simp] theorem run_monad_lift {ρ : Type u} {m : Type u → Type v} {α : Type u} (r : ρ) [Monad m] {n : Type u → Type u_1} [has_monad_lift_t n m] (x : n α) : run (monad_lift x) r = monad_lift x :=
  rfl

@[simp] theorem run_monad_map {ρ : Type u} {m : Type u → Type v} {α : Type u} (x : reader_t ρ m α) (r : ρ) [Monad m] {m' : Type u → Type v} {n : Type u → Type u_1} {n' : Type u → Type u_1} [Monad m'] [monad_functor_t n n' m m'] (f : {α : Type u} → n α → n' α) : run (monad_map f x) r = monad_map f (run x r) :=
  rfl

@[simp] theorem run_read {ρ : Type u} {m : Type u → Type v} (r : ρ) [Monad m] : run reader_t.read r = pure r :=
  rfl

end reader_t


protected instance reader_t.is_lawful_monad (ρ : Type u) (m : Type u → Type v) [Monad m] [is_lawful_monad m] : is_lawful_monad (reader_t ρ m) := sorry

namespace option_t


theorem ext {α : Type u} {m : Type u → Type v} {x : option_t m α} {x' : option_t m α} (h : run x = run x') : x = x' := sorry

@[simp] theorem run_pure {α : Type u} {m : Type u → Type v} [Monad m] (a : α) : run (pure a) = pure (some a) :=
  rfl

@[simp] theorem run_bind {α : Type u} {β : Type u} {m : Type u → Type v} (x : option_t m α) [Monad m] (f : α → option_t m β) : run (x >>= f) = run x >>= option_t.bind_cont f :=
  rfl

@[simp] theorem run_map {α : Type u} {β : Type u} {m : Type u → Type v} (x : option_t m α) [Monad m] (f : α → β) [is_lawful_monad m] : run (f <$> x) = option.map f <$> run x := sorry

@[simp] theorem run_monad_lift {α : Type u} {m : Type u → Type v} [Monad m] {n : Type u → Type u_1} [has_monad_lift_t n m] (x : n α) : run (monad_lift x) = some <$> monad_lift x :=
  rfl

@[simp] theorem run_monad_map {α : Type u} {m : Type u → Type v} (x : option_t m α) [Monad m] {m' : Type u → Type v} {n : Type u → Type u_1} {n' : Type u → Type u_1} [Monad m'] [monad_functor_t n n' m m'] (f : {α : Type u} → n α → n' α) : run (monad_map f x) = monad_map f (run x) :=
  rfl

end option_t


protected instance option_t.is_lawful_monad (m : Type u → Type v) [Monad m] [is_lawful_monad m] : is_lawful_monad (option_t m) := sorry

