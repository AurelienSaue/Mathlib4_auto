/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.computability.encoding
import Mathlib.computability.turing_machine
import Mathlib.data.polynomial.basic
import Mathlib.data.polynomial.eval
import Mathlib.PostPort

universes l u_1 

namespace Mathlib

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in turing_machine.lean), a definition of when a TM gives a certain
output (in a certain time), and the definition of computability (in polytime or any time function)
of a function between two types that have an encoding (as in encoding.lean).

## Main theorems

- `id_computable_in_poly_time` : a TM + a proof it computes the identity on a type in polytime.
- `id_computable`              : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type stmt); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, so on). However, as functions
only contain a finite number of executions and each one is executed at most once, this execution
time is up to multiplication by a constant the amount of fundamental steps.
-/

namespace turing


/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `turing.TM2` in `turing_machine.lean`), with an input and output stack,
 a main function, an initial state and some finiteness guarantees. -/
structure fin_tm2 
where
  K : Type
  K_decidable_eq : DecidableEq K
  K_fin : fintype K
  k₀ : K
  k₁ : K
  Γ : K → Type
  Λ : Type
  main : Λ
  Λ_fin : fintype Λ
  σ : Type
  initial_state : σ
  σ_fin : fintype σ
  Γk₀_fin : fintype (Γ k₀)
  M : Λ → TM2.stmt Γ Λ σ

namespace fin_tm2


protected instance K.decidable_eq (tm : fin_tm2) : DecidableEq (K tm) :=
  K_decidable_eq tm

protected instance σ.inhabited (tm : fin_tm2) : Inhabited (σ tm) :=
  { default := initial_state tm }

/-- The type of statements (functions) corresponding to this TM. -/
def stmt (tm : fin_tm2)  :=
  TM2.stmt (Γ tm) (Λ tm) (σ tm)

/-- The type of configurations (functions) corresponding to this TM. -/
def cfg (tm : fin_tm2)  :=
  TM2.cfg (Γ tm) (Λ tm) (σ tm)

protected instance inhabited_cfg (tm : fin_tm2) : Inhabited (cfg tm) :=
  TM2.cfg.inhabited (Γ tm) (Λ tm) (σ tm)

/-- The step function corresponding to this TM. -/
@[simp] def step (tm : fin_tm2) : cfg tm → Option (cfg tm) :=
  TM2.step (M tm)

end fin_tm2


/-- The initial configuration corresponding to a list in the input alphabet. -/
def init_list (tm : fin_tm2) (s : List (fin_tm2.Γ tm (fin_tm2.k₀ tm))) : fin_tm2.cfg tm :=
  TM2.cfg.mk (some (fin_tm2.main tm)) (fin_tm2.initial_state tm)
    fun (k : fin_tm2.K tm) =>
      dite (k = fin_tm2.k₀ tm) (fun (h : k = fin_tm2.k₀ tm) => eq.mpr sorry s) fun (_x : ¬k = fin_tm2.k₀ tm) => []

/-- The final configuration corresponding to a list in the output alphabet. -/
def halt_list (tm : fin_tm2) (s : List (fin_tm2.Γ tm (fin_tm2.k₁ tm))) : fin_tm2.cfg tm :=
  TM2.cfg.mk none (fin_tm2.initial_state tm)
    fun (k : fin_tm2.K tm) =>
      dite (k = fin_tm2.k₁ tm) (fun (h : k = fin_tm2.k₁ tm) => eq.mpr sorry s) fun (_x : ¬k = fin_tm2.k₁ tm) => []

/-- A "proof" of the fact that f eventually reaches b when repeatedly evaluated on a,
remembering the number of steps it takes. -/
structure evals_to {σ : Type u_1} (f : σ → Option σ) (a : σ) (b : Option σ) 
where
  steps : ℕ
  evals_in_steps : nat.iterate (flip bind f) steps ↑a = b

/-- A "proof" of the fact that `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`, remembering the number of steps it takes. -/
structure evals_to_in_time {σ : Type u_1} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) 
extends evals_to f a b
where
  steps_le_m : evals_to.steps _to_evals_to ≤ m

/-- Reflexivity of `evals_to` in 0 steps. -/
def evals_to.refl {σ : Type u_1} (f : σ → Option σ) (a : σ) : evals_to f a ↑a :=
  evals_to.mk 0 sorry

/-- Transitivity of `evals_to` in the sum of the numbers of steps. -/
def evals_to.trans {σ : Type u_1} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ) (h₁ : evals_to f a ↑b) (h₂ : evals_to f b c) : evals_to f a c :=
  evals_to.mk (evals_to.steps h₂ + evals_to.steps h₁) sorry

/-- Reflexivity of `evals_to_in_time` in 0 steps. -/
def evals_to_in_time.refl {σ : Type u_1} (f : σ → Option σ) (a : σ) : evals_to_in_time f a (↑a) 0 :=
  evals_to_in_time.mk (evals_to.refl f a) sorry

/-- Transitivity of `evals_to_in_time` in the sum of the numbers of steps. -/
def evals_to_in_time.trans {σ : Type u_1} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ) (m₁ : ℕ) (m₂ : ℕ) (h₁ : evals_to_in_time f a (↑b) m₁) (h₂ : evals_to_in_time f b c m₂) : evals_to_in_time f a c (m₂ + m₁) :=
  evals_to_in_time.mk (evals_to.trans f a b c (evals_to_in_time.to_evals_to h₁) (evals_to_in_time.to_evals_to h₂)) sorry

/-- A proof of tm outputting l' when given l. -/
def tm2_outputs (tm : fin_tm2) (l : List (fin_tm2.Γ tm (fin_tm2.k₀ tm))) (l' : Option (List (fin_tm2.Γ tm (fin_tm2.k₁ tm))))  :=
  evals_to (fin_tm2.step tm) (init_list tm l) (option.map (halt_list tm) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def tm2_outputs_in_time (tm : fin_tm2) (l : List (fin_tm2.Γ tm (fin_tm2.k₀ tm))) (l' : Option (List (fin_tm2.Γ tm (fin_tm2.k₁ tm)))) (m : ℕ)  :=
  evals_to_in_time (fin_tm2.step tm) (init_list tm l) (option.map (halt_list tm) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def tm2_outputs_in_time.to_tm2_outputs {tm : fin_tm2} {l : List (fin_tm2.Γ tm (fin_tm2.k₀ tm))} {l' : Option (List (fin_tm2.Γ tm (fin_tm2.k₁ tm)))} {m : ℕ} (h : tm2_outputs_in_time tm l l' m) : tm2_outputs tm l l' :=
  evals_to_in_time.to_evals_to h

/-- A Turing machine with input alphabet equivalent to Γ₀ and output alphabet equivalent to Γ₁. -/
structure tm2_computable_aux (Γ₀ : Type) (Γ₁ : Type) 
where
  tm : fin_tm2
  input_alphabet : fin_tm2.Γ tm (fin_tm2.k₀ tm) ≃ Γ₀
  output_alphabet : fin_tm2.Γ tm (fin_tm2.k₁ tm) ≃ Γ₁

/-- A Turing machine + a proof it outputs f. -/
structure tm2_computable {α : Type} {β : Type} (ea : computability.fin_encoding α) (eb : computability.fin_encoding β) (f : α → β) 
extends tm2_computable_aux (computability.encoding.Γ (computability.fin_encoding.to_encoding ea))
  (computability.encoding.Γ (computability.fin_encoding.to_encoding eb))
where
  outputs_fun : (a : α) →
  tm2_outputs (tm2_computable_aux.tm _to_tm2_computable_aux)
    (list.map (equiv.inv_fun (tm2_computable_aux.input_alphabet _to_tm2_computable_aux))
      (computability.encoding.encode (computability.fin_encoding.to_encoding ea) a))
    (some
      (list.map (equiv.inv_fun (tm2_computable_aux.output_alphabet _to_tm2_computable_aux))
        (computability.encoding.encode (computability.fin_encoding.to_encoding eb) (f a))))

/-- A Turing machine + a time function + a proof it outputs f in at most time(len(input)) steps. -/
structure tm2_computable_in_time {α : Type} {β : Type} (ea : computability.fin_encoding α) (eb : computability.fin_encoding β) (f : α → β) 
extends tm2_computable_aux (computability.encoding.Γ (computability.fin_encoding.to_encoding ea))
  (computability.encoding.Γ (computability.fin_encoding.to_encoding eb))
where
  time : ℕ → ℕ
  outputs_fun : (a : α) →
  tm2_outputs_in_time (tm2_computable_aux.tm _to_tm2_computable_aux)
    (list.map (equiv.inv_fun (tm2_computable_aux.input_alphabet _to_tm2_computable_aux))
      (computability.encoding.encode (computability.fin_encoding.to_encoding ea) a))
    (some
      (list.map (equiv.inv_fun (tm2_computable_aux.output_alphabet _to_tm2_computable_aux))
        (computability.encoding.encode (computability.fin_encoding.to_encoding eb) (f a))))
    (time (list.length (computability.encoding.encode (computability.fin_encoding.to_encoding ea) a)))

/-- A Turing machine + a polynomial time function + a proof it outputs f in at most time(len(input))
steps. -/
structure tm2_computable_in_poly_time {α : Type} {β : Type} (ea : computability.fin_encoding α) (eb : computability.fin_encoding β) (f : α → β) 
extends tm2_computable_aux (computability.encoding.Γ (computability.fin_encoding.to_encoding ea))
  (computability.encoding.Γ (computability.fin_encoding.to_encoding eb))
where
  time : polynomial ℕ
  outputs_fun : (a : α) →
  tm2_outputs_in_time (tm2_computable_aux.tm _to_tm2_computable_aux)
    (list.map (equiv.inv_fun (tm2_computable_aux.input_alphabet _to_tm2_computable_aux))
      (computability.encoding.encode (computability.fin_encoding.to_encoding ea) a))
    (some
      (list.map (equiv.inv_fun (tm2_computable_aux.output_alphabet _to_tm2_computable_aux))
        (computability.encoding.encode (computability.fin_encoding.to_encoding eb) (f a))))
    (polynomial.eval (list.length (computability.encoding.encode (computability.fin_encoding.to_encoding ea) a)) time)

/-- A forgetful map, forgetting the time bound on the number of steps. -/
def tm2_computable_in_time.to_tm2_computable {α : Type} {β : Type} {ea : computability.fin_encoding α} {eb : computability.fin_encoding β} {f : α → β} (h : tm2_computable_in_time ea eb f) : tm2_computable ea eb f :=
  tm2_computable.mk (tm2_computable_in_time.to_tm2_computable_aux h)
    fun (a : α) => tm2_outputs_in_time.to_tm2_outputs (tm2_computable_in_time.outputs_fun h a)

/-- A forgetful map, forgetting that the time function is polynomial. -/
def tm2_computable_in_poly_time.to_tm2_computable_in_time {α : Type} {β : Type} {ea : computability.fin_encoding α} {eb : computability.fin_encoding β} {f : α → β} (h : tm2_computable_in_poly_time ea eb f) : tm2_computable_in_time ea eb f :=
  tm2_computable_in_time.mk (tm2_computable_in_poly_time.to_tm2_computable_aux h)
    (fun (n : ℕ) => polynomial.eval n (tm2_computable_in_poly_time.time h)) (tm2_computable_in_poly_time.outputs_fun h)

/-- A Turing machine computing the identity on α. -/
def id_computer {α : Type} (ea : computability.fin_encoding α) : fin_tm2 :=
  fin_tm2.mk PUnit.unit PUnit.unit
    (fun (_x : Unit) => computability.encoding.Γ (computability.fin_encoding.to_encoding ea)) Unit PUnit.unit Unit
    PUnit.unit fun (_x : Unit) => TM2.stmt.halt

protected instance inhabited_fin_tm2 : Inhabited fin_tm2 :=
  { default := id_computer Inhabited.default }

/-- A proof that the identity map on α is computable in polytime. -/
def id_computable_in_poly_time {α : Type} (ea : computability.fin_encoding α) : tm2_computable_in_poly_time ea ea id :=
  tm2_computable_in_poly_time.mk (tm2_computable_aux.mk (id_computer ea) (equiv.cast sorry) (equiv.cast sorry)) 1
    fun (_x : α) => evals_to_in_time.mk (evals_to.mk 1 sorry) sorry

protected instance inhabited_tm2_computable_in_poly_time : Inhabited (tm2_computable_in_poly_time Inhabited.default Inhabited.default id) :=
  { default := id_computable_in_poly_time Inhabited.default }

protected instance inhabited_tm2_outputs_in_time : Inhabited
  (tm2_outputs_in_time (id_computer computability.fin_encoding_bool_bool)
    (list.map (equiv.inv_fun (equiv.cast inhabited_tm2_outputs_in_time._proof_1)) [false])
    (some (list.map (equiv.inv_fun (equiv.cast inhabited_tm2_outputs_in_time._proof_2)) [false]))
    (polynomial.eval
      (list.length
        (computability.encoding.encode (computability.fin_encoding.to_encoding computability.fin_encoding_bool_bool)
          false))
      (tm2_computable_in_poly_time.time (id_computable_in_poly_time computability.fin_encoding_bool_bool)))) :=
  { default :=
      tm2_computable_in_poly_time.outputs_fun (id_computable_in_poly_time computability.fin_encoding_bool_bool) false }

protected instance inhabited_tm2_outputs : Inhabited
  (tm2_outputs (id_computer computability.fin_encoding_bool_bool)
    (list.map (equiv.inv_fun (equiv.cast inhabited_tm2_outputs._proof_1)) [false])
    (some (list.map (equiv.inv_fun (equiv.cast inhabited_tm2_outputs._proof_2)) [false]))) :=
  { default := tm2_outputs_in_time.to_tm2_outputs Inhabited.default }

protected instance inhabited_evals_to_in_time : Inhabited (evals_to_in_time (fun (_x : Unit) => some PUnit.unit) PUnit.unit (some PUnit.unit) 0) :=
  { default := evals_to_in_time.refl (fun (_x : Unit) => some PUnit.unit) PUnit.unit }

protected instance inhabited_tm2_evals_to : Inhabited (evals_to (fun (_x : Unit) => some PUnit.unit) PUnit.unit (some PUnit.unit)) :=
  { default := evals_to.refl (fun (_x : Unit) => some PUnit.unit) PUnit.unit }

/-- A proof that the identity map on α is computable in time. -/
def id_computable_in_time {α : Type} (ea : computability.fin_encoding α) : tm2_computable_in_time ea ea id :=
  tm2_computable_in_poly_time.to_tm2_computable_in_time (id_computable_in_poly_time ea)

protected instance inhabited_tm2_computable_in_time : Inhabited (tm2_computable_in_time computability.fin_encoding_bool_bool computability.fin_encoding_bool_bool id) :=
  { default := id_computable_in_time Inhabited.default }

/-- A proof that the identity map on α is computable. -/
def id_computable {α : Type} (ea : computability.fin_encoding α) : tm2_computable ea ea id :=
  tm2_computable_in_time.to_tm2_computable (id_computable_in_time ea)

protected instance inhabited_tm2_computable : Inhabited (tm2_computable computability.fin_encoding_bool_bool computability.fin_encoding_bool_bool id) :=
  { default := id_computable Inhabited.default }

protected instance inhabited_tm2_computable_aux : Inhabited (tm2_computable_aux Bool Bool) :=
  { default := tm2_computable.to_tm2_computable_aux Inhabited.default }

