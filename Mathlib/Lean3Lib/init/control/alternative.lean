/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.logic
import Mathlib.Lean3Lib.init.control.applicative
 

universes u v l 

namespace Mathlib

class has_orelse (f : Type u → Type v) 
where
  orelse : {α : Type u} → f α → f α → f α

infixr:2 " <|> " => Mathlib.has_orelse.orelse

class alternative (f : Type u → Type v) 
extends has_orelse f, Applicative f
where
  failure : {α : Type u} → f α

def failure {f : Type u → Type v} [alternative f] {α : Type u} : f α :=
  alternative.failure

/-- If the condition `p` is decided to be false, then fail, otherwise, return unit. -/
def guard {f : Type → Type v} [alternative f] (p : Prop) [Decidable p] : f Unit :=
  ite p (pure Unit.unit) failure

def assert {f : Type → Type v} [alternative f] (p : Prop) [Decidable p] : f (Inhabited p) :=
  dite p (fun (h : p) => pure { default := h }) fun (h : ¬p) => failure

/- Later we define a coercion from bool to Prop, but this version will still be useful.
   Given (t : tactic bool), we can write t >>= guardb -/

def guardb {f : Type → Type v} [alternative f] : Bool → f Unit :=
  sorry

def optional {f : Type u → Type v} [alternative f] {α : Type u} (x : f α) : f (Option α) :=
  some <$> x <|> pure none

