/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Monad combinators, as in Haskell's Control.Monad.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.control.monad
import Mathlib.Lean3Lib.init.control.alternative
import Mathlib.Lean3Lib.init.data.list.basic
import PostPort

universes u v w u_1 u_2 u_3 

namespace Mathlib

def list.mmap {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) : List α → m (List β) :=
  sorry

def list.mmap' {m : Type → Type v} [Monad m] {α : Type u} {β : Type} (f : α → m β) : List α → m Unit :=
  sorry

def mjoin {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  a >>= id

def list.mfilter {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α) :=
  sorry

def list.mfoldl {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (s → α → m s) → s → List α → m s :=
  sorry

def list.mfoldr {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} : (α → s → m s) → s → List α → m s :=
  sorry

def list.mfirst {m : Type u → Type v} [Monad m] [alternative m] {α : Type w} {β : Type u} (f : α → m β) : List α → m β :=
  sorry

def when {m : Type → Type} [Monad m] (c : Prop) [h : Decidable c] (t : m Unit) : m Unit :=
  ite c t (pure Unit.unit)

def mcond {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm : m α) (fm : m α) : m α :=
  do 
    let b ← mbool 
    cond b tm fm

def mwhen {m : Type → Type} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  mcond c t (return Unit.unit)

namespace monad


def mapm {m : Type u_1 → Type u_2} [Monad m] {α : Type u_3} {β : Type u_1} (f : α → m β) : List α → m (List β) :=
  mmap

def mapm' {m : Type → Type u_1} [Monad m] {α : Type u_2} {β : Type} (f : α → m β) : List α → m Unit :=
  mmap'

def join {m : Type u_1 → Type u_1} [Monad m] {α : Type u_1} (a : m (m α)) : m α :=
  mjoin

def filter {m : Type → Type u_1} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α) :=
  mfilter

def foldl {m : Type u_1 → Type u_2} [Monad m] {s : Type u_1} {α : Type u_3} : (s → α → m s) → s → List α → m s :=
  mfoldl

def cond {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm : m α) (fm : m α) : m α :=
  mcond

def sequence {m : Type u → Type v} [Monad m] {α : Type u} : List (m α) → m (List α) :=
  sorry

def sequence' {m : Type → Type u} [Monad m] {α : Type} : List (m α) → m Unit :=
  sorry

def whenb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  cond b t (return Unit.unit)

def unlessb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  cond b (return Unit.unit) t

