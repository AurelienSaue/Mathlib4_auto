/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl (CMU)
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.tactic.core
import PostPort

universes u 

namespace Mathlib

theorem monotonicity.pi {α : Sort u} {p : α → Prop} {q : α → Prop} (h : ∀ (a : α), implies (p a) (q a)) : implies (∀ (a : α), p a) (∀ (a : α), q a) :=
  fun (h' : ∀ (a : α), p a) (a : α) => h a (h' a)

theorem monotonicity.imp {p : Prop} {p' : Prop} {q : Prop} {q' : Prop} (h₁ : implies p' q') (h₂ : implies q p) : implies (p → p') (q → q') :=
  fun (h : p → p') => h₁ ∘ h ∘ h₂

theorem monotonicity.const (p : Prop) : implies p p :=
  id

theorem monotonicity.true (p : Prop) : implies p True :=
  fun (_x : p) => trivial

theorem monotonicity.false (p : Prop) : implies False p :=
  false.elim

theorem monotonicity.exists {α : Sort u} {p : α → Prop} {q : α → Prop} (h : ∀ (a : α), implies (p a) (q a)) : implies (∃ (a : α), p a) (∃ (a : α), q a) :=
  exists_imp_exists h

theorem monotonicity.and {p : Prop} {p' : Prop} {q : Prop} {q' : Prop} (hp : implies p p') (hq : implies q q') : implies (p ∧ q) (p' ∧ q') :=
  and.imp hp hq

theorem monotonicity.or {p : Prop} {p' : Prop} {q : Prop} {q' : Prop} (hp : implies p p') (hq : implies q q') : implies (p ∨ q) (p' ∨ q') :=
  or.imp hp hq

theorem monotonicity.not {p : Prop} {q : Prop} (h : implies p q) : implies (¬q) (¬p) :=
  mt h

