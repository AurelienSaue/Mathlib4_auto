/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fin2
import Mathlib.data.typevec
import Mathlib.logic.function.basic
import Mathlib.tactic.basic
import Mathlib.PostPort

universes u_1 u_2 l u v 

namespace Mathlib

/-!

Functors between the category of tuples of types, and the category Type

Features:

`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

-/

/-- multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class mvfunctor {n : ℕ} (F : typevec n → Type u_2) 
where
  map : {α β : typevec n} → typevec.arrow α β → F α → F β

namespace mvfunctor


/-- predicate lifting over multivariate functors -/
def liftp {n : ℕ} {F : typevec n → Type v} [mvfunctor F] {α : typevec n} (p : (i : fin2 n) → α i → Prop) (x : F α)  :=
  ∃ (u : F fun (i : fin2 n) => Subtype (p i)), map (fun (i : fin2 n) => subtype.val) u = x

/-- relational lifting over multivariate functors -/
def liftr {n : ℕ} {F : typevec n → Type v} [mvfunctor F] {α : typevec n} (r : {i : fin2 n} → α i → α i → Prop) (x : F α) (y : F α)  :=
  ∃ (u : F fun (i : fin2 n) => Subtype fun (p : α i × α i) => r (prod.fst p) (prod.snd p)),
    map (fun (i : fin2 n) (t : Subtype fun (p : α i × α i) => r (prod.fst p) (prod.snd p)) => prod.fst (subtype.val t))
          u =
        x ∧
      map (fun (i : fin2 n) (t : Subtype fun (p : α i × α i) => r (prod.fst p) (prod.snd p)) => prod.snd (subtype.val t))
          u =
        y

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def supp {n : ℕ} {F : typevec n → Type v} [mvfunctor F] {α : typevec n} (x : F α) (i : fin2 n) : set (α i) :=
  set_of fun (y : α i) => ∀ {p : (i : fin2 n) → α i → Prop}, liftp p x → p i y

theorem of_mem_supp {n : ℕ} {F : typevec n → Type v} [mvfunctor F] {α : typevec n} {x : F α} {p : {i : fin2 n} → α i → Prop} (h : liftp p x) (i : fin2 n) (y : α i) (H : y ∈ supp x i) : p y :=
  hy h

end mvfunctor


/-- laws for `mvfunctor` -/
class is_lawful_mvfunctor {n : ℕ} (F : typevec n → Type u_2) [mvfunctor F] 
where
  id_map : ∀ {α : typevec n} (x : F α), mvfunctor.map typevec.id x = x
  comp_map : ∀ {α β γ : typevec n} (g : typevec.arrow α β) (h : typevec.arrow β γ) (x : F α),
  mvfunctor.map (typevec.comp h g) x = mvfunctor.map h (mvfunctor.map g x)

namespace mvfunctor


/-- adapt `mvfunctor.liftp` to accept predicates as arrows -/
def liftp' {n : ℕ} {α : typevec n} {F : typevec n → Type v} [mvfunctor F] (p : typevec.arrow α (typevec.repeat n Prop)) : F α → Prop :=
  liftp fun (i : fin2 n) (x : α i) => typevec.of_repeat (p i x)

/-- adapt `mvfunctor.liftp` to accept relations as arrows -/
def liftr' {n : ℕ} {α : typevec n} {F : typevec n → Type v} [mvfunctor F] (r : typevec.arrow (typevec.prod α α) (typevec.repeat n Prop)) : F α → F α → Prop :=
  liftr fun (i : fin2 n) (x y : α i) => typevec.of_repeat (r i (typevec.prod.mk i x y))

@[simp] theorem id_map {n : ℕ} {α : typevec n} {F : typevec n → Type v} [mvfunctor F] [is_lawful_mvfunctor F] (x : F α) : map typevec.id x = x :=
  is_lawful_mvfunctor.id_map x

@[simp] theorem id_map' {n : ℕ} {α : typevec n} {F : typevec n → Type v} [mvfunctor F] [is_lawful_mvfunctor F] (x : F α) : map (fun (i : fin2 n) (a : α i) => a) x = x :=
  id_map x

theorem map_map {n : ℕ} {α : typevec n} {β : typevec n} {γ : typevec n} {F : typevec n → Type v} [mvfunctor F] [is_lawful_mvfunctor F] (g : typevec.arrow α β) (h : typevec.arrow β γ) (x : F α) : map h (map g x) = map (typevec.comp h g) x :=
  Eq.symm (comp_map g h x)

theorem exists_iff_exists_of_mono {n : ℕ} {α : typevec n} {β : typevec n} (F : typevec n → Type v) [mvfunctor F] [is_lawful_mvfunctor F] {p : F α → Prop} {q : F β → Prop} (f : typevec.arrow α β) (g : typevec.arrow β α) (h₀ : typevec.comp f g = typevec.id) (h₁ : ∀ (u : F α), p u ↔ q (map f u)) : (∃ (u : F α), p u) ↔ ∃ (u : F β), q u := sorry

theorem liftp_def {n : ℕ} {α : typevec n} {F : typevec n → Type v} [mvfunctor F] (p : typevec.arrow α (typevec.repeat n Prop)) [is_lawful_mvfunctor F] (x : F α) : liftp' p x ↔ ∃ (u : F (typevec.subtype_ p)), map (typevec.subtype_val p) u = x := sorry

theorem liftr_def {n : ℕ} {α : typevec n} {F : typevec n → Type v} [mvfunctor F] (r : typevec.arrow (typevec.prod α α) (typevec.repeat n Prop)) [is_lawful_mvfunctor F] (x : F α) (y : F α) : liftr' r x y ↔
  ∃ (u : F (typevec.subtype_ r)),
    map (typevec.comp typevec.prod.fst (typevec.subtype_val r)) u = x ∧
      map (typevec.comp typevec.prod.snd (typevec.subtype_val r)) u = y := sorry

end mvfunctor


namespace mvfunctor


theorem liftp_last_pred_iff {n : ℕ} {F : typevec (n + 1) → Type u_1} [mvfunctor F] [is_lawful_mvfunctor F] {α : typevec n} {β : Type u} (p : β → Prop) (x : F (α ::: β)) : liftp' (typevec.pred_last' α p) x ↔ liftp (typevec.pred_last α p) x := sorry

theorem liftr_last_rel_iff {n : ℕ} {F : typevec (n + 1) → Type u_1} [mvfunctor F] [is_lawful_mvfunctor F] {α : typevec n} {β : Type u} (rr : β → β → Prop) (x : F (α ::: β)) (y : F (α ::: β)) : liftr' (typevec.rel_last' α rr) x y ↔ liftr (typevec.rel_last α rr) x y := sorry

