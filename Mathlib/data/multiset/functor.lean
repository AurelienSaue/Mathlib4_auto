/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.basic
import Mathlib.control.traversable.lemmas
import Mathlib.control.traversable.instances
import Mathlib.PostPort

universes u_1 u u_2 

namespace Mathlib

/-!
# Functoriality of `multiset`.
-/

namespace multiset


protected instance functor : Functor multiset :=
  { map := map, mapConst := fun (α β : Type u_1) => map ∘ function.const β }

@[simp] theorem fmap_def {α' : Type u_1} {β' : Type u_1} {s : multiset α'} (f : α' → β') : f <$> s = map f s :=
  rfl

protected instance is_lawful_functor : is_lawful_functor multiset := sorry

def traverse {F : Type u → Type u} [Applicative F] [is_comm_applicative F] {α' : Type u} {β' : Type u} (f : α' → F β') : multiset α' → F (multiset β') :=
  quotient.lift (Functor.map coe ∘ traverse f) sorry

protected instance monad : Monad multiset :=
  { toApplicative :=
      { toFunctor := { map := Functor.map, mapConst := Functor.mapConst },
        toPure := { pure := fun (α : Type u_1) (x : α) => x ::ₘ 0 },
        toSeq :=
          { seq := fun (α β : Type u_1) (f : multiset (α → β)) (x : multiset α) => bind f fun (_x : α → β) => map _x x },
        toSeqLeft :=
          { seqLeft :=
              fun (α β : Type u_1) (a : multiset α) (b : multiset β) =>
                (fun (α β : Type u_1) (f : multiset (α → β)) (x : multiset α) => bind f fun (_x : α → β) => map _x x) β α
                  (map (function.const β) a) b },
        toSeqRight :=
          { seqRight :=
              fun (α β : Type u_1) (a : multiset α) (b : multiset β) =>
                (fun (α β : Type u_1) (f : multiset (α → β)) (x : multiset α) => bind f fun (_x : α → β) => map _x x) β β
                  (map (function.const α id) a) b } },
    toBind := { bind := bind } }

@[simp] theorem pure_def {α : Type u_1} : pure = fun (x : α) => x ::ₘ 0 :=
  rfl

@[simp] theorem bind_def {α : Type u_1} {β : Type u_1} : bind = bind :=
  rfl

protected instance is_lawful_monad : is_lawful_monad multiset := sorry

@[simp] theorem lift_beta {α : Type u_1} {β : Type u_2} (x : List α) (f : List α → β) (h : ∀ (a b : List α), a ≈ b → f a = f b) : quotient.lift f h ↑x = f x :=
  quotient.lift_beta f h x

@[simp] theorem map_comp_coe {α : Type u_1} {β : Type u_1} (h : α → β) : Functor.map h ∘ coe = coe ∘ Functor.map h := sorry

theorem id_traverse {α : Type u_1} (x : multiset α) : traverse id.mk x = x := sorry

theorem comp_traverse {G : Type u_1 → Type u_1} {H : Type u_1 → Type u_1} [Applicative G] [Applicative H] [is_comm_applicative G] [is_comm_applicative H] {α : Type u_1} {β : Type u_1} {γ : Type u_1} (g : α → G β) (h : β → H γ) (x : multiset α) : traverse (functor.comp.mk ∘ Functor.map h ∘ g) x = functor.comp.mk (traverse h <$> traverse g x) := sorry

theorem map_traverse {G : Type u_1 → Type u_1} [Applicative G] [is_comm_applicative G] {α : Type u_1} {β : Type u_1} {γ : Type u_1} (g : α → G β) (h : β → γ) (x : multiset α) : Functor.map h <$> traverse g x = traverse (Functor.map h ∘ g) x := sorry

theorem traverse_map {G : Type u_1 → Type u_1} [Applicative G] [is_comm_applicative G] {α : Type u_1} {β : Type u_1} {γ : Type u_1} (g : α → β) (h : β → G γ) (x : multiset α) : traverse h (map g x) = traverse (h ∘ g) x := sorry

theorem naturality {G : Type u_1 → Type u_1} {H : Type u_1 → Type u_1} [Applicative G] [Applicative H] [is_comm_applicative G] [is_comm_applicative H] (eta : applicative_transformation G H) {α : Type u_1} {β : Type u_1} (f : α → G β) (x : multiset α) : coe_fn eta (multiset β) (traverse f x) = traverse (coe_fn eta β ∘ f) x := sorry

