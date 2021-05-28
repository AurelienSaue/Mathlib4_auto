/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Instances for identity and composition functors
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.control.functor
import Mathlib.algebra.group.basic
import PostPort

universes u v u_1 w u_2 

namespace Mathlib

theorem applicative.map_seq_map {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {α : Type u} {β : Type u} {γ : Type u} {σ : Type u} (f : α → β → γ) (g : σ → β) (x : F α) (y : F σ) : f <$> x <*> g <$> y = (flip function.comp g ∘ f) <$> x <*> y := sorry

theorem applicative.pure_seq_eq_map' {F : Type u → Type v} [Applicative F] [is_lawful_applicative F] {α : Type u} {β : Type u} (f : α → β) : Seq.seq (pure f) = Functor.map f := sorry

theorem applicative.ext {F : Type u → Type u_1} {A1 : Applicative F} {A2 : Applicative F} [is_lawful_applicative F] [is_lawful_applicative F] (H1 : ∀ {α : Type u} (x : α), pure x = pure x) (H2 : ∀ {α β : Type u} (f : F (α → β)) (x : F α), f <*> x = f <*> x) : A1 = A2 := sorry

protected instance id.is_comm_applicative : is_comm_applicative id :=
  is_comm_applicative.mk fun (α β : Type u_1) (a : id α) (b : id β) => Eq.refl (Prod.mk <$> a <*> b)

namespace functor


namespace comp


theorem map_pure {F : Type u → Type w} {G : Type v → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type v} {β : Type v} (f : α → β) (x : α) : f <$> pure x = pure (f x) := sorry

theorem seq_pure {F : Type u → Type w} {G : Type v → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type v} {β : Type v} (f : comp F G (α → β)) (x : α) : f <*> pure x = (fun (g : α → β) => g x) <$> f := sorry

theorem seq_assoc {F : Type u → Type w} {G : Type v → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type v} {β : Type v} {γ : Type v} (x : comp F G α) (f : comp F G (α → β)) (g : comp F G (β → γ)) : g <*> (f <*> x) = function.comp <$> g <*> f <*> x := sorry

theorem pure_seq_eq_map {F : Type u → Type w} {G : Type v → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] {α : Type v} {β : Type v} (f : α → β) (x : comp F G α) : pure f <*> x = f <$> x := sorry

protected instance is_lawful_applicative {F : Type u → Type w} {G : Type v → Type u} [Applicative F] [Applicative G] [is_lawful_applicative F] [is_lawful_applicative G] : is_lawful_applicative (comp F G) :=
  is_lawful_applicative.mk pure_seq_eq_map map_pure seq_pure seq_assoc

theorem applicative_id_comp {F : Type u_1 → Type u_2} [AF : Applicative F] [LF : is_lawful_applicative F] : comp.applicative = AF :=
  applicative.ext (fun (α : Type u_1) (x : α) => rfl) fun (α β : Type u_1) (f : F (α → β)) (x : F α) => rfl

theorem applicative_comp_id {F : Type u_1 → Type u_2} [AF : Applicative F] [LF : is_lawful_applicative F] : comp.applicative = AF := sorry

protected instance is_comm_applicative {f : Type u → Type w} {g : Type v → Type u} [Applicative f] [Applicative g] [is_comm_applicative f] [is_comm_applicative g] : is_comm_applicative (comp f g) := sorry

end comp


end functor


theorem comp.seq_mk {α : Type w} {β : Type w} {f : Type u → Type v} {g : Type w → Type u} [Applicative f] [Applicative g] (h : f (g (α → β))) (x : f (g α)) : functor.comp.mk h <*> functor.comp.mk x = functor.comp.mk (Seq.seq <$> h <*> x) :=
  rfl

protected instance functor.const.applicative {α : Type u_1} [HasOne α] [Mul α] : Applicative (functor.const α) := sorry

protected instance functor.const.is_lawful_applicative {α : Type u_1} [monoid α] : is_lawful_applicative (functor.const α) := sorry

protected instance functor.add_const.applicative {α : Type u_1} [HasZero α] [Add α] : Applicative (functor.add_const α) := sorry

protected instance functor.add_const.is_lawful_applicative {α : Type u_1} [add_monoid α] : is_lawful_applicative (functor.add_const α) := sorry

