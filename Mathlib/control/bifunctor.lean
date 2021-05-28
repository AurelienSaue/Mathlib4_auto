/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Functors with two arguments
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.logic.function.basic
import Mathlib.control.functor
import Mathlib.tactic.core
import Mathlib.PostPort

universes u₀ u₁ u₂ l l_3 l_2 l_1 u_1 u_2 

namespace Mathlib

class bifunctor (F : Type u₀ → Type u₁ → Type u₂) 
where
  bimap : {α α' : Type u₀} → {β β' : Type u₁} → (α → α') → (β → β') → F α β → F α' β'

class is_lawful_bifunctor (F : Type u₀ → Type u₁ → Type u₂) [bifunctor F] 
where
  id_bimap : ∀ {α : Type u₀} {β : Type u₁} (x : F α β), bimap id id x = x
  bimap_bimap : ∀ {α₀ α₁ α₂ : Type u₀} {β₀ β₁ β₂ : Type u₁} (f : α₀ → α₁) (f' : α₁ → α₂) (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α₀ β₀),
  bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x

theorem is_lawful_bifunctor.bimap_id_id {F : Type l_3 → Type l_2 → Type l_1} [bifunctor F] [c : is_lawful_bifunctor F] {α : Type l_3} {β : Type l_2} : bimap id id = id :=
  funext fun (x : F α β) => id_bimap x

theorem is_lawful_bifunctor.bimap_comp_bimap {F : Type l_3 → Type l_2 → Type l_1} [bifunctor F] [c : is_lawful_bifunctor F] {α₀ : Type l_3} {α₁ : Type l_3} {α₂ : Type l_3} {β₀ : Type l_2} {β₁ : Type l_2} {β₂ : Type l_2} (f : α₀ → α₁) (f' : α₁ → α₂) (g : β₀ → β₁) (g' : β₁ → β₂) : bimap f' g' ∘ bimap f g = bimap (f' ∘ f) (g' ∘ g) :=
  funext fun (x : F α₀ β₀) => bimap_bimap f f' g g' x

namespace bifunctor


def fst {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] {α : Type u₀} {α' : Type u₀} {β : Type u₁} (f : α → α') : F α β → F α' β :=
  bimap f id

def snd {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] {α : Type u₀} {β : Type u₁} {β' : Type u₁} (f : β → β') : F α β → F α β' :=
  bimap id f

theorem id_fst {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] [is_lawful_bifunctor F] {α : Type u₀} {β : Type u₁} (x : F α β) : fst id x = x :=
  id_bimap

theorem snd_id {F : Type l_3 → Type l_2 → Type l_1} [bifunctor F] [is_lawful_bifunctor F] {α : Type l_3} {β : Type l_2} : snd id = id :=
  funext fun (x : F α β) => id_snd x

theorem comp_fst {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] [is_lawful_bifunctor F] {α₀ : Type u₀} {α₁ : Type u₀} {α₂ : Type u₀} {β : Type u₁} (f : α₀ → α₁) (f' : α₁ → α₂) (x : F α₀ β) : fst f' (fst f x) = fst (f' ∘ f) x := sorry

theorem fst_snd {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] [is_lawful_bifunctor F] {α₀ : Type u₀} {α₁ : Type u₀} {β₀ : Type u₁} {β₁ : Type u₁} (f : α₀ → α₁) (f' : β₀ → β₁) (x : F α₀ β₀) : fst f (snd f' x) = bimap f f' x := sorry

theorem snd_comp_fst {F : Type l_3 → Type l_2 → Type l_1} [bifunctor F] [is_lawful_bifunctor F] {α₀ : Type l_3} {α₁ : Type l_3} {β₀ : Type l_2} {β₁ : Type l_2} (f : α₀ → α₁) (f' : β₀ → β₁) : snd f' ∘ fst f = bimap f f' :=
  funext fun (x : F α₀ β₀) => snd_fst f f' x

theorem comp_snd {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] [is_lawful_bifunctor F] {α : Type u₀} {β₀ : Type u₁} {β₁ : Type u₁} {β₂ : Type u₁} (g : β₀ → β₁) (g' : β₁ → β₂) (x : F α β₀) : snd g' (snd g x) = snd (g' ∘ g) x := sorry

end bifunctor


protected instance prod.bifunctor : bifunctor Prod :=
  bifunctor.mk prod.map

protected instance prod.is_lawful_bifunctor : is_lawful_bifunctor Prod :=
  is_lawful_bifunctor.mk sorry sorry

protected instance bifunctor.const : bifunctor functor.const :=
  bifunctor.mk fun (α α' : Type u_1) (β β_1 : Type u_2) (f : α → α') (_x : β → β_1) => f

protected instance is_lawful_bifunctor.const : is_lawful_bifunctor functor.const :=
  is_lawful_bifunctor.mk sorry sorry

protected instance bifunctor.flip {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] : bifunctor (flip F) :=
  bifunctor.mk fun (α α' : Type u₁) (β β' : Type u₀) (f : α → α') (f' : β → β') (x : flip F α β) => bimap f' f x

protected instance is_lawful_bifunctor.flip {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] [is_lawful_bifunctor F] : is_lawful_bifunctor (flip F) :=
  is_lawful_bifunctor.mk sorry sorry

protected instance sum.bifunctor : bifunctor sum :=
  bifunctor.mk sum.map

protected instance sum.is_lawful_bifunctor : is_lawful_bifunctor sum :=
  is_lawful_bifunctor.mk sorry sorry

protected instance bifunctor.functor {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] {α : Type u₀} : Functor (F α) :=
  { map := fun (_x _x_1 : Type u₁) => bifunctor.snd,
    mapConst := fun (α_1 β : Type u₁) => bifunctor.snd ∘ function.const β }

protected instance bifunctor.is_lawful_functor {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] [is_lawful_bifunctor F] {α : Type u₀} : is_lawful_functor (F α) :=
  is_lawful_functor.mk
    (fun (α_1 : Type u₁) (x : F α α_1) =>
      eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : F α α_1) (e_1 : a = a_1) (ᾰ ᾰ_1 : F α α_1) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (id <$> x) x (Eq.trans (congr_fun bifunctor.snd_id x) (id.def x)) x x (Eq.refl x))
            (propext (eq_self_iff_true x))))
        trivial)
    fun (α_1 β γ : Type u₁) (g : α_1 → β) (h : β → γ) (x : F α α_1) =>
      eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : F α γ) (e_1 : a = a_1) (ᾰ ᾰ_1 : F α γ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              ((h ∘ g) <$> x) (bifunctor.snd (h ∘ g) x) (Eq.refl (bifunctor.snd (h ∘ g) x)) (h <$> g <$> x)
              (bifunctor.snd (h ∘ g) x) (bifunctor.comp_snd g h x))
            (propext (eq_self_iff_true (bifunctor.snd (h ∘ g) x)))))
        trivial

protected instance function.bicompl.bifunctor {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] (G : Type u_1 → Type u₀) (H : Type u_2 → Type u₁) [Functor G] [Functor H] : bifunctor (function.bicompl F G H) :=
  bifunctor.mk
    fun (α α' : Type u_1) (β β' : Type u_2) (f : α → α') (f' : β → β') (x : function.bicompl F G H α β) =>
      bimap (Functor.map f) (Functor.map f') x

protected instance function.bicompl.is_lawful_bifunctor {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] (G : Type u_1 → Type u₀) (H : Type u_2 → Type u₁) [Functor G] [Functor H] [is_lawful_functor G] [is_lawful_functor H] [is_lawful_bifunctor F] : is_lawful_bifunctor (function.bicompl F G H) :=
  is_lawful_bifunctor.mk sorry sorry

protected instance function.bicompr.bifunctor {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] (G : Type u₂ → Type u_1) [Functor G] : bifunctor (function.bicompr G F) :=
  bifunctor.mk
    fun (α α' : Type u₀) (β β' : Type u₁) (f : α → α') (f' : β → β') (x : function.bicompr G F α β) => bimap f f' <$> x

protected instance function.bicompr.is_lawful_bifunctor {F : Type u₀ → Type u₁ → Type u₂} [bifunctor F] (G : Type u₂ → Type u_1) [Functor G] [is_lawful_functor G] [is_lawful_bifunctor F] : is_lawful_bifunctor (function.bicompr G F) :=
  is_lawful_bifunctor.mk sorry sorry

