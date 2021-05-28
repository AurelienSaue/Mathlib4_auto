/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.meta.interactive
import Mathlib.Lean3Lib.init.control.lawful
import Mathlib.PostPort

universes u v u_1 

namespace Mathlib

def set (α : Type u)  :=
  α → Prop

def set_of {α : Type u} (p : α → Prop) : set α :=
  p

namespace set


protected def mem {α : Type u} (a : α) (s : set α)  :=
  s a

protected instance has_mem {α : Type u} : has_mem α (set α) :=
  has_mem.mk set.mem

protected def subset {α : Type u} (s₁ : set α) (s₂ : set α)  :=
  ∀ {a : α}, a ∈ s₁ → a ∈ s₂

protected instance has_subset {α : Type u} : has_subset (set α) :=
  has_subset.mk set.subset

protected def sep {α : Type u} (p : α → Prop) (s : set α) : set α :=
  set_of fun (a : α) => a ∈ s ∧ p a

protected instance has_sep {α : Type u} : has_sep α (set α) :=
  has_sep.mk set.sep

protected instance has_emptyc {α : Type u} : has_emptyc (set α) :=
  has_emptyc.mk fun (a : α) => False

def univ {α : Type u} : set α :=
  fun (a : α) => True

protected def insert {α : Type u} (a : α) (s : set α) : set α :=
  set_of fun (b : α) => b = a ∨ b ∈ s

protected instance has_insert {α : Type u} : has_insert α (set α) :=
  has_insert.mk set.insert

protected instance has_singleton {α : Type u} : has_singleton α (set α) :=
  has_singleton.mk fun (a : α) => set_of fun (b : α) => b = a

protected instance is_lawful_singleton {α : Type u} : is_lawful_singleton α (set α) :=
  is_lawful_singleton.mk fun (a : α) => funext fun (b : α) => propext (or_false (b = a))

protected def union {α : Type u} (s₁ : set α) (s₂ : set α) : set α :=
  set_of fun (a : α) => a ∈ s₁ ∨ a ∈ s₂

protected instance has_union {α : Type u} : has_union (set α) :=
  has_union.mk set.union

protected def inter {α : Type u} (s₁ : set α) (s₂ : set α) : set α :=
  set_of fun (a : α) => a ∈ s₁ ∧ a ∈ s₂

protected instance has_inter {α : Type u} : has_inter (set α) :=
  has_inter.mk set.inter

def compl {α : Type u} (s : set α) : set α :=
  set_of fun (a : α) => ¬a ∈ s

protected def diff {α : Type u} (s : set α) (t : set α) : set α :=
  has_sep.sep (fun (a : α) => ¬a ∈ t) s

protected instance has_sdiff {α : Type u} : has_sdiff (set α) :=
  has_sdiff.mk set.diff

def powerset {α : Type u} (s : set α) : set (set α) :=
  set_of fun (t : set α) => t ⊆ s

prefix:100 "𝒫" => Mathlib.set.powerset

def sUnion {α : Type u} (s : set (set α)) : set α :=
  set_of fun (t : α) => ∃ (a : set α), ∃ (H : a ∈ s), t ∈ a

prefix:110 "⋃₀" => Mathlib.set.sUnion

def image {α : Type u} {β : Type v} (f : α → β) (s : set α) : set β :=
  set_of fun (b : β) => ∃ (a : α), a ∈ s ∧ f a = b

protected instance functor : Functor set :=
  { map := image, mapConst := fun (α β : Type u_1) => image ∘ function.const β }

protected instance is_lawful_functor : is_lawful_functor set :=
  is_lawful_functor.mk
    (fun (_x : Type u_1) (s : set _x) =>
      funext
        fun (b : _x) =>
          propext
            { mp := fun (_x : Functor.map id s b) => sorry,
              mpr := fun (sb : s b) => Exists.intro b { left := sb, right := rfl } })
    fun (_x _x_1 _x_2 : Type u_1) (g : _x → _x_1) (h : _x_1 → _x_2) (s : set _x) =>
      funext
        fun (c : _x_2) =>
          propext
            { mp := fun (_x : Functor.map (h ∘ g) s c) => sorry, mpr := fun (_x : Functor.map h (g <$> s) c) => sorry }

