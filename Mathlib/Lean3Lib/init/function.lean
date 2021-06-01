/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.data.prod
import Mathlib.Lean3Lib.init.funext
import Mathlib.Lean3Lib.init.logic
 

universes u₁ u₂ u₃ u₄ 

namespace Mathlib

/-!
# General operations on functions
-/

namespace function


/-- Composition of functions: `(f ∘ g) x = f (g x)`. -/
def comp {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β → φ) (g : α → β) : α → φ :=
  fun (x : α) => f (g x)

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
def dcomp {α : Sort u₁} {β : α → Sort u₂} {φ : {x : α} → β x → Sort u₃} (f : {x : α} → (y : β x) → φ y) (g : (x : α) → β x) (x : α) : φ (g x) :=
  f (g x)

infixr:90 " ∘ " => Mathlib.function.comp

infixr:80 " ∘' " => Mathlib.function.dcomp

def comp_right {α : Sort u₁} {β : Sort u₂} (f : β → β → β) (g : α → β) : β → α → β :=
  fun (b : β) (a : α) => f b (g a)

def comp_left {α : Sort u₁} {β : Sort u₂} (f : β → β → β) (g : α → β) : α → β → β :=
  fun (a : α) (b : β) => f (g a) b

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
def on_fun {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β → β → φ) (g : α → β) : α → α → φ :=
  fun (x y : α) => f (g x) (g y)

def combine {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁} (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ) : α → β → ζ :=
  fun (x : α) (y : β) => op (f x y) (g x y)

/-- Constant `λ _, a`. -/
def const {α : Sort u₁} (β : Sort u₂) (a : α) : β → α :=
  fun (x : β) => a

def swap {α : Sort u₁} {β : Sort u₂} {φ : α → β → Sort u₃} (f : (x : α) → (y : β) → φ x y) (y : β) (x : α) : φ x y :=
  f x y

def app {α : Sort u₁} {β : α → Sort u₂} (f : (x : α) → β x) (x : α) : β x :=
  f x

infixl:2 " on " => Mathlib.function.on_fun

theorem left_id {α : Sort u₁} {β : Sort u₂} (f : α → β) : id ∘ f = f :=
  rfl

theorem right_id {α : Sort u₁} {β : Sort u₂} (f : α → β) : f ∘ id = f :=
  rfl

@[simp] theorem comp_app {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β → φ) (g : α → β) (a : α) : comp f g a = f (g a) :=
  rfl

theorem comp.assoc {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ g ∘ h :=
  rfl

@[simp] theorem comp.left_id {α : Sort u₁} {β : Sort u₂} (f : α → β) : id ∘ f = f :=
  rfl

@[simp] theorem comp.right_id {α : Sort u₁} {β : Sort u₂} (f : α → β) : f ∘ id = f :=
  rfl

theorem comp_const_right {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β → φ) (b : β) : f ∘ const α b = const α (f b) :=
  rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def injective {α : Sort u₁} {β : Sort u₂} (f : α → β)  :=
  ∀ {a₁ a₂ : α}, f a₁ = f a₂ → a₁ = a₂

theorem injective.comp {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g : β → φ} {f : α → β} (hg : injective g) (hf : injective f) : injective (g ∘ f) :=
  fun (a₁ a₂ : α) (h : comp g f a₁ = comp g f a₂) => hf (hg h)

/-- A function `f : α → β` is calles surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def surjective {α : Sort u₁} {β : Sort u₂} (f : α → β)  :=
  ∀ (b : β), ∃ (a : α), f a = b

theorem surjective.comp {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g : β → φ} {f : α → β} (hg : surjective g) (hf : surjective f) : surjective (g ∘ f) := sorry

/-- A function is called bijective if it is both injective and surjective. -/
def bijective {α : Sort u₁} {β : Sort u₂} (f : α → β)  :=
  injective f ∧ surjective f

theorem bijective.comp {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g : β → φ} {f : α → β} : bijective g → bijective f → bijective (g ∘ f) := sorry

/-- `left_inverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def left_inverse {α : Sort u₁} {β : Sort u₂} (g : β → α) (f : α → β)  :=
  ∀ (x : α), g (f x) = x

/-- `has_left_inverse f` means that `f` has an unspecified left inverse. -/
def has_left_inverse {α : Sort u₁} {β : Sort u₂} (f : α → β)  :=
  ∃ (finv : β → α), left_inverse finv f

/-- `right_inverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def right_inverse {α : Sort u₁} {β : Sort u₂} (g : β → α) (f : α → β)  :=
  left_inverse f g

/-- `has_right_inverse f` means that `f` has an unspecified right inverse. -/
def has_right_inverse {α : Sort u₁} {β : Sort u₂} (f : α → β)  :=
  ∃ (finv : β → α), right_inverse finv f

theorem left_inverse.injective {α : Sort u₁} {β : Sort u₂} {g : β → α} {f : α → β} : left_inverse g f → injective f :=
  fun (h : left_inverse g f) (a b : α) (faeqfb : f a = f b) =>
    Eq.trans (Eq.trans (Eq.symm (h a)) (congr_arg g faeqfb)) (h b)

theorem has_left_inverse.injective {α : Sort u₁} {β : Sort u₂} {f : α → β} : has_left_inverse f → injective f :=
  fun (h : has_left_inverse f) =>
    exists.elim h fun (finv : β → α) (inv : left_inverse finv f) => left_inverse.injective inv

theorem right_inverse_of_injective_of_left_inverse {α : Sort u₁} {β : Sort u₂} {f : α → β} {g : β → α} (injf : injective f) (lfg : left_inverse f g) : right_inverse f g :=
  fun (x : α) => (fun (h : f (g (f x)) = f x) => injf h) (lfg (f x))

theorem right_inverse.surjective {α : Sort u₁} {β : Sort u₂} {f : α → β} {g : β → α} (h : right_inverse g f) : surjective f :=
  fun (y : β) => Exists.intro (g y) (h y)

theorem has_right_inverse.surjective {α : Sort u₁} {β : Sort u₂} {f : α → β} : has_right_inverse f → surjective f :=
  fun (ᾰ : has_right_inverse f) =>
    Exists.dcases_on ᾰ
      fun (ᾰ_w : β → α) (ᾰ_h : right_inverse ᾰ_w f) => idRhs (surjective f) (right_inverse.surjective ᾰ_h)

theorem left_inverse_of_surjective_of_right_inverse {α : Sort u₁} {β : Sort u₂} {f : α → β} {g : β → α} (surjf : surjective f) (rfg : right_inverse f g) : left_inverse f g :=
  fun (y : β) =>
    exists.elim (surjf y) fun (x : α) (hx : f x = y) => Eq.trans (Eq.trans (hx ▸ rfl) (Eq.symm (rfg x) ▸ rfl)) hx

theorem injective_id {α : Sort u₁} : injective id :=
  fun (a₁ a₂ : α) (h : id a₁ = id a₂) => h

theorem surjective_id {α : Sort u₁} : surjective id :=
  fun (a : α) => Exists.intro a rfl

theorem bijective_id {α : Sort u₁} : bijective id :=
  { left := injective_id, right := surjective_id }

end function


namespace function


/-- Interpret a function on `α × β` as a function with two arguments. -/
def curry {α : Type u₁} {β : Type u₂} {φ : Type u₃} : (α × β → φ) → α → β → φ :=
  fun (f : α × β → φ) (a : α) (b : β) => f (a, b)

/-- Interpret a function with two arguments as a function on `α × β` -/
def uncurry {α : Type u₁} {β : Type u₂} {φ : Type u₃} : (α → β → φ) → α × β → φ :=
  fun (f : α → β → φ) (a : α × β) => f (prod.fst a) (prod.snd a)

@[simp] theorem curry_uncurry {α : Type u₁} {β : Type u₂} {φ : Type u₃} (f : α → β → φ) : curry (uncurry f) = f :=
  rfl

@[simp] theorem uncurry_curry {α : Type u₁} {β : Type u₂} {φ : Type u₃} (f : α × β → φ) : uncurry (curry f) = f := sorry

protected theorem left_inverse.id {α : Type u₁} {β : Type u₂} {g : β → α} {f : α → β} (h : left_inverse g f) : g ∘ f = id :=
  funext h

protected def right_inverse.id {α : Type u₁} {β : Type u₂} {g : β → α} {f : α → β} (h : right_inverse g f) : f ∘ g = id :=
  funext h

