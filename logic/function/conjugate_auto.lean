/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.logic.function.basic
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Semiconjugate and commuting maps

We define the following predicates:

* `function.semiconj`: `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`;
* `function.semiconj₂: `f : α → β` semiconjugates a binary operation `ga : α → α → α`
  to `gb : β → β → β` if `f (ga x y) = gb (f x) (f y)`;
* `f : α → α` commutes with `g : α → α` if `f ∘ g = g ∘ f`, or equivalently `semiconj f g g`.

-/

namespace function


/-- We say that `f : α → β` semiconjugates `ga : α → α` to `gb : β → β` if `f ∘ ga = gb ∘ f`. -/
def semiconj {α : Type u_1} {β : Type u_2} (f : α → β) (ga : α → α) (gb : β → β)  :=
  ∀ (x : α), f (ga x) = gb (f x)

namespace semiconj


protected theorem comp_eq {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {gb : β → β} (h : semiconj f ga gb) : f ∘ ga = gb ∘ f :=
  funext h

protected theorem eq {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {gb : β → β} (h : semiconj f ga gb) (x : α) : f (ga x) = gb (f x) :=
  h x

theorem comp_right {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {ga' : α → α} {gb : β → β} {gb' : β → β} (h : semiconj f ga gb) (h' : semiconj f ga' gb') : semiconj f (ga ∘ ga') (gb ∘ gb') := sorry

theorem comp_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {fab : α → β} {fbc : β → γ} {ga : α → α} {gb : β → β} {gc : γ → γ} (hab : semiconj fab ga gb) (hbc : semiconj fbc gb gc) : semiconj (fbc ∘ fab) ga gc := sorry

theorem id_right {α : Type u_1} {β : Type u_2} {f : α → β} : semiconj f id id :=
  fun (_x : α) => rfl

theorem id_left {α : Type u_1} {ga : α → α} : semiconj id ga ga :=
  fun (_x : α) => rfl

theorem inverses_right {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α} {ga' : α → α} {gb : β → β} {gb' : β → β} (h : semiconj f ga gb) (ha : right_inverse ga' ga) (hb : left_inverse gb' gb) : semiconj f ga' gb' := sorry

end semiconj


/-- Two maps `f g : α → α` commute if `f ∘ g = g ∘ f`. -/
def commute {α : Type u_1} (f : α → α) (g : α → α)  :=
  semiconj f g g

theorem semiconj.commute {α : Type u_1} {f : α → α} {g : α → α} (h : semiconj f g g) : commute f g :=
  h

namespace commute


theorem refl {α : Type u_1} (f : α → α) : commute f f :=
  fun (_x : α) => Eq.refl (f (f _x))

theorem symm {α : Type u_1} {f : α → α} {g : α → α} (h : commute f g) : commute g f :=
  fun (x : α) => Eq.symm (h x)

theorem comp_right {α : Type u_1} {f : α → α} {g : α → α} {g' : α → α} (h : commute f g) (h' : commute f g') : commute f (g ∘ g') :=
  semiconj.comp_right h h'

theorem comp_left {α : Type u_1} {f : α → α} {f' : α → α} {g : α → α} (h : commute f g) (h' : commute f' g) : commute (f ∘ f') g :=
  symm (comp_right (symm h) (symm h'))

theorem id_right {α : Type u_1} {f : α → α} : commute f id :=
  semiconj.id_right

theorem id_left {α : Type u_1} {f : α → α} : commute id f :=
  semiconj.id_left

end commute


/-- A map `f` semiconjugates a binary operation `ga` to a binary operation `gb` if
for all `x`, `y` we have `f (ga x y) = gb (f x) (f y)`. E.g., a `monoid_hom`
semiconjugates `(*)` to `(*)`. -/
def semiconj₂ {α : Type u_1} {β : Type u_2} (f : α → β) (ga : α → α → α) (gb : β → β → β)  :=
  ∀ (x y : α), f (ga x y) = gb (f x) (f y)

namespace semiconj₂


protected theorem eq {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β} (h : semiconj₂ f ga gb) (x : α) (y : α) : f (ga x y) = gb (f x) (f y) :=
  h x y

protected theorem comp_eq {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β} (h : semiconj₂ f ga gb) : bicompr f ga = bicompl gb f f :=
  funext fun (x : α) => funext (h x)

theorem id_left {α : Type u_1} (op : α → α → α) : semiconj₂ id op op :=
  fun (_x _x_1 : α) => rfl

theorem comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β} {ga : α → α → α} {gb : β → β → β} {f' : β → γ} {gc : γ → γ → γ} (hf' : semiconj₂ f' gb gc) (hf : semiconj₂ f ga gb) : semiconj₂ (f' ∘ f) ga gc := sorry

theorem is_associative_right {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β} [is_associative α ga] (h : semiconj₂ f ga gb) (h_surj : surjective f) : is_associative β gb := sorry

theorem is_associative_left {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β} [is_associative β gb] (h : semiconj₂ f ga gb) (h_inj : injective f) : is_associative α ga := sorry

theorem is_idempotent_right {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β} [is_idempotent α ga] (h : semiconj₂ f ga gb) (h_surj : surjective f) : is_idempotent β gb := sorry

theorem is_idempotent_left {α : Type u_1} {β : Type u_2} {f : α → β} {ga : α → α → α} {gb : β → β → β} [is_idempotent β gb] (h : semiconj₂ f ga gb) (h_inj : injective f) : is_idempotent α ga := sorry

