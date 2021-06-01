/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.concrete_category.bundled_hom
import Mathlib.PostPort

universes u l 

namespace Mathlib

/-!
# Category instances for structures that use unbundled homs

This file provides basic infrastructure to define concrete
categories using unbundled homs (see `class unbundled_hom`), and
define forgetful functors between them (see
`unbundled_hom.mk_has_forget₂`).
-/

namespace category_theory


/-- A class for unbundled homs used to define a category. `hom` must
take two types `α`, `β` and instances of the corresponding structures,
and return a predicate on `α → β`. -/
class unbundled_hom {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → (α → β) → Prop) where
  hom_id : ∀ {α : Type u} (ia : c α), hom ia ia id
  hom_comp :
    ∀ {α β γ : Type u} {Iα : c α} {Iβ : c β} {Iγ : c γ} {g : β → γ} {f : α → β},
      hom Iβ Iγ g → hom Iα Iβ f → hom Iα Iγ (g ∘ f)

namespace unbundled_hom


protected instance bundled_hom (c : Type u → Type u)
    (hom : {α β : Type u} → c α → c β → (α → β) → Prop) [𝒞 : unbundled_hom hom] :
    bundled_hom fun (α β : Type u) (Iα : c α) (Iβ : c β) => Subtype (hom Iα Iβ) :=
  bundled_hom.mk (fun (_x _x_1 : Type u) (_x_2 : c _x) (_x_3 : c _x_1) => subtype.val)
    (fun (α : Type u) (Iα : c α) => { val := id, property := sorry })
    fun (_x _x_1 _x_2 : Type u) (_x_3 : c _x) (_x_4 : c _x_1) (_x_5 : c _x_2)
      (g : Subtype (hom _x_4 _x_5)) (f : Subtype (hom _x_3 _x_4)) =>
      { val := subtype.val g ∘ subtype.val f, property := sorry }

/-- A custom constructor for forgetful functor between concrete categories defined using `unbundled_hom`. -/
def mk_has_forget₂ {c : Type u → Type u} {hom : {α β : Type u} → c α → c β → (α → β) → Prop}
    [𝒞 : unbundled_hom hom] {c' : Type u → Type u}
    {hom' : {α β : Type u} → c' α → c' β → (α → β) → Prop} [𝒞' : unbundled_hom hom']
    (obj : {α : Type u} → c α → c' α)
    (map :
      ∀ {α β : Type u} {Iα : c α} {Iβ : c β} {f : α → β}, hom Iα Iβ f → hom' (obj Iα) (obj Iβ) f) :
    has_forget₂ (bundled c) (bundled c') :=
  bundled_hom.mk_has_forget₂ obj
    (fun (X Y : bundled c) (f : X ⟶ Y) => { val := subtype.val f, property := sorry }) sorry

end Mathlib