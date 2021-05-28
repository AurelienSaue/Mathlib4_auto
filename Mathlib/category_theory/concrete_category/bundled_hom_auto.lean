/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yury Kudryashov
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.concrete_category.basic
import Mathlib.category_theory.concrete_category.bundled
import PostPort

universes u l 

namespace Mathlib

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types,
along with an `is_monoid_hom` typeclass), but the general trend is towards using bundled homs.

This file provides a basic infrastructure to define concrete categories using bundled homs, and
define forgetful functors between them.
-/

namespace category_theory


/-- Class for bundled homs. Note that the arguments order follows that of lemmas for `monoid_hom`.
This way we can use `⟨@monoid_hom.to_fun, @monoid_hom.id ...⟩` in an instance. -/
class bundled_hom {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) 
where
  to_fun : {α β : Type u} → (Iα : c α) → (Iβ : c β) → hom Iα Iβ → α → β
  id : {α : Type u} → (I : c α) → hom I I
  comp : {α β γ : Type u} → (Iα : c α) → (Iβ : c β) → (Iγ : c γ) → hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ
  hom_ext : autoParam (∀ {α β : Type u} (Iα : c α) (Iβ : c β), function.injective (to_fun Iα Iβ))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  id_to_fun : autoParam (∀ {α : Type u} (I : c α), to_fun I I (id I) = id)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  comp_to_fun : autoParam
  (∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ) (f : hom Iα Iβ) (g : hom Iβ Iγ),
    to_fun Iα Iγ (comp Iα Iβ Iγ g f) = to_fun Iβ Iγ g ∘ to_fun Iα Iβ f)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

namespace bundled_hom


/-- Every `@bundled_hom c _` defines a category with objects in `bundled c`.

This instance generates the type-class problem `bundled_hom ?m` (which is why this is marked as
`[nolint]`). Currently that is not a problem, as there are almost no instances of `bundled_hom`. -/
protected instance category {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) [𝒞 : bundled_hom hom] : category (bundled c) :=
  category.mk

/-- A category given by `bundled_hom` is a concrete category.

This instance generates the type-class problem `bundled_hom ?m` (which is why this is marked as
`[nolint]`). Currently that is not a problem, as there are almost no instances of `bundled_hom`. -/
protected instance category_theory.bundled.category_theory.concrete_category {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) [𝒞 : bundled_hom hom] : concrete_category (bundled c) :=
  concrete_category.mk
    (functor.mk (fun (X : bundled c) => ↥X)
      fun (X Y : bundled c) (f : X ⟶ Y) => to_fun 𝒞 (bundled.str X) (bundled.str Y) f)

/-- A version of `has_forget₂.mk'` for categories defined using `@bundled_hom`. -/
def mk_has_forget₂ {c : Type u → Type u} {hom : {α β : Type u} → c α → c β → Type u} [𝒞 : bundled_hom hom] {d : Type u → Type u} {hom_d : {α β : Type u} → d α → d β → Type u} [bundled_hom hom_d] (obj : {α : Type u} → c α → d α) (map : {X Y : bundled c} → (X ⟶ Y) → (bundled.map obj X ⟶ bundled.map obj Y)) (h_map : ∀ {X Y : bundled c} (f : X ⟶ Y), ⇑(map f) = ⇑f) : has_forget₂ (bundled c) (bundled d) :=
  has_forget₂.mk' (bundled.map obj) sorry map sorry

/--
The `hom` corresponding to first forgetting along `F`, then taking the `hom` associated to `c`.

For typical usage, see the construction of `CommMon` from `Mon`.
-/
def map_hom {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) {d : Type u → Type u} (F : {α : Type u} → d α → c α) {α : Type u} {β : Type u} (Iα : d α) (Iβ : d β)  :=
  hom (F iα) (F iβ)

/--
Construct the `bundled_hom` induced by a map between type classes.
This is useful for building categories such as `CommMon` from `Mon`.
-/
def map {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) [𝒞 : bundled_hom hom] {d : Type u → Type u} (F : {α : Type u} → d α → c α) : bundled_hom (map_hom hom F) :=
  mk (fun (α β : Type u) (iα : d α) (iβ : d β) (f : map_hom hom F iα iβ) => to_fun 𝒞 (F iα) (F iβ) f)
    (fun (α : Type u) (iα : d α) => id 𝒞 (F iα))
    fun (α β γ : Type u) (iα : d α) (iβ : d β) (iγ : d γ) (f : map_hom hom F iβ iγ) (g : map_hom hom F iα iβ) =>
      comp 𝒞 (F iα) (F iβ) (F iγ) f g

/--
We use the empty `parent_projection` class to label functions like `comm_monoid.to_monoid`,
which we would like to use to automatically construct `bundled_hom` instances from.

Once we've set up `Mon` as the category of bundled monoids,
this allows us to set up `CommMon` by defining an instance
```instance : parent_projection (comm_monoid.to_monoid) := ⟨⟩```
-/
class parent_projection {c : Type u → Type u} {d : Type u → Type u} (F : {α : Type u} → d α → c α) 
where

protected instance bundled_hom_of_parent_projection {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) [𝒞 : bundled_hom hom] {d : Type u → Type u} (F : {α : Type u} → d α → c α) [parent_projection F] : bundled_hom (map_hom hom F) :=
  map hom F

protected instance forget₂ {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) [𝒞 : bundled_hom hom] {d : Type u → Type u} (F : {α : Type u} → d α → c α) [parent_projection F] : has_forget₂ (bundled d) (bundled c) :=
  has_forget₂.mk (functor.mk (fun (X : bundled d) => bundled.mk ↥X) fun (X Y : bundled d) (f : X ⟶ Y) => f)

protected instance forget₂_full {c : Type u → Type u} (hom : {α β : Type u} → c α → c β → Type u) [𝒞 : bundled_hom hom] {d : Type u → Type u} (F : {α : Type u} → d α → c α) [parent_projection F] : full (forget₂ (bundled d) (bundled c)) :=
  full.mk
    fun (X Y : bundled d)
      (f : functor.obj (forget₂ (bundled d) (bundled c)) X ⟶ functor.obj (forget₂ (bundled d) (bundled c)) Y) => f

