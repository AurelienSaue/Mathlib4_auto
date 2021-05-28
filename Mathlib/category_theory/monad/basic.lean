/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Adam Topaz
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.functor_category
import Mathlib.PostPort

universes v₁ u₁ l 

namespace Mathlib

namespace category_theory


/--
The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
class monad {C : Type u₁} [category C] (T : C ⥤ C) 
where
  η : 𝟭 ⟶ T
  μ : T ⋙ T ⟶ T
  assoc' : autoParam
  (∀ (X : C),
    functor.map T (nat_trans.app μ X) ≫ nat_trans.app μ X = nat_trans.app μ (functor.obj T X) ≫ nat_trans.app μ X)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  left_unit' : autoParam (∀ (X : C), nat_trans.app η (functor.obj T X) ≫ nat_trans.app μ X = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right_unit' : autoParam (∀ (X : C), functor.map T (nat_trans.app η X) ≫ nat_trans.app μ X = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem monad.assoc {C : Type u₁} [category C] {T : C ⥤ C} [c : monad T] (X : C) : functor.map T (nat_trans.app (monad.μ T) X) ≫ nat_trans.app (monad.μ T) X =
  nat_trans.app (monad.μ T) (functor.obj T X) ≫ nat_trans.app (monad.μ T) X := sorry

@[simp] theorem monad.left_unit {C : Type u₁} [category C] {T : C ⥤ C} [c : monad T] (X : C) : nat_trans.app (monad.η T) (functor.obj T X) ≫ nat_trans.app (monad.μ T) X = 𝟙 := sorry

@[simp] theorem monad.right_unit {C : Type u₁} [category C] {T : C ⥤ C} [c : monad T] (X : C) : functor.map T (nat_trans.app (monad.η T) X) ≫ nat_trans.app (monad.μ T) X = 𝟙 := sorry

@[simp] theorem monad.right_unit_assoc {C : Type u₁} [category C] {T : C ⥤ C} [c : monad T] (X : C) {X' : C} (f' : functor.obj T X ⟶ X') : functor.map T (nat_trans.app (monad.η T) X) ≫ nat_trans.app (monad.μ T) X ≫ f' = f' := sorry

notation:1024 "η_" => Mathlib.category_theory.monad.η

notation:1024 "μ_" => Mathlib.category_theory.monad.μ

/--
The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
class comonad {C : Type u₁} [category C] (G : C ⥤ C) 
where
  ε : G ⟶ 𝟭
  δ : G ⟶ G ⋙ G
  coassoc' : autoParam
  (∀ (X : C),
    nat_trans.app δ X ≫ functor.map G (nat_trans.app δ X) = nat_trans.app δ X ≫ nat_trans.app δ (functor.obj G X))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  left_counit' : autoParam (∀ (X : C), nat_trans.app δ X ≫ nat_trans.app ε (functor.obj G X) = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  right_counit' : autoParam (∀ (X : C), nat_trans.app δ X ≫ functor.map G (nat_trans.app ε X) = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

theorem comonad.coassoc {C : Type u₁} [category C] {G : C ⥤ C} [c : comonad G] (X : C) : nat_trans.app (comonad.δ G) X ≫ functor.map G (nat_trans.app (comonad.δ G) X) =
  nat_trans.app (comonad.δ G) X ≫ nat_trans.app (comonad.δ G) (functor.obj G X) := sorry

@[simp] theorem comonad.left_counit {C : Type u₁} [category C] {G : C ⥤ C} [c : comonad G] (X : C) : nat_trans.app (comonad.δ G) X ≫ nat_trans.app (comonad.ε G) (functor.obj G X) = 𝟙 := sorry

@[simp] theorem comonad.right_counit {C : Type u₁} [category C] {G : C ⥤ C} [c : comonad G] (X : C) : nat_trans.app (comonad.δ G) X ≫ functor.map G (nat_trans.app (comonad.ε G) X) = 𝟙 := sorry

@[simp] theorem comonad.left_counit_assoc {C : Type u₁} [category C] {G : C ⥤ C} [c : comonad G] (X : C) {X' : C} (f' : functor.obj G X ⟶ X') : nat_trans.app (comonad.δ G) X ≫ nat_trans.app (comonad.ε G) (functor.obj G X) ≫ f' = f' := sorry

notation:1024 "ε_" => Mathlib.category_theory.comonad.ε

notation:1024 "δ_" => Mathlib.category_theory.comonad.δ

/-- A morphisms of monads is a natural transformation compatible with η and μ. -/
structure monad_hom {C : Type u₁} [category C] (M : C ⥤ C) (N : C ⥤ C) [monad M] [monad N] 
extends nat_trans M N
where
  app_η' : autoParam (∀ {X : C}, nat_trans.app η_ X ≫ nat_trans.app _to_nat_trans X = nat_trans.app η_ X)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  app_μ' : autoParam
  (∀ {X : C},
    nat_trans.app μ_ X ≫ nat_trans.app _to_nat_trans X =
      (functor.map M (nat_trans.app _to_nat_trans X) ≫ nat_trans.app _to_nat_trans (functor.obj N X)) ≫
        nat_trans.app μ_ X)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem monad_hom.app_η {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [monad M] [monad N] (c : monad_hom M N) {X : C} : nat_trans.app η_ X ≫ nat_trans.app (monad_hom.to_nat_trans c) X = nat_trans.app η_ X := sorry

@[simp] theorem monad_hom.app_μ {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [monad M] [monad N] (c : monad_hom M N) {X : C} : nat_trans.app μ_ X ≫ nat_trans.app (monad_hom.to_nat_trans c) X =
  (functor.map M (nat_trans.app (monad_hom.to_nat_trans c) X) ≫
      nat_trans.app (monad_hom.to_nat_trans c) (functor.obj N X)) ≫
    nat_trans.app μ_ X := sorry

@[simp] theorem monad_hom.app_η_assoc {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [monad M] [monad N] (c : monad_hom M N) {X : C} {X' : C} (f' : functor.obj N X ⟶ X') : nat_trans.app η_ X ≫ nat_trans.app (monad_hom.to_nat_trans c) X ≫ f' = nat_trans.app η_ X ≫ f' := sorry

/-- A morphisms of comonads is a natural transformation compatible with η and μ. -/
structure comonad_hom {C : Type u₁} [category C] (M : C ⥤ C) (N : C ⥤ C) [comonad M] [comonad N] 
extends nat_trans M N
where
  app_ε' : autoParam (∀ {X : C}, nat_trans.app _to_nat_trans X ≫ nat_trans.app ε_ X = nat_trans.app ε_ X)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  app_δ' : autoParam
  (∀ {X : C},
    nat_trans.app _to_nat_trans X ≫ nat_trans.app δ_ X =
      nat_trans.app δ_ X ≫
        nat_trans.app _to_nat_trans (functor.obj M X) ≫ functor.map N (nat_trans.app _to_nat_trans X))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem comonad_hom.app_ε {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [comonad M] [comonad N] (c : comonad_hom M N) {X : C} : nat_trans.app (comonad_hom.to_nat_trans c) X ≫ nat_trans.app ε_ X = nat_trans.app ε_ X := sorry

@[simp] theorem comonad_hom.app_δ {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [comonad M] [comonad N] (c : comonad_hom M N) {X : C} : nat_trans.app (comonad_hom.to_nat_trans c) X ≫ nat_trans.app δ_ X =
  nat_trans.app δ_ X ≫
    nat_trans.app (comonad_hom.to_nat_trans c) (functor.obj M X) ≫
      functor.map N (nat_trans.app (comonad_hom.to_nat_trans c) X) := sorry

@[simp] theorem comonad_hom.app_δ_assoc {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [comonad M] [comonad N] (c : comonad_hom M N) {X : C} {X' : C} (f' : functor.obj N (functor.obj N X) ⟶ X') : nat_trans.app (comonad_hom.to_nat_trans c) X ≫ nat_trans.app δ_ X ≫ f' =
  nat_trans.app δ_ X ≫
    nat_trans.app (comonad_hom.to_nat_trans c) (functor.obj M X) ≫
      functor.map N (nat_trans.app (comonad_hom.to_nat_trans c) X) ≫ f' := sorry

namespace monad_hom


theorem ext {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [monad M] [monad N] (f : monad_hom M N) (g : monad_hom M N) : to_nat_trans f = to_nat_trans g → f = g := sorry

/-- The identity natural transformations is a morphism of monads. -/
def id {C : Type u₁} [category C] (M : C ⥤ C) [monad M] : monad_hom M M :=
  mk (nat_trans.mk (nat_trans.app 𝟙))

protected instance inhabited {C : Type u₁} [category C] {M : C ⥤ C} [monad M] : Inhabited (monad_hom M M) :=
  { default := id M }

/-- The composition of two morphisms of monads. -/
def comp {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} {L : C ⥤ C} [monad M] [monad N] [monad L] (f : monad_hom M N) (g : monad_hom N L) : monad_hom M L :=
  mk (nat_trans.mk fun (X : C) => nat_trans.app (to_nat_trans f) X ≫ nat_trans.app (to_nat_trans g) X)

@[simp] theorem id_comp {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [monad M] [monad N] (f : monad_hom M N) : comp (id M) f = f :=
  ext (comp (id M) f) f
    (nat_trans.ext (to_nat_trans (comp (id M) f)) (to_nat_trans f)
      (funext fun (x : C) => category.id_comp (nat_trans.app (to_nat_trans f) x)))

@[simp] theorem comp_id {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [monad M] [monad N] (f : monad_hom M N) : comp f (id N) = f :=
  ext (comp f (id N)) f
    (nat_trans.ext (to_nat_trans (comp f (id N))) (to_nat_trans f)
      (funext fun (x : C) => category.comp_id (nat_trans.app (to_nat_trans f) x)))

/-- Note: `category_theory.monad.bundled` provides a category instance for bundled monads.-/
@[simp] theorem assoc {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} {L : C ⥤ C} {K : C ⥤ C} [monad M] [monad N] [monad L] [monad K] (f : monad_hom M N) (g : monad_hom N L) (h : monad_hom L K) : comp (comp f g) h = comp f (comp g h) := sorry

end monad_hom


namespace comonad_hom


theorem ext {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [comonad M] [comonad N] (f : comonad_hom M N) (g : comonad_hom M N) : to_nat_trans f = to_nat_trans g → f = g := sorry

/-- The identity natural transformations is a morphism of comonads. -/
def id {C : Type u₁} [category C] (M : C ⥤ C) [comonad M] : comonad_hom M M :=
  mk (nat_trans.mk (nat_trans.app 𝟙))

protected instance inhabited {C : Type u₁} [category C] {M : C ⥤ C} [comonad M] : Inhabited (comonad_hom M M) :=
  { default := id M }

/-- The composition of two morphisms of comonads. -/
def comp {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} {L : C ⥤ C} [comonad M] [comonad N] [comonad L] (f : comonad_hom M N) (g : comonad_hom N L) : comonad_hom M L :=
  mk (nat_trans.mk fun (X : C) => nat_trans.app (to_nat_trans f) X ≫ nat_trans.app (to_nat_trans g) X)

@[simp] theorem id_comp {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [comonad M] [comonad N] (f : comonad_hom M N) : comp (id M) f = f :=
  ext (comp (id M) f) f
    (nat_trans.ext (to_nat_trans (comp (id M) f)) (to_nat_trans f)
      (funext fun (x : C) => category.id_comp (nat_trans.app (to_nat_trans f) x)))

@[simp] theorem comp_id {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} [comonad M] [comonad N] (f : comonad_hom M N) : comp f (id N) = f :=
  ext (comp f (id N)) f
    (nat_trans.ext (to_nat_trans (comp f (id N))) (to_nat_trans f)
      (funext fun (x : C) => category.comp_id (nat_trans.app (to_nat_trans f) x)))

/-- Note: `category_theory.monad.bundled` provides a category instance for bundled comonads.-/
@[simp] theorem assoc {C : Type u₁} [category C] {M : C ⥤ C} {N : C ⥤ C} {L : C ⥤ C} {K : C ⥤ C} [comonad M] [comonad N] [comonad L] [comonad K] (f : comonad_hom M N) (g : comonad_hom N L) (h : comonad_hom L K) : comp (comp f g) h = comp f (comp g h) := sorry

end comonad_hom


namespace monad


protected instance category_theory.functor.id.monad {C : Type u₁} [category C] : monad 𝟭 :=
  mk 𝟙 𝟙

end monad


namespace comonad


protected instance category_theory.functor.id.comonad {C : Type u₁} [category C] : comonad 𝟭 :=
  mk 𝟙 𝟙

