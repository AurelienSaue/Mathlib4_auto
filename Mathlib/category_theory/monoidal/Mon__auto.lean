/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.monoidal.discrete
import Mathlib.category_theory.monoidal.unitors
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.algebra.punit_instances
import Mathlib.PostPort

universes v₁ u₁ l u₂ v₂ u_1 u_2 

namespace Mathlib

/-!
# The category of monoids in a monoidal category.
-/

/--
A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ (C : Type u₁) [category_theory.category C] [category_theory.monoidal_category C]
    where
  X : C
  one : 𝟙_ ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul' :
    autoParam ((one ⊗ 𝟙) ≫ mul = category_theory.iso.hom λ_)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  mul_one' :
    autoParam ((𝟙 ⊗ one) ≫ mul = category_theory.iso.hom ρ_)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  mul_assoc' :
    autoParam ((mul ⊗ 𝟙) ≫ mul = category_theory.iso.hom α_ ≫ (𝟙 ⊗ mul) ≫ mul)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

-- Obviously there is some flexibility stating this axiom.

-- This one has left- and right-hand sides matching the statement of `monoid.mul_assoc`,

-- and chooses to place the associator on the right-hand side.

-- The heuristic is that unitors and associators "don't have much weight".

theorem Mon_.one_mul {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (c : Mon_ C) :
    (Mon_.one c ⊗ 𝟙) ≫ Mon_.mul c = category_theory.iso.hom λ_ :=
  sorry

theorem Mon_.mul_one {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (c : Mon_ C) :
    (𝟙 ⊗ Mon_.one c) ≫ Mon_.mul c = category_theory.iso.hom ρ_ :=
  sorry

@[simp] theorem Mon_.mul_assoc {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (c : Mon_ C) :
    (Mon_.mul c ⊗ 𝟙) ≫ Mon_.mul c = category_theory.iso.hom α_ ≫ (𝟙 ⊗ Mon_.mul c) ≫ Mon_.mul c :=
  sorry

theorem Mon_.one_mul_assoc {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (c : Mon_ C) {X' : C} (f' : Mon_.X c ⟶ X') :
    (Mon_.one c ⊗ 𝟙) ≫ Mon_.mul c ≫ f' = category_theory.iso.hom λ_ ≫ f' :=
  sorry

@[simp] theorem Mon_.mul_assoc_assoc {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (c : Mon_ C) {X' : C} (f' : Mon_.X c ⟶ X') :
    (Mon_.mul c ⊗ 𝟙) ≫ Mon_.mul c ≫ f' =
        category_theory.iso.hom α_ ≫ (𝟙 ⊗ Mon_.mul c) ≫ Mon_.mul c ≫ f' :=
  sorry

namespace Mon_


/--
The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simp] theorem trivial_one (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] : one (trivial C) = 𝟙 :=
  Eq.refl (one (trivial C))

protected instance inhabited (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] : Inhabited (Mon_ C) :=
  { default := trivial C }

@[simp] theorem one_mul_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {Z : C} (f : Z ⟶ X M) :
    (one M ⊗ f) ≫ mul M = category_theory.iso.hom λ_ ≫ f :=
  sorry

@[simp] theorem mul_one_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {Z : C} (f : Z ⟶ X M) :
    (f ⊗ one M) ≫ mul M = category_theory.iso.hom ρ_ ≫ f :=
  sorry

theorem assoc_flip {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C]
    {M : Mon_ C} : (𝟙 ⊗ mul M) ≫ mul M = category_theory.iso.inv α_ ≫ (mul M ⊗ 𝟙) ≫ mul M :=
  sorry

/-- A morphism of monoid objects. -/
structure hom {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C]
    (M : Mon_ C) (N : Mon_ C)
    where
  hom : X M ⟶ X N
  one_hom' :
    autoParam (one M ≫ hom = one N)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  mul_hom' :
    autoParam (mul M ≫ hom = (hom ⊗ hom) ≫ mul N)
      (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
        (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem hom.one_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {N : Mon_ C} (c : hom M N) :
    one M ≫ hom.hom c = one N :=
  sorry

@[simp] theorem hom.mul_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {N : Mon_ C} (c : hom M N) :
    mul M ≫ hom.hom c = (hom.hom c ⊗ hom.hom c) ≫ mul N :=
  sorry

@[simp] theorem hom.mul_hom_assoc {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {N : Mon_ C} (c : hom M N) {X' : C}
    (f' : X N ⟶ X') : mul M ≫ hom.hom c ≫ f' = (hom.hom c ⊗ hom.hom c) ≫ mul N ≫ f' :=
  sorry

/-- The identity morphism on a monoid object. -/
def id {C : Type u₁} [category_theory.category C] [category_theory.monoidal_category C]
    (M : Mon_ C) : hom M M :=
  hom.mk 𝟙

protected instance hom_inhabited {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (M : Mon_ C) : Inhabited (hom M M) :=
  { default := id M }

/-- Composition of morphisms of monoid objects. -/
@[simp] theorem comp_hom {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {N : Mon_ C} {O : Mon_ C} (f : hom M N)
    (g : hom N O) : hom.hom (comp f g) = hom.hom f ≫ hom.hom g :=
  Eq.refl (hom.hom (comp f g))

protected instance category_theory.category {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] : category_theory.category (Mon_ C) :=
  category_theory.category.mk

@[simp] theorem id_hom' {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (M : Mon_ C) : hom.hom 𝟙 = 𝟙 :=
  rfl

@[simp] theorem comp_hom' {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] {M : Mon_ C} {N : Mon_ C} {K : Mon_ C} (f : M ⟶ N)
    (g : N ⟶ K) : hom.hom (f ≫ g) = hom.hom f ≫ hom.hom g :=
  rfl

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simp] theorem forget_map (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] (A : Mon_ C) (B : Mon_ C) (f : A ⟶ B) :
    category_theory.functor.map (forget C) f = hom.hom f :=
  Eq.refl (category_theory.functor.map (forget C) f)

protected instance forget_faithful {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] : category_theory.faithful (forget C) :=
  category_theory.faithful.mk

protected instance category_theory.has_hom.hom.hom.category_theory.is_iso {C : Type u₁}
    [category_theory.category C] [category_theory.monoidal_category C] {A : Mon_ C} {B : Mon_ C}
    (f : A ⟶ B) [e : category_theory.is_iso (category_theory.functor.map (forget C) f)] :
    category_theory.is_iso (hom.hom f) :=
  e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
protected instance forget.category_theory.reflects_isomorphisms {C : Type u₁}
    [category_theory.category C] [category_theory.monoidal_category C] :
    category_theory.reflects_isomorphisms (forget C) :=
  category_theory.reflects_isomorphisms.mk
    fun (X Y : Mon_ C) (f : X ⟶ Y)
      (e : category_theory.is_iso (category_theory.functor.map (forget C) f)) =>
      category_theory.is_iso.mk (hom.mk (inv (hom.hom f)))

protected instance unique_hom_from_trivial {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] (A : Mon_ C) : unique (trivial C ⟶ A) :=
  unique.mk { default := hom.mk (one A) } sorry

protected instance category_theory.limits.has_initial {C : Type u₁} [category_theory.category C]
    [category_theory.monoidal_category C] : category_theory.limits.has_initial (Mon_ C) :=
  category_theory.limits.has_initial_of_unique (trivial C)

end Mon_


namespace category_theory.lax_monoidal_functor


/--
A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
-- TODO: map_Mod F A : Mod A ⥤ Mod (F.map_Mon A)

@[simp] theorem map_Mon_obj_X {C : Type u₁} [category C] [monoidal_category C] {D : Type u₂}
    [category D] [monoidal_category D] (F : lax_monoidal_functor C D) (A : Mon_ C) :
    Mon_.X (functor.obj (map_Mon F) A) = functor.obj (to_functor F) (Mon_.X A) :=
  Eq.refl (Mon_.X (functor.obj (map_Mon F) A))

/-- `map_Mon` is functorial in the lax monoidal functor. -/
def map_Mon_functor (C : Type u₁) [category C] [monoidal_category C] (D : Type u₂) [category D]
    [monoidal_category D] : lax_monoidal_functor C D ⥤ Mon_ C ⥤ Mon_ D :=
  functor.mk map_Mon
    fun (F G : lax_monoidal_functor C D) (α : F ⟶ G) =>
      nat_trans.mk
        fun (A : Mon_ C) =>
          Mon_.hom.mk (nat_trans.app (monoidal_nat_trans.to_nat_trans α) (Mon_.X A))

end category_theory.lax_monoidal_functor


namespace Mon_


namespace equiv_lax_monoidal_functor_punit


/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
def lax_monoidal_to_Mon (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] :
    category_theory.lax_monoidal_functor (category_theory.discrete PUnit) C ⥤ Mon_ C :=
  category_theory.functor.mk
    (fun (F : category_theory.lax_monoidal_functor (category_theory.discrete PUnit) C) =>
      category_theory.functor.obj (category_theory.lax_monoidal_functor.map_Mon F)
        (trivial (category_theory.discrete PUnit)))
    fun (F G : category_theory.lax_monoidal_functor (category_theory.discrete PUnit) C)
      (α : F ⟶ G) =>
      category_theory.nat_trans.app
        (category_theory.functor.map
          (category_theory.lax_monoidal_functor.map_Mon_functor (category_theory.discrete PUnit) C)
          α)
        (trivial (category_theory.discrete PUnit))

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
def Mon_to_lax_monoidal (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] :
    Mon_ C ⥤ category_theory.lax_monoidal_functor (category_theory.discrete PUnit) C :=
  category_theory.functor.mk
    (fun (A : Mon_ C) =>
      category_theory.lax_monoidal_functor.mk
        (category_theory.functor.mk (fun (_x : category_theory.discrete PUnit) => X A)
          fun (_x _x_1 : category_theory.discrete PUnit) (_x : _x ⟶ _x_1) => 𝟙)
        (one A) fun (_x _x : category_theory.discrete PUnit) => mul A)
    fun (A B : Mon_ C) (f : A ⟶ B) =>
      category_theory.monoidal_nat_trans.mk
        (category_theory.nat_trans.mk fun (_x : category_theory.discrete PUnit) => hom.hom f)

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simp] theorem unit_iso_inv_app_to_nat_trans_app (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C]
    (X : category_theory.lax_monoidal_functor (category_theory.discrete PUnit) C) :
    ∀ (X_1 : category_theory.discrete PUnit),
        category_theory.nat_trans.app
            (category_theory.monoidal_nat_trans.to_nat_trans
              (category_theory.nat_trans.app (category_theory.iso.inv (unit_iso C)) X))
            X_1 =
          inv
            (category_theory.eq_to_hom
              (congr_arg
                (category_theory.functor.obj (category_theory.lax_monoidal_functor.to_functor X))
                (unit_iso._proof_1 X_1))) :=
  sorry

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simp] theorem counit_iso_inv_app_hom (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] (X : Mon_ C) :
    hom.hom (category_theory.nat_trans.app (category_theory.iso.inv (counit_iso C)) X) = 𝟙 :=
  Eq.refl 𝟙

end equiv_lax_monoidal_functor_punit


/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
def equiv_lax_monoidal_functor_punit (C : Type u₁) [category_theory.category C]
    [category_theory.monoidal_category C] :
    category_theory.lax_monoidal_functor (category_theory.discrete PUnit) C ≌ Mon_ C :=
  category_theory.equivalence.mk' sorry sorry sorry sorry

end Mathlib