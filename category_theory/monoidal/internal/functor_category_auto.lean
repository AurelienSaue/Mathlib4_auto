/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.monoidal.CommMon_
import Mathlib.category_theory.monoidal.functor_category
import PostPort

universes u₁ u₂ v₁ v₂ 

namespace Mathlib

/-!
# `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing as functors from `C` into the monoid objects of `D`.

This is formalised as:
* `Mon_functor_category_equivalence : Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`

The intended application is that as `Ring ≌ Mon_ Ab` (not yet constructed!),
we have `presheaf Ring X ≌ presheaf (Mon_ Ab) X ≌ Mon_ (presheaf Ab X)`,
and we can model a module over a presheaf of rings as a module object in `presheaf Ab X`.

## Future work
Presumably this statement is not specific to monoids,
and could be generalised to any internal algebraic objects,
if the appropriate framework was available.
-/

namespace category_theory.monoidal


namespace Mon_functor_category_equivalence


/--
Functor translating a monoid object in a functor category
to a functor into the category of monoid objects.
-/
@[simp] theorem functor_map_app_hom {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] (A : Mon_ (C ⥤ D)) (B : Mon_ (C ⥤ D)) (f : A ⟶ B) (X : C) : Mon_.hom.hom (nat_trans.app (functor.map functor f) X) = nat_trans.app (Mon_.hom.hom f) X :=
  Eq.refl (Mon_.hom.hom (nat_trans.app (functor.map functor f) X))

/--
Functor translating a functor into the category of monoid objects
to a monoid object in the functor category
-/
@[simp] theorem inverse_map_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] (F : C ⥤ Mon_ D) (G : C ⥤ Mon_ D) (α : F ⟶ G) (X : C) : nat_trans.app (Mon_.hom.hom (functor.map inverse α)) X = Mon_.hom.hom (nat_trans.app α X) :=
  Eq.refl (nat_trans.app (Mon_.hom.hom (functor.map inverse α)) X)

/--
The unit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simp] theorem unit_iso_inv_app_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] (X : Mon_ (C ⥤ D)) (_x : C) : nat_trans.app (Mon_.hom.hom (nat_trans.app (iso.inv unit_iso) X)) _x = 𝟙 :=
  Eq.refl 𝟙

/--
The counit for the equivalence `Mon_ (C ⥤ D) ≌ C ⥤ Mon_ D`.
-/
@[simp] theorem counit_iso_inv_app_app_hom {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] (X : C ⥤ Mon_ D) : ∀ (X_1 : C), Mon_.hom.hom (nat_trans.app (nat_trans.app (iso.inv counit_iso) X) X_1) = 𝟙 :=
  fun (X_1 : C) => Eq.refl 𝟙

end Mon_functor_category_equivalence


/--
When `D` is a monoidal category,
monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the monoid objects of `D`.
-/
@[simp] theorem Mon_functor_category_equivalence_counit_iso (C : Type u₁) [category C] (D : Type u₂) [category D] [monoidal_category D] : equivalence.counit_iso (Mon_functor_category_equivalence C D) = Mon_functor_category_equivalence.counit_iso :=
  Eq.refl (equivalence.counit_iso (Mon_functor_category_equivalence C D))

namespace CommMon_functor_category_equivalence


/--
Functor translating a commutative monoid object in a functor category
to a functor into the category of commutative monoid objects.
-/
@[simp] theorem functor_obj_map {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] (A : CommMon_ (C ⥤ D)) {X : C} {Y : C} : ∀ (ᾰ : X ⟶ Y),
  functor.map (functor.obj functor A) ᾰ =
    functor.map (functor.obj (equivalence.functor (Mon_functor_category_equivalence C D)) (CommMon_.to_Mon_ A)) ᾰ :=
  fun (ᾰ : X ⟶ Y) => Eq.refl (functor.map (functor.obj functor A) ᾰ)

/--
Functor translating a functor into the category of commutative monoid objects
to a commutative monoid object in the functor category
-/
def inverse {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] : (C ⥤ CommMon_ D) ⥤ CommMon_ (C ⥤ D) :=
  functor.mk
    (fun (F : C ⥤ CommMon_ D) =>
      CommMon_.mk
        (Mon_.mk
          (Mon_.X
            (functor.obj (equivalence.inverse (Mon_functor_category_equivalence C D)) (F ⋙ CommMon_.forget₂_Mon_ D)))
          (Mon_.one
            (functor.obj (equivalence.inverse (Mon_functor_category_equivalence C D)) (F ⋙ CommMon_.forget₂_Mon_ D)))
          (Mon_.mul
            (functor.obj (equivalence.inverse (Mon_functor_category_equivalence C D)) (F ⋙ CommMon_.forget₂_Mon_ D)))))
    fun (F G : C ⥤ CommMon_ D) (α : F ⟶ G) =>
      functor.map (equivalence.inverse (Mon_functor_category_equivalence C D)) (whisker_right α (CommMon_.forget₂_Mon_ D))

/--
The unit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
@[simp] theorem unit_iso_inv_app_hom_app {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] (X : CommMon_ (C ⥤ D)) (_x : C) : nat_trans.app (Mon_.hom.hom (nat_trans.app (iso.inv unit_iso) X)) _x = 𝟙 :=
  Eq.refl 𝟙

/--
The counit for the equivalence `CommMon_ (C ⥤ D) ≌ C ⥤ CommMon_ D`.
-/
def counit_iso {C : Type u₁} [category C] {D : Type u₂} [category D] [monoidal_category D] [braided_category D] : inverse ⋙ functor ≅ 𝟭 :=
  nat_iso.of_components
    (fun (A : C ⥤ CommMon_ D) => nat_iso.of_components (fun (X : C) => iso.mk (Mon_.hom.mk 𝟙) (Mon_.hom.mk 𝟙)) sorry)
    sorry

end CommMon_functor_category_equivalence


/--
When `D` is a braided monoidal category,
commutative monoid objects in `C ⥤ D` are the same thing
as functors from `C` into the commutative monoid objects of `D`.
-/
@[simp] theorem CommMon_functor_category_equivalence_inverse (C : Type u₁) [category C] (D : Type u₂) [category D] [monoidal_category D] [braided_category D] : equivalence.inverse (CommMon_functor_category_equivalence C D) = CommMon_functor_category_equivalence.inverse :=
  Eq.refl (equivalence.inverse (CommMon_functor_category_equivalence C D))

