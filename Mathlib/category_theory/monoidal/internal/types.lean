/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.category.Mon.basic
import Mathlib.category_theory.monoidal.CommMon_
import Mathlib.category_theory.monoidal.types
import Mathlib.PostPort

universes u 

namespace Mathlib

/-!
# `Mon_ (Type u) ≌ Mon.{u}`

The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.

Moreover, this equivalence is compatible with the forgetful functors to `Type`.
-/

namespace Mon_Type_equivalence_Mon


protected instance Mon_monoid (A : Mon_ (Type u)) : monoid (Mon_.X A) :=
  monoid.mk (fun (x y : Mon_.X A) => Mon_.mul A (x, y)) sorry (Mon_.one A PUnit.unit) sorry sorry

/--
Converting a monoid object in `Type` to a bundled monoid.
-/
def functor : Mon_ (Type u) ⥤ Mon :=
  category_theory.functor.mk (fun (A : Mon_ (Type u)) => category_theory.bundled.mk (Mon_.X A))
    fun (A B : Mon_ (Type u)) (f : A ⟶ B) => monoid_hom.mk (Mon_.hom.hom f) sorry sorry

/--
Converting a bundled monoid to a monoid object in `Type`.
-/
def inverse : Mon ⥤ Mon_ (Type u) :=
  category_theory.functor.mk
    (fun (A : Mon) => Mon_.mk (↥A) (fun (_x : 𝟙_) => 1) fun (p : ↥A ⊗ ↥A) => prod.fst p * prod.snd p)
    fun (A B : Mon) (f : A ⟶ B) => Mon_.hom.mk ⇑f

end Mon_Type_equivalence_Mon


/--
The category of internal monoid objects in `Type`
is equivalent to the category of "native" bundled monoids.
-/
def Mon_Type_equivalence_Mon : Mon_ (Type u) ≌ Mon :=
  category_theory.equivalence.mk' sorry sorry
    (category_theory.nat_iso.of_components
      (fun (A : Mon_ (Type u)) => category_theory.iso.mk (Mon_.hom.mk 𝟙) (Mon_.hom.mk 𝟙)) sorry)
    (category_theory.nat_iso.of_components
      (fun (A : Mon) => category_theory.iso.mk (monoid_hom.mk id sorry sorry) (monoid_hom.mk id sorry sorry)) sorry)

/--
The equivalence `Mon_ (Type u) ≌ Mon.{u}`
is naturally compatible with the forgetful functors to `Type u`.
-/
def Mon_Type_equivalence_Mon_forget : Mon_Type_equivalence_Mon.functor ⋙ category_theory.forget Mon ≅ Mon_.forget (Type u) :=
  category_theory.nat_iso.of_components
    (fun (A : Mon_ (Type u)) =>
      category_theory.iso.refl
        (category_theory.functor.obj (Mon_Type_equivalence_Mon.functor ⋙ category_theory.forget Mon) A))
    sorry

protected instance Mon_Type_inhabited : Inhabited (Mon_ (Type u)) :=
  { default := category_theory.functor.obj Mon_Type_equivalence_Mon.inverse (Mon.of PUnit) }

namespace CommMon_Type_equivalence_CommMon


protected instance CommMon_comm_monoid (A : CommMon_ (Type u)) : comm_monoid (Mon_.X (CommMon_.to_Mon_ A)) :=
  comm_monoid.mk monoid.mul sorry monoid.one sorry sorry sorry

/--
Converting a commutative monoid object in `Type` to a bundled commutative monoid.
-/
def functor : CommMon_ (Type u) ⥤ CommMon :=
  category_theory.functor.mk (fun (A : CommMon_ (Type u)) => category_theory.bundled.mk (Mon_.X (CommMon_.to_Mon_ A)))
    fun (A B : CommMon_ (Type u)) (f : A ⟶ B) => category_theory.functor.map Mon_Type_equivalence_Mon.functor f

/--
Converting a bundled commutative monoid to a commutative monoid object in `Type`.
-/
def inverse : CommMon ⥤ CommMon_ (Type u) :=
  category_theory.functor.mk
    (fun (A : CommMon) =>
      CommMon_.mk
        (Mon_.mk
          (Mon_.X
            (category_theory.functor.obj Mon_Type_equivalence_Mon.inverse
              (category_theory.functor.obj (category_theory.forget₂ CommMon Mon) A)))
          (Mon_.one
            (category_theory.functor.obj Mon_Type_equivalence_Mon.inverse
              (category_theory.functor.obj (category_theory.forget₂ CommMon Mon) A)))
          (Mon_.mul
            (category_theory.functor.obj Mon_Type_equivalence_Mon.inverse
              (category_theory.functor.obj (category_theory.forget₂ CommMon Mon) A)))))
    fun (A B : CommMon) (f : A ⟶ B) => category_theory.functor.map Mon_Type_equivalence_Mon.inverse f

end CommMon_Type_equivalence_CommMon


/--
The category of internal commutative monoid objects in `Type`
is equivalent to the category of "native" bundled commutative monoids.
-/
def CommMon_Type_equivalence_CommMon : CommMon_ (Type u) ≌ CommMon :=
  category_theory.equivalence.mk' sorry sorry
    (category_theory.nat_iso.of_components
      (fun (A : CommMon_ (Type u)) => category_theory.iso.mk (Mon_.hom.mk 𝟙) (Mon_.hom.mk 𝟙)) sorry)
    (category_theory.nat_iso.of_components
      (fun (A : CommMon) => category_theory.iso.mk (monoid_hom.mk id sorry sorry) (monoid_hom.mk id sorry sorry)) sorry)

/--
The equivalences `Mon_ (Type u) ≌ Mon.{u}` and `CommMon_ (Type u) ≌ CommMon.{u}`
are naturally compatible with the forgetful functors to `Mon` and `Mon_ (Type u)`.
-/
def CommMon_Type_equivalence_CommMon_forget : CommMon_Type_equivalence_CommMon.functor ⋙ category_theory.forget₂ CommMon Mon ≅
  CommMon_.forget₂_Mon_ (Type u) ⋙ Mon_Type_equivalence_Mon.functor :=
  category_theory.nat_iso.of_components
    (fun (A : CommMon_ (Type u)) =>
      category_theory.iso.refl
        (category_theory.functor.obj (CommMon_Type_equivalence_CommMon.functor ⋙ category_theory.forget₂ CommMon Mon) A))
    sorry

protected instance CommMon_Type_inhabited : Inhabited (CommMon_ (Type u)) :=
  { default := category_theory.functor.obj CommMon_Type_equivalence_CommMon.inverse (CommMon.of PUnit) }

