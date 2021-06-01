/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.conj
import Mathlib.category_theory.yoneda
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ u₃ u₄ v₃ v₄ 

namespace Mathlib

namespace category_theory


/--
If the left adjoint is fully faithful, then the unit is an isomorphism.

See
* Lemma 4.5.13 from [Riehl][riehl2017]
* https://math.stackexchange.com/a/2727177
* https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
protected instance unit_is_iso_of_L_fully_faithful {C : Type u₁} [category C] {D : Type u₂}
    [category D] {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) [full L] [faithful L] :
    is_iso (adjunction.unit h) :=
  nat_iso.is_iso_of_is_iso_app (adjunction.unit h)

/--
If the right adjoint is fully faithful, then the counit is an isomorphism.

See https://stacks.math.columbia.edu/tag/07RB (we only prove the forward direction!)
-/
protected instance counit_is_iso_of_R_fully_faithful {C : Type u₁} [category C] {D : Type u₂}
    [category D] {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) [full R] [faithful R] :
    is_iso (adjunction.counit h) :=
  nat_iso.is_iso_of_is_iso_app (adjunction.counit h)

-- TODO also prove the converses?

-- def L_full_of_unit_is_iso [is_iso (adjunction.unit h)] : full L := sorry

-- def L_faithful_of_unit_is_iso [is_iso (adjunction.unit h)] : faithful L := sorry

-- def R_full_of_counit_is_iso [is_iso (adjunction.counit h)] : full R := sorry

-- def R_faithful_of_counit_is_iso [is_iso (adjunction.counit h)] : faithful R := sorry

-- TODO also do the statements from Riehl 4.5.13 for full and faithful separately?

-- TODO: This needs some lemmas describing the produced adjunction, probably in terms of `adj`,

-- `iC` and `iD`.

/--
If `C` is a full subcategory of `C'` and `D` is a full subcategory of `D'`, then we can restrict
an adjunction `L' ⊣ R'` where `L' : C' ⥤ D'` and `R' : D' ⥤ C'` to `C` and `D`.
The construction here is slightly more general, in that `C` is required only to have a full and
faithful "inclusion" functor `iC : C ⥤ C'` (and similarly `iD : D ⥤ D'`) which commute (up to
natural isomorphism) with the proposed restrictions.
-/
def adjunction.restrict_fully_faithful {C : Type u₁} [category C] {D : Type u₂} [category D]
    {C' : Type u₃} [category C'] {D' : Type u₄} [category D'] (iC : C ⥤ C') (iD : D ⥤ D')
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R') {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD)
    (comm2 : iD ⋙ R' ≅ R ⋙ iC) [full iC] [faithful iC] [full iD] [faithful iD] : L ⊣ R :=
  adjunction.mk_of_hom_equiv
    (adjunction.core_hom_equiv.mk
      fun (X : C) (Y : D) =>
        equiv.trans
          (equiv.trans
            (equiv.trans
              (equiv.trans (equiv_of_fully_faithful iD)
                (iso.hom_congr (iso.app (iso.symm comm1) X) (iso.refl (functor.obj iD Y))))
              (adjunction.hom_equiv adj (functor.obj iC X) (functor.obj iD Y)))
            (iso.hom_congr (iso.refl (functor.obj iC X)) (iso.app comm2 Y)))
          (equiv.symm (equiv_of_fully_faithful iC)))

end Mathlib