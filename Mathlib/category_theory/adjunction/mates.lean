/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.conj
import Mathlib.category_theory.yoneda
import Mathlib.PostPort

universes u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ 

namespace Mathlib

/-!
# Mate of natural transformations

This file establishes the bijection between the 2-cells

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, and shows that in the special case where `G,H` are identity then the
bijection preserves and reflects isomorphisms (i.e. we have bijections `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, and
if either side is an iso then the other side is as well).

On its own, this bijection is not particularly useful but it includes a number of interesting cases
as specializations.

For instance, this generalises the fact that adjunctions are unique (since if `L₁ ≅ L₂` then we
deduce `R₁ ≅ R₂`).
Another example arises from considering the square representing that a functor `H` preserves
products, in particular the morphism `HA ⨯ H- ⟶ H(A ⨯ -)`. Then provided `(A ⨯ -)` and `HA ⨯ -` have
left adjoints (for instance if the relevant categories are cartesian closed), the transferred
natural transformation is the exponential comparison morphism: `H(A ^ -) ⟶ HA ^ H-`.
Furthermore if `H` has a left adjoint `L`, this morphism is an isomorphism iff its mate
`L(HA ⨯ -) ⟶ A ⨯ L-` is an isomorphism, see
https://ncatlab.org/nlab/show/Frobenius+reciprocity#InCategoryTheory.
This also relates to Grothendieck's yoga of six operations, though this is not spelled out in
mathlib: https://ncatlab.org/nlab/show/six+operations.
-/

namespace category_theory


/--
Suppose we have a square of functors (where the top and bottom are adjunctions `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` respectively).

      C ↔ D
    G ↓   ↓ H
      E ↔ F

Then we have a bijection between natural transformations `G ⋙ L₂ ⟶ L₁ ⋙ H` and
`R₁ ⋙ G ⟶ H ⋙ R₂`.
This can be seen as a bijection of the 2-cells:

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/
def transfer_nat_trans {C : Type u₁} {D : Type u₂} [category C] [category D] {E : Type u₃} {F : Type u₄} [category E] [category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) :=
  equiv.mk
    (fun (h : G ⋙ L₂ ⟶ L₁ ⋙ H) =>
      nat_trans.mk
        fun (X : D) =>
          nat_trans.app (adjunction.unit adj₂) (functor.obj G (functor.obj R₁ X)) ≫
            functor.map R₂
              (nat_trans.app h (functor.obj R₁ X) ≫ functor.map H (nat_trans.app (adjunction.counit adj₁) X)))
    (fun (h : R₁ ⋙ G ⟶ H ⋙ R₂) =>
      nat_trans.mk
        fun (X : C) =>
          functor.map L₂ (functor.map G (nat_trans.app (adjunction.unit adj₁) X) ≫ nat_trans.app h (functor.obj L₁ X)) ≫
            nat_trans.app (adjunction.counit adj₂) (functor.obj H (functor.obj L₁ X)))
    sorry sorry

theorem transfer_nat_trans_counit {C : Type u₁} {D : Type u₂} [category C] [category D] {E : Type u₃} {F : Type u₄} [category E] [category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (Y : D) : functor.map L₂ (nat_trans.app (coe_fn (transfer_nat_trans adj₁ adj₂) f) Y) ≫
    nat_trans.app (adjunction.counit adj₂) (functor.obj H Y) =
  nat_trans.app f (functor.obj R₁ Y) ≫ functor.map H (nat_trans.app (adjunction.counit adj₁) Y) := sorry

theorem unit_transfer_nat_trans {C : Type u₁} {D : Type u₂} [category C] [category D] {E : Type u₃} {F : Type u₄} [category E] [category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : G ⋙ L₂ ⟶ L₁ ⋙ H) (X : C) : functor.map G (nat_trans.app (adjunction.unit adj₁) X) ≫
    nat_trans.app (coe_fn (transfer_nat_trans adj₁ adj₂) f) (functor.obj L₁ X) =
  nat_trans.app (adjunction.unit adj₂) (functor.obj G (functor.obj 𝟭 X)) ≫
    functor.map R₂ (nat_trans.app f (functor.obj 𝟭 X)) := sorry

/--
Given two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` both between categories `C`, `D`, there is a
bijection between natural transformations `L₂ ⟶ L₁` and natural transformations `R₁ ⟶ R₂`.
This is defined as a special case of `transfer_nat_trans`, where the two "vertical" functors are
identity.
TODO: Generalise to when the two vertical functors are equivalences rather than being exactly `𝟭`.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a transformation is an iso
iff its image under the bijection is an iso, see eg `category_theory.transfer_nat_trans_self_iso`.
This is in contrast to the general case `transfer_nat_trans` which does not in general have this
property.
-/
def transfer_nat_trans_self {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
  equiv.trans
    (equiv.trans (equiv.symm (iso.hom_congr (functor.left_unitor L₂) (functor.right_unitor L₁)))
      (transfer_nat_trans adj₁ adj₂))
    (iso.hom_congr (functor.right_unitor R₁) (functor.left_unitor R₂))

theorem transfer_nat_trans_self_counit {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : L₂ ⟶ L₁) (X : D) : functor.map L₂ (nat_trans.app (coe_fn (transfer_nat_trans_self adj₁ adj₂) f) X) ≫
    nat_trans.app (adjunction.counit adj₂) X =
  nat_trans.app f (functor.obj R₁ X) ≫ nat_trans.app (adjunction.counit adj₁) X := sorry

theorem unit_transfer_nat_trans_self {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : L₂ ⟶ L₁) (X : C) : nat_trans.app (adjunction.unit adj₁) X ≫
    nat_trans.app (coe_fn (transfer_nat_trans_self adj₁ adj₂) f) (functor.obj L₁ X) =
  nat_trans.app (adjunction.unit adj₂) X ≫ functor.map R₂ (nat_trans.app f X) := sorry

@[simp] theorem transfer_nat_trans_self_id {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) : coe_fn (transfer_nat_trans_self adj₁ adj₁) 𝟙 = 𝟙 := sorry

@[simp] theorem transfer_nat_trans_self_symm_id {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) : coe_fn (equiv.symm (transfer_nat_trans_self adj₁ adj₁)) 𝟙 = 𝟙 := sorry

theorem transfer_nat_trans_self_comp {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {L₃ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} {R₃ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (f : L₂ ⟶ L₁) (g : L₃ ⟶ L₂) : coe_fn (transfer_nat_trans_self adj₁ adj₂) f ≫ coe_fn (transfer_nat_trans_self adj₂ adj₃) g =
  coe_fn (transfer_nat_trans_self adj₁ adj₃) (g ≫ f) := sorry

theorem transfer_nat_trans_self_symm_comp {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {L₃ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} {R₃ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (f : R₂ ⟶ R₁) (g : R₃ ⟶ R₂) : coe_fn (equiv.symm (transfer_nat_trans_self adj₂ adj₁)) f ≫ coe_fn (equiv.symm (transfer_nat_trans_self adj₃ adj₂)) g =
  coe_fn (equiv.symm (transfer_nat_trans_self adj₃ adj₁)) (g ≫ f) := sorry

theorem transfer_nat_trans_self_comm {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {f : L₂ ⟶ L₁} {g : L₁ ⟶ L₂} (gf : g ≫ f = 𝟙) : coe_fn (transfer_nat_trans_self adj₁ adj₂) f ≫ coe_fn (transfer_nat_trans_self adj₂ adj₁) g = 𝟙 := sorry

theorem transfer_nat_trans_self_symm_comm {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {f : R₁ ⟶ R₂} {g : R₂ ⟶ R₁} (gf : g ≫ f = 𝟙) : coe_fn (equiv.symm (transfer_nat_trans_self adj₁ adj₂)) f ≫ coe_fn (equiv.symm (transfer_nat_trans_self adj₂ adj₁)) g =
  𝟙 := sorry

/--
If `f` is an isomorphism, then the transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_of_iso`.
-/
protected instance transfer_nat_trans_self_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : L₂ ⟶ L₁) [is_iso f] : is_iso (coe_fn (transfer_nat_trans_self adj₁ adj₂) f) :=
  is_iso.mk (coe_fn (transfer_nat_trans_self adj₂ adj₁) (inv f))

/--
If `f` is an isomorphism, then the un-transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_of_iso`.
-/
protected instance transfer_nat_trans_self_symm_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : R₁ ⟶ R₂) [is_iso f] : is_iso (coe_fn (equiv.symm (transfer_nat_trans_self adj₁ adj₂)) f) :=
  is_iso.mk (coe_fn (equiv.symm (transfer_nat_trans_self adj₂ adj₁)) (inv f))

/--
If `f` is a natural transformation whose transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_iso`.
-/
def transfer_nat_trans_self_of_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : L₂ ⟶ L₁) [is_iso (coe_fn (transfer_nat_trans_self adj₁ adj₂) f)] : is_iso f :=
  eq.mpr sorry
    (eq.mp sorry
      (category_theory.transfer_nat_trans_self_symm_iso adj₁ adj₂ (coe_fn (transfer_nat_trans_self adj₁ adj₂) f)))

/--
If `f` is a natural transformation whose un-transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_iso`.
-/
def transfer_nat_trans_self_symm_of_iso {C : Type u₁} {D : Type u₂} [category C] [category D] {L₁ : C ⥤ D} {L₂ : C ⥤ D} {R₁ : D ⥤ C} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (f : R₁ ⟶ R₂) [is_iso (coe_fn (equiv.symm (transfer_nat_trans_self adj₁ adj₂)) f)] : is_iso f :=
  eq.mpr sorry
    (eq.mp sorry
      (category_theory.transfer_nat_trans_self_iso adj₁ adj₂ (coe_fn (equiv.symm (transfer_nat_trans_self adj₁ adj₂)) f)))

