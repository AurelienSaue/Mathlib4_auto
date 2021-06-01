/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.yoneda
import Mathlib.category_theory.opposites
import Mathlib.PostPort

universes u₁ u₂ v₁ v₂ 

namespace Mathlib

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.
These constructions are used to show uniqueness of adjoints (up to natural isomorphism).

## Tags
adjunction, opposite, uniqueness
-/

namespace adjunction


/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
def adjoint_of_op_adjoint_op {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : C ⥤ D) (G : D ⥤ C)
    (h : category_theory.functor.op G ⊣ category_theory.functor.op F) : F ⊣ G :=
  category_theory.adjunction.mk_of_hom_equiv
    (category_theory.adjunction.core_hom_equiv.mk
      fun (X : C) (Y : D) =>
        equiv.trans
          (equiv.symm
            (equiv.trans (category_theory.adjunction.hom_equiv h (opposite.op Y) (opposite.op X))
              (category_theory.op_equiv (opposite.op Y)
                (category_theory.functor.obj (category_theory.functor.op F) (opposite.op X)))))
          (category_theory.op_equiv
            (category_theory.functor.obj (category_theory.functor.op G) (opposite.op Y))
            (opposite.op X)))

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjoint_unop_of_adjoint_op {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : C ⥤ D) (G : Dᵒᵖ ⥤ (Cᵒᵖ))
    (h : G ⊣ category_theory.functor.op F) : F ⊣ category_theory.functor.unop G :=
  adjoint_of_op_adjoint_op F (category_theory.functor.unop G)
    (category_theory.adjunction.of_nat_iso_left h
      (category_theory.iso.symm (category_theory.functor.op_unop_iso G)))

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unop_adjoint_of_op_adjoint {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) (G : D ⥤ C)
    (h : category_theory.functor.op G ⊣ F) : category_theory.functor.unop F ⊣ G :=
  adjoint_of_op_adjoint_op (category_theory.functor.unop F) G
    (category_theory.adjunction.of_nat_iso_right h
      (category_theory.iso.symm (category_theory.functor.op_unop_iso F)))

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unop_adjoint_unop_of_adjoint {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) (G : Dᵒᵖ ⥤ (Cᵒᵖ)) (h : G ⊣ F) :
    category_theory.functor.unop F ⊣ category_theory.functor.unop G :=
  adjoint_unop_of_adjoint_op (category_theory.functor.unop F) G
    (category_theory.adjunction.of_nat_iso_right h
      (category_theory.iso.symm (category_theory.functor.op_unop_iso F)))

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
def op_adjoint_op_of_adjoint {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) :
    category_theory.functor.op F ⊣ category_theory.functor.op G :=
  category_theory.adjunction.mk_of_hom_equiv
    (category_theory.adjunction.core_hom_equiv.mk
      fun (X : Cᵒᵖ) (Y : Dᵒᵖ) =>
        equiv.trans
          (category_theory.op_equiv (category_theory.functor.obj (category_theory.functor.op F) X)
            Y)
          (equiv.trans
            (equiv.symm
              (category_theory.adjunction.hom_equiv h (opposite.unop Y) (opposite.unop X)))
            (equiv.symm
              (category_theory.op_equiv X
                (opposite.op (category_theory.functor.obj G (opposite.unop Y)))))))

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjoint_op_of_adjoint_unop {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) (G : D ⥤ C)
    (h : G ⊣ category_theory.functor.unop F) : F ⊣ category_theory.functor.op G :=
  category_theory.adjunction.of_nat_iso_left
    (op_adjoint_op_of_adjoint (category_theory.functor.unop F) G h)
    (category_theory.functor.op_unop_iso F)

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def op_adjoint_of_unop_adjoint {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : C ⥤ D) (G : Dᵒᵖ ⥤ (Cᵒᵖ))
    (h : category_theory.functor.unop G ⊣ F) : category_theory.functor.op F ⊣ G :=
  category_theory.adjunction.of_nat_iso_right
    (op_adjoint_op_of_adjoint F (category_theory.functor.unop G) h)
    (category_theory.functor.op_unop_iso G)

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjoint_of_unop_adjoint_unop {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] (F : Cᵒᵖ ⥤ (Dᵒᵖ)) (G : Dᵒᵖ ⥤ (Cᵒᵖ))
    (h : category_theory.functor.unop G ⊣ category_theory.functor.unop F) : F ⊣ G :=
  category_theory.adjunction.of_nat_iso_right
    (adjoint_op_of_adjoint_unop F (category_theory.functor.unop G) h)
    (category_theory.functor.op_unop_iso G)

/--
If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fully_faithful_cancel_right` to show left adjoints are unique.
-/
def left_adjoints_coyoneda_equiv {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] {F : C ⥤ D} {F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) :
    category_theory.functor.op F ⋙ category_theory.coyoneda ≅
        category_theory.functor.op F' ⋙ category_theory.coyoneda :=
  category_theory.nat_iso.of_components
    (fun (X : Cᵒᵖ) =>
      category_theory.nat_iso.of_components
        (fun (Y : D) =>
          equiv.to_iso
            (equiv.trans (category_theory.adjunction.hom_equiv adj1 (opposite.unop X) Y)
              (equiv.symm (category_theory.adjunction.hom_equiv adj2 (opposite.unop X) Y))))
        sorry)
    sorry

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
def left_adjoint_uniq {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] {F : C ⥤ D} {F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G) : F ≅ F' :=
  category_theory.nat_iso.remove_op
    (category_theory.fully_faithful_cancel_right category_theory.coyoneda
      (left_adjoints_coyoneda_equiv adj2 adj1))

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
def right_adjoint_uniq {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] {F : C ⥤ D} {G : D ⥤ C} {G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F ⊣ G') : G ≅ G' :=
  category_theory.nat_iso.remove_op
    (left_adjoint_uniq (op_adjoint_op_of_adjoint G' F adj2) (op_adjoint_op_of_adjoint G F adj1))

/--
Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.
-/
def nat_iso_of_left_adjoint_nat_iso {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] {F : C ⥤ D} {F' : C ⥤ D} {G : D ⥤ C} {G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G') (l : F ≅ F') : G ≅ G' :=
  right_adjoint_uniq adj1
    (category_theory.adjunction.of_nat_iso_left adj2 (category_theory.iso.symm l))

/--
Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.
-/
def nat_iso_of_right_adjoint_nat_iso {C : Type u₁} [category_theory.category C] {D : Type u₂}
    [category_theory.category D] {F : C ⥤ D} {F' : C ⥤ D} {G : D ⥤ C} {G' : D ⥤ C} (adj1 : F ⊣ G)
    (adj2 : F' ⊣ G') (r : G ≅ G') : F ≅ F' :=
  left_adjoint_uniq adj1
    (category_theory.adjunction.of_nat_iso_right adj2 (category_theory.iso.symm r))

end Mathlib