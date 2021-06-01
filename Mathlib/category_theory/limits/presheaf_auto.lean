/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.adjunction.default
import Mathlib.category_theory.elements
import Mathlib.category_theory.limits.functor_category
import Mathlib.category_theory.limits.preserves.limits
import Mathlib.category_theory.limits.shapes.terminal
import Mathlib.category_theory.limits.types
import Mathlib.PostPort

universes u₁ u₂ 

namespace Mathlib

/-!
# Colimit of representables

This file constructs an adjunction `yoneda_adjunction` between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a
functor `A : C ⥤ ℰ`, where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ`
has colimits).

This adjunction is used to show that every presheaf is a colimit of representables.

Further, the left adjoint `colimit_adj.extend_along_yoneda : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies
`yoneda ⋙ L ≅ A`, that is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through
`yoneda : C ⥤ Cᵒᵖ ⥤ Type u`. It is the left Kan extension of `A` along the yoneda embedding,
sometimes known as the Yoneda extension.

`unique_extension_along_yoneda` shows `extend_along_yoneda` is unique amongst cocontinuous functors
with this property, establishing the presheaf category as the free cocompletion of a small category.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

namespace category_theory


namespace colimit_adj


/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
def restricted_yoneda {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ] (A : C ⥤ ℰ) :
    ℰ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  yoneda ⋙ functor.obj (whiskering_left (Cᵒᵖ) (ℰᵒᵖ) (Type u₁)) (functor.op A)

/--
The functor `restricted_yoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restricted_yoneda_yoneda {C : Type u₁} [small_category C] : restricted_yoneda yoneda ≅ 𝟭 :=
  nat_iso.of_components
    (fun (P : Cᵒᵖ ⥤ Type u₁) =>
      nat_iso.of_components (fun (X : Cᵒᵖ) => yoneda_sections_small (opposite.unop X) P) sorry)
    sorry

/--
(Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimit_adj.restricted_yoneda`.
It is shown in `restrict_yoneda_hom_equiv_natural` that this is a natural bijection.
-/
def restrict_yoneda_hom_equiv {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ]
    (A : C ⥤ ℰ) (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ)
    {c : limits.cocone (functor.left_op (category_of_elements.π P) ⋙ A)} (t : limits.is_colimit c) :
    (limits.cocone.X c ⟶ E) ≃ (P ⟶ functor.obj (restricted_yoneda A) E) :=
  equiv.trans (iso.to_equiv (limits.is_colimit.hom_iso' t E))
    (equiv.mk
      (fun
        (k :
        Subtype
          fun
            (p :
            (j : functor.elements Pᵒᵖ) →
              functor.obj (functor.left_op (category_of_elements.π P) ⋙ A) j ⟶ E) =>
            ∀ {j j' : functor.elements Pᵒᵖ} (f : j ⟶ j'),
              functor.map (functor.left_op (category_of_elements.π P) ⋙ A) f ≫ p j' = p j) =>
        nat_trans.mk
          fun (c : Cᵒᵖ) (p : functor.obj P c) => subtype.val k (opposite.op (sigma.mk c p)))
      (fun (τ : P ⟶ functor.obj (restricted_yoneda A) E) =>
        { val :=
            fun (p : functor.elements Pᵒᵖ) =>
              nat_trans.app τ (sigma.fst (opposite.unop p)) (sigma.snd (opposite.unop p)),
          property := sorry })
      sorry sorry)

/--
(Implementation). Show that the bijection in `restrict_yoneda_hom_equiv` is natural (on the right).
-/
theorem restrict_yoneda_hom_equiv_natural {C : Type u₁} [small_category C] {ℰ : Type u₂}
    [category ℰ] (A : C ⥤ ℰ) (P : Cᵒᵖ ⥤ Type u₁) (E₁ : ℰ) (E₂ : ℰ) (g : E₁ ⟶ E₂)
    {c : limits.cocone (functor.left_op (category_of_elements.π P) ⋙ A)} (t : limits.is_colimit c)
    (k : limits.cocone.X c ⟶ E₁) :
    coe_fn (restrict_yoneda_hom_equiv A P E₂ t) (k ≫ g) =
        coe_fn (restrict_yoneda_hom_equiv A P E₁ t) k ≫ functor.map (restricted_yoneda A) g :=
  sorry

/--
The left adjoint to the functor `restricted_yoneda` (shown in `yoneda_adjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `is_extension_along_yoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
def extend_along_yoneda {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ] (A : C ⥤ ℰ)
    [limits.has_colimits ℰ] : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
  adjunction.left_adjoint_of_equiv
    (fun (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) =>
      restrict_yoneda_hom_equiv A P E
        (limits.colimit.is_colimit (functor.left_op (category_of_elements.π P) ⋙ A)))
    sorry

@[simp] theorem extend_along_yoneda_obj {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ]
    (A : C ⥤ ℰ) [limits.has_colimits ℰ] (P : Cᵒᵖ ⥤ Type u₁) :
    functor.obj (extend_along_yoneda A) P =
        limits.colimit (functor.left_op (category_of_elements.π P) ⋙ A) :=
  rfl

/--
Show `extend_along_yoneda` is left adjoint to `restricted_yoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
def yoneda_adjunction {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ] (A : C ⥤ ℰ)
    [limits.has_colimits ℰ] : extend_along_yoneda A ⊣ restricted_yoneda A :=
  adjunction.adjunction_of_equiv_left
    (fun (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) =>
      restrict_yoneda_hom_equiv A P E
        (limits.colimit.is_colimit (functor.left_op (category_of_elements.π P) ⋙ A)))
    (extend_along_yoneda._proof_4 A)

/--
The initial object in the category of elements for a representable functor. In `is_initial` it is
shown that this is initial.
-/
def elements.initial {C : Type u₁} [small_category C] (A : C) :
    functor.elements (functor.obj yoneda A) :=
  sigma.mk (opposite.op A) 𝟙

/--
Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def is_initial {C : Type u₁} [small_category C] (A : C) : limits.is_initial (elements.initial A) :=
  limits.is_colimit.mk
    fun (s : limits.cocone (functor.empty (functor.elements (functor.obj yoneda A)))) =>
      { val := has_hom.hom.op (sigma.snd (limits.cocone.X s)), property := sorry }

/--
`extend_along_yoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
`unique_extension_along_yoneda` shows it is unique among functors preserving colimits with this
property (up to isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 1 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def is_extension_along_yoneda {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ]
    (A : C ⥤ ℰ) [limits.has_colimits ℰ] : yoneda ⋙ extend_along_yoneda A ≅ A :=
  nat_iso.of_components
    (fun (X : C) =>
      limits.is_colimit.cocone_point_unique_up_to_iso
        (limits.colimit.is_colimit
          (functor.left_op (category_of_elements.π (functor.obj yoneda X)) ⋙ A))
        (limits.colimit_of_diagram_terminal (limits.terminal_op_of_initial (is_initial X))
          (functor.left_op (category_of_elements.π (functor.obj yoneda X)) ⋙ A)))
    sorry

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
protected instance extend_along_yoneda.category_theory.limits.preserves_colimits {C : Type u₁}
    [small_category C] {ℰ : Type u₂} [category ℰ] (A : C ⥤ ℰ) [limits.has_colimits ℰ] :
    limits.preserves_colimits (extend_along_yoneda A) :=
  adjunction.left_adjoint_preserves_colimits (yoneda_adjunction A)

end colimit_adj


/--
Since `extend_along_yoneda A` is adjoint to `restricted_yoneda A`, if we use `A = yoneda`
then `restricted_yoneda A` is isomorphic to the identity, and so `extend_along_yoneda A` is as well.
-/
def extend_along_yoneda_yoneda {C : Type u₁} [small_category C] :
    colimit_adj.extend_along_yoneda yoneda ≅ 𝟭 :=
  adjunction.nat_iso_of_right_adjoint_nat_iso (colimit_adj.yoneda_adjunction yoneda) adjunction.id
    colimit_adj.restricted_yoneda_yoneda

/--
A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`cocone_of_representable` gives a cocone for this functor which is a colimit and has point `P`.
-/
-- Maybe this should be reducible or an abbreviation?

def functor_to_representables {C : Type u₁} [small_category C] (P : Cᵒᵖ ⥤ Type u₁) :
    functor.elements Pᵒᵖ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  functor.left_op (category_of_elements.π P) ⋙ yoneda

/--
This is a cocone with point `P` for the functor `functor_to_representables P`. It is shown in
`colimit_of_representable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
def cocone_of_representable {C : Type u₁} [small_category C] (P : Cᵒᵖ ⥤ Type u₁) :
    limits.cocone (functor_to_representables P) :=
  limits.cocone.extend (limits.colimit.cocone (functor_to_representables P))
    (nat_trans.app (iso.hom extend_along_yoneda_yoneda) P)

@[simp] theorem cocone_of_representable_X {C : Type u₁} [small_category C] (P : Cᵒᵖ ⥤ Type u₁) :
    limits.cocone.X (cocone_of_representable P) = P :=
  rfl

/-- An explicit formula for the legs of the cocone `cocone_of_representable`. -/
-- Marking this as a simp lemma seems to make things more awkward.

theorem cocone_of_representable_ι_app {C : Type u₁} [small_category C] (P : Cᵒᵖ ⥤ Type u₁)
    (j : functor.elements Pᵒᵖ) :
    nat_trans.app (limits.cocone.ι (cocone_of_representable P)) j =
        iso.inv
          (yoneda_sections_small (functor.obj (functor.left_op (category_of_elements.π P)) j)
            (functor.obj
              (functor.obj (functor.const (functor.elements Pᵒᵖ))
                (limits.cocone.X (cocone_of_representable P)))
              j))
          (sigma.snd (opposite.unop j)) :=
  sorry

/-- The legs of the cocone `cocone_of_representable` are natural in the choice of presheaf. -/
theorem cocone_of_representable_naturality {C : Type u₁} [small_category C] {P₁ : Cᵒᵖ ⥤ Type u₁}
    {P₂ : Cᵒᵖ ⥤ Type u₁} (α : P₁ ⟶ P₂) (j : functor.elements P₁ᵒᵖ) :
    nat_trans.app (limits.cocone.ι (cocone_of_representable P₁)) j ≫ α =
        nat_trans.app (limits.cocone.ι (cocone_of_representable P₂))
          (functor.obj (functor.op (category_of_elements.map α)) j) :=
  sorry

/--
The cocone with point `P` given by `the_cocone` is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimit_of_representable {C : Type u₁} [small_category C] (P : Cᵒᵖ ⥤ Type u₁) :
    limits.is_colimit (cocone_of_representable P) :=
  limits.is_colimit.of_point_iso (limits.colimit.is_colimit (functor_to_representables P))

/--
Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
def nat_iso_of_nat_iso_on_representables {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ]
    (L₁ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (L₂ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) [limits.preserves_colimits L₁]
    [limits.preserves_colimits L₂] (h : yoneda ⋙ L₁ ≅ yoneda ⋙ L₂) : L₁ ≅ L₂ :=
  nat_iso.of_components
    (fun (P : Cᵒᵖ ⥤ Type u₁) =>
      limits.is_colimit.cocone_points_iso_of_nat_iso
        (limits.is_colimit_of_preserves L₁ (colimit_of_representable P))
        (limits.is_colimit_of_preserves L₂ (colimit_of_representable P))
        (functor.associator (functor.left_op (category_of_elements.π P)) yoneda L₁ ≪≫
          iso_whisker_left (functor.left_op (category_of_elements.π P)) h))
    sorry

/--
Show that `extend_along_yoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def unique_extension_along_yoneda {C : Type u₁} [small_category C] {ℰ : Type u₂} [category ℰ]
    (A : C ⥤ ℰ) [limits.has_colimits ℰ] (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (hL : yoneda ⋙ L ≅ A)
    [limits.preserves_colimits L] : L ≅ colimit_adj.extend_along_yoneda A :=
  nat_iso_of_nat_iso_on_representables L (colimit_adj.extend_along_yoneda A)
    (hL ≪≫ iso.symm (colimit_adj.is_extension_along_yoneda A))

/--
If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. This is a special case of
`is_left_adjoint_of_preserves_colimits` used to prove that.
-/
def is_left_adjoint_of_preserves_colimits_aux {C : Type u₁} [small_category C] {ℰ : Type u₂}
    [category ℰ] [limits.has_colimits ℰ] (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) [limits.preserves_colimits L] :
    is_left_adjoint L :=
  is_left_adjoint.mk (colimit_adj.restricted_yoneda (yoneda ⋙ L))
    (adjunction.of_nat_iso_left (colimit_adj.yoneda_adjunction (yoneda ⋙ L))
      (iso.symm (unique_extension_along_yoneda (yoneda ⋙ L) L (iso.refl (yoneda ⋙ L)))))

/--
If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `left_adjoint_preserves_colimits`.
-/
def is_left_adjoint_of_preserves_colimits {C : Type u₁} [small_category C] {ℰ : Type u₂}
    [category ℰ] [limits.has_colimits ℰ] (L : (C ⥤ Type u₁) ⥤ ℰ) [limits.preserves_colimits L] :
    is_left_adjoint L :=
  let e : Cᵒᵖᵒᵖ ⥤ Type u₁ ≌ C ⥤ Type u₁ := equivalence.congr_left (op_op_equivalence C);
  let t : is_left_adjoint (equivalence.functor e ⋙ L) :=
    is_left_adjoint_of_preserves_colimits_aux (equivalence.functor e ⋙ L);
  adjunction.left_adjoint_of_nat_iso (equivalence.inv_fun_id_assoc e L)

end Mathlib