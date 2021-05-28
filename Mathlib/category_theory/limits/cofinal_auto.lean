/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.punit
import Mathlib.category_theory.comma
import Mathlib.category_theory.is_connected
import Mathlib.category_theory.limits.yoneda
import Mathlib.category_theory.limits.types
import PostPort

universes v u 

namespace Mathlib

/-!
# Cofinal functors

A functor `F : C ⥤ D` is cofinal if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

We prove the following three statements are equivalent:
1. `F : C ⥤ D` is cofinal.
2. Every functor `G : D ⥤ E` has a colimit if and only if `F ⋙ G` does,
   and these colimits are isomorphic via `colimit.pre G F`.
3. `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit`.

Starting at 1. we show (in `cocones_equiv`) that
the categories of cocones over `G : D ⥤ E` and over `F ⋙ G` are equivalent.
(In fact, via an equivalence which does not change the cocone point.)
This readily implies 2., as `comp_has_colimit`, `has_colimit_of_comp`, and `colimit_iso`.

From 2. we can specialize to `G = coyoneda.obj (op d)` to obtain 3., as `colimit_comp_coyoneda_iso`.

From 3., we prove 1. directly in `cofinal_of_colimit_comp_coyoneda_iso_punit`.

We also show these conditions imply:
4. Every functor `H : Dᵒᵖ ⥤ E` has a limit if and only if `F.op ⋙ H` does,
   and these limits are isomorphic via `limit.pre H F.op`.


## Naming
There is some discrepancy in the literature about naming; some say 'final' instead of 'cofinal'.
The explanation for this is that the 'co' prefix here is *not* the usual category-theoretic one
indicating duality, but rather indicating the sense of "along with".

While the trend seems to be towards using 'final', for now we go with the bulk of the literature
and use 'cofinal'.

## References
* https://stacks.math.columbia.edu/tag/09WN
* https://ncatlab.org/nlab/show/final+functor
* Borceux, Handbook of Categorical Algebra I, Section 2.11.
  (Note he reverses the roles of definition and main result relative to here!)
-/

namespace category_theory


/--
A functor `F : C ⥤ D` is cofinal if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected.

See https://stacks.math.columbia.edu/tag/04E6
-/
def cofinal {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D)  :=
  ∀ (d : D), is_connected (comma (functor.from_punit d) F)

protected instance comma.is_connected {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [ℱ : cofinal F] (d : D) : is_connected (comma (functor.from_punit d) F) :=
  ℱ d

namespace cofinal


protected instance category_theory.comma.nonempty {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] (d : D) : Nonempty (comma (functor.from_punit d) F) :=
  is_connected.is_nonempty

/--
When `F : C ⥤ D` is cofinal, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
def lift {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] (d : D) : C :=
  comma.right (classical.arbitrary (comma (functor.from_punit d) F))

/--
When `F : C ⥤ D` is cofinal, we denote by `hom_to_lift` an arbitrary choice of morphism
`d ⟶ F.obj (lift F d)`.
-/
def hom_to_lift {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] (d : D) : d ⟶ functor.obj F (lift F d) :=
  comma.hom (classical.arbitrary (comma (functor.from_punit d) F))

/--
We provide an induction principle for reasoning about `lift` and `hom_to_lift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `hom_to_lift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : d ⟶ F.obj X₀` below),
and to show that how to transport such a construction
*both* directions along a morphism between such choices.
-/
theorem induction {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {d : D} (Z : (X : C) → (d ⟶ functor.obj F X) → Prop) (h₁ : ∀ (X₁ X₂ : C) (k₁ : d ⟶ functor.obj F X₁) (k₂ : d ⟶ functor.obj F X₂) (f : X₁ ⟶ X₂),
  k₁ ≫ functor.map F f = k₂ → Z X₁ k₁ → Z X₂ k₂) (h₂ : ∀ (X₁ X₂ : C) (k₁ : d ⟶ functor.obj F X₁) (k₂ : d ⟶ functor.obj F X₂) (f : X₁ ⟶ X₂),
  k₁ ≫ functor.map F f = k₂ → Z X₂ k₂ → Z X₁ k₁) {X₀ : C} {k₀ : d ⟶ functor.obj F X₀} (z : Z X₀ k₀) : Z (lift F d) (hom_to_lift F d) := sorry

/--
Given a cocone over `F ⋙ G`, we can construct a `cocone G` with the same cocone point.
-/
@[simp] theorem extend_cocone_map_hom {C : Type v} [small_category C] {D : Type v} [small_category D] {F : C ⥤ D} [cofinal F] {E : Type u} [category E] {G : D ⥤ E} (X : limits.cocone (F ⋙ G)) (Y : limits.cocone (F ⋙ G)) (f : X ⟶ Y) : limits.cocone_morphism.hom (functor.map extend_cocone f) = limits.cocone_morphism.hom f :=
  Eq.refl (limits.cocone_morphism.hom (functor.map extend_cocone f))

@[simp] theorem colimit_cocone_comp_aux {C : Type v} [small_category C] {D : Type v} [small_category D] {F : C ⥤ D} [cofinal F] {E : Type u} [category E] {G : D ⥤ E} (s : limits.cocone (F ⋙ G)) (j : C) : functor.map G (hom_to_lift F (functor.obj F j)) ≫ nat_trans.app (limits.cocone.ι s) (lift F (functor.obj F j)) =
  nat_trans.app (limits.cocone.ι s) j := sorry

/-- An auxilliary construction for `extend_cone`, moving `op` around. -/
def extend_cone_cone_to_cocone {C : Type v} [small_category C] {D : Type v} [small_category D] {E : Type u} [category E] {F : C ⥤ D} {H : Dᵒᵖ ⥤ E} (c : limits.cone (functor.op F ⋙ H)) : limits.cocone (F ⋙ functor.right_op H) :=
  limits.cocone.mk (opposite.op (limits.cone.X c))
    (nat_trans.mk fun (j : C) => has_hom.hom.op (nat_trans.app (limits.cone.π c) (opposite.op j)))

/-- An auxilliary construction for `extend_cone`, moving `op` around. -/
def extend_cone_cocone_to_cone {D : Type v} [small_category D] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (c : limits.cocone (functor.right_op H)) : limits.cone H :=
  limits.cone.mk (opposite.unop (limits.cocone.X c))
    (nat_trans.mk fun (j : Dᵒᵖ) => has_hom.hom.unop (nat_trans.app (limits.cocone.ι c) (opposite.unop j)))

/--
Given a cone over `F.op ⋙ H`, we can construct a `cone H` with the same cone point.
-/
@[simp] theorem extend_cone_map_hom {C : Type v} [small_category C] {D : Type v} [small_category D] {F : C ⥤ D} [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (X : limits.cone (functor.op F ⋙ H)) (Y : limits.cone (functor.op F ⋙ H)) (f : X ⟶ Y) : limits.cone_morphism.hom (functor.map extend_cone f) = limits.cone_morphism.hom f :=
  Eq.refl (limits.cone_morphism.hom (functor.map extend_cone f))

@[simp] theorem limit_cone_comp_aux {C : Type v} [small_category C] {D : Type v} [small_category D] {F : C ⥤ D} [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (s : limits.cone (functor.op F ⋙ H)) (j : Cᵒᵖ) : nat_trans.app (limits.cone.π s) (opposite.op (lift F (functor.obj F (opposite.unop j)))) ≫
    functor.map H (has_hom.hom.op (hom_to_lift F (functor.obj F (opposite.unop j)))) =
  nat_trans.app (limits.cone.π s) j :=
  has_hom.hom.op_inj (colimit_cocone_comp_aux (extend_cone_cone_to_cocone s) (opposite.unop j))

/--
If `F` is cofinal,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`,
for any `G : D ⥤ E`.
-/
@[simp] theorem cocones_equiv_unit_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] (G : D ⥤ E) : equivalence.unit_iso (cocones_equiv F G) =
  nat_iso.of_components
    (fun (c : limits.cocone (F ⋙ G)) =>
      limits.cocones.ext (iso.refl (limits.cocone.X (functor.obj 𝟭 c))) (cocones_equiv._proof_1 F G c))
    (cocones_equiv._proof_2 F G) :=
  Eq.refl (equivalence.unit_iso (cocones_equiv F G))

/--
If `F` is cofinal,
the category of cones on `F.op ⋙ H` is equivalent to the category of cones on `H`,
for any `H : Dᵒᵖ ⥤ E`.
-/
@[simp] theorem cones_equiv_counit_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] (H : Dᵒᵖ ⥤ E) : equivalence.counit_iso (cones_equiv F H) =
  nat_iso.of_components
    (fun (c : limits.cone H) =>
      limits.cones.ext (iso.refl (limits.cone.X (functor.obj (limits.cones.whiskering (functor.op F) ⋙ extend_cone) c)))
        (cones_equiv._proof_3 F H c))
    (cones_equiv._proof_4 F H) :=
  Eq.refl (equivalence.counit_iso (cones_equiv F H))

-- We could have done this purely formally in terms of `cocones_equiv`,

-- without having defined `extend_cone` at all,

-- but it comes at the cost of moving a *lot* of opposites around:

-- (((cones.functoriality_equivalence _ (op_op_equivalence E)).symm.trans

--   ((((cocone_equivalence_op_cone_op _).symm.trans

--     (cocones_equiv F (unop_unop _ ⋙ H.op))).trans

--     (cocone_equivalence_op_cone_op _)).unop)).trans

--   (cones.functoriality_equivalence _ (op_op_equivalence E))).trans

--   (cones.postcompose_equivalence (nat_iso.of_components (λ X, iso.refl _) (by tidy) :

--     H ≅ (unop_unop D ⋙ H.op).op ⋙ (op_op_equivalence E).functor)).symm

/--
When `F : C ⥤ D` is cofinal, and `t : cocone G` for some `G : D ⥤ E`,
`t.whisker F` is a colimit cocone exactly when `t` is.
-/
def is_colimit_whisker_equiv {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} (t : limits.cocone G) : limits.is_colimit (limits.cocone.whisker F t) ≃ limits.is_colimit t :=
  limits.is_colimit.of_cocone_equiv (equivalence.symm (cocones_equiv F G))

/--
When `F : C ⥤ D` is cofinal, and `t : cone H` for some `H : Dᵒᵖ ⥤ E`,
`t.whisker F.op` is a limit cone exactly when `t` is.
-/
def is_limit_whisker_equiv {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (t : limits.cone H) : limits.is_limit (limits.cone.whisker (functor.op F) t) ≃ limits.is_limit t :=
  limits.is_limit.of_cone_equiv (equivalence.symm (cones_equiv F H))

/--
When `F` is cofinal, and `t : cocone (F ⋙ G)`,
`extend_cocone.obj t` is a colimit coconne exactly when `t` is.
-/
def is_colimit_extend_cocone_equiv {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} (t : limits.cocone (F ⋙ G)) : limits.is_colimit (functor.obj extend_cocone t) ≃ limits.is_colimit t :=
  limits.is_colimit.of_cocone_equiv (cocones_equiv F G)

/--
When `F` is cofinal, and `t : cone (F.op ⋙ H)`,
`extend_cone.obj t` is a limit conne exactly when `t` is.
-/
def is_limit_extend_cone_equiv {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (t : limits.cone (functor.op F ⋙ H)) : limits.is_limit (functor.obj extend_cone t) ≃ limits.is_limit t :=
  limits.is_limit.of_cone_equiv (cones_equiv F H)

/-- Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `F ⋙ G`. -/
@[simp] theorem colimit_cocone_comp_cocone {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} (t : limits.colimit_cocone G) : limits.colimit_cocone.cocone (colimit_cocone_comp F t) = limits.cocone.whisker F (limits.colimit_cocone.cocone t) :=
  Eq.refl (limits.colimit_cocone.cocone (colimit_cocone_comp F t))

/-- Given a limit cone over `H : Dᵒᵖ ⥤ E` we can construct a limit cone over `F.op ⋙ H`. -/
@[simp] theorem limit_cone_comp_cone {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (t : limits.limit_cone H) : limits.limit_cone.cone (limit_cone_comp F t) = limits.cone.whisker (functor.op F) (limits.limit_cone.cone t) :=
  Eq.refl (limits.limit_cone.cone (limit_cone_comp F t))

protected instance comp_has_colimit {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} [limits.has_colimit G] : limits.has_colimit (F ⋙ G) :=
  limits.has_colimit.mk (colimit_cocone_comp F (limits.get_colimit_cocone G))

protected instance comp_has_limit {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} [limits.has_limit H] : limits.has_limit (functor.op F ⋙ H) :=
  limits.has_limit.mk (limit_cone_comp F (limits.get_limit_cone H))

theorem colimit_pre_is_iso_aux {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} {t : limits.cocone G} (P : limits.is_colimit t) : limits.is_colimit.desc (coe_fn (equiv.symm (is_colimit_whisker_equiv F t)) P) (limits.cocone.whisker F t) = 𝟙 := sorry

protected instance colimit_pre_is_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} [limits.has_colimit G] : is_iso (limits.colimit.pre G F) :=
  eq.mpr sorry (eq.mpr sorry (id is_iso.comp_is_iso))

theorem limit_pre_is_iso_aux {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} {t : limits.cone H} (P : limits.is_limit t) : limits.is_limit.lift (coe_fn (equiv.symm (is_limit_whisker_equiv F t)) P) (limits.cone.whisker (functor.op F) t) = 𝟙 := sorry

protected instance limit_pre_is_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} [limits.has_limit H] : is_iso (limits.limit.pre H (functor.op F)) :=
  eq.mpr sorry (eq.mpr sorry (id is_iso.comp_is_iso))

/--
When `F : C ⥤ D` is cofinal, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] (G : D ⥤ E) [limits.has_colimit G] : limits.colimit (F ⋙ G) ≅ limits.colimit G :=
  as_iso (limits.colimit.pre G F)

/--
When `F : C ⥤ D` is cofinal, and `H : Dᵒᵖ ⥤ E` has a limit, then `F.op ⋙ H` has a limit also and
`limit (F.op ⋙ H) ≅ limit H`

https://stacks.math.columbia.edu/tag/04E7
-/
def limit_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] (H : Dᵒᵖ ⥤ E) [limits.has_limit H] : limits.limit (functor.op F ⋙ H) ≅ limits.limit H :=
  iso.symm (as_iso (limits.limit.pre H (functor.op F)))

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simp] theorem colimit_cocone_of_comp_is_colimit {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} (t : limits.colimit_cocone (F ⋙ G)) : limits.colimit_cocone.is_colimit (colimit_cocone_of_comp F t) =
  coe_fn (equiv.symm (is_colimit_extend_cocone_equiv F (limits.colimit_cocone.cocone t)))
    (limits.colimit_cocone.is_colimit t) :=
  Eq.refl (limits.colimit_cocone.is_colimit (colimit_cocone_of_comp F t))

/-- Given a limit cone over `F.op ⋙ H` we can construct a limit cone over `H`. -/
@[simp] theorem limit_cone_of_comp_is_limit {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} (t : limits.limit_cone (functor.op F ⋙ H)) : limits.limit_cone.is_limit (limit_cone_of_comp F t) =
  coe_fn (equiv.symm (is_limit_extend_cone_equiv F (limits.limit_cone.cone t))) (limits.limit_cone.is_limit t) :=
  Eq.refl (limits.limit_cone.is_limit (limit_cone_of_comp F t))

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_has_colimit`.)
-/
theorem has_colimit_of_comp {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} [limits.has_colimit (F ⋙ G)] : limits.has_colimit G :=
  limits.has_colimit.mk (colimit_cocone_of_comp F (limits.get_colimit_cocone (F ⋙ G)))

/--
When `F` is cofinal, and `F.op ⋙ H` has a limit, then `H` has a limit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_has_limit`.)
-/
theorem has_limit_of_comp {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} [limits.has_limit (functor.op F ⋙ H)] : limits.has_limit H :=
  limits.has_limit.mk (limit_cone_of_comp F (limits.get_limit_cone (functor.op F ⋙ H)))

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso' {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {G : D ⥤ E} [limits.has_colimit (F ⋙ G)] : limits.colimit (F ⋙ G) ≅ limits.colimit G :=
  as_iso (limits.colimit.pre G F)

/--
When `F` is cofinal, and `F.op ⋙ H` has a limit, then `H` has a limit also and
`limit (F.op ⋙ H) ≅ limit H`

https://stacks.math.columbia.edu/tag/04E7
-/
def limit_iso' {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] {E : Type u} [category E] {H : Dᵒᵖ ⥤ E} [limits.has_limit (functor.op F ⋙ H)] : limits.limit (functor.op F ⋙ H) ≅ limits.limit H :=
  iso.symm (as_iso (limits.limit.pre H (functor.op F)))

/--
If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda.obj (op d))`
is an isomorphism (as it always is when `F` is cofinal),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit`
(simply because `colimit (coyoneda.obj (op d)) ≅ punit`).
-/
def colimit_comp_coyoneda_iso {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] (d : D) [is_iso (limits.colimit.pre (functor.obj coyoneda (opposite.op d)) F)] : limits.colimit (F ⋙ functor.obj coyoneda (opposite.op d)) ≅ PUnit :=
  as_iso (limits.colimit.pre (functor.obj coyoneda (opposite.op d)) F) ≪≫ coyoneda.colimit_coyoneda_iso (opposite.op d)

theorem zigzag_of_eqv_gen_quot_rel {C : Type v} [small_category C] {D : Type v} [small_category D] {F : C ⥤ D} {d : D} {f₁ : sigma fun (X : C) => d ⟶ functor.obj F X} {f₂ : sigma fun (X : C) => d ⟶ functor.obj F X} (t : eqv_gen (limits.types.quot.rel (F ⋙ functor.obj coyoneda (opposite.op d))) f₁ f₂) : zigzag (comma.mk (sigma.snd f₁)) (comma.mk (sigma.snd f₂)) := sorry

/--
If `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit` for all `d : D`, then `F` is cofinal.
-/
theorem cofinal_of_colimit_comp_coyoneda_iso_punit {C : Type v} [small_category C] {D : Type v} [small_category D] (F : C ⥤ D) [cofinal F] (I : (d : D) → limits.colimit (F ⋙ functor.obj coyoneda (opposite.op d)) ≅ PUnit) : cofinal F := sorry

