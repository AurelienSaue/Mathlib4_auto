/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Scott Morrison, Floris van Doorn
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.category_theory.adjunction.basic
import Mathlib.category_theory.limits.cones
import Mathlib.category_theory.reflects_isomorphisms
import PostPort

universes v u l u' u'' 

namespace Mathlib

/-!
# Limits and colimits

We set up the general theory of limits and colimits in a category.
In this introduction we only describe the setup for limits;
it is repeated, with slightly different names, for colimits.

The three main structures involved are
* `is_limit c`, for `c : cone F`, `F : J ⥤ C`, expressing that `c` is a limit cone,
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

`has_limit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).


Typically there are two different ways one can use the limits library:
1. working with particular cones, and terms of type `is_limit`
2. working solely with `has_limit`.

While `has_limit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `has_limit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.X ⟶ limit F`, the universal morphism from any other `c : cone F`, etc.

Key to using the `has_limit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `has_limits_of_shape J C` and `has_limits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `is_limit`,
and then a result in terms of `has_limit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `has_limit`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

namespace category_theory.limits


/--
A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`.

See https://stacks.math.columbia.edu/tag/002E.
  -/
structure is_limit {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (t : cone F) 
where
  lift : (s : cone F) → cone.X s ⟶ cone.X t
  fac' : autoParam (∀ (s : cone F) (j : J), lift s ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  uniq' : autoParam
  (∀ (s : cone F) (m : cone.X s ⟶ cone.X t),
    (∀ (j : J), m ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j) → m = lift s)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem is_limit.fac {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (c : is_limit t) (s : cone F) (j : J) : is_limit.lift c s ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j := sorry

@[simp] theorem is_limit.fac_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (c : is_limit t) (s : cone F) (j : J) {X' : C} (f' : functor.obj F j ⟶ X') : is_limit.lift c s ≫ nat_trans.app (cone.π t) j ≫ f' = nat_trans.app (cone.π s) j ≫ f' := sorry

theorem is_limit.uniq {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (c : is_limit t) (s : cone F) (m : cone.X s ⟶ cone.X t) (w : ∀ (j : J), m ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j) : m = is_limit.lift c s := sorry

namespace is_limit


protected instance subsingleton {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} : subsingleton (is_limit t) := sorry

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cone point
of any cone over `F` to the cone point of a limit cone over `G`. -/
def map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (s : cone F) {t : cone G} (P : is_limit t) (α : F ⟶ G) : cone.X s ⟶ cone.X t :=
  lift P (functor.obj (cones.postcompose α) s)

@[simp] theorem map_π_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (c : cone F) {d : cone G} (hd : is_limit d) (α : F ⟶ G) (j : J) {X' : C} (f' : functor.obj G j ⟶ X') : map c hd α ≫ nat_trans.app (cone.π d) j ≫ f' = nat_trans.app (cone.π c) j ≫ nat_trans.app α j ≫ f' := sorry

theorem lift_self {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {c : cone F} (t : is_limit c) : lift t c = 𝟙 :=
  Eq.symm (uniq t c 𝟙 fun (j : J) => category.id_comp (nat_trans.app (cone.π c) j))

/- Repackaging the definition in terms of cone morphisms. -/

/-- The universal morphism from any other cone to a limit cone. -/
@[simp] theorem lift_cone_morphism_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) (s : cone F) : cone_morphism.hom (lift_cone_morphism h s) = lift h s :=
  Eq.refl (cone_morphism.hom (lift_cone_morphism h s))

theorem uniq_cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {t : cone F} (h : is_limit t) {f : s ⟶ t} {f' : s ⟶ t} : f = f' :=
  (fun (this : ∀ {g : s ⟶ t}, g = lift_cone_morphism h s) => Eq.trans this (Eq.symm this))
    fun (g : s ⟶ t) => cone_morphism.ext g (lift_cone_morphism h s) (uniq h s (cone_morphism.hom g) (cone_morphism.w g))

/--
Alternative constructor for `is_limit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
def mk_cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (lift : (s : cone F) → s ⟶ t) (uniq' : ∀ (s : cone F) (m : s ⟶ t), m = lift s) : is_limit t :=
  mk fun (s : cone F) => cone_morphism.hom (lift s)

/-- Limit cones on `F` are unique up to isomorphism. -/
def unique_up_to_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) : s ≅ t :=
  iso.mk (lift_cone_morphism Q s) (lift_cone_morphism P t)

/-- Any cone morphism between limit cones is an isomorphism. -/
def hom_is_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) (f : s ⟶ t) : is_iso f :=
  is_iso.mk (lift_cone_morphism P t)

/-- Limits of `F` are unique up to isomorphism. -/
def cone_point_unique_up_to_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) : cone.X s ≅ cone.X t :=
  functor.map_iso (cones.forget F) (unique_up_to_iso P Q)

@[simp] theorem cone_point_unique_up_to_iso_hom_comp {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) (j : J) : iso.hom (cone_point_unique_up_to_iso P Q) ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j :=
  cone_morphism.w (iso.hom (unique_up_to_iso P Q)) j

@[simp] theorem cone_point_unique_up_to_iso_inv_comp_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) (j : J) {X' : C} (f' : functor.obj F j ⟶ X') : iso.inv (cone_point_unique_up_to_iso P Q) ≫ nat_trans.app (cone.π s) j ≫ f' = nat_trans.app (cone.π t) j ≫ f' := sorry

@[simp] theorem lift_comp_cone_point_unique_up_to_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) : lift P r ≫ iso.hom (cone_point_unique_up_to_iso P Q) = lift Q r := sorry

@[simp] theorem lift_comp_cone_point_unique_up_to_iso_inv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {s : cone F} {t : cone F} (P : is_limit s) (Q : is_limit t) : lift Q r ≫ iso.inv (cone_point_unique_up_to_iso P Q) = lift P r := sorry

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def of_iso_limit {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {t : cone F} (P : is_limit r) (i : r ≅ t) : is_limit t :=
  mk_cone_morphism (fun (s : cone F) => lift_cone_morphism P s ≫ iso.hom i) sorry

@[simp] theorem of_iso_limit_lift {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {t : cone F} (P : is_limit r) (i : r ≅ t) (s : cone F) : lift (of_iso_limit P i) s = lift P s ≫ cone_morphism.hom (iso.hom i) :=
  rfl

/-- Isomorphism of cones preserves whether or not they are limiting cones. -/
def equiv_iso_limit {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {t : cone F} (i : r ≅ t) : is_limit r ≃ is_limit t :=
  equiv.mk (fun (h : is_limit r) => of_iso_limit h i) (fun (h : is_limit t) => of_iso_limit h (iso.symm i)) sorry sorry

@[simp] theorem equiv_iso_limit_apply {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {t : cone F} (i : r ≅ t) (P : is_limit r) : coe_fn (equiv_iso_limit i) P = of_iso_limit P i :=
  rfl

@[simp] theorem equiv_iso_limit_symm_apply {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {t : cone F} (i : r ≅ t) (P : is_limit t) : coe_fn (equiv.symm (equiv_iso_limit i)) P = of_iso_limit P (iso.symm i) :=
  rfl

/--
If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
def of_point_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cone F} {t : cone F} (P : is_limit r) [i : is_iso (lift P t)] : is_limit t :=
  of_iso_limit P (iso.symm (as_iso (lift_cone_morphism P t)))

theorem hom_lift {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) {W : C} (m : W ⟶ cone.X t) : m = lift h (cone.mk W (nat_trans.mk fun (b : J) => m ≫ nat_trans.app (cone.π t) b)) :=
  uniq h (cone.mk W (nat_trans.mk fun (b : J) => m ≫ nat_trans.app (cone.π t) b)) m fun (b : J) => rfl

/-- Two morphisms into a limit are equal if their compositions with
  each cone morphism are equal. -/
theorem hom_ext {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) {W : C} {f : W ⟶ cone.X t} {f' : W ⟶ cone.X t} (w : ∀ (j : J), f ≫ nat_trans.app (cone.π t) j = f' ≫ nat_trans.app (cone.π t) j) : f = f' := sorry

/--
Given a right adjoint functor between categories of cones,
the image of a limit cone is a limit cone.
-/
def of_right_adjoint {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cone G ⥤ cone F) [is_right_adjoint h] {c : cone G} (t : is_limit c) : is_limit (functor.obj h c) :=
  mk_cone_morphism
    (fun (s : cone F) =>
      coe_fn (adjunction.hom_equiv (adjunction.of_right_adjoint h) s c)
        (lift_cone_morphism t (functor.obj (left_adjoint h) s)))
    sorry

/--
Given two functors which have equivalent categories of cones, we can transport a limiting cone across
the equivalence.
-/
def of_cone_equiv {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cone G ≌ cone F) {c : cone G} : is_limit (functor.obj (equivalence.functor h) c) ≃ is_limit c :=
  equiv.mk
    (fun (P : is_limit (functor.obj (equivalence.functor h) c)) =>
      of_iso_limit (of_right_adjoint (equivalence.inverse h) P) (iso.app (iso.symm (equivalence.unit_iso h)) c))
    (of_right_adjoint (equivalence.functor h)) sorry sorry

@[simp] theorem of_cone_equiv_apply_desc {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cone G ≌ cone F) {c : cone G} (P : is_limit (functor.obj (equivalence.functor h) c)) (s : cone G) : lift (coe_fn (of_cone_equiv h) P) s =
  (cone_morphism.hom (nat_trans.app (iso.hom (equivalence.unit_iso h)) s) ≫
      cone_morphism.hom
        (functor.map (functor.inv (equivalence.functor h))
          (lift_cone_morphism P (functor.obj (equivalence.functor h) s)))) ≫
    cone_morphism.hom (nat_trans.app (iso.inv (equivalence.unit_iso h)) c) :=
  rfl

@[simp] theorem of_cone_equiv_symm_apply_desc {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cone G ≌ cone F) {c : cone G} (P : is_limit c) (s : cone F) : lift (coe_fn (equiv.symm (of_cone_equiv h)) P) s =
  cone_morphism.hom (nat_trans.app (iso.inv (equivalence.counit_iso h)) s) ≫
    cone_morphism.hom
      (functor.map (equivalence.functor h) (lift_cone_morphism P (functor.obj (equivalence.inverse h) s))) :=
  rfl

/--
A cone postcomposed with a natural isomorphism is a limit cone if and only if the original cone is.
-/
def postcompose_hom_equiv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ≅ G) (c : cone F) : is_limit (functor.obj (cones.postcompose (iso.hom α)) c) ≃ is_limit c :=
  of_cone_equiv (cones.postcompose_equivalence α)

/--
A cone postcomposed with the inverse of a natural isomorphism is a limit cone if and only if
the original cone is.
-/
def postcompose_inv_equiv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ≅ G) (c : cone G) : is_limit (functor.obj (cones.postcompose (iso.inv α)) c) ≃ is_limit c :=
  postcompose_hom_equiv (iso.symm α) c

/--
The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simp] theorem cone_points_iso_of_nat_iso_inv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t) (w : F ≅ G) : iso.inv (cone_points_iso_of_nat_iso P Q w) = map t P (iso.inv w) :=
  Eq.refl (iso.inv (cone_points_iso_of_nat_iso P Q w))

theorem cone_points_iso_of_nat_iso_hom_comp_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t) (w : F ≅ G) (j : J) {X' : C} (f' : functor.obj G j ⟶ X') : iso.hom (cone_points_iso_of_nat_iso P Q w) ≫ nat_trans.app (cone.π t) j ≫ f' =
  nat_trans.app (cone.π s) j ≫ nat_trans.app (iso.hom w) j ≫ f' := sorry

theorem cone_points_iso_of_nat_iso_inv_comp_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t) (w : F ≅ G) (j : J) {X' : C} (f' : functor.obj F j ⟶ X') : iso.inv (cone_points_iso_of_nat_iso P Q w) ≫ nat_trans.app (cone.π s) j ≫ f' =
  nat_trans.app (cone.π t) j ≫ nat_trans.app (iso.inv w) j ≫ f' := sorry

theorem lift_comp_cone_points_iso_of_nat_iso_hom_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {r : cone F} {s : cone F} {t : cone G} (P : is_limit s) (Q : is_limit t) (w : F ≅ G) {X' : C} (f' : cone.X t ⟶ X') : lift P r ≫ iso.hom (cone_points_iso_of_nat_iso P Q w) ≫ f' = map r Q (iso.hom w) ≫ f' := sorry

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} (P : is_limit s) (e : K ≌ J) : is_limit (cone.whisker (equivalence.functor e) s) :=
  of_right_adjoint (equivalence.functor (cones.whiskering_equivalence e)) P

/--
We can prove two cone points `(s : cone F).X` and `(t.cone F).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simp] theorem cone_points_iso_of_equivalence_hom {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {s : cone F} {G : K ⥤ C} {t : cone G} (P : is_limit s) (Q : is_limit t) (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) : iso.hom (cone_points_iso_of_equivalence P Q e w) =
  lift Q
    (functor.obj
      (equivalence.functor
        (cones.equivalence_of_reindexing (equivalence.symm e)
          (iso.symm (iso_whisker_left (equivalence.inverse e) w) ≪≫ equivalence.inv_fun_id_assoc e G)))
      s) :=
  Eq.refl (iso.hom (cone_points_iso_of_equivalence P Q e w))

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
  a cone on `F` with vertex `W`. -/
def hom_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) (W : C) : (W ⟶ cone.X t) ≅ functor.obj (functor.const J) W ⟶ F :=
  iso.mk (fun (f : W ⟶ cone.X t) => cone.π (cone.extend t f))
    fun (π : functor.obj (functor.const J) W ⟶ F) => lift h (cone.mk W π)

@[simp] theorem hom_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) {W : C} (f : W ⟶ cone.X t) : iso.hom (hom_iso h W) f = cone.π (cone.extend t f) :=
  rfl

/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with vertex `W`. -/
def nat_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) : functor.obj yoneda (cone.X t) ≅ functor.cones F :=
  nat_iso.of_components (fun (W : Cᵒᵖ) => hom_iso h (opposite.unop W)) sorry

/--
Another, more explicit, formulation of the universal property of a limit cone.
See also `hom_iso`.
-/
def hom_iso' {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (h : is_limit t) (W : C) : (W ⟶ cone.X t) ≅
  Subtype fun (p : (j : J) → W ⟶ functor.obj F j) => ∀ {j j' : J} (f : j ⟶ j'), p j ≫ functor.map F f = p j' :=
  hom_iso h W ≪≫
    iso.mk
      (fun (π : functor.obj (functor.const J) W ⟶ F) => { val := fun (j : J) => nat_trans.app π j, property := sorry })
      fun
        (p :
        Subtype fun (p : (j : J) → W ⟶ functor.obj F j) => ∀ {j j' : J} (f : j ⟶ j'), p j ≫ functor.map F f = p j') =>
        nat_trans.mk fun (j : J) => subtype.val p j

/-- If G : C → D is a faithful functor which sends t to a limit cone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} {D : Type u'} [category D] (G : C ⥤ D) [faithful G] (ht : is_limit (functor.map_cone G t)) (lift : (s : cone F) → cone.X s ⟶ cone.X t) (h : ∀ (s : cone F), functor.map G (lift s) = lift ht (functor.map_cone G s)) : is_limit t :=
  mk lift

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a limit implies
`G.map_cone c` is also a limit.
-/
def map_cone_equiv {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {K : J ⥤ C} {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) {c : cone K} (t : is_limit (functor.map_cone F c)) : is_limit (functor.map_cone G c) :=
  coe_fn (postcompose_inv_equiv (iso_whisker_left K h) (functor.map_cone G c))
    (of_iso_limit t (iso.symm (functor.postcompose_whisker_left_map_cone (iso.symm h) c)))

/--
A cone is a limit cone exactly if
there is a unique cone morphism from any other cone.
-/
def iso_unique_cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} : is_limit t ≅ (s : cone F) → unique (s ⟶ t) :=
  iso.mk (fun (h : is_limit t) (s : cone F) => unique.mk { default := lift_cone_morphism h s } sorry)
    fun (h : (s : cone F) → unique (s ⟶ t)) => mk fun (s : cone F) => cone_morphism.hom Inhabited.default

namespace of_nat_iso


/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point `Y`. -/
def cone_of_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) {Y : C} (f : Y ⟶ X) : cone F :=
  cone.mk Y (nat_trans.app (iso.hom h) (opposite.op Y) f)

/-- If `F.cones` is represented by `X`, each cone `s` gives a morphism `s.X ⟶ X`. -/
def hom_of_cone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) (s : cone F) : cone.X s ⟶ X :=
  nat_trans.app (iso.inv h) (opposite.op (cone.X s)) (cone.π s)

@[simp] theorem cone_of_hom_of_cone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) (s : cone F) : cone_of_hom h (hom_of_cone h s) = s := sorry

@[simp] theorem hom_of_cone_of_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) {Y : C} (f : Y ⟶ X) : hom_of_cone h (cone_of_hom h f) = f :=
  congr_fun (congr_fun (congr_arg nat_trans.app (iso.hom_inv_id h)) (opposite.op Y)) f

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
def limit_cone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) : cone F :=
  cone_of_hom h 𝟙

/-- If `F.cones` is represented by `X`, the cone corresponding to a morphism `f : Y ⟶ X` is
the limit cone extended by `f`. -/
theorem cone_of_hom_fac {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) {Y : C} (f : Y ⟶ X) : cone_of_hom h f = cone.extend (limit_cone h) f := sorry

/-- If `F.cones` is represented by `X`, any cone is the extension of the limit cone by the
corresponding morphism. -/
theorem cone_fac {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) (s : cone F) : cone.extend (limit_cone h) (hom_of_cone h s) = s := sorry

end of_nat_iso


/--
If `F.cones` is representable, then the cone corresponding to the identity morphism on
the representing object is a limit cone.
-/
def of_nat_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj yoneda X ≅ functor.cones F) : is_limit (of_nat_iso.limit_cone h) :=
  mk fun (s : cone F) => sorry

end is_limit


/--
A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`.

See https://stacks.math.columbia.edu/tag/002F.
-/
structure is_colimit {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (t : cocone F) 
where
  desc : (s : cocone F) → cocone.X t ⟶ cocone.X s
  fac' : autoParam (∀ (s : cocone F) (j : J), nat_trans.app (cocone.ι t) j ≫ desc s = nat_trans.app (cocone.ι s) j)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  uniq' : autoParam
  (∀ (s : cocone F) (m : cocone.X t ⟶ cocone.X s),
    (∀ (j : J), nat_trans.app (cocone.ι t) j ≫ m = nat_trans.app (cocone.ι s) j) → m = desc s)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

@[simp] theorem is_colimit.fac {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (c : is_colimit t) (s : cocone F) (j : J) : nat_trans.app (cocone.ι t) j ≫ is_colimit.desc c s = nat_trans.app (cocone.ι s) j := sorry

@[simp] theorem is_colimit.fac_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (c : is_colimit t) (s : cocone F) (j : J) {X' : C} (f' : cocone.X s ⟶ X') : nat_trans.app (cocone.ι t) j ≫ is_colimit.desc c s ≫ f' = nat_trans.app (cocone.ι s) j ≫ f' := sorry

theorem is_colimit.uniq {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (c : is_colimit t) (s : cocone F) (m : cocone.X t ⟶ cocone.X s) (w : ∀ (j : J), nat_trans.app (cocone.ι t) j ≫ m = nat_trans.app (cocone.ι s) j) : m = is_colimit.desc c s := sorry

namespace is_colimit


protected instance subsingleton {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} : subsingleton (is_colimit t) := sorry

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cocone point
of a colimit cocone over `F` to the cocone point of any cocone over `G`. -/
def map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cocone F} (P : is_colimit s) (t : cocone G) (α : F ⟶ G) : cocone.X s ⟶ cocone.X t :=
  desc P (functor.obj (cocones.precompose α) t)

@[simp] theorem ι_map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {c : cocone F} (hc : is_colimit c) (d : cocone G) (α : F ⟶ G) (j : J) : nat_trans.app (cocone.ι c) j ≫ map hc d α = nat_trans.app α j ≫ nat_trans.app (cocone.ι d) j :=
  fac hc (functor.obj (cocones.precompose α) d) j

@[simp] theorem desc_self {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) : desc h t = 𝟙 :=
  Eq.symm (uniq h t 𝟙 fun (j : J) => category.comp_id (nat_trans.app (cocone.ι t) j))

/- Repackaging the definition in terms of cocone morphisms. -/

/-- The universal morphism from a colimit cocone to any other cocone. -/
def desc_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) (s : cocone F) : t ⟶ s :=
  cocone_morphism.mk (desc h s)

theorem uniq_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {t : cocone F} (h : is_colimit t) {f : t ⟶ s} {f' : t ⟶ s} : f = f' :=
  (fun (this : ∀ {g : t ⟶ s}, g = desc_cocone_morphism h s) => Eq.trans this (Eq.symm this))
    fun (g : t ⟶ s) =>
      cocone_morphism.ext g (desc_cocone_morphism h s) (uniq h s (cocone_morphism.hom g) (cocone_morphism.w g))

/--
Alternative constructor for `is_colimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/
def mk_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (desc : (s : cocone F) → t ⟶ s) (uniq' : ∀ (s : cocone F) (m : t ⟶ s), m = desc s) : is_colimit t :=
  mk fun (s : cocone F) => cocone_morphism.hom (desc s)

/-- Colimit cocones on `F` are unique up to isomorphism. -/
@[simp] theorem unique_up_to_iso_inv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) : iso.inv (unique_up_to_iso P Q) = desc_cocone_morphism Q s :=
  Eq.refl (iso.inv (unique_up_to_iso P Q))

/-- Any cocone morphism between colimit cocones is an isomorphism. -/
def hom_is_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) (f : s ⟶ t) : is_iso f :=
  is_iso.mk (desc_cocone_morphism Q s)

/-- Colimits of `F` are unique up to isomorphism. -/
def cocone_point_unique_up_to_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) : cocone.X s ≅ cocone.X t :=
  functor.map_iso (cocones.forget F) (unique_up_to_iso P Q)

@[simp] theorem comp_cocone_point_unique_up_to_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) (j : J) : nat_trans.app (cocone.ι s) j ≫ iso.hom (cocone_point_unique_up_to_iso P Q) = nat_trans.app (cocone.ι t) j :=
  cocone_morphism.w (iso.hom (unique_up_to_iso P Q)) j

@[simp] theorem comp_cocone_point_unique_up_to_iso_inv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) (j : J) : nat_trans.app (cocone.ι t) j ≫ iso.inv (cocone_point_unique_up_to_iso P Q) = nat_trans.app (cocone.ι s) j :=
  cocone_morphism.w (iso.inv (unique_up_to_iso P Q)) j

@[simp] theorem cocone_point_unique_up_to_iso_hom_desc_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) {X' : C} (f' : cocone.X r ⟶ X') : iso.hom (cocone_point_unique_up_to_iso P Q) ≫ desc Q r ≫ f' = desc P r ≫ f' := sorry

@[simp] theorem cocone_point_unique_up_to_iso_inv_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {s : cocone F} {t : cocone F} (P : is_colimit s) (Q : is_colimit t) : iso.inv (cocone_point_unique_up_to_iso P Q) ≫ desc P r = desc Q r := sorry

/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/
def of_iso_colimit {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {t : cocone F} (P : is_colimit r) (i : r ≅ t) : is_colimit t :=
  mk_cocone_morphism (fun (s : cocone F) => iso.inv i ≫ desc_cocone_morphism P s) sorry

@[simp] theorem of_iso_colimit_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {t : cocone F} (P : is_colimit r) (i : r ≅ t) (s : cocone F) : desc (of_iso_colimit P i) s = cocone_morphism.hom (iso.inv i) ≫ desc P s :=
  rfl

/-- Isomorphism of cocones preserves whether or not they are colimiting cocones. -/
def equiv_iso_colimit {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {t : cocone F} (i : r ≅ t) : is_colimit r ≃ is_colimit t :=
  equiv.mk (fun (h : is_colimit r) => of_iso_colimit h i) (fun (h : is_colimit t) => of_iso_colimit h (iso.symm i)) sorry
    sorry

@[simp] theorem equiv_iso_colimit_apply {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {t : cocone F} (i : r ≅ t) (P : is_colimit r) : coe_fn (equiv_iso_colimit i) P = of_iso_colimit P i :=
  rfl

@[simp] theorem equiv_iso_colimit_symm_apply {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {t : cocone F} (i : r ≅ t) (P : is_colimit t) : coe_fn (equiv.symm (equiv_iso_colimit i)) P = of_iso_colimit P (iso.symm i) :=
  rfl

/--
If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/
def of_point_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {r : cocone F} {t : cocone F} (P : is_colimit r) [i : is_iso (desc P t)] : is_colimit t :=
  of_iso_colimit P (as_iso (desc_cocone_morphism P t))

theorem hom_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) {W : C} (m : cocone.X t ⟶ W) : m = desc h (cocone.mk W (nat_trans.mk fun (b : J) => nat_trans.app (cocone.ι t) b ≫ m)) :=
  uniq h (cocone.mk W (nat_trans.mk fun (b : J) => nat_trans.app (cocone.ι t) b ≫ m)) m fun (b : J) => rfl

/-- Two morphisms out of a colimit are equal if their compositions with
  each cocone morphism are equal. -/
theorem hom_ext {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) {W : C} {f : cocone.X t ⟶ W} {f' : cocone.X t ⟶ W} (w : ∀ (j : J), nat_trans.app (cocone.ι t) j ≫ f = nat_trans.app (cocone.ι t) j ≫ f') : f = f' := sorry

/--
Given a left adjoint functor between categories of cocones,
the image of a colimit cocone is a colimit cocone.
-/
def of_left_adjoint {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cocone G ⥤ cocone F) [is_left_adjoint h] {c : cocone G} (t : is_colimit c) : is_colimit (functor.obj h c) :=
  mk_cocone_morphism
    (fun (s : cocone F) =>
      coe_fn (equiv.symm (adjunction.hom_equiv (adjunction.of_left_adjoint h) c s))
        (desc_cocone_morphism t (functor.obj (right_adjoint h) s)))
    sorry

/--
Given two functors which have equivalent categories of cocones,
we can transport a colimiting cocone across the equivalence.
-/
def of_cocone_equiv {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cocone G ≌ cocone F) {c : cocone G} : is_colimit (functor.obj (equivalence.functor h) c) ≃ is_colimit c :=
  equiv.mk
    (fun (P : is_colimit (functor.obj (equivalence.functor h) c)) =>
      of_iso_colimit (of_left_adjoint (equivalence.inverse h) P) (iso.app (iso.symm (equivalence.unit_iso h)) c))
    (of_left_adjoint (equivalence.functor h)) sorry sorry

@[simp] theorem of_cocone_equiv_apply_desc {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cocone G ≌ cocone F) {c : cocone G} (P : is_colimit (functor.obj (equivalence.functor h) c)) (s : cocone G) : desc (coe_fn (of_cocone_equiv h) P) s =
  cocone_morphism.hom (nat_trans.app (equivalence.unit h) c) ≫
    cocone_morphism.hom
        (functor.map (equivalence.inverse h) (desc_cocone_morphism P (functor.obj (equivalence.functor h) s))) ≫
      cocone_morphism.hom (nat_trans.app (equivalence.unit_inv h) s) :=
  rfl

@[simp] theorem of_cocone_equiv_symm_apply_desc {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {D : Type u'} [category D] {G : K ⥤ D} (h : cocone G ≌ cocone F) {c : cocone G} (P : is_colimit c) (s : cocone F) : desc (coe_fn (equiv.symm (of_cocone_equiv h)) P) s =
  cocone_morphism.hom
      (functor.map (equivalence.functor h) (desc_cocone_morphism P (functor.obj (equivalence.inverse h) s))) ≫
    cocone_morphism.hom (nat_trans.app (equivalence.counit h) s) :=
  rfl

/--
A cocone precomposed with a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precompose_hom_equiv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ≅ G) (c : cocone G) : is_colimit (functor.obj (cocones.precompose (iso.hom α)) c) ≃ is_colimit c :=
  of_cocone_equiv (cocones.precompose_equivalence α)

/--
A cocone precomposed with the inverse of a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precompose_inv_equiv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} (α : F ≅ G) (c : cocone F) : is_colimit (functor.obj (cocones.precompose (iso.inv α)) c) ≃ is_colimit c :=
  precompose_hom_equiv (iso.symm α) c

/--
The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simp] theorem cocone_points_iso_of_nat_iso_inv {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cocone F} {t : cocone G} (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) : iso.inv (cocone_points_iso_of_nat_iso P Q w) = map Q s (iso.inv w) :=
  Eq.refl (iso.inv (cocone_points_iso_of_nat_iso P Q w))

theorem comp_cocone_points_iso_of_nat_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cocone F} {t : cocone G} (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) (j : J) : nat_trans.app (cocone.ι s) j ≫ iso.hom (cocone_points_iso_of_nat_iso P Q w) =
  nat_trans.app (iso.hom w) j ≫ nat_trans.app (cocone.ι t) j := sorry

theorem comp_cocone_points_iso_of_nat_iso_inv_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cocone F} {t : cocone G} (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) (j : J) {X' : C} (f' : cocone.X s ⟶ X') : nat_trans.app (cocone.ι t) j ≫ iso.inv (cocone_points_iso_of_nat_iso P Q w) ≫ f' =
  nat_trans.app (iso.inv w) j ≫ nat_trans.app (cocone.ι s) j ≫ f' := sorry

theorem cocone_points_iso_of_nat_iso_hom_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} {s : cocone F} {r : cocone G} {t : cocone G} (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) : iso.hom (cocone_points_iso_of_nat_iso P Q w) ≫ desc Q r = map P r (iso.hom w) := sorry

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} (P : is_colimit s) (e : K ≌ J) : is_colimit (cocone.whisker (equivalence.functor e) s) :=
  of_left_adjoint (equivalence.functor (cocones.whiskering_equivalence e)) P

/--
We can prove two cocone points `(s : cocone F).X` and `(t.cocone F).X` are isomorphic if
* both cocones are colimit ccoones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simp] theorem cocone_points_iso_of_equivalence_hom {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} {s : cocone F} {G : K ⥤ C} {t : cocone G} (P : is_colimit s) (Q : is_colimit t) (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) : iso.hom (cocone_points_iso_of_equivalence P Q e w) =
  desc P (functor.obj (equivalence.functor (cocones.equivalence_of_reindexing e w)) t) :=
  Eq.refl (iso.hom (cocone_points_iso_of_equivalence P Q e w))

/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
  a cocone on `F` with vertex `W`. -/
def hom_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) (W : C) : (cocone.X t ⟶ W) ≅ F ⟶ functor.obj (functor.const J) W :=
  iso.mk (fun (f : cocone.X t ⟶ W) => cocone.ι (cocone.extend t f))
    fun (ι : F ⟶ functor.obj (functor.const J) W) => desc h (cocone.mk W ι)

@[simp] theorem hom_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) {W : C} (f : cocone.X t ⟶ W) : iso.hom (hom_iso h W) f = cocone.ι (cocone.extend t f) :=
  rfl

/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with vertex `W`. -/
def nat_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) : functor.obj coyoneda (opposite.op (cocone.X t)) ≅ functor.cocones F :=
  nat_iso.of_components (hom_iso h) sorry

/--
Another, more explicit, formulation of the universal property of a colimit cocone.
See also `hom_iso`.
-/
def hom_iso' {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (h : is_colimit t) (W : C) : (cocone.X t ⟶ W) ≅
  Subtype fun (p : (j : J) → functor.obj F j ⟶ W) => ∀ {j j' : J} (f : j ⟶ j'), functor.map F f ≫ p j' = p j :=
  hom_iso h W ≪≫
    iso.mk
      (fun (ι : F ⟶ functor.obj (functor.const J) W) => { val := fun (j : J) => nat_trans.app ι j, property := sorry })
      fun
        (p :
        Subtype fun (p : (j : J) → functor.obj F j ⟶ W) => ∀ {j j' : J} (f : j ⟶ j'), functor.map F f ≫ p j' = p j) =>
        nat_trans.mk fun (j : J) => subtype.val p j

/-- If G : C → D is a faithful functor which sends t to a colimit cocone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} {D : Type u'} [category D] (G : C ⥤ D) [faithful G] (ht : is_colimit (functor.map_cocone G t)) (desc : (s : cocone F) → cocone.X t ⟶ cocone.X s) (h : ∀ (s : cocone F), functor.map G (desc s) = desc ht (functor.map_cocone G s)) : is_colimit t :=
  mk desc

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a colimit implies
`G.map_cone c` is also a colimit.
-/
def map_cocone_equiv {J : Type v} [small_category J] {C : Type u} [category C] {D : Type u'} [category D] {K : J ⥤ C} {F : C ⥤ D} {G : C ⥤ D} (h : F ≅ G) {c : cocone K} (t : is_colimit (functor.map_cocone F c)) : is_colimit (functor.map_cocone G c) :=
  of_iso_colimit (coe_fn (equiv.symm (precompose_inv_equiv (iso_whisker_left K h) (functor.map_cocone F c))) t)
    (functor.precompose_whisker_left_map_cocone h c)

/--
A cocone is a colimit cocone exactly if
there is a unique cocone morphism from any other cocone.
-/
def iso_unique_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} : is_colimit t ≅ (s : cocone F) → unique (t ⟶ s) :=
  iso.mk (fun (h : is_colimit t) (s : cocone F) => unique.mk { default := desc_cocone_morphism h s } sorry)
    fun (h : (s : cocone F) → unique (t ⟶ s)) => mk fun (s : cocone F) => cocone_morphism.hom Inhabited.default

namespace of_nat_iso


/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone point `Y`. -/
def cocone_of_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) {Y : C} (f : X ⟶ Y) : cocone F :=
  cocone.mk Y (nat_trans.app (iso.hom h) Y f)

/-- If `F.cocones` is corepresented by `X`, each cocone `s` gives a morphism `X ⟶ s.X`. -/
def hom_of_cocone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) (s : cocone F) : X ⟶ cocone.X s :=
  nat_trans.app (iso.inv h) (cocone.X s) (cocone.ι s)

@[simp] theorem cocone_of_hom_of_cocone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) (s : cocone F) : cocone_of_hom h (hom_of_cocone h s) = s := sorry

@[simp] theorem hom_of_cocone_of_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) {Y : C} (f : X ⟶ Y) : hom_of_cocone h (cocone_of_hom h f) = f :=
  congr_fun (congr_fun (congr_arg nat_trans.app (iso.hom_inv_id h)) Y) f

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
def colimit_cocone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) : cocone F :=
  cocone_of_hom h 𝟙

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to a morphism `f : Y ⟶ X` is
the colimit cocone extended by `f`. -/
theorem cocone_of_hom_fac {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) {Y : C} (f : X ⟶ Y) : cocone_of_hom h f = cocone.extend (colimit_cocone h) f := sorry

/-- If `F.cocones` is corepresented by `X`, any cocone is the extension of the colimit cocone by the
corresponding morphism. -/
theorem cocone_fac {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) (s : cocone F) : cocone.extend (colimit_cocone h) (hom_of_cocone h s) = s := sorry

end of_nat_iso


/--
If `F.cocones` is corepresentable, then the cocone corresponding to the identity morphism on
the representing object is a colimit cocone.
-/
def of_nat_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {X : C} (h : functor.obj coyoneda (opposite.op X) ≅ functor.cocones F) : is_colimit (of_nat_iso.colimit_cocone h) :=
  mk fun (s : cocone F) => sorry

end is_colimit


/-- `limit_cone F` contains a cone over `F` together with the information that it is a limit. -/
structure limit_cone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) 
where
  cone : cone F
  is_limit : is_limit cone

/-- `has_limit F` represents the mere existence of a limit for `F`. -/
class has_limit {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) 
  mk' ::
where (exists_limit : Nonempty (limit_cone F))

theorem has_limit.mk {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (d : limit_cone F) : has_limit F :=
  has_limit.mk' (Nonempty.intro d)

/-- Use the axiom of choice to extract explicit `limit_cone F` from `has_limit F`. -/
def get_limit_cone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] : limit_cone F :=
  Classical.choice has_limit.exists_limit

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class has_limits_of_shape (J : Type v) [small_category J] (C : Type u) [category C] 
where
  has_limit : ∀ (F : J ⥤ C), has_limit F

/-- `C` has all (small) limits if it has limits of every shape. -/
class has_limits (C : Type u) [category C] 
where
  has_limits_of_shape : ∀ (J : Type v) [𝒥 : small_category J], has_limits_of_shape J C

protected instance has_limit_of_has_limits_of_shape {C : Type u} [category C] {J : Type v} [small_category J] [H : has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
  has_limits_of_shape.has_limit F

protected instance has_limits_of_shape_of_has_limits {C : Type u} [category C] {J : Type v} [small_category J] [H : has_limits C] : has_limits_of_shape J C :=
  has_limits.has_limits_of_shape J

/- Interface to the `has_limit` class. -/

/-- An arbitrary choice of limit cone for a functor. -/
def limit.cone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] : cone F :=
  limit_cone.cone (get_limit_cone F)

/-- An arbitrary choice of limit object of a functor. -/
def limit {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] : C :=
  cone.X sorry

/-- The projection from the limit object to a value of the functor. -/
def limit.π {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ functor.obj F j :=
  nat_trans.app (cone.π (limit.cone F)) j

@[simp] theorem limit.cone_X {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] : cone.X (limit.cone F) = limit F :=
  rfl

@[simp] theorem limit.cone_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] : nat_trans.app (cone.π (limit.cone F)) = limit.π F :=
  rfl

@[simp] theorem limit.w {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] {j : J} {j' : J} (f : j ⟶ j') : limit.π F j ≫ functor.map F f = limit.π F j' :=
  cone.w (limit.cone F) f

/-- Evidence that the arbitrary choice of cone provied by `limit.cone F` is a limit cone. -/
def limit.is_limit {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
  limit_cone.is_limit (get_limit_cone F)

/-- The morphism from the cone point of any other cone to the limit object. -/
def limit.lift {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (c : cone F) : cone.X c ⟶ limit F :=
  is_limit.lift (limit.is_limit F) c

@[simp] theorem limit.is_limit_lift {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (c : cone F) : is_limit.lift (limit.is_limit F) c = limit.lift F c :=
  rfl

@[simp] theorem limit.lift_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) : limit.lift F c ≫ limit.π F j = nat_trans.app (cone.π c) j :=
  is_limit.fac (limit.is_limit F) c j

/--
Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def lim_map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  is_limit.map (limit.cone F) (limit.is_limit G) α

@[simp] theorem lim_map_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) (j : J) : lim_map α ≫ limit.π G j = limit.π F j ≫ nat_trans.app α j :=
  limit.lift_π (functor.obj (cones.postcompose α) (limit.cone F)) j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
def limit.cone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (c : cone F) : c ⟶ limit.cone F :=
  is_limit.lift_cone_morphism (limit.is_limit F) c

@[simp] theorem limit.cone_morphism_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (c : cone F) : cone_morphism.hom (limit.cone_morphism c) = limit.lift F c :=
  rfl

theorem limit.cone_morphism_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) : cone_morphism.hom (limit.cone_morphism c) ≫ limit.π F j = nat_trans.app (cone.π c) j := sorry

@[simp] theorem limit.cone_point_unique_up_to_iso_hom_comp {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {c : cone F} (hc : is_limit c) (j : J) : iso.hom (is_limit.cone_point_unique_up_to_iso hc (limit.is_limit F)) ≫ limit.π F j = nat_trans.app (cone.π c) j :=
  is_limit.cone_point_unique_up_to_iso_hom_comp hc (limit.is_limit F) j

@[simp] theorem limit.cone_point_unique_up_to_iso_inv_comp {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {c : cone F} (hc : is_limit c) (j : J) : iso.inv (is_limit.cone_point_unique_up_to_iso (limit.is_limit F) hc) ≫ limit.π F j = nat_trans.app (cone.π c) j :=
  is_limit.cone_point_unique_up_to_iso_inv_comp (limit.is_limit F) hc j

/--
Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point.
-/
def limit.iso_limit_cone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (t : limit_cone F) : limit F ≅ cone.X (limit_cone.cone t) :=
  is_limit.cone_point_unique_up_to_iso (limit.is_limit F) (limit_cone.is_limit t)

@[simp] theorem limit.iso_limit_cone_hom_π_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) {X' : C} (f' : functor.obj F j ⟶ X') : iso.hom (limit.iso_limit_cone t) ≫ nat_trans.app (cone.π (limit_cone.cone t)) j ≫ f' = limit.π F j ≫ f' := sorry

@[simp] theorem limit.iso_limit_cone_inv_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) : iso.inv (limit.iso_limit_cone t) ≫ limit.π F j = nat_trans.app (cone.π (limit_cone.cone t)) j := sorry

theorem limit.hom_ext {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {X : C} {f : X ⟶ limit F} {f' : X ⟶ limit F} (w : ∀ (j : J), f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  is_limit.hom_ext (limit.is_limit F) w

@[simp] theorem limit.lift_map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] [has_limit G] (c : cone F) (α : F ⟶ G) : limit.lift F c ≫ lim_map α = limit.lift G (functor.obj (cones.postcompose α) c) := sorry

@[simp] theorem limit.lift_cone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] : limit.lift F (limit.cone F) = 𝟙 :=
  is_limit.lift_self (limit.is_limit F)

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.hom_iso {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (W : C) : (W ⟶ limit F) ≅ functor.obj (functor.cones F) (opposite.op W) :=
  is_limit.hom_iso (limit.is_limit F) W

@[simp] theorem limit.hom_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] {W : C} (f : W ⟶ limit F) : iso.hom (limit.hom_iso F W) f = functor.map (functor.const J) f ≫ cone.π (limit.cone F) :=
  is_limit.hom_iso_hom (limit.is_limit F) f

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.hom_iso' {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (W : C) : (W ⟶ limit F) ≅
  Subtype fun (p : (j : J) → W ⟶ functor.obj F j) => ∀ {j j' : J} (f : j ⟶ j'), p j ≫ functor.map F f = p j' :=
  is_limit.hom_iso' (limit.is_limit F) W

theorem limit.lift_extend {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ cone.X c) : limit.lift F (cone.extend c f) = f ≫ limit.lift F c := sorry

/--
If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
theorem has_limit_of_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] (α : F ≅ G) : has_limit G :=
  has_limit.mk
    (limit_cone.mk (functor.obj (cones.postcompose (iso.hom α)) (limit.cone F))
      (is_limit.mk fun (s : cone G) => limit.lift F (functor.obj (cones.postcompose (iso.inv α)) s)))

/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
-- See the construction of limits from products and equalizers

-- for an example usage.

theorem has_limit.of_cones_iso {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C) (h : functor.cones F ≅ functor.cones G) [has_limit F] : has_limit G :=
  has_limit.mk
    (limit_cone.mk (is_limit.of_nat_iso.limit_cone (is_limit.nat_iso (limit.is_limit F) ≪≫ h))
      (is_limit.of_nat_iso (is_limit.nat_iso (limit.is_limit F) ≪≫ h)))

/--
The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_limit.iso_of_nat_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) : limit F ≅ limit G :=
  is_limit.cone_points_iso_of_nat_iso (limit.is_limit F) (limit.is_limit G) w

@[simp] theorem has_limit.iso_of_nat_iso_hom_π {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) (j : J) : iso.hom (has_limit.iso_of_nat_iso w) ≫ limit.π G j = limit.π F j ≫ nat_trans.app (iso.hom w) j :=
  is_limit.cone_points_iso_of_nat_iso_hom_comp (limit.is_limit F) (limit.is_limit G) w j

@[simp] theorem has_limit.lift_iso_of_nat_iso_hom_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_limit F] [has_limit G] (t : cone F) (w : F ≅ G) {X' : C} (f' : limit G ⟶ X') : limit.lift F t ≫ iso.hom (has_limit.iso_of_nat_iso w) ≫ f' =
  limit.lift G (functor.obj (cones.postcompose (iso.hom w)) t) ≫ f' := sorry

/--
The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_limit.iso_of_equivalence {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G] (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) : limit F ≅ limit G :=
  is_limit.cone_points_iso_of_equivalence (limit.is_limit F) (limit.is_limit G) e w

@[simp] theorem has_limit.iso_of_equivalence_hom_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G] (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) (k : K) : iso.hom (has_limit.iso_of_equivalence e w) ≫ limit.π G k =
  limit.π F (functor.obj (equivalence.inverse e) k) ≫
    nat_trans.app (iso.inv w) (functor.obj (equivalence.inverse e) k) ≫
      functor.map G (nat_trans.app (equivalence.counit e) k) := sorry

@[simp] theorem has_limit.iso_of_equivalence_inv_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G] (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) (j : J) : iso.inv (has_limit.iso_of_equivalence e w) ≫ limit.π F j =
  limit.π G (functor.obj (equivalence.functor e) j) ≫ nat_trans.app (iso.hom w) j := sorry

/--
The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) (cone.whisker E (limit.cone F))

@[simp] theorem limit.pre_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (functor.obj E k) := sorry

@[simp] theorem limit.lift_pre {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] (c : cone F) : limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (cone.whisker E c) := sorry

@[simp] theorem limit.pre_pre {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)] {L : Type v} [small_category L] (D : L ⥤ K) [has_limit (D ⋙ E ⋙ F)] : limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) := sorry

/---
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
theorem limit.pre_eq {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_limit F] {E : K ⥤ J} [has_limit (E ⋙ F)] (s : limit_cone (E ⋙ F)) (t : limit_cone F) : limit.pre F E =
  iso.hom (limit.iso_limit_cone t) ≫
    is_limit.lift (limit_cone.is_limit s) (cone.whisker E (limit_cone.cone t)) ≫ iso.inv (limit.iso_limit_cone s) := sorry

/--
The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
def limit.post {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] : functor.obj G (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (functor.map_cone G (limit.cone F))

@[simp] theorem limit.post_π_assoc {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] (j : J) {X' : D} (f' : functor.obj (F ⋙ G) j ⟶ X') : limit.post F G ≫ limit.π (F ⋙ G) j ≫ f' = functor.map G (limit.π F j) ≫ f' := sorry

@[simp] theorem limit.lift_post {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] (c : cone F) : functor.map G (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (functor.map_cone G c) := sorry

@[simp] theorem limit.post_post {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)] {E : Type u''} [category E] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] : functor.map H (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) := sorry

/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals -/

/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) -/

theorem limit.pre_post {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {D : Type u'} [category D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D) [has_limit F] [has_limit (E ⋙ F)] [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)] : functor.map G (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E := sorry

/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/

/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/

protected instance has_limit_equivalence_comp {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} (e : K ≌ J) [has_limit F] : has_limit (equivalence.functor e ⋙ F) :=
  has_limit.mk
    (limit_cone.mk (cone.whisker (equivalence.functor e) (limit.cone F))
      (is_limit.whisker_equivalence (limit.is_limit F) e))

/--
If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
theorem has_limit_of_equivalence_comp {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} (e : K ≌ J) [has_limit (equivalence.functor e ⋙ F)] : has_limit F :=
  has_limit_of_iso (equivalence.inv_fun_id_assoc e F)

-- `has_limit_comp_equivalence` and `has_limit_of_comp_equivalence`

-- are proved in `category_theory/adjunction/limits.lean`.

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
def lim {J : Type v} [small_category J] {C : Type u} [category C] [has_limits_of_shape J C] : (J ⥤ C) ⥤ C :=
  functor.mk (fun (F : J ⥤ C) => limit F) fun (F G : J ⥤ C) (α : F ⟶ G) => lim_map α

-- We generate this manually since `simps` gives it a weird name.

@[simp] theorem lim_map_eq_lim_map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) : functor.map lim α = lim_map α :=
  rfl

theorem limit.map_pre {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_limits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) [has_limits_of_shape K C] (E : K ⥤ J) : functor.map lim α ≫ limit.pre G E = limit.pre F E ≫ functor.map lim (whisker_left E α) := sorry

theorem limit.map_pre' {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] [has_limits_of_shape J C] [has_limits_of_shape K C] (F : J ⥤ C) {E₁ : K ⥤ J} {E₂ : K ⥤ J} (α : E₁ ⟶ E₂) : limit.pre F E₂ = limit.pre F E₁ ≫ functor.map lim (whisker_right α F) := sorry

theorem limit.id_pre {J : Type v} [small_category J] {C : Type u} [category C] [has_limits_of_shape J C] (F : J ⥤ C) : limit.pre F 𝟭 = functor.map lim (iso.inv (functor.left_unitor F)) := sorry

/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
theorem limit.map_post {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_limits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) {D : Type u'} [category D] [has_limits_of_shape J D] (H : C ⥤ D) : functor.map H (lim_map α) ≫ limit.post G H = limit.post F H ≫ lim_map (whisker_right α H) := sorry

   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/

/--
The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def lim_yoneda {J : Type v} [small_category J] {C : Type u} [category C] [has_limits_of_shape J C] : lim ⋙ yoneda ≅ cones J C :=
  nat_iso.of_components
    (fun (F : J ⥤ C) => nat_iso.of_components (fun (W : Cᵒᵖ) => limit.hom_iso F (opposite.unop W)) sorry) sorry

/--
We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem has_limits_of_shape_of_equivalence {J : Type v} [small_category J] {C : Type u} [category C] {J' : Type v} [small_category J'] (e : J ≌ J') [has_limits_of_shape J C] : has_limits_of_shape J' C :=
  has_limits_of_shape.mk fun (F : J' ⥤ C) => has_limit_of_equivalence_comp e

/-- `colimit_cocone F` contains a cocone over `F` together with the information that it is a
    colimit. -/
structure colimit_cocone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) 
where
  cocone : cocone F
  is_colimit : is_colimit cocone

/-- `has_colimit F` represents the mere existence of a colimit for `F`. -/
class has_colimit {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) 
  mk' ::
where (exists_colimit : Nonempty (colimit_cocone F))

theorem has_colimit.mk {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} (d : colimit_cocone F) : has_colimit F :=
  has_colimit.mk' (Nonempty.intro d)

/-- Use the axiom of choice to extract explicit `colimit_cocone F` from `has_colimit F`. -/
def get_colimit_cocone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
  Classical.choice has_colimit.exists_colimit

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
class has_colimits_of_shape (J : Type v) [small_category J] (C : Type u) [category C] 
where
  has_colimit : ∀ (F : J ⥤ C), has_colimit F

/-- `C` has all (small) colimits if it has colimits of every shape. -/
class has_colimits (C : Type u) [category C] 
where
  has_colimits_of_shape : ∀ (J : Type v) [𝒥 : small_category J], has_colimits_of_shape J C

protected instance has_colimit_of_has_colimits_of_shape {C : Type u} [category C] {J : Type v} [small_category J] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
  has_colimits_of_shape.has_colimit F

protected instance has_colimits_of_shape_of_has_colimits {C : Type u} [category C] {J : Type v} [small_category J] [H : has_colimits C] : has_colimits_of_shape J C :=
  has_colimits.has_colimits_of_shape J

/- Interface to the `has_colimit` class. -/

/-- An arbitrary choice of colimit cocone of a functor. -/
def colimit.cocone {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] : cocone F :=
  colimit_cocone.cocone (get_colimit_cocone F)

/-- An arbitrary choice of colimit object of a functor. -/
def colimit {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] : C :=
  cocone.X sorry

/-- The coprojection from a value of the functor to the colimit object. -/
def colimit.ι {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (j : J) : functor.obj F j ⟶ colimit F :=
  nat_trans.app (cocone.ι (colimit.cocone F)) j

@[simp] theorem colimit.cocone_ι {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (j : J) : nat_trans.app (cocone.ι (colimit.cocone F)) j = colimit.ι F j :=
  rfl

@[simp] theorem colimit.cocone_X {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] : cocone.X (colimit.cocone F) = colimit F :=
  rfl

@[simp] theorem colimit.w {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] {j : J} {j' : J} (f : j ⟶ j') : functor.map F f ≫ colimit.ι F j' = colimit.ι F j :=
  cocone.w (colimit.cocone F) f

/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/
def colimit.is_colimit {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
  colimit_cocone.is_colimit (get_colimit_cocone F)

/-- The morphism from the colimit object to the cone point of any other cocone. -/
def colimit.desc {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ cocone.X c :=
  is_colimit.desc (colimit.is_colimit F) c

@[simp] theorem colimit.is_colimit_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (c : cocone F) : is_colimit.desc (colimit.is_colimit F) c = colimit.desc F c :=
  rfl

/--
We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `tactic/reassoc_axiom.lean`)
 -/
@[simp] theorem colimit.ι_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) : colimit.ι F j ≫ colimit.desc F c = nat_trans.app (cocone.ι c) j :=
  is_colimit.fac (colimit.is_colimit F) c j

/--
Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colim_map {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
  is_colimit.map (colimit.is_colimit F) (colimit.cocone G) α

@[simp] theorem ι_colim_map_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) (j : J) {X' : C} (f' : colimit G ⟶ X') : colimit.ι F j ≫ colim_map α ≫ f' = nat_trans.app α j ≫ colimit.ι G j ≫ f' := sorry

/-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/
def colimit.cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (c : cocone F) : colimit.cocone F ⟶ c :=
  is_colimit.desc_cocone_morphism (colimit.is_colimit F) c

@[simp] theorem colimit.cocone_morphism_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (c : cocone F) : cocone_morphism.hom (colimit.cocone_morphism c) = colimit.desc F c :=
  rfl

theorem colimit.ι_cocone_morphism {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) : colimit.ι F j ≫ cocone_morphism.hom (colimit.cocone_morphism c) = nat_trans.app (cocone.ι c) j := sorry

@[simp] theorem colimit.comp_cocone_point_unique_up_to_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {c : cocone F} (hc : is_colimit c) (j : J) : colimit.ι F j ≫ iso.hom (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) hc) =
  nat_trans.app (cocone.ι c) j :=
  is_colimit.comp_cocone_point_unique_up_to_iso_hom (colimit.is_colimit F) hc j

@[simp] theorem colimit.comp_cocone_point_unique_up_to_iso_inv_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {c : cocone F} (hc : is_colimit c) (j : J) {X' : C} (f' : cocone.X c ⟶ X') : colimit.ι F j ≫ iso.inv (is_colimit.cocone_point_unique_up_to_iso hc (colimit.is_colimit F)) ≫ f' =
  nat_trans.app (cocone.ι c) j ≫ f' := sorry

/--
Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone point.
-/
def colimit.iso_colimit_cocone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) : colimit F ≅ cocone.X (colimit_cocone.cocone t) :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) (colimit_cocone.is_colimit t)

@[simp] theorem colimit.iso_colimit_cocone_ι_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) : colimit.ι F j ≫ iso.hom (colimit.iso_colimit_cocone t) = nat_trans.app (cocone.ι (colimit_cocone.cocone t)) j := sorry

@[simp] theorem colimit.iso_colimit_cocone_ι_inv_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) {X' : C} (f' : colimit F ⟶ X') : nat_trans.app (cocone.ι (colimit_cocone.cocone t)) j ≫ iso.inv (colimit.iso_colimit_cocone t) ≫ f' = colimit.ι F j ≫ f' := sorry

theorem colimit.hom_ext {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {X : C} {f : colimit F ⟶ X} {f' : colimit F ⟶ X} (w : ∀ (j : J), colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
  is_colimit.hom_ext (colimit.is_colimit F) w

@[simp] theorem colimit.desc_cocone {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] : colimit.desc F (colimit.cocone F) = 𝟙 :=
  is_colimit.desc_self (colimit.is_colimit F)

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.hom_iso {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (W : C) : (colimit F ⟶ W) ≅ functor.obj (functor.cocones F) W :=
  is_colimit.hom_iso (colimit.is_colimit F) W

@[simp] theorem colimit.hom_iso_hom {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] {W : C} (f : colimit F ⟶ W) : iso.hom (colimit.hom_iso F W) f = cocone.ι (colimit.cocone F) ≫ functor.map (functor.const J) f :=
  is_colimit.hom_iso_hom (colimit.is_colimit F) f

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.hom_iso' {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (W : C) : (colimit F ⟶ W) ≅
  Subtype fun (p : (j : J) → functor.obj F j ⟶ W) => ∀ {j j' : J} (f : j ⟶ j'), functor.map F f ≫ p j' = p j :=
  is_colimit.hom_iso' (colimit.is_colimit F) W

theorem colimit.desc_extend {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : cocone.X c ⟶ X) : colimit.desc F (cocone.extend c f) = colimit.desc F c ≫ f := sorry

/--
If `F` has a colimit, so does any naturally isomorphic functor.
-/
-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.

-- This is intentional; it seems to help with elaboration.

theorem has_colimit_of_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_colimit F] (α : G ≅ F) : has_colimit G :=
  has_colimit.mk
    (colimit_cocone.mk (functor.obj (cocones.precompose (iso.hom α)) (colimit.cocone F))
      (is_colimit.mk fun (s : cocone G) => colimit.desc F (functor.obj (cocones.precompose (iso.inv α)) s)))

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
theorem has_colimit.of_cocones_iso {C : Type u} [category C] {J : Type v} {K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C) (h : functor.cocones F ≅ functor.cocones G) [has_colimit F] : has_colimit G :=
  has_colimit.mk
    (colimit_cocone.mk (is_colimit.of_nat_iso.colimit_cocone (is_colimit.nat_iso (colimit.is_colimit F) ≪≫ h))
      (is_colimit.of_nat_iso (is_colimit.nat_iso (colimit.is_colimit F) ≪≫ h)))

/--
The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_colimit.iso_of_nat_iso {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) : colimit F ≅ colimit G :=
  is_colimit.cocone_points_iso_of_nat_iso (colimit.is_colimit F) (colimit.is_colimit G) w

@[simp] theorem has_colimit.iso_of_nat_iso_ι_hom {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) (j : J) : colimit.ι F j ≫ iso.hom (has_colimit.iso_of_nat_iso w) = nat_trans.app (iso.hom w) j ≫ colimit.ι G j :=
  is_colimit.comp_cocone_points_iso_of_nat_iso_hom (colimit.is_colimit F) (colimit.is_colimit G) w j

@[simp] theorem has_colimit.iso_of_nat_iso_hom_desc_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {G : J ⥤ C} [has_colimit F] [has_colimit G] (t : cocone G) (w : F ≅ G) {X' : C} (f' : cocone.X t ⟶ X') : iso.hom (has_colimit.iso_of_nat_iso w) ≫ colimit.desc G t ≫ f' =
  colimit.desc F (functor.obj (cocones.precompose (iso.hom w)) t) ≫ f' := sorry

/--
The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_colimit.iso_of_equivalence {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G] (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) : colimit F ≅ colimit G :=
  is_colimit.cocone_points_iso_of_equivalence (colimit.is_colimit F) (colimit.is_colimit G) e w

@[simp] theorem has_colimit.iso_of_equivalence_hom_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G] (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) (j : J) : colimit.ι F j ≫ iso.hom (has_colimit.iso_of_equivalence e w) =
  functor.map F (nat_trans.app (equivalence.unit e) j) ≫
    nat_trans.app (iso.inv w) (functor.obj (equivalence.functor e ⋙ equivalence.inverse e) j) ≫
      colimit.ι G (functor.obj (equivalence.functor e) (functor.obj (equivalence.functor e ⋙ equivalence.inverse e) j)) := sorry

@[simp] theorem has_colimit.iso_of_equivalence_inv_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G] (e : J ≌ K) (w : equivalence.functor e ⋙ G ≅ F) (k : K) : colimit.ι G k ≫ iso.inv (has_colimit.iso_of_equivalence e w) =
  functor.map G (nat_trans.app (equivalence.counit_inv e) k) ≫
    nat_trans.app (iso.hom w) (functor.obj (equivalence.inverse e) k) ≫
      colimit.ι F (functor.obj (equivalence.inverse e) k) := sorry

/--
The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) (cocone.whisker E (colimit.cocone F))

@[simp] theorem colimit.ι_pre_assoc {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] (k : K) {X' : C} (f' : colimit F ⟶ X') : colimit.ι (E ⋙ F) k ≫ colimit.pre F E ≫ f' = colimit.ι F (functor.obj E k) ≫ f' := sorry

@[simp] theorem colimit.pre_desc {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] (c : cocone F) : colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (cocone.whisker E c) := sorry

@[simp] theorem colimit.pre_pre {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ C) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)] {L : Type v} [small_category L] (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)] : colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) := sorry

/---
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
theorem colimit.pre_eq {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_colimit F] {E : K ⥤ J} [has_colimit (E ⋙ F)] (s : colimit_cocone (E ⋙ F)) (t : colimit_cocone F) : colimit.pre F E =
  iso.hom (colimit.iso_colimit_cocone s) ≫
    is_colimit.desc (colimit_cocone.is_colimit s) (cocone.whisker E (colimit_cocone.cocone t)) ≫
      iso.inv (colimit.iso_colimit_cocone t) := sorry

/--
The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] : colimit (F ⋙ G) ⟶ functor.obj G (colimit F) :=
  colimit.desc (F ⋙ G) (functor.map_cocone G (colimit.cocone F))

@[simp] theorem colimit.ι_post_assoc {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] (j : J) {X' : D} (f' : functor.obj G (colimit F) ⟶ X') : colimit.ι (F ⋙ G) j ≫ colimit.post F G ≫ f' = functor.map G (colimit.ι F j) ≫ f' := sorry

@[simp] theorem colimit.post_desc {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] (c : cocone F) : colimit.post F G ≫ functor.map G (colimit.desc F c) = colimit.desc (F ⋙ G) (functor.map_cocone G c) := sorry

@[simp] theorem colimit.post_post {J : Type v} [small_category J] {C : Type u} [category C] (F : J ⥤ C) {D : Type u'} [category D] [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)] {E : Type u''} [category E] (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] : colimit.post (F ⋙ G) H ≫ functor.map H (colimit.post F G) = colimit.post F (G ⋙ H) := sorry

/- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals -/

/- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H)) -/

theorem colimit.pre_post {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {D : Type u'} [category D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D) [has_colimit F] [has_colimit (E ⋙ F)] [has_colimit (F ⋙ G)] [has_colimit ((E ⋙ F) ⋙ G)] : colimit.post (E ⋙ F) G ≫ functor.map G (colimit.pre F E) = colimit.pre (F ⋙ G) E ≫ colimit.post F G := sorry

/- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs -/

/- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or -/

protected instance has_colimit_equivalence_comp {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} (e : K ≌ J) [has_colimit F] : has_colimit (equivalence.functor e ⋙ F) :=
  has_colimit.mk
    (colimit_cocone.mk (cocone.whisker (equivalence.functor e) (colimit.cocone F))
      (is_colimit.whisker_equivalence (colimit.is_colimit F) e))

/--
If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
theorem has_colimit_of_equivalence_comp {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} (e : K ≌ J) [has_colimit (equivalence.functor e ⋙ F)] : has_colimit F :=
  has_colimit_of_iso (iso.symm (equivalence.inv_fun_id_assoc e F))

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
def colim {J : Type v} [small_category J] {C : Type u} [category C] [has_colimits_of_shape J C] : (J ⥤ C) ⥤ C :=
  functor.mk (fun (F : J ⥤ C) => colimit F) fun (F G : J ⥤ C) (α : F ⟶ G) => colim_map α

@[simp] theorem colimit.ι_map_assoc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) (j : J) {X' : C} (f' : functor.obj colim G ⟶ X') : colimit.ι F j ≫ functor.map colim α ≫ f' = nat_trans.app α j ≫ colimit.ι G j ≫ f' := sorry

@[simp] theorem colimit.map_desc {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) (c : cocone G) : functor.map colim α ≫ colimit.desc G c = colimit.desc F (functor.obj (cocones.precompose α) c) := sorry

theorem colimit.pre_map {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ C} [has_colimits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) [has_colimits_of_shape K C] (E : K ⥤ J) : colimit.pre F E ≫ functor.map colim α = functor.map colim (whisker_left E α) ≫ colimit.pre G E := sorry

theorem colimit.pre_map' {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] [has_colimits_of_shape J C] [has_colimits_of_shape K C] (F : J ⥤ C) {E₁ : K ⥤ J} {E₂ : K ⥤ J} (α : E₁ ⟶ E₂) : colimit.pre F E₁ = functor.map colim (whisker_right α F) ≫ colimit.pre F E₂ := sorry

theorem colimit.pre_id {J : Type v} [small_category J] {C : Type u} [category C] [has_colimits_of_shape J C] (F : J ⥤ C) : colimit.pre F 𝟭 = functor.map colim (iso.hom (functor.left_unitor F)) := sorry

/- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
theorem colimit.map_post {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} [has_colimits_of_shape J C] {G : J ⥤ C} (α : F ⟶ G) {D : Type u'} [category D] [has_colimits_of_shape J D] (H : C ⥤ D) : colimit.post F H ≫ functor.map H (functor.map colim α) = functor.map colim (whisker_right α H) ≫ colimit.post G H := sorry

   H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/

/--
The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colim_coyoneda {J : Type v} [small_category J] {C : Type u} [category C] [has_colimits_of_shape J C] : functor.op colim ⋙ coyoneda ≅ cocones J C :=
  nat_iso.of_components (fun (F : J ⥤ Cᵒᵖ) => nat_iso.of_components (colimit.hom_iso (opposite.unop F)) sorry) sorry

/--
We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem has_colimits_of_shape_of_equivalence {J : Type v} [small_category J] {C : Type u} [category C] {J' : Type v} [small_category J'] (e : J ≌ J') [has_colimits_of_shape J C] : has_colimits_of_shape J' C :=
  has_colimits_of_shape.mk fun (F : J' ⥤ C) => has_colimit_of_equivalence_comp e

/--
If `t : cone F` is a limit cone, then `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit.op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} (P : is_limit t) : is_colimit (cone.op t) :=
  is_colimit.mk fun (s : cocone (functor.op F)) => has_hom.hom.op (is_limit.lift P (cocone.unop s))

/--
If `t : cocone F` is a colimit cocone, then `t.op : cone F.op` is a limit cone.
-/
def is_colimit.op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} (P : is_colimit t) : is_limit (cocone.op t) :=
  is_limit.mk fun (s : cone (functor.op F)) => has_hom.hom.op (is_colimit.desc P (cone.unop s))

/--
If `t : cone F.op` is a limit cone, then `t.unop : cocone F` is a colimit cocone.
-/
def is_limit.unop {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone (functor.op F)} (P : is_limit t) : is_colimit (cone.unop t) :=
  is_colimit.mk fun (s : cocone F) => has_hom.hom.unop (is_limit.lift P (cocone.op s))

/--
If `t : cocone F.op` is a colimit cocone, then `t.unop : cone F.` is a limit cone.
-/
def is_colimit.unop {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone (functor.op F)} (P : is_colimit t) : is_limit (cocone.unop t) :=
  is_limit.mk fun (s : cone F) => has_hom.hom.unop (is_colimit.desc P (cone.op s))

/--
`t : cone F` is a limit cone if and only is `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit_equiv_is_colimit_op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cone F} : is_limit t ≃ is_colimit (cone.op t) :=
  equiv_of_subsingleton_of_subsingleton is_limit.op
    fun (P : is_colimit (cone.op t)) =>
      is_limit.of_iso_limit (is_colimit.unop P) (cones.ext (iso.refl (cone.X (cocone.unop (cone.op t)))) sorry)

/--
`t : cocone F` is a colimit cocone if and only is `t.op : cone F.op` is a limit cone.
-/
def is_colimit_equiv_is_limit_op {J : Type v} [small_category J] {C : Type u} [category C] {F : J ⥤ C} {t : cocone F} : is_colimit t ≃ is_limit (cocone.op t) :=
  equiv_of_subsingleton_of_subsingleton is_colimit.op
    fun (P : is_limit (cocone.op t)) =>
      is_colimit.of_iso_colimit (is_limit.unop P) (cocones.ext (iso.refl (cocone.X (cone.unop (cocone.op t)))) sorry)

