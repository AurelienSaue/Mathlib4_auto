/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.epi_mono
import Mathlib.category_theory.limits.limits
import Mathlib.PostPort

universes v l u_1 u u₂ 

namespace Mathlib

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject {a ∈ A | f(a) = g(a)} known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `walking_parallel_pair` is the indexing category used for (co)equalizer_diagrams
* `parallel_pair` is a functor from `walking_parallel_pair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallel_pair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `is_iso_limit_cone_parallel_pair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

namespace category_theory.limits


/-- The type of objects for the diagram indexing a (co)equalizer. -/
inductive walking_parallel_pair 
where
| zero : walking_parallel_pair
| one : walking_parallel_pair

/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
inductive walking_parallel_pair_hom : walking_parallel_pair → walking_parallel_pair → Type v
where
| left : walking_parallel_pair_hom walking_parallel_pair.zero walking_parallel_pair.one
| right : walking_parallel_pair_hom walking_parallel_pair.zero walking_parallel_pair.one
| id : (X : walking_parallel_pair) → walking_parallel_pair_hom X X

/-- Satisfying the inhabited linter -/
protected instance walking_parallel_pair_hom.inhabited : Inhabited (walking_parallel_pair_hom walking_parallel_pair.zero walking_parallel_pair.one) :=
  { default := walking_parallel_pair_hom.left }

/-- Composition of morphisms in the indexing diagram for (co)equalizers. -/
def walking_parallel_pair_hom.comp (X : walking_parallel_pair) (Y : walking_parallel_pair) (Z : walking_parallel_pair) (f : walking_parallel_pair_hom X Y) (g : walking_parallel_pair_hom Y Z) : walking_parallel_pair_hom X Z :=
  sorry

protected instance walking_parallel_pair_hom_category : small_category walking_parallel_pair :=
  category.mk

@[simp] theorem walking_parallel_pair_hom_id (X : walking_parallel_pair) : walking_parallel_pair_hom.id X = 𝟙 :=
  rfl

/-- `parallel_pair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
    common domain and codomain. -/
def parallel_pair {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : walking_parallel_pair ⥤ C :=
  functor.mk (fun (x : walking_parallel_pair) => sorry) fun (x y : walking_parallel_pair) (h : x ⟶ y) => sorry

@[simp] theorem parallel_pair_obj_zero {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : functor.obj (parallel_pair f g) walking_parallel_pair.zero = X :=
  rfl

@[simp] theorem parallel_pair_obj_one {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : functor.obj (parallel_pair f g) walking_parallel_pair.one = Y :=
  rfl

@[simp] theorem parallel_pair_map_left {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : functor.map (parallel_pair f g) walking_parallel_pair_hom.left = f :=
  rfl

@[simp] theorem parallel_pair_map_right {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) : functor.map (parallel_pair f g) walking_parallel_pair_hom.right = g :=
  rfl

@[simp] theorem parallel_pair_functor_obj {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (j : walking_parallel_pair) : functor.obj
    (parallel_pair (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right)) j =
  functor.obj F j := sorry

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallel_pair` -/
def diagram_iso_parallel_pair {C : Type u} [category C] (F : walking_parallel_pair ⥤ C) : F ≅ parallel_pair (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right) :=
  nat_iso.of_components (fun (j : walking_parallel_pair) => eq_to_iso sorry) sorry

/-- A fork on `f` and `g` is just a `cone (parallel_pair f g)`. -/
def fork {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y)  :=
  cone (parallel_pair f g)

/-- A cofork on `f` and `g` is just a `cocone (parallel_pair f g)`. -/
def cofork {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y)  :=
  cocone (parallel_pair f g)

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms `t.π.app zero : t.X ⟶ X`
    and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is interesting, and we give it the
    shorter name `fork.ι t`. -/
def fork.ι {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : fork f g) : functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X t)) walking_parallel_pair.zero ⟶
  functor.obj (parallel_pair f g) walking_parallel_pair.zero :=
  nat_trans.app (cone.π t) walking_parallel_pair.zero

/-- A cofork `t` on the parallel_pair `f g : X ⟶ Y` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cofork.π t`. -/
def cofork.π {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : cofork f g) : functor.obj (parallel_pair f g) walking_parallel_pair.one ⟶
  functor.obj (functor.obj (functor.const walking_parallel_pair) (cocone.X t)) walking_parallel_pair.one :=
  nat_trans.app (cocone.ι t) walking_parallel_pair.one

@[simp] theorem fork.ι_eq_app_zero {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : fork f g) : fork.ι t = nat_trans.app (cone.π t) walking_parallel_pair.zero :=
  rfl

@[simp] theorem cofork.π_eq_app_one {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : cofork f g) : cofork.π t = nat_trans.app (cocone.ι t) walking_parallel_pair.one :=
  rfl

@[simp] theorem fork.app_zero_left {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (s : fork f g) : nat_trans.app (cone.π s) walking_parallel_pair.zero ≫ f = nat_trans.app (cone.π s) walking_parallel_pair.one := sorry

@[simp] theorem fork.app_zero_right {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (s : fork f g) : nat_trans.app (cone.π s) walking_parallel_pair.zero ≫ g = nat_trans.app (cone.π s) walking_parallel_pair.one := sorry

@[simp] theorem cofork.left_app_one_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (s : cofork f g) {X' : C} (f' : functor.obj (functor.obj (functor.const walking_parallel_pair) (cocone.X s)) walking_parallel_pair.one ⟶ X') : f ≫ nat_trans.app (cocone.ι s) walking_parallel_pair.one ≫ f' =
  nat_trans.app (cocone.ι s) walking_parallel_pair.zero ≫ f' := sorry

@[simp] theorem cofork.right_app_one_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (s : cofork f g) {X' : C} (f' : functor.obj (functor.obj (functor.const walking_parallel_pair) (cocone.X s)) walking_parallel_pair.one ⟶ X') : g ≫ nat_trans.app (cocone.ι s) walking_parallel_pair.one ≫ f' =
  nat_trans.app (cocone.ι s) walking_parallel_pair.zero ≫ f' := sorry

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[simp] theorem fork.of_ι_X {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : cone.X (fork.of_ι ι w) = P :=
  Eq.refl (cone.X (fork.of_ι ι w))

/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
    `f ≫ π = g ≫ π`. -/
@[simp] theorem cofork.of_π_ι_app {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : ∀ (X_1 : walking_parallel_pair),
  nat_trans.app (cocone.ι (cofork.of_π π w)) X_1 = walking_parallel_pair.cases_on X_1 (f ≫ π) π :=
  fun (X_1 : walking_parallel_pair) => Eq.refl (nat_trans.app (cocone.ι (cofork.of_π π w)) X_1)

theorem fork.ι_of_ι {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork.ι (fork.of_ι ι w) = ι :=
  rfl

theorem cofork.π_of_π {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork.π (cofork.of_π π w) = π :=
  rfl

theorem fork.condition {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : fork f g) : fork.ι t ≫ f = fork.ι t ≫ g := sorry

theorem cofork.condition {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : cofork f g) : f ≫ cofork.π t = g ≫ cofork.π t := sorry

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
    first map -/
theorem fork.equalizer_ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (s : fork f g) {W : C} {k : W ⟶ cone.X s} {l : W ⟶ cone.X s} (h : k ≫ fork.ι s = l ≫ fork.ι s) (j : walking_parallel_pair) : k ≫ nat_trans.app (cone.π s) j = l ≫ nat_trans.app (cone.π s) j := sorry

/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
    the second map -/
theorem cofork.coequalizer_ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (s : cofork f g) {W : C} {k : cocone.X s ⟶ W} {l : cocone.X s ⟶ W} (h : cofork.π s ≫ k = cofork.π s ≫ l) (j : walking_parallel_pair) : nat_trans.app (cocone.ι s) j ≫ k = nat_trans.app (cocone.ι s) j ≫ l := sorry

theorem fork.is_limit.hom_ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : fork f g} (hs : is_limit s) {W : C} {k : W ⟶ cone.X s} {l : W ⟶ cone.X s} (h : k ≫ fork.ι s = l ≫ fork.ι s) : k = l :=
  is_limit.hom_ext hs (fork.equalizer_ext s h)

theorem cofork.is_colimit.hom_ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : cofork f g} (hs : is_colimit s) {W : C} {k : cocone.X s ⟶ W} {l : cocone.X s ⟶ W} (h : cofork.π s ≫ k = cofork.π s ≫ l) : k = l :=
  is_colimit.hom_ext hs (cofork.coequalizer_ext s h)

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
    `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
def fork.is_limit.lift' {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : fork f g} (hs : is_limit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : Subtype fun (l : W ⟶ cone.X s) => l ≫ fork.ι s = k :=
  { val := is_limit.lift hs (fork.of_ι k h), property := sorry }

/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
    `f ≫ k = g ≫ k` induces a morphism `l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/
def cofork.is_colimit.desc' {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : cofork f g} (hs : is_colimit s) {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : Subtype fun (l : cocone.X s ⟶ W) => cofork.π s ≫ l = k :=
  { val := is_colimit.desc hs (cofork.of_π k h), property := sorry }

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def fork.is_limit.mk {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : fork f g) (lift : (s : fork f g) → cone.X s ⟶ cone.X t) (fac : ∀ (s : fork f g), lift s ≫ fork.ι t = fork.ι s) (uniq : ∀ (s : fork f g) (m : cone.X s ⟶ cone.X t),
  (∀ (j : walking_parallel_pair), m ≫ nat_trans.app (cone.π t) j = nat_trans.app (cone.π s) j) → m = lift s) : is_limit t :=
  is_limit.mk lift

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def fork.is_limit.mk' {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : fork f g) (create : (s : fork f g) →
  Subtype
    fun
      (l :
      functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X s)) walking_parallel_pair.zero ⟶
        functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X t)) walking_parallel_pair.zero) =>
      l ≫ fork.ι t = fork.ι s ∧
        ∀
          {m :
            functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X s)) walking_parallel_pair.zero ⟶
              functor.obj (functor.obj (functor.const walking_parallel_pair) (cone.X t)) walking_parallel_pair.zero},
          m ≫ fork.ι t = fork.ι s → m = l) : is_limit t :=
  fork.is_limit.mk t (fun (s : fork f g) => subtype.val (create s)) sorry sorry

/-- This is a slightly more convenient method to verify that a cofork is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def cofork.is_colimit.mk {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : cofork f g) (desc : (s : cofork f g) → cocone.X t ⟶ cocone.X s) (fac : ∀ (s : cofork f g), cofork.π t ≫ desc s = cofork.π s) (uniq : ∀ (s : cofork f g) (m : cocone.X t ⟶ cocone.X s),
  (∀ (j : walking_parallel_pair), nat_trans.app (cocone.ι t) j ≫ m = nat_trans.app (cocone.ι s) j) → m = desc s) : is_colimit t :=
  is_colimit.mk desc

/-- This is another convenient method to verify that a fork is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def cofork.is_colimit.mk' {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (t : cofork f g) (create : (s : cofork f g) →
  Subtype
    fun (l : cocone.X t ⟶ cocone.X s) =>
      cofork.π t ≫ l = cofork.π s ∧
        ∀
          {m :
            functor.obj (functor.obj (functor.const walking_parallel_pair) (cocone.X t)) walking_parallel_pair.one ⟶
              functor.obj (functor.obj (functor.const walking_parallel_pair) (cocone.X s)) walking_parallel_pair.one},
          cofork.π t ≫ m = cofork.π s → m = l) : is_colimit t :=
  cofork.is_colimit.mk t (fun (s : cofork f g) => subtype.val (create s)) sorry sorry

/--
Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point are in
bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `fork.is_limit.hom_iso_natural`.
This is a special case of `is_limit.hom_iso'`, often useful to construct adjunctions.
-/
def fork.is_limit.hom_iso {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {t : fork f g} (ht : is_limit t) (Z : C) : (Z ⟶ cone.X t) ≃ Subtype fun (h : Z ⟶ X) => h ≫ f = h ≫ g :=
  equiv.mk (fun (k : Z ⟶ cone.X t) => { val := k ≫ fork.ι t, property := sorry })
    (fun (h : Subtype fun (h : Z ⟶ X) => h ≫ f = h ≫ g) => subtype.val (fork.is_limit.lift' ht ↑h sorry)) sorry sorry

/-- The bijection of `fork.is_limit.hom_iso` is natural in `Z`. -/
theorem fork.is_limit.hom_iso_natural {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {t : fork f g} (ht : is_limit t) {Z : C} {Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ cone.X t) : ↑(coe_fn (fork.is_limit.hom_iso ht Z') (q ≫ k)) = q ≫ ↑(coe_fn (fork.is_limit.hom_iso ht Z) k) :=
  category.assoc q k (fork.ι t)

/--
Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `cofork.is_colimit.hom_iso_natural`.
This is a special case of `is_colimit.hom_iso'`, often useful to construct adjunctions.
-/
def cofork.is_colimit.hom_iso {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {t : cofork f g} (ht : is_colimit t) (Z : C) : (cocone.X t ⟶ Z) ≃ Subtype fun (h : Y ⟶ Z) => f ≫ h = g ≫ h :=
  equiv.mk (fun (k : cocone.X t ⟶ Z) => { val := cofork.π t ≫ k, property := sorry })
    (fun (h : Subtype fun (h : Y ⟶ Z) => f ≫ h = g ≫ h) => subtype.val (cofork.is_colimit.desc' ht ↑h sorry)) sorry sorry

/-- The bijection of `cofork.is_colimit.hom_iso` is natural in `Z`. -/
theorem cofork.is_colimit.hom_iso_natural {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {t : cofork f g} {Z : C} {Z' : C} (q : Z ⟶ Z') (ht : is_colimit t) (k : cocone.X t ⟶ Z) : ↑(coe_fn (cofork.is_colimit.hom_iso ht Z') (k ≫ q)) = ↑(coe_fn (cofork.is_colimit.hom_iso ht Z) k) ≫ q :=
  Eq.symm (category.assoc (cofork.π t) k q)

/-- This is a helper construction that can be useful when verifying that a category has all
    equalizers. Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map right`,
    we get a cone on `F`.

    If you're thinking about using this, have a look at `has_equalizers_of_has_limit_parallel_pair`,
    which you may find to be an easier way of achieving your goal. -/
def cone.of_fork {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : fork (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right)) : cone F :=
  cone.mk (cone.X t) (nat_trans.mk fun (X : walking_parallel_pair) => nat_trans.app (cone.π t) X ≫ eq_to_hom sorry)

/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.map right`,
    we get a cocone on `F`.

    If you're thinking about using this, have a look at
    `has_coequalizers_of_has_colimit_parallel_pair`, which you may find to be an easier way of
    achieving your goal. -/
def cocone.of_cofork {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : cofork (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right)) : cocone F :=
  cocone.mk (cocone.X t) (nat_trans.mk fun (X : walking_parallel_pair) => eq_to_hom sorry ≫ nat_trans.app (cocone.ι t) X)

@[simp] theorem cone.of_fork_π {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : fork (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right)) (j : walking_parallel_pair) : nat_trans.app (cone.π (cone.of_fork t)) j =
  nat_trans.app (cone.π t) j ≫
    eq_to_hom
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : C) (e_1 : a = a_1) (ᾰ ᾰ_1 : C) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (functor.obj
                (parallel_pair (functor.map F walking_parallel_pair_hom.left)
                  (functor.map F walking_parallel_pair_hom.right))
                j)
              (functor.obj F j) (parallel_pair_functor_obj j) (functor.obj F j) (functor.obj F j)
              (Eq.refl (functor.obj F j)))
            (propext (eq_self_iff_true (functor.obj F j)))))
        trivial) :=
  rfl

@[simp] theorem cocone.of_cofork_ι {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : cofork (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right)) (j : walking_parallel_pair) : nat_trans.app (cocone.ι (cocone.of_cofork t)) j =
  eq_to_hom
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : C) (e_1 : a = a_1) (ᾰ ᾰ_1 : C) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (functor.obj F j) (functor.obj F j) (Eq.refl (functor.obj F j))
              (functor.obj
                (parallel_pair (functor.map F walking_parallel_pair_hom.left)
                  (functor.map F walking_parallel_pair_hom.right))
                j)
              (functor.obj F j) (parallel_pair_functor_obj j))
            (propext (eq_self_iff_true (functor.obj F j)))))
        trivial) ≫
    nat_trans.app (cocone.ι t) j :=
  rfl

/-- Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
    `F.map left` and `F.map right`. -/
def fork.of_cone {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : cone F) : fork (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right) :=
  cone.mk (cone.X t) (nat_trans.mk fun (X : walking_parallel_pair) => nat_trans.app (cone.π t) X ≫ eq_to_hom sorry)

/-- Given `F : walking_parallel_pair ⥤ C`, which is really the same as
    `parallel_pair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork on
    `F.map left` and `F.map right`. -/
def cofork.of_cocone {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : cocone F) : cofork (functor.map F walking_parallel_pair_hom.left) (functor.map F walking_parallel_pair_hom.right) :=
  cocone.mk (cocone.X t) (nat_trans.mk fun (X : walking_parallel_pair) => eq_to_hom sorry ≫ nat_trans.app (cocone.ι t) X)

@[simp] theorem fork.of_cone_π {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : cone F) (j : walking_parallel_pair) : nat_trans.app (cone.π (fork.of_cone t)) j =
  nat_trans.app (cone.π t) j ≫
    eq_to_hom
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : C) (e_1 : a = a_1) (ᾰ ᾰ_1 : C) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (functor.obj F j) (functor.obj F j) (Eq.refl (functor.obj F j))
              (functor.obj
                (parallel_pair (functor.map F walking_parallel_pair_hom.left)
                  (functor.map F walking_parallel_pair_hom.right))
                j)
              (functor.obj F j) (parallel_pair_functor_obj j))
            (propext (eq_self_iff_true (functor.obj F j)))))
        trivial) :=
  rfl

@[simp] theorem cofork.of_cocone_ι {C : Type u} [category C] {F : walking_parallel_pair ⥤ C} (t : cocone F) (j : walking_parallel_pair) : nat_trans.app (cocone.ι (cofork.of_cocone t)) j =
  eq_to_hom
      (eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : C) (e_1 : a = a_1) (ᾰ ᾰ_1 : C) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
              (functor.obj
                (parallel_pair (functor.map F walking_parallel_pair_hom.left)
                  (functor.map F walking_parallel_pair_hom.right))
                j)
              (functor.obj F j) (parallel_pair_functor_obj j) (functor.obj F j) (functor.obj F j)
              (Eq.refl (functor.obj F j)))
            (propext (eq_self_iff_true (functor.obj F j)))))
        trivial) ≫
    nat_trans.app (cocone.ι t) j :=
  rfl

/--
Helper function for constructing morphisms between equalizer forks.
-/
@[simp] theorem fork.mk_hom_hom {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : fork f g} {t : fork f g} (k : cone.X s ⟶ cone.X t) (w : k ≫ fork.ι t = fork.ι s) : cone_morphism.hom (fork.mk_hom k w) = k :=
  Eq.refl (cone_morphism.hom (fork.mk_hom k w))

/--
To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simp] theorem fork.ext_hom {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : fork f g} {t : fork f g} (i : cone.X s ≅ cone.X t) (w : iso.hom i ≫ fork.ι t = fork.ι s) : iso.hom (fork.ext i w) = fork.mk_hom (iso.hom i) w :=
  Eq.refl (iso.hom (fork.ext i w))

/--
Helper function for constructing morphisms between coequalizer coforks.
-/
@[simp] theorem cofork.mk_hom_hom {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : cofork f g} {t : cofork f g} (k : cocone.X s ⟶ cocone.X t) (w : cofork.π s ≫ k = cofork.π t) : cocone_morphism.hom (cofork.mk_hom k w) = k :=
  Eq.refl (cocone_morphism.hom (cofork.mk_hom k w))

/--
To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def cofork.ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {s : cofork f g} {t : cofork f g} (i : cocone.X s ≅ cocone.X t) (w : cofork.π s ≫ iso.hom i = cofork.π t) : s ≅ t :=
  iso.mk (cofork.mk_hom (iso.hom i) w) (cofork.mk_hom (iso.inv i) sorry)

/--
`has_equalizer f g` represents a particular choice of limiting cone
for the parallel pair of morphisms `f` and `g`.
-/
def has_equalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y)  :=
  has_limit (parallel_pair f g)

/-- If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `equalizer f g`. -/
def equalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : C :=
  limit (parallel_pair f g)

/-- If an equalizer of `f` and `g` exists, we can access the inclusion
    `equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
def equalizer.ι {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : equalizer f g ⟶ X :=
  limit.π (parallel_pair f g) walking_parallel_pair.zero

/--
An equalizer cone for a parallel pair `f` and `g`.
-/
def equalizer.fork {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : fork f g :=
  limit.cone (parallel_pair f g)

@[simp] theorem equalizer.fork_ι {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : fork.ι (equalizer.fork f g) = equalizer.ι f g :=
  rfl

@[simp] theorem equalizer.fork_π_app_zero {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : nat_trans.app (cone.π (equalizer.fork f g)) walking_parallel_pair.zero = equalizer.ι f g :=
  rfl

theorem equalizer.condition {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
  fork.condition (limit.cone (parallel_pair f g))

/-- The equalizer built from `equalizer.ι f g` is limiting. -/
def equalizer_is_equalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] : is_limit (fork.of_ι (equalizer.ι f g) (equalizer.condition f g)) :=
  is_limit.of_iso_limit (limit.is_limit (parallel_pair f g))
    (fork.ext (iso.refl (cone.X (limit.cone (parallel_pair f g)))) sorry)

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer of `f` and `g`
    via `equalizer.lift : W ⟶ equalizer f g`. -/
def equalizer.lift {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_equalizer f g] {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
  limit.lift (parallel_pair f g) (fork.of_ι k h)

@[simp] theorem equalizer.lift_ι_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_equalizer f g] {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) {X' : C} (f' : X ⟶ X') : equalizer.lift k h ≫ equalizer.ι f g ≫ f' = k ≫ f' := sorry

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ equalizer f g`
    satisfying `l ≫ equalizer.ι f g = k`. -/
def equalizer.lift' {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_equalizer f g] {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : Subtype fun (l : W ⟶ equalizer f g) => l ≫ equalizer.ι f g = k :=
  { val := equalizer.lift k h, property := equalizer.lift_ι k h }

/-- Two maps into an equalizer are equal if they are are equal when composed with the equalizer
    map. -/
theorem equalizer.hom_ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_equalizer f g] {W : C} {k : W ⟶ equalizer f g} {l : W ⟶ equalizer f g} (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
  fork.is_limit.hom_ext (limit.is_limit (parallel_pair f g)) h

/-- An equalizer morphism is a monomorphism -/
protected instance equalizer.ι_mono {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_equalizer f g] : mono (equalizer.ι f g) :=
  mono.mk fun (Z : C) (h k : Z ⟶ equalizer f g) (w : h ≫ equalizer.ι f g = k ≫ equalizer.ι f g) => equalizer.hom_ext w

/-- The equalizer morphism in any limit cone is a monomorphism. -/
theorem mono_of_is_limit_parallel_pair {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {c : cone (parallel_pair f g)} (i : is_limit c) : mono (fork.ι c) := sorry

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
def id_fork {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (h : f = g) : fork f g :=
  fork.of_ι 𝟙 sorry

/-- The identity on `X` is an equalizer of `(f, g)`, if `f = g`. -/
def is_limit_id_fork {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (h : f = g) : is_limit (id_fork h) :=
  fork.is_limit.mk (id_fork h) (fun (s : fork f g) => fork.ι s) sorry sorry

/-- Every equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
def is_iso_limit_cone_parallel_pair_of_eq {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (h₀ : f = g) {c : cone (parallel_pair f g)} (h : is_limit c) : is_iso (nat_trans.app (cone.π c) walking_parallel_pair.zero) :=
  is_iso.of_iso (is_limit.cone_point_unique_up_to_iso h (is_limit_id_fork h₀))

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
def equalizer.ι_of_eq {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_equalizer f g] (h : f = g) : is_iso (equalizer.ι f g) :=
  is_iso_limit_cone_parallel_pair_of_eq h (limit.is_limit (parallel_pair f g))

/-- Every equalizer of `(f, f)` is an isomorphism. -/
def is_iso_limit_cone_parallel_pair_of_self {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {c : cone (parallel_pair f f)} (h : is_limit c) : is_iso (nat_trans.app (cone.π c) walking_parallel_pair.zero) :=
  is_iso_limit_cone_parallel_pair_of_eq sorry h

/-- An equalizer that is an epimorphism is an isomorphism. -/
def is_iso_limit_cone_parallel_pair_of_epi {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {c : cone (parallel_pair f g)} (h : is_limit c) [epi (nat_trans.app (cone.π c) walking_parallel_pair.zero)] : is_iso (nat_trans.app (cone.π c) walking_parallel_pair.zero) :=
  is_iso_limit_cone_parallel_pair_of_eq sorry h

protected instance has_equalizer_of_self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : has_equalizer f f :=
  has_limit.mk (limit_cone.mk (id_fork rfl) (is_limit_id_fork rfl))

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
protected instance equalizer.ι_of_self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : is_iso (equalizer.ι f f) :=
  equalizer.ι_of_eq sorry

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
def equalizer.iso_source_of_self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : equalizer f f ≅ X :=
  as_iso (equalizer.ι f f)

@[simp] theorem equalizer.iso_source_of_self_hom {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : iso.hom (equalizer.iso_source_of_self f) = equalizer.ι f f :=
  rfl

@[simp] theorem equalizer.iso_source_of_self_inv {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : iso.inv (equalizer.iso_source_of_self f) =
  equalizer.lift 𝟙
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : X ⟶ Y) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ Y) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (𝟙 ≫ f)
            f (category.id_comp f) (𝟙 ≫ f) f (category.id_comp f))
          (propext (eq_self_iff_true f))))
      trivial) :=
  rfl

/--
`has_coequalizer f g` represents a particular choice of colimiting cocone
for the parallel pair of morphisms `f` and `g`.
-/
def has_coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y)  :=
  has_colimit (parallel_pair f g)

/-- If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of such by
    saying `coequalizer f g`. -/
def coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] : C :=
  colimit (parallel_pair f g)

/--  If a coequalizer of `f` and `g` exists, we can access the corresponding projection by
    saying `coequalizer.π f g`. -/
def coequalizer.π {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] : Y ⟶ coequalizer f g :=
  colimit.ι (parallel_pair f g) walking_parallel_pair.one

/--
An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`.
-/
def coequalizer.cofork {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] : cofork f g :=
  colimit.cocone (parallel_pair f g)

@[simp] theorem coequalizer.cofork_π {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] : cofork.π (coequalizer.cofork f g) = coequalizer.π f g :=
  rfl

@[simp] theorem coequalizer.cofork_ι_app_one {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] : nat_trans.app (cocone.ι (coequalizer.cofork f g)) walking_parallel_pair.one = coequalizer.π f g :=
  rfl

theorem coequalizer.condition_assoc {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] {X' : C} (f' : coequalizer f g ⟶ X') : f ≫ coequalizer.π f g ≫ f' = g ≫ coequalizer.π f g ≫ f' := sorry

/-- The cofork built from `coequalizer.π f g` is colimiting. -/
def coequalizer_is_coequalizer {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] : is_colimit (cofork.of_π (coequalizer.π f g) (coequalizer.condition f g)) :=
  is_colimit.of_iso_colimit (colimit.is_colimit (parallel_pair f g))
    (cofork.ext (iso.refl (cocone.X (colimit.cocone (parallel_pair f g)))) sorry)

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequalizer of `f`
    and `g` via `coequalizer.desc : coequalizer f g ⟶ W`. -/
def coequalizer.desc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_coequalizer f g] {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : coequalizer f g ⟶ W :=
  colimit.desc (parallel_pair f g) (cofork.of_π k h)

@[simp] theorem coequalizer.π_desc_assoc {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_coequalizer f g] {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) {X' : C} (f' : W ⟶ X') : coequalizer.π f g ≫ coequalizer.desc k h ≫ f' = k ≫ f' := sorry

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
    `l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`. -/
def coequalizer.desc' {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_coequalizer f g] {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : Subtype fun (l : coequalizer f g ⟶ W) => coequalizer.π f g ≫ l = k :=
  { val := coequalizer.desc k h, property := coequalizer.π_desc k h }

/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
    map -/
theorem coequalizer.hom_ext {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_coequalizer f g] {W : C} {k : coequalizer f g ⟶ W} {l : coequalizer f g ⟶ W} (h : coequalizer.π f g ≫ k = coequalizer.π f g ≫ l) : k = l :=
  cofork.is_colimit.hom_ext (colimit.is_colimit (parallel_pair f g)) h

/-- A coequalizer morphism is an epimorphism -/
protected instance coequalizer.π_epi {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_coequalizer f g] : epi (coequalizer.π f g) :=
  epi.mk
    fun (Z : C) (h k : coequalizer f g ⟶ Z) (w : coequalizer.π f g ≫ h = coequalizer.π f g ≫ k) => coequalizer.hom_ext w

/-- The coequalizer morphism in any colimit cocone is an epimorphism. -/
theorem epi_of_is_colimit_parallel_pair {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {c : cocone (parallel_pair f g)} (i : is_colimit c) : epi (nat_trans.app (cocone.ι c) walking_parallel_pair.one) := sorry

/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/
def id_cofork {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (h : f = g) : cofork f g :=
  cofork.of_π 𝟙 sorry

/-- The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`.  -/
def is_colimit_id_cofork {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (h : f = g) : is_colimit (id_cofork h) :=
  cofork.is_colimit.mk (id_cofork h) (fun (s : cofork f g) => cofork.π s) sorry sorry

/-- Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
def is_iso_colimit_cocone_parallel_pair_of_eq {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} (h₀ : f = g) {c : cocone (parallel_pair f g)} (h : is_colimit c) : is_iso (nat_trans.app (cocone.ι c) walking_parallel_pair.one) :=
  is_iso.of_iso (is_colimit.cocone_point_unique_up_to_iso (is_colimit_id_cofork h₀) h)

/-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
def coequalizer.π_of_eq {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} [has_coequalizer f g] (h : f = g) : is_iso (coequalizer.π f g) :=
  is_iso_colimit_cocone_parallel_pair_of_eq h (colimit.is_colimit (parallel_pair f g))

/-- Every coequalizer of `(f, f)` is an isomorphism. -/
def is_iso_colimit_cocone_parallel_pair_of_self {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {c : cocone (parallel_pair f f)} (h : is_colimit c) : is_iso (nat_trans.app (cocone.ι c) walking_parallel_pair.one) :=
  is_iso_colimit_cocone_parallel_pair_of_eq sorry h

/-- A coequalizer that is a monomorphism is an isomorphism. -/
def is_iso_limit_cocone_parallel_pair_of_epi {C : Type u} [category C] {X : C} {Y : C} {f : X ⟶ Y} {g : X ⟶ Y} {c : cocone (parallel_pair f g)} (h : is_colimit c) [mono (nat_trans.app (cocone.ι c) walking_parallel_pair.one)] : is_iso (nat_trans.app (cocone.ι c) walking_parallel_pair.one) :=
  is_iso_colimit_cocone_parallel_pair_of_eq sorry h

protected instance has_coequalizer_of_self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : has_coequalizer f f :=
  has_colimit.mk (colimit_cocone.mk (id_cofork rfl) (is_colimit_id_cofork rfl))

/-- The coequalizer projection for `(f, f)` is an isomorphism. -/
protected instance coequalizer.π_of_self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : is_iso (coequalizer.π f f) :=
  coequalizer.π_of_eq sorry

/-- The coequalizer of a morphism with itself is isomorphic to the target. -/
def coequalizer.iso_target_of_self {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : coequalizer f f ≅ Y :=
  iso.symm (as_iso (coequalizer.π f f))

@[simp] theorem coequalizer.iso_target_of_self_hom {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : iso.hom (coequalizer.iso_target_of_self f) =
  coequalizer.desc 𝟙
    (eq.mpr
      (id
        (Eq.trans
          ((fun (a a_1 : X ⟶ Y) (e_1 : a = a_1) (ᾰ ᾰ_1 : X ⟶ Y) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (f ≫ 𝟙)
            f (category.comp_id f) (f ≫ 𝟙) f (category.comp_id f))
          (propext (eq_self_iff_true f))))
      trivial) :=
  rfl

@[simp] theorem coequalizer.iso_target_of_self_inv {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) : iso.inv (coequalizer.iso_target_of_self f) = coequalizer.π f f :=
  rfl

/--
The comparison morphism for the equalizer of `f,g`.
This is an isomorphism iff `G` preserves the equalizer of `f,g`; see
`category_theory/limits/preserves/shapes/equalizers.lean`
-/
def equalizer_comparison {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {D : Type u₂} [category D] (G : C ⥤ D) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] : functor.obj G (equalizer f g) ⟶ equalizer (functor.map G f) (functor.map G g) :=
  equalizer.lift (functor.map G (equalizer.ι f g)) sorry

@[simp] theorem equalizer_comparison_comp_π_assoc {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {D : Type u₂} [category D] (G : C ⥤ D) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] {X' : D} (f' : functor.obj G X ⟶ X') : equalizer_comparison f g G ≫ equalizer.ι (functor.map G f) (functor.map G g) ≫ f' = functor.map G (equalizer.ι f g) ≫ f' := sorry

@[simp] theorem map_lift_equalizer_comparison {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {D : Type u₂} [category D] (G : C ⥤ D) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] {Z : C} {h : Z ⟶ X} (w : h ≫ f = h ≫ g) : functor.map G (equalizer.lift h w) ≫ equalizer_comparison f g G =
  equalizer.lift (functor.map G h)
    (eq.mpr
      (id
        ((fun (a a_1 : functor.obj G Z ⟶ functor.obj G Y) (e_1 : a = a_1) (ᾰ ᾰ_1 : functor.obj G Z ⟶ functor.obj G Y)
            (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
          (functor.map G h ≫ functor.map G f) (functor.map G (h ≫ g))
          (Eq.trans (Eq.symm (functor.map_comp G h f))
            ((fun (c : C ⥤ D) {X Y : C} (ᾰ ᾰ_1 : X ⟶ Y) (e_4 : ᾰ = ᾰ_1) => congr_arg (functor.map c) e_4) G (h ≫ f)
              (h ≫ g) w))
          (functor.map G h ≫ functor.map G g) (functor.map G (h ≫ g)) (Eq.symm (functor.map_comp G h g))))
      (Eq.refl (functor.map G (h ≫ g)))) := sorry

/-- The comparison morphism for the coequalizer of `f,g`. -/
def coequalizer_comparison {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {D : Type u₂} [category D] (G : C ⥤ D) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] : coequalizer (functor.map G f) (functor.map G g) ⟶ functor.obj G (coequalizer f g) :=
  coequalizer.desc (functor.map G (coequalizer.π f g)) sorry

@[simp] theorem ι_comp_coequalizer_comparison {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {D : Type u₂} [category D] (G : C ⥤ D) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] : coequalizer.π (functor.map G f) (functor.map G g) ≫ coequalizer_comparison f g G = functor.map G (coequalizer.π f g) :=
  coequalizer.π_desc (functor.map G (coequalizer.π f g)) (coequalizer_comparison._proof_1 f g G)

@[simp] theorem coequalizer_comparison_map_desc_assoc {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) {D : Type u₂} [category D] (G : C ⥤ D) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] {Z : C} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) {X' : D} (f' : functor.obj G Z ⟶ X') : coequalizer_comparison f g G ≫ functor.map G (coequalizer.desc h w) ≫ f' =
  coequalizer.desc (functor.map G h)
      (eq.mpr
        (id
          ((fun (a a_1 : functor.obj G X ⟶ functor.obj G Z) (e_1 : a = a_1) (ᾰ ᾰ_1 : functor.obj G X ⟶ functor.obj G Z)
              (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
            (functor.map G f ≫ functor.map G h) (functor.map G (g ≫ h))
            (Eq.trans (Eq.symm (functor.map_comp G f h))
              ((fun (c : C ⥤ D) {X Y : C} (ᾰ ᾰ_1 : X ⟶ Y) (e_4 : ᾰ = ᾰ_1) => congr_arg (functor.map c) e_4) G (f ≫ h)
                (g ≫ h) w))
            (functor.map G g ≫ functor.map G h) (functor.map G (g ≫ h)) (Eq.symm (functor.map_comp G g h))))
        (Eq.refl (functor.map G (g ≫ h)))) ≫
    f' := sorry

/-- `has_equalizers` represents a choice of equalizer for every pair of morphisms -/
def has_equalizers (C : Type u) [category C]  :=
  has_limits_of_shape walking_parallel_pair C

/-- `has_coequalizers` represents a choice of coequalizer for every pair of morphisms -/
def has_coequalizers (C : Type u) [category C]  :=
  has_colimits_of_shape walking_parallel_pair C

/-- If `C` has all limits of diagrams `parallel_pair f g`, then it has all equalizers -/
theorem has_equalizers_of_has_limit_parallel_pair (C : Type u) [category C] [∀ {X Y : C} {f g : X ⟶ Y}, has_limit (parallel_pair f g)] : has_equalizers C :=
  has_limits_of_shape.mk fun (F : walking_parallel_pair ⥤ C) => has_limit_of_iso (iso.symm (diagram_iso_parallel_pair F))

/-- If `C` has all colimits of diagrams `parallel_pair f g`, then it has all coequalizers -/
theorem has_coequalizers_of_has_colimit_parallel_pair (C : Type u) [category C] [∀ {X Y : C} {f g : X ⟶ Y}, has_colimit (parallel_pair f g)] : has_coequalizers C :=
  has_colimits_of_shape.mk fun (F : walking_parallel_pair ⥤ C) => has_colimit_of_iso (diagram_iso_parallel_pair F)

-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `split_mono_equalizes` that it is a limit cone.
-/
@[simp] theorem cone_of_split_mono_X {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] : cone.X (cone_of_split_mono f) = X :=
  Eq.refl (cone.X (cone_of_split_mono f))

/--
A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
-/
def split_mono_equalizes {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_mono f] : is_limit (cone_of_split_mono f) :=
  fork.is_limit.mk' (cone_of_split_mono f)
    fun (s : fork 𝟙 (retraction f ≫ f)) => { val := fork.ι s ≫ retraction f, property := sorry }

-- In this section we show that a split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `split_epi_coequalizes` that it is a colimit cocone.
-/
def cocone_of_split_epi {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] : cocone (parallel_pair 𝟙 (f ≫ section_ f)) :=
  cofork.of_π f sorry

/--
A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
-/
def split_epi_coequalizes {C : Type u} [category C] {X : C} {Y : C} (f : X ⟶ Y) [split_epi f] : is_colimit (cocone_of_split_epi f) :=
  cofork.is_colimit.mk' (cocone_of_split_epi f)
    fun (s : cofork 𝟙 (f ≫ section_ f)) => { val := section_ f ≫ cofork.π s, property := sorry }

