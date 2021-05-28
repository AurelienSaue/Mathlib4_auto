/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.PostPort

universes u₁ u₂ v 

namespace Mathlib

/-!
# Preserving pullbacks

Constructions to relate the notions of preserving pullbacks and reflecting pullbacks to concrete
pullback cones.

In particular, we show that `pullback_comparison G f g` is an isomorphism iff `G` preserves
the pullback of `f` and `g`.

## TODO

* Dualise to pushouts
* Generalise to wide pullbacks

-/

namespace category_theory.limits


/--
The map of a pullback cone is a limit iff the fork consisting of the mapped morphisms is a limit.
This essentially lets us commute `pullback_cone.mk` with `functor.map_cone`.
-/
def is_limit_map_cone_pullback_cone_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g) : is_limit (functor.map_cone G (pullback_cone.mk h k comm)) ≃
  is_limit
    (pullback_cone.mk (functor.map G h) (functor.map G k) (is_limit_map_cone_pullback_cone_equiv._proof_1 G comm)) :=
  equiv.trans
    (equiv.symm
      (is_limit.postcompose_hom_equiv (diagram_iso_cospan (cospan f g ⋙ G))
        (functor.map_cone G (pullback_cone.mk h k comm))))
    (is_limit.equiv_iso_limit
      (cones.ext
        (iso.refl
          (cone.X
            (functor.obj (cones.postcompose (iso.hom (diagram_iso_cospan (cospan f g ⋙ G))))
              (functor.map_cone G (pullback_cone.mk h k comm)))))
        sorry))

/-- The property of preserving pullbacks expressed in terms of binary fans. -/
def is_limit_pullback_cone_map_of_is_limit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g) [preserves_limit (cospan f g) G] (l : is_limit (pullback_cone.mk h k comm)) : is_limit (pullback_cone.mk (functor.map G h) (functor.map G k) (is_limit_map_cone_pullback_cone_equiv._proof_1 G comm)) :=
  coe_fn (is_limit_map_cone_pullback_cone_equiv G comm) (preserves_limit.preserves l)

/-- The property of reflecting pullbacks expressed in terms of binary fans. -/
def is_limit_of_is_limit_pullback_cone_map {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {W : C} {X : C} {Y : C} {Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : W ⟶ X} {k : W ⟶ Y} (comm : h ≫ f = k ≫ g) [reflects_limit (cospan f g) G] (l : is_limit (pullback_cone.mk (functor.map G h) (functor.map G k) (is_limit_map_cone_pullback_cone_equiv._proof_1 G comm))) : is_limit (pullback_cone.mk h k comm) :=
  reflects_limit.reflects (coe_fn (equiv.symm (is_limit_map_cone_pullback_cone_equiv G comm)) l)

/--
If `G` preserves pullbacks and `C` has them, then the pullback cone constructed of the mapped
morphisms of the pullback cone is a limit.
-/
def is_limit_of_has_pullback_of_preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [preserves_limit (cospan f g) G] : is_limit
  (pullback_cone.mk (functor.map G pullback.fst) (functor.map G pullback.snd)
    (is_limit_of_has_pullback_of_preserves_limit._proof_1 G f g)) :=
  is_limit_pullback_cone_map_of_is_limit G pullback.condition (pullback_is_pullback f g)

/--
If the pullback comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
pullback of `(f,g)`.
-/
def preserves_pullback.of_iso_comparison {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] [i : is_iso (pullback_comparison G f g)] : preserves_limit (cospan f g) G :=
  preserves_limit_of_preserves_limit_cone (pullback_is_pullback f g)
    (coe_fn (equiv.symm (is_limit_map_cone_pullback_cone_equiv G pullback.condition))
      (is_limit.of_point_iso (limit.is_limit (cospan (functor.map G f) (functor.map G g)))))

/--
If `G` preserves the pullback of `(f,g)`, then the pullback comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def preserves_pullback.iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] [preserves_limit (cospan f g) G] : functor.obj G (pullback f g) ≅ pullback (functor.map G f) (functor.map G g) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_pullback_of_preserves_limit G f g)
    (limit.is_limit (cospan (functor.map G f) (functor.map G g)))

@[simp] theorem preserves_pullback.iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] [preserves_limit (cospan f g) G] : iso.hom (preserves_pullback.iso G f g) = pullback_comparison G f g :=
  rfl

protected instance pullback_comparison.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [has_pullback f g] [has_pullback (functor.map G f) (functor.map G g)] [preserves_limit (cospan f g) G] : is_iso (pullback_comparison G f g) :=
  eq.mpr sorry (is_iso.of_iso (preserves_pullback.iso G f g))

