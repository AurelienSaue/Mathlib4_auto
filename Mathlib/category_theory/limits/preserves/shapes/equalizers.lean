/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.split_coequalizer
import Mathlib.category_theory.limits.preserves.basic
import Mathlib.PostPort

universes u₁ u₂ v 

namespace Mathlib

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizer_comparison G f` is an isomorphism iff `G` preserves
the limit of `f` as well as the dual.
-/

namespace category_theory.limits


/--
The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `fork.of_ι` with `functor.map_cone`.
-/
def is_limit_map_cone_fork_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g) : is_limit (functor.map_cone G (fork.of_ι h w)) ≃
  is_limit (fork.of_ι (functor.map G h) (is_limit_map_cone_fork_equiv._proof_1 G w)) :=
  equiv.trans
    (equiv.symm
      (is_limit.postcompose_hom_equiv (diagram_iso_parallel_pair (parallel_pair f g ⋙ G))
        (functor.map_cone G (fork.of_ι h w))))
    (is_limit.equiv_iso_limit
      (fork.ext
        (iso.refl
          (cone.X
            (functor.obj (cones.postcompose (iso.hom (diagram_iso_parallel_pair (parallel_pair f g ⋙ G))))
              (functor.map_cone G (fork.of_ι h w)))))
        sorry))

/-- The property of preserving equalizers expressed in terms of forks. -/
def is_limit_fork_map_of_is_limit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g) [preserves_limit (parallel_pair f g) G] (l : is_limit (fork.of_ι h w)) : is_limit (fork.of_ι (functor.map G h) (is_limit_map_cone_fork_equiv._proof_1 G w)) :=
  coe_fn (is_limit_map_cone_fork_equiv G w) (preserves_limit.preserves l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
def is_limit_of_is_limit_fork_map {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g) [reflects_limit (parallel_pair f g) G] (l : is_limit (fork.of_ι (functor.map G h) (is_limit_of_is_limit_fork_map._proof_1 G w))) : is_limit (fork.of_ι h w) :=
  reflects_limit.reflects (coe_fn (equiv.symm (is_limit_map_cone_fork_equiv G w)) l)

/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
def is_limit_of_has_equalizer_of_preserves_limit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] [preserves_limit (parallel_pair f g) G] : is_limit (fork.of_ι (functor.map G (equalizer.ι f g)) (is_limit_of_has_equalizer_of_preserves_limit._proof_1 G f g)) :=
  is_limit_fork_map_of_is_limit G (equalizer.condition f g) (equalizer_is_equalizer f g)

/--
If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
def preserves_equalizer.of_iso_comparison {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] [i : is_iso (equalizer_comparison f g G)] : preserves_limit (parallel_pair f g) G :=
  preserves_limit_of_preserves_limit_cone (equalizer_is_equalizer f g)
    (coe_fn (equiv.symm (is_limit_map_cone_fork_equiv G (equalizer.condition f g)))
      (is_limit.of_point_iso (limit.is_limit (parallel_pair (functor.map G f) (functor.map G g)))))

/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
def preserves_equalizer.iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] [preserves_limit (parallel_pair f g) G] : functor.obj G (equalizer f g) ≅ equalizer (functor.map G f) (functor.map G g) :=
  is_limit.cone_point_unique_up_to_iso (is_limit_of_has_equalizer_of_preserves_limit G f g)
    (limit.is_limit (parallel_pair (functor.map G f) (functor.map G g)))

@[simp] theorem preserves_equalizer.iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] [preserves_limit (parallel_pair f g) G] : iso.hom (preserves_equalizer.iso G f g) = equalizer_comparison f g G :=
  rfl

protected instance equalizer_comparison.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_equalizer f g] [has_equalizer (functor.map G f) (functor.map G g)] [preserves_limit (parallel_pair f g) G] : is_iso (equalizer_comparison f g G) :=
  eq.mpr sorry (is_iso.of_iso (preserves_equalizer.iso G f g))

/--
The map of a cofork is a colimit iff the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `cofork.of_π` with `functor.map_cocone`.
-/
def is_colimit_map_cocone_cofork_equiv {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) : is_colimit (functor.map_cocone G (cofork.of_π h w)) ≃
  is_colimit (cofork.of_π (functor.map G h) (is_colimit_map_cocone_cofork_equiv._proof_1 G w)) :=
  equiv.trans
    (equiv.symm
      (is_colimit.precompose_inv_equiv (diagram_iso_parallel_pair (parallel_pair f g ⋙ G))
        (functor.map_cocone G (cofork.of_π h w))))
    (is_colimit.equiv_iso_colimit
      (cofork.ext
        (iso.refl
          (cocone.X
            (functor.obj (cocones.precompose (iso.inv (diagram_iso_parallel_pair (parallel_pair f g ⋙ G))))
              (functor.map_cocone G (cofork.of_π h w)))))
        sorry))

/-- The property of preserving coequalizers expressed in terms of coforks. -/
def is_colimit_cofork_map_of_is_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) [preserves_colimit (parallel_pair f g) G] (l : is_colimit (cofork.of_π h w)) : is_colimit (cofork.of_π (functor.map G h) (is_colimit_map_cocone_cofork_equiv._proof_1 G w)) :=
  coe_fn (is_colimit_map_cocone_cofork_equiv G w) (preserves_colimit.preserves l)

/-- The property of reflecting coequalizers expressed in terms of coforks. -/
def is_colimit_of_is_colimit_cofork_map {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} {Z : C} {f : X ⟶ Y} {g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h) [reflects_colimit (parallel_pair f g) G] (l : is_colimit (cofork.of_π (functor.map G h) (is_colimit_of_is_colimit_cofork_map._proof_1 G w))) : is_colimit (cofork.of_π h w) :=
  reflects_colimit.reflects (coe_fn (equiv.symm (is_colimit_map_cocone_cofork_equiv G w)) l)

/--
If `G` preserves coequalizers and `C` has them, then the cofork constructed of the mapped morphisms
of a cofork is a colimit.
-/
def is_colimit_of_has_coequalizer_of_preserves_colimit {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] [preserves_colimit (parallel_pair f g) G] : is_colimit
  (cofork.of_π (functor.map G (coequalizer.π f g)) (is_colimit_of_has_coequalizer_of_preserves_colimit._proof_1 G f g)) :=
  is_colimit_cofork_map_of_is_colimit G (coequalizer.condition f g) (coequalizer_is_coequalizer f g)

/--
If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
coequalizer of `(f,g)`.
-/
def of_iso_comparison {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] [i : is_iso (coequalizer_comparison f g G)] : preserves_colimit (parallel_pair f g) G :=
  preserves_colimit_of_preserves_colimit_cocone (coequalizer_is_coequalizer f g)
    (coe_fn (equiv.symm (is_colimit_map_cocone_cofork_equiv G (coequalizer.condition f g)))
      (is_colimit.of_point_iso (colimit.is_colimit (parallel_pair (functor.map G f) (functor.map G g)))))

/--
If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map for `G` at `(f,g)`
is an isomorphism.
-/
def preserves_coequalizer.iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] [preserves_colimit (parallel_pair f g) G] : coequalizer (functor.map G f) (functor.map G g) ≅ functor.obj G (coequalizer f g) :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit (parallel_pair (functor.map G f) (functor.map G g)))
    (is_colimit_of_has_coequalizer_of_preserves_colimit G f g)

@[simp] theorem preserves_coequalizer.iso_hom {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] [preserves_colimit (parallel_pair f g) G] : iso.hom (preserves_coequalizer.iso G f g) = coequalizer_comparison f g G :=
  rfl

protected instance coequalizer_comparison.category_theory.is_iso {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_coequalizer f g] [has_coequalizer (functor.map G f) (functor.map G g)] [preserves_colimit (parallel_pair f g) G] : is_iso (coequalizer_comparison f g G) :=
  eq.mpr sorry (is_iso.of_iso (preserves_coequalizer.iso G f g))

/-- Any functor preserves coequalizers of split pairs. -/
protected instance preserves_split_coequalizers {C : Type u₁} [category C] {D : Type u₂} [category D] (G : C ⥤ D) {X : C} {Y : C} (f : X ⟶ Y) (g : X ⟶ Y) [has_split_coequalizer f g] : preserves_colimit (parallel_pair f g) G :=
  preserves_colimit_of_preserves_colimit_cocone
    (is_split_coequalizer.is_coequalizer (has_split_coequalizer.is_split_coequalizer f g))
    (coe_fn (equiv.symm (is_colimit_map_cocone_cofork_equiv G sorry))
      (is_split_coequalizer.is_coequalizer (is_split_coequalizer.map (has_split_coequalizer.is_split_coequalizer f g) G)))

