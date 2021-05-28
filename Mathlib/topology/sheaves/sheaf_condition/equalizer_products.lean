/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.sheaves.presheaf
import Mathlib.category_theory.limits.punit
import Mathlib.category_theory.limits.shapes.products
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.full_subcategory
import Mathlib.PostPort

universes u v 

namespace Mathlib

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ F.obj (U i)` and `∏ F.obj (U i) ⊓ (U j)`.

-/

namespace Top


namespace presheaf


namespace sheaf_condition_equalizer_products


/-- The product of the sections of a presheaf over a family of open sets. -/
/--
def pi_opens {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : C :=
  ∏ fun (i : ι) => category_theory.functor.obj F (opposite.op (U i))

The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def pi_inters {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : C :=
  ∏ fun (p : ι × ι) => category_theory.functor.obj F (opposite.op (U (prod.fst p) ⊓ U (prod.snd p)))

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def left_res {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : pi_opens F U ⟶ pi_inters F U :=
  category_theory.limits.pi.lift
    fun (p : ι × ι) =>
      category_theory.limits.pi.π (fun (i : ι) => category_theory.functor.obj F (opposite.op (U i))) (prod.fst p) ≫
        category_theory.functor.map F
          (category_theory.has_hom.hom.op (topological_space.opens.inf_le_left (U (prod.fst p)) (U (prod.snd p))))

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def right_res {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : pi_opens F U ⟶ pi_inters F U :=
  category_theory.limits.pi.lift
    fun (p : ι × ι) =>
      category_theory.limits.pi.π (fun (i : ι) => category_theory.functor.obj F (opposite.op (U i))) (prod.snd p) ≫
        category_theory.functor.map F
          (category_theory.has_hom.hom.op (topological_space.opens.inf_le_right (U (prod.fst p)) (U (prod.snd p))))

/--
The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.functor.obj F (opposite.op (supr U)) ⟶ pi_opens F U :=
  category_theory.limits.pi.lift
    fun (i : ι) => category_theory.functor.map F (category_theory.has_hom.hom.op (topological_space.opens.le_supr U i))

theorem w {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : res F U ≫ left_res F U = res F U ≫ right_res F U := sorry

/--
The equalizer diagram for the sheaf condition.
-/
def diagram {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.walking_parallel_pair ⥤ C :=
  category_theory.limits.parallel_pair (left_res F U) (right_res F U)

/--
The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.fork (left_res F U) (right_res F U) :=
  category_theory.limits.fork.of_ι (res F U) sorry

@[simp] theorem fork_X {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.cone.X (fork F U) = category_theory.functor.obj F (opposite.op (supr U)) :=
  rfl

@[simp] theorem fork_ι {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.limits.fork.ι (fork F U) = res F U :=
  rfl

@[simp] theorem fork_π_app_walking_parallel_pair_zero {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.nat_trans.app (category_theory.limits.cone.π (fork F U))
    category_theory.limits.walking_parallel_pair.zero =
  res F U :=
  rfl

@[simp] theorem fork_π_app_walking_parallel_pair_one {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} (F : presheaf C X) {ι : Type v} (U : ι → topological_space.opens ↥X) : category_theory.nat_trans.app (category_theory.limits.cone.π (fork F U))
    category_theory.limits.walking_parallel_pair.one =
  res F U ≫ left_res F U :=
  rfl

/-- Isomorphic presheaves have isomorphic `pi_opens` for any cover `U`. -/
@[simp] def pi_opens.iso_of_iso {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} (U : ι → topological_space.opens ↥X) {G : presheaf C X} (α : F ≅ G) : pi_opens F U ≅ pi_opens G U :=
  category_theory.limits.pi.map_iso fun (X_1 : ι) => category_theory.iso.app α (opposite.op (U X_1))

/-- Isomorphic presheaves have isomorphic `pi_inters` for any cover `U`. -/
@[simp] def pi_inters.iso_of_iso {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} (U : ι → topological_space.opens ↥X) {G : presheaf C X} (α : F ≅ G) : pi_inters F U ≅ pi_inters G U :=
  category_theory.limits.pi.map_iso
    fun (X_1 : ι × ι) => category_theory.iso.app α (opposite.op (U (prod.fst X_1) ⊓ U (prod.snd X_1)))

/-- Isomorphic presheaves have isomorphic sheaf condition diagrams. -/
def diagram.iso_of_iso {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} (U : ι → topological_space.opens ↥X) {G : presheaf C X} (α : F ≅ G) : diagram F U ≅ diagram G U :=
  category_theory.nat_iso.of_components
    (fun (X_1 : category_theory.limits.walking_parallel_pair) =>
      category_theory.limits.walking_parallel_pair.cases_on X_1 (pi_opens.iso_of_iso U α) (pi_inters.iso_of_iso U α))
    sorry

/--
If `F G : presheaf C X` are isomorphic presheaves,
then the `fork F U`, the canonical cone of the sheaf condition diagram for `F`,
is isomorphic to `fork F G` postcomposed with the corresponding isomorphism between
sheaf condition diagrams.
-/
def fork.iso_of_iso {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} (U : ι → topological_space.opens ↥X) {G : presheaf C X} (α : F ≅ G) : fork F U ≅
  category_theory.functor.obj
    (category_theory.limits.cones.postcompose (category_theory.iso.inv (diagram.iso_of_iso U α))) (fork G U) :=
  category_theory.limits.fork.ext (category_theory.iso.app α (opposite.op (supr U))) sorry

/--
Push forward a cover along an open embedding.
-/
@[simp] def cover.of_open_embedding {X : Top} {ι : Type v} {V : Top} {j : V ⟶ X} (oe : open_embedding ⇑j) (𝒰 : ι → topological_space.opens ↥V) : ι → topological_space.opens ↥X :=
  fun (i : ι) => category_theory.functor.obj (is_open_map.functor sorry) (𝒰 i)

/--
The isomorphism between `pi_opens` corresponding to an open embedding.
-/
@[simp] def pi_opens.iso_of_open_embedding {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} {V : Top} {j : V ⟶ X} (oe : open_embedding ⇑j) (𝒰 : ι → topological_space.opens ↥V) : pi_opens (category_theory.functor.op (is_open_map.functor (pi_opens.iso_of_open_embedding._proof_2 oe)) ⋙ F) 𝒰 ≅
  pi_opens F (cover.of_open_embedding oe 𝒰) :=
  category_theory.limits.pi.map_iso
    fun (X_1 : ι) =>
      category_theory.functor.map_iso F
        (category_theory.iso.refl
          (category_theory.functor.obj (category_theory.functor.op (is_open_map.functor sorry)) (opposite.op (𝒰 X_1))))

/--
The isomorphism between `pi_inters` corresponding to an open embedding.
-/
@[simp] def pi_inters.iso_of_open_embedding {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} {V : Top} {j : V ⟶ X} (oe : open_embedding ⇑j) (𝒰 : ι → topological_space.opens ↥V) : pi_inters (category_theory.functor.op (is_open_map.functor (pi_inters.iso_of_open_embedding._proof_2 oe)) ⋙ F) 𝒰 ≅
  pi_inters F (cover.of_open_embedding oe 𝒰) :=
  category_theory.limits.pi.map_iso
    fun (X_1 : ι × ι) =>
      category_theory.functor.map_iso F
        (id
          (category_theory.iso.op
            (category_theory.iso.mk (category_theory.hom_of_le sorry) (category_theory.hom_of_le sorry))))

/-- The isomorphism of sheaf condition diagrams corresponding to an open embedding. -/
def diagram.iso_of_open_embedding {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} {V : Top} {j : V ⟶ X} (oe : open_embedding ⇑j) (𝒰 : ι → topological_space.opens ↥V) : diagram (category_theory.functor.op (is_open_map.functor (diagram.iso_of_open_embedding._proof_2 oe)) ⋙ F) 𝒰 ≅
  diagram F (cover.of_open_embedding oe 𝒰) :=
  category_theory.nat_iso.of_components
    (fun (X_1 : category_theory.limits.walking_parallel_pair) =>
      category_theory.limits.walking_parallel_pair.cases_on X_1 (pi_opens.iso_of_open_embedding oe 𝒰)
        (pi_inters.iso_of_open_embedding oe 𝒰))
    sorry

/--
If `F : presheaf C X` is a presheaf, and `oe : U ⟶ X` is an open embedding,
then the sheaf condition fork for a cover `𝒰` in `U` for the composition of `oe` and `F` is
isomorphic to sheaf condition fork for `oe '' 𝒰`, precomposed with the isomorphism
of indexing diagrams `diagram.iso_of_open_embedding`.

We use this to show that the restriction of sheaf along an open embedding is still a sheaf.
-/
def fork.iso_of_open_embedding {C : Type u} [category_theory.category C] [category_theory.limits.has_products C] {X : Top} {F : presheaf C X} {ι : Type v} {V : Top} {j : V ⟶ X} (oe : open_embedding ⇑j) (𝒰 : ι → topological_space.opens ↥V) : fork (category_theory.functor.op (is_open_map.functor (fork.iso_of_open_embedding._proof_2 oe)) ⋙ F) 𝒰 ≅
  category_theory.functor.obj
    (category_theory.limits.cones.postcompose (category_theory.iso.inv (diagram.iso_of_open_embedding oe 𝒰)))
    (fork F (cover.of_open_embedding oe 𝒰)) :=
  category_theory.limits.fork.ext
    (id
      (category_theory.functor.map_iso F
        (category_theory.iso.op
          (category_theory.iso.mk (category_theory.hom_of_le sorry) (category_theory.hom_of_le sorry)))))
    sorry

