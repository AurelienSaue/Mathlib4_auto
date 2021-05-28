/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.limits
import Mathlib.category_theory.products.basic
import Mathlib.category_theory.currying
import Mathlib.PostPort

universes v u l 

namespace Mathlib

/-!
# A Fubini theorem for categorical limits

We prove that $lim_{J × K} G = lim_J (lim_K G(j, -))$ for a functor `G : J × K ⥤ C`,
when all the appropriate limits exist.

We begin working with a functor `F : J ⥤ K ⥤ C`. We'll write `G : J × K ⥤ C` for the associated
"uncurried" functor.

In the first part, given a coherent family `D` of limit cones over the functors `F.obj j`,
and a cone `c` over `G`, we construct a cone over the cone points of `D`.
We then show that if `c` is a limit cone, the constructed cone is also a limit cone.

In the second part, we state the Fubini theorem in the setting where limits are
provided by suitable `has_limit` classes.

We construct
`limit_uncurry_iso_limit_comp_lim F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`
and give simp lemmas characterising it.
For convenience, we also provide
`limit_iso_limit_curry_comp_lim G : limit G ≅ limit ((curry.obj G) ⋙ lim)`
in terms of the uncurried functor.

## Future work

The dual statement.
-/

namespace category_theory.limits


/--
A structure carrying a diagram of cones over the the functors `F.obj j`.
-/
-- We could try introducing a "dependent functor type" to handle this?

structure diagram_of_cones {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) 
where
  obj : (j : J) → cone (functor.obj F j)
  map : {j j' : J} → (f : j ⟶ j') → functor.obj (cones.postcompose (functor.map F f)) (obj j) ⟶ obj j'
  id : autoParam (J → cone_morphism.hom (map 𝟙) = 𝟙)
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])
  comp : autoParam
  (∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
    cone_morphism.hom (map (f ≫ g)) = cone_morphism.hom (map f) ≫ cone_morphism.hom (map g))
  (Lean.Syntax.ident Lean.SourceInfo.none (String.toSubstring "Mathlib.obviously")
    (Lean.Name.mkStr (Lean.Name.mkStr Lean.Name.anonymous "Mathlib") "obviously") [])

/--
Extract the functor `J ⥤ C` consisting of the cone points and the maps between them,
from a `diagram_of_cones`.
-/
@[simp] theorem diagram_of_cones.cone_points_obj {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ K ⥤ C} (D : diagram_of_cones F) (j : J) : functor.obj (diagram_of_cones.cone_points D) j = cone.X (diagram_of_cones.obj D j) :=
  Eq.refl (functor.obj (diagram_of_cones.cone_points D) j)

/--
Given a diagram `D` of limit cones over the `F.obj j`, and a cone over `uncurry.obj F`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
def cone_of_cone_uncurry {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ K ⥤ C} {D : diagram_of_cones F} (Q : (j : J) → is_limit (diagram_of_cones.obj D j)) (c : cone (functor.obj uncurry F)) : cone (diagram_of_cones.cone_points D) :=
  cone.mk (cone.X c)
    (nat_trans.mk
      fun (j : J) =>
        is_limit.lift (Q j) (cone.mk (cone.X c) (nat_trans.mk fun (k : K) => nat_trans.app (cone.π c) (j, k))))

/--
`cone_of_cone_uncurry Q c` is a limit cone when `c` is a limit cone.`
-/
def cone_of_cone_uncurry_is_limit {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] {F : J ⥤ K ⥤ C} {D : diagram_of_cones F} (Q : (j : J) → is_limit (diagram_of_cones.obj D j)) {c : cone (functor.obj uncurry F)} (P : is_limit c) : is_limit (cone_of_cone_uncurry Q c) :=
  is_limit.mk
    fun (s : cone (diagram_of_cones.cone_points D)) =>
      is_limit.lift P
        (cone.mk (cone.X s)
          (nat_trans.mk
            fun (p : J × K) =>
              nat_trans.app (cone.π s) (prod.fst p) ≫
                nat_trans.app (cone.π (diagram_of_cones.obj D (prod.fst p))) (prod.snd p)))

/--
Given a functor `F : J ⥤ K ⥤ C`, with all needed limits,
we can construct a diagram consisting of the limit cone over each functor `F.obj j`,
and the universal cone morphisms between these.
-/
def diagram_of_cones.mk_of_has_limits {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) [has_limits_of_shape K C] : diagram_of_cones F :=
  diagram_of_cones.mk (fun (j : J) => limit.cone (functor.obj F j))
    fun (j j' : J) (f : j ⟶ j') => cone_morphism.mk (functor.map lim (functor.map F f))

-- Satisfying the inhabited linter.

protected instance diagram_of_cones_inhabited {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) [has_limits_of_shape K C] : Inhabited (diagram_of_cones F) :=
  { default := diagram_of_cones.mk_of_has_limits F }

@[simp] theorem diagram_of_cones.mk_of_has_limits_cone_points {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) [has_limits_of_shape K C] : diagram_of_cones.cone_points (diagram_of_cones.mk_of_has_limits F) = F ⋙ lim :=
  rfl

/--
The Fubini theorem for a functor `F : J ⥤ K ⥤ C`,
showing that the limit of `uncurry.obj F` can be computed as
the limit of the limits of the functors `F.obj j`.
-/
def limit_uncurry_iso_limit_comp_lim {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) [has_limits_of_shape K C] [has_limit (functor.obj uncurry F)] [has_limit (F ⋙ lim)] : limit (functor.obj uncurry F) ≅ limit (F ⋙ lim) :=
  let c : cone (functor.obj uncurry F) := limit.cone (functor.obj uncurry F);
  let P : is_limit c := limit.is_limit (functor.obj uncurry F);
  let G : diagram_of_cones F := diagram_of_cones.mk_of_has_limits F;
  let Q : (j : J) → is_limit (diagram_of_cones.obj G j) := fun (j : J) => limit.is_limit (functor.obj F j);
  is_limit.cone_point_unique_up_to_iso (cone_of_cone_uncurry_is_limit Q P) (limit.is_limit (F ⋙ lim))

@[simp] theorem limit_uncurry_iso_limit_comp_lim_hom_π_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) [has_limits_of_shape K C] [has_limit (functor.obj uncurry F)] [has_limit (F ⋙ lim)] {j : J} {k : K} : iso.hom (limit_uncurry_iso_limit_comp_lim F) ≫ limit.π (F ⋙ lim) j ≫ limit.π (functor.obj F j) k =
  limit.π (functor.obj uncurry F) (j, k) := sorry

@[simp] theorem limit_uncurry_iso_limit_comp_lim_inv_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (F : J ⥤ K ⥤ C) [has_limits_of_shape K C] [has_limit (functor.obj uncurry F)] [has_limit (F ⋙ lim)] {j : J} {k : K} : iso.inv (limit_uncurry_iso_limit_comp_lim F) ≫ limit.π (functor.obj uncurry F) (j, k) =
  limit.π (F ⋙ lim) j ≫ limit.π (functor.obj F j) k := sorry

/--
The Fubini theorem for a functor `G : J × K ⥤ C`,
showing that the limit of `G` can be computed as
the limit of the limits of the functors `G.obj (j, _)`.
-/
def limit_iso_limit_curry_comp_lim {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (G : J × K ⥤ C) [has_limits_of_shape K C] [has_limit G] [has_limit (functor.obj curry G ⋙ lim)] : limit G ≅ limit (functor.obj curry G ⋙ lim) :=
  has_limit.iso_of_nat_iso (iso.app (equivalence.unit_iso (equivalence.symm currying)) G) ≪≫
    limit_uncurry_iso_limit_comp_lim (functor.obj curry G)

@[simp] theorem limit_iso_limit_curry_comp_lim_hom_π_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (G : J × K ⥤ C) [has_limits_of_shape K C] [has_limit G] [has_limit (functor.obj curry G ⋙ lim)] {j : J} {k : K} : iso.hom (limit_iso_limit_curry_comp_lim G) ≫
    limit.π (functor.obj curry G ⋙ lim) j ≫ limit.π (functor.obj (functor.obj curry G) j) k =
  limit.π G (j, k) := sorry

@[simp] theorem limit_iso_limit_curry_comp_lim_inv_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (G : J × K ⥤ C) [has_limits_of_shape K C] [has_limit G] [has_limit (functor.obj curry G ⋙ lim)] {j : J} {k : K} : iso.inv (limit_iso_limit_curry_comp_lim G) ≫ limit.π G (j, k) =
  limit.π (functor.obj curry G ⋙ lim) j ≫ limit.π (functor.obj (functor.obj curry G) j) k := sorry

/--
A variant of the Fubini theorem for a functor `G : J × K ⥤ C`,
showing that $\lim_k \lim_j G(j,k) ≅ \lim_j \lim_k G(j,k)$.
-/
def limit_curry_swap_comp_lim_iso_limit_curry_comp_lim {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (G : J × K ⥤ C) [has_limits C] : limit (functor.obj curry (prod.swap K J ⋙ G) ⋙ lim) ≅ limit (functor.obj curry G ⋙ lim) :=
  (iso.symm (limit_iso_limit_curry_comp_lim (prod.swap K J ⋙ G)) ≪≫
      has_limit.iso_of_equivalence (prod.braiding K J) (iso.refl (equivalence.functor (prod.braiding K J) ⋙ G))) ≪≫
    limit_iso_limit_curry_comp_lim G

@[simp] theorem limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_hom_π_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (G : J × K ⥤ C) [has_limits C] {j : J} {k : K} : iso.hom (limit_curry_swap_comp_lim_iso_limit_curry_comp_lim G) ≫
    limit.π (functor.obj curry G ⋙ lim) j ≫ limit.π (functor.obj (functor.obj curry G) j) k =
  limit.π (functor.obj curry (prod.swap K J ⋙ G) ⋙ lim) k ≫
    limit.π (functor.obj (functor.obj curry (prod.swap K J ⋙ G)) k) j := sorry

@[simp] theorem limit_curry_swap_comp_lim_iso_limit_curry_comp_lim_inv_π_π {J : Type v} {K : Type v} [small_category J] [small_category K] {C : Type u} [category C] (G : J × K ⥤ C) [has_limits C] {j : J} {k : K} : iso.inv (limit_curry_swap_comp_lim_iso_limit_curry_comp_lim G) ≫
    limit.π (functor.obj curry (prod.swap K J ⋙ G) ⋙ lim) k ≫
      limit.π (functor.obj (functor.obj curry (prod.swap K J ⋙ G)) k) j =
  limit.π (functor.obj curry G ⋙ lim) j ≫ limit.π (functor.obj (functor.obj curry G) j) k := sorry

