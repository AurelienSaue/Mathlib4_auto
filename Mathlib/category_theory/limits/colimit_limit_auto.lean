/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.types
import Mathlib.category_theory.currying
import Mathlib.PostPort

universes v u 

namespace Mathlib

/-!
# The morphism comparing a colimit of limits with the corresponding limit of colimits.

For `F : J × K ⥤ C` there is always a morphism $\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
While it is not usually an isomorphism, with additional hypotheses on `J` and `K` it may be,
in which case we say that "colimits commute with limits".

The prototypical example, proved in `category_theory.limits.filtered_colimit_commutes_finite_limit`,
is that when `C = Type`, filtered colimits commute with finite limits.

## References
* Borceux, Handbook of categorical algebra 1, Section 2.13
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/

namespace category_theory.limits


theorem map_id_left_eq_curry_map {J : Type v} {K : Type v} [small_category J] [small_category K]
    {C : Type u} [category C] (F : J × K ⥤ C) {j : J} {k : K} {k' : K} {f : k ⟶ k'} :
    functor.map F (𝟙, f) = functor.map (functor.obj (functor.obj curry F) j) f :=
  rfl

theorem map_id_right_eq_curry_swap_map {J : Type v} {K : Type v} [small_category J]
    [small_category K] {C : Type u} [category C] (F : J × K ⥤ C) {j : J} {j' : J} {f : j ⟶ j'}
    {k : K} :
    functor.map F (f, 𝟙) = functor.map (functor.obj (functor.obj curry (prod.swap K J ⋙ F)) k) f :=
  rfl

/--
The universal morphism
$\colim_k \lim_j F(j,k) → \lim_j \colim_k F(j, k)$.
-/
def colimit_limit_to_limit_colimit {J : Type v} {K : Type v} [small_category J] [small_category K]
    {C : Type u} [category C] (F : J × K ⥤ C) [has_limits_of_shape J C]
    [has_colimits_of_shape K C] :
    colimit (functor.obj curry (prod.swap K J ⋙ F) ⋙ lim) ⟶ limit (functor.obj curry F ⋙ colim) :=
  limit.lift (functor.obj curry F ⋙ colim)
    (cone.mk (cocone.X (colimit.cocone (functor.obj curry (prod.swap K J ⋙ F) ⋙ lim)))
      (nat_trans.mk
        fun (j : J) =>
          colimit.desc (functor.obj curry (prod.swap K J ⋙ F) ⋙ lim)
            (cocone.mk (cocone.X (colimit.cocone (functor.obj (functor.obj curry F) j)))
              (nat_trans.mk
                fun (k : K) =>
                  limit.π (functor.obj (functor.obj curry (prod.swap K J ⋙ F)) k) j ≫
                    colimit.ι (functor.obj (functor.obj curry F) j) k))))

/--
Since `colimit_limit_to_limit_colimit` is a morphism from a colimit to a limit,
this lemma characterises it.
-/
@[simp] theorem ι_colimit_limit_to_limit_colimit_π {J : Type v} {K : Type v} [small_category J]
    [small_category K] {C : Type u} [category C] (F : J × K ⥤ C) [has_limits_of_shape J C]
    [has_colimits_of_shape K C] (j : J) (k : K) :
    colimit.ι (functor.obj curry (prod.swap K J ⋙ F) ⋙ lim) k ≫
          colimit_limit_to_limit_colimit F ≫ limit.π (functor.obj curry F ⋙ colim) j =
        limit.π (functor.obj (functor.obj curry (prod.swap K J ⋙ F)) k) j ≫
          colimit.ι (functor.obj (functor.obj curry F) j) k :=
  sorry

@[simp] theorem ι_colimit_limit_to_limit_colimit_π_apply {J : Type v} {K : Type v}
    [small_category J] [small_category K] (F : J × K ⥤ Type v) (j : J) (k : K)
    (f : functor.obj (functor.obj curry (prod.swap K J ⋙ F) ⋙ lim) k) :
    limit.π (functor.obj curry F ⋙ colim) j
          (colimit_limit_to_limit_colimit F
            (colimit.ι (functor.obj curry (prod.swap K J ⋙ F) ⋙ lim) k f)) =
        colimit.ι (functor.obj (functor.obj curry F) j) k
          (limit.π (functor.obj (functor.obj curry (prod.swap K J ⋙ F)) k) j f) :=
  sorry

end Mathlib