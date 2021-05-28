/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.category_theory.limits.shapes.equalizers
import Mathlib.category_theory.limits.shapes.binary_products
import Mathlib.category_theory.limits.shapes.pullbacks
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: provide the dual result.
-/

namespace category_theory.limits


-- We hide the "implementation details" inside a namespace

namespace has_equalizers_of_pullbacks_and_binary_products


/-- Define the equalizing object -/
def construct_equalizer {C : Type u} [category C] [has_binary_products C] [has_pullbacks C] (F : walking_parallel_pair ⥤ C) : C :=
  pullback (prod.lift 𝟙 (functor.map F walking_parallel_pair_hom.left))
    (prod.lift 𝟙 (functor.map F walking_parallel_pair_hom.right))

/-- Define the equalizing morphism -/
def pullback_fst {C : Type u} [category C] [has_binary_products C] [has_pullbacks C] (F : walking_parallel_pair ⥤ C) : construct_equalizer F ⟶ functor.obj F walking_parallel_pair.zero :=
  pullback.fst

theorem pullback_fst_eq_pullback_snd {C : Type u} [category C] [has_binary_products C] [has_pullbacks C] (F : walking_parallel_pair ⥤ C) : pullback_fst F = pullback.snd := sorry

/-- Define the equalizing cone -/
def equalizer_cone {C : Type u} [category C] [has_binary_products C] [has_pullbacks C] (F : walking_parallel_pair ⥤ C) : cone F :=
  cone.of_fork (fork.of_ι (pullback_fst F) sorry)

/-- Show the equalizing cone is a limit -/
def equalizer_cone_is_limit {C : Type u} [category C] [has_binary_products C] [has_pullbacks C] (F : walking_parallel_pair ⥤ C) : is_limit (equalizer_cone F) :=
  is_limit.mk
    fun (c : cone F) =>
      pullback.lift (nat_trans.app (cone.π c) walking_parallel_pair.zero)
        (nat_trans.app (cone.π c) walking_parallel_pair.zero) sorry

end has_equalizers_of_pullbacks_and_binary_products


/-- Any category with pullbacks and binary products, has equalizers. -/
-- This is not an instance, as it is not always how one wants to construct equalizers!

theorem has_equalizers_of_pullbacks_and_binary_products {C : Type u} [category C] [has_binary_products C] [has_pullbacks C] : has_equalizers C :=
  has_limits_of_shape.mk fun (F : walking_parallel_pair ⥤ C) => has_limit.mk (limit_cone.mk sorry sorry)

