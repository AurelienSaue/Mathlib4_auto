/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.geometry.manifold.algebra.monoid
import PostPort

universes u_1 u_2 u_3 u_4 l u_5 u_6 u_7 u_8 

namespace Mathlib

/-!
# Lie groups

A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.

## Main definitions and statements

* `lie_add_group I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `lie_group I G`     : a Lie multiplicative group where `G` is a manifold on the model with
                        corners `I`.
* `lie_add_group_morphism I I' G G'`  : morphism of addittive Lie groups
* `lie_group_morphism I I' G G'`      : morphism of Lie groups
* `lie_add_group_core I G`            : allows to define a Lie additive group without first proving
                                        it is a topological additive group.
* `lie_group_core I G`                : allows to define a Lie group without first proving
                                        it is a topological group.

* `reals_lie_group`                   : real numbers are a Lie group


## Implementation notes
A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : model_with_corners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, beause in the product situation,
the model space is `model_prod E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : model_with_corners 𝕜 E H`.
-/

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
class lie_add_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (G : Type u_4) [add_group G] [topological_space G] [topological_add_group G] [charted_space H G] 
extends has_smooth_add I G
where
  smooth_neg : smooth I I fun (a : G) => -a

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
class lie_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (G : Type u_4) [group G] [topological_space G] [topological_group G] [charted_space H G] 
extends has_smooth_mul I G
where
  smooth_inv : smooth I I fun (a : G) => a⁻¹

theorem smooth_pow {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [topological_space G] [charted_space H G] [group G] [topological_group G] [lie_group I G] (n : ℕ) : smooth I I fun (a : G) => a ^ n := sorry

theorem smooth_inv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [topological_space G] [charted_space H G] [group G] [topological_group G] [lie_group I G] : smooth I I fun (x : G) => x⁻¹ :=
  lie_group.smooth_inv

theorem smooth.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [topological_space G] [charted_space H G] [add_group G] [topological_add_group G] [lie_add_group I G] {E' : Type u_6} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_7} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M : Type u_8} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M] {f : M → G} (hf : smooth I' I f) : smooth I' I fun (x : M) => -f x :=
  times_cont_mdiff.comp lie_add_group.smooth_neg hf

theorem smooth_on.neg {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [topological_space G] [charted_space H G] [add_group G] [topological_add_group G] [lie_add_group I G] {E' : Type u_6} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_7} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M : Type u_8} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M] {f : M → G} {s : set M} (hf : smooth_on I' I f s) : smooth_on I' I (fun (x : M) => -f x) s :=
  smooth.comp_smooth_on smooth_neg hf

/- Instance of product group -/

protected instance prod.lie_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_4} [topological_space G] [charted_space H G] [group G] [topological_group G] [lie_group I G] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {G' : Type u_7} [topological_space G'] [charted_space H' G'] [group G'] [topological_group G'] [lie_group I' G'] : lie_group (model_with_corners.prod I I') (G × G') :=
  lie_group.mk has_smooth_mul.compatible has_smooth_mul.smooth_mul
    (smooth.prod_mk (smooth.inv smooth_fst) (smooth.inv smooth_snd))

/-- Morphism of additive Lie groups. -/
structure lie_add_group_morphism {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E') (G : Type u_4) [topological_space G] [charted_space E G] [add_group G] [topological_add_group G] [lie_add_group I G] (G' : Type u_5) [topological_space G'] [charted_space E' G'] [add_group G'] [topological_add_group G'] [lie_add_group I' G'] 
extends smooth_add_monoid_morphism I I' G G'
where

/-- Morphism of Lie groups. -/
structure lie_group_morphism {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E') (G : Type u_4) [topological_space G] [charted_space E G] [group G] [topological_group G] [lie_group I G] (G' : Type u_5) [topological_space G'] [charted_space E' G'] [group G'] [topological_group G'] [lie_group I' G'] 
extends smooth_monoid_morphism I I' G G'
where

protected instance lie_group_morphism.has_one {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'} {G : Type u_4} [topological_space G] [charted_space E G] [group G] [topological_group G] [lie_group I G] {G' : Type u_5} [topological_space G'] [charted_space E' G'] [group G'] [topological_group G'] [lie_group I' G'] : HasOne (lie_group_morphism I I' G G') :=
  { one := lie_group_morphism.mk (smooth_monoid_morphism.mk (smooth_monoid_morphism.to_monoid_hom 1) sorry) }

protected instance lie_add_group_morphism.inhabited {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'} {G : Type u_4} [topological_space G] [charted_space E G] [add_group G] [topological_add_group G] [lie_add_group I G] {G' : Type u_5} [topological_space G'] [charted_space E' G'] [add_group G'] [topological_add_group G'] [lie_add_group I' G'] : Inhabited (lie_add_group_morphism I I' G G') :=
  { default := 0 }

protected instance lie_add_group_morphism.has_coe_to_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'} {G : Type u_4} [topological_space G] [charted_space E G] [add_group G] [topological_add_group G] [lie_add_group I G] {G' : Type u_5} [topological_space G'] [charted_space E' G'] [add_group G'] [topological_add_group G'] [lie_add_group I' G'] : has_coe_to_fun (lie_add_group_morphism I I' G G') :=
  has_coe_to_fun.mk (fun (a : lie_add_group_morphism I I' G G') => G → G')
    fun (a : lie_add_group_morphism I I' G G') =>
      add_monoid_hom.to_fun
        (smooth_add_monoid_morphism.to_add_monoid_hom (lie_add_group_morphism.to_smooth_add_monoid_morphism a))

/-- Sometimes one might want to define a Lie additive group `G` without having proved previously
that `G` is a topological additive group. In such case it is possible to use `lie_add_group_core`
that does not require such instance, and then get a Lie group by invoking `to_lie_add_group`. -/
structure lie_add_group_core {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E E) (G : Type u_3) [add_group G] [topological_space G] [charted_space E G] 
extends smooth_manifold_with_corners I G
where
  smooth_add : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p + prod.snd p
  smooth_neg : smooth I I fun (a : G) => -a

/-- Sometimes one might want to define a Lie group `G` without having proved previously that `G` is
a topological group. In such case it is possible to use `lie_group_core` that does not require such
instance, and then get a Lie group by invoking `to_lie_group` defined below. -/
structure lie_group_core {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E E) (G : Type u_3) [group G] [topological_space G] [charted_space E G] 
extends smooth_manifold_with_corners I G
where
  smooth_mul : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p * prod.snd p
  smooth_inv : smooth I I fun (a : G) => a⁻¹

-- The linter does not recognize that the followings are structure projections, disable it

namespace lie_group_core


protected theorem Mathlib.lie_add_group_core.to_topological_add_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E} {G : Type u_4} [topological_space G] [charted_space E G] [add_group G] (c : lie_add_group_core I G) : topological_add_group G :=
  topological_add_group.mk (times_cont_mdiff.continuous (lie_add_group_core.smooth_neg c))

protected theorem to_lie_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E} {G : Type u_4} [topological_space G] [charted_space E G] [group G] (c : lie_group_core I G) : lie_group I G :=
  lie_group.mk smooth_manifold_with_corners.compatible (smooth_mul c) (smooth_inv c)

end lie_group_core


/-! ### Normed spaces are Lie groups -/

protected instance normed_space_lie_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] : lie_add_group (model_with_corners_self 𝕜 E) E := sorry

