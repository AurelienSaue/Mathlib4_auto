/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.times_cont_mdiff
import Mathlib.PostPort

universes u_2 u_3 u_4 u_5 l u_6 u_7 u_8 u_1 

namespace Mathlib

/-!
# Smooth monoid
A smooth monoid is a monoid that is also a smooth manifold, in which multiplication is a smooth map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about smooth monoids: `has_smooth_mul` and its
additive counterpart `has_smooth_add`. These structures are general enough to also talk about smooth
semigroups.
-/

/-- Basic hypothesis to talk about a smooth (Lie) additive monoid or a smooth additive
semigroup. A smooth additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_smooth_add α`. -/
class has_smooth_add {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (G : Type u_5) [Add G] [topological_space G] [has_continuous_add G] [charted_space H G] 
extends smooth_manifold_with_corners I G
where
  smooth_add : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p + prod.snd p

/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `monoid G`
and `has_smooth_mul I G`. -/
class has_smooth_mul {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (G : Type u_5) [Mul G] [topological_space G] [has_continuous_mul G] [charted_space H G] 
extends smooth_manifold_with_corners I G
where
  smooth_mul : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p * prod.snd p

theorem smooth_mul {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [Mul G] [topological_space G] [has_continuous_mul G] [charted_space H G] [has_smooth_mul I G] : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p * prod.snd p :=
  has_smooth_mul.smooth_mul

theorem smooth.mul {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [Mul G] [topological_space G] [has_continuous_mul G] [charted_space H G] [has_smooth_mul I G] {E' : Type u_6} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_7} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M : Type u_8} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M] {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) : smooth I' I (f * g) :=
  times_cont_mdiff.comp smooth_mul (smooth.prod_mk hf hg)

theorem smooth_add_left {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [Add G] [topological_space G] [has_continuous_add G] [charted_space H G] [has_smooth_add I G] {a : G} : smooth I I fun (b : G) => a + b :=
  times_cont_mdiff.comp smooth_add (smooth.prod_mk smooth_const smooth_id)

theorem smooth_add_right {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [Add G] [topological_space G] [has_continuous_add G] [charted_space H G] [has_smooth_add I G] {a : G} : smooth I I fun (b : G) => b + a :=
  times_cont_mdiff.comp smooth_add (smooth.prod_mk smooth_id smooth_const)

theorem smooth_on.add {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {G : Type u_5} [Add G] [topological_space G] [has_continuous_add G] [charted_space H G] [has_smooth_add I G] {E' : Type u_6} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_7} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {M : Type u_8} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M] {f : M → G} {g : M → G} {s : set M} (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) : smooth_on I' I (f + g) s :=
  smooth.comp_smooth_on smooth_add (smooth_on.prod_mk hf hg)

/- Instance of product -/

protected instance has_smooth_add.sum {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_3} [topological_space H] (I : model_with_corners 𝕜 E H) (G : Type u_4) [topological_space G] [charted_space H G] [Add G] [has_continuous_add G] [has_smooth_add I G] {E' : Type u_5} [normed_group E'] [normed_space 𝕜 E'] {H' : Type u_6} [topological_space H'] (I' : model_with_corners 𝕜 E' H') (G' : Type u_7) [topological_space G'] [charted_space H' G'] [Add G'] [has_continuous_add G'] [has_smooth_add I' G'] : has_smooth_add (model_with_corners.prod I I') (G × G') :=
  has_smooth_add.mk smooth_manifold_with_corners.compatible
    (smooth.prod_mk
      (smooth.add (times_cont_mdiff.smooth (times_cont_mdiff.comp smooth_fst smooth_fst))
        (times_cont_mdiff.comp smooth_fst smooth_snd))
      (smooth.add (times_cont_mdiff.smooth (times_cont_mdiff.comp smooth_snd smooth_fst))
        (times_cont_mdiff.comp smooth_snd smooth_snd)))

/-- Morphism of additive smooth monoids. -/
structure smooth_add_monoid_morphism {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {E' : Type u_4} [normed_group E'] [normed_space 𝕜 E'] (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E') (G : Type u_5) [topological_space G] [charted_space E G] [add_monoid G] [has_continuous_add G] [has_smooth_add I G] (G' : Type u_6) [topological_space G'] [charted_space E' G'] [add_monoid G'] [has_continuous_add G'] [has_smooth_add I' G'] 
extends G →+ G'
where
  smooth_to_fun : smooth I I' (add_monoid_hom.to_fun _to_add_monoid_hom)

/-- Morphism of smooth monoids. -/
structure smooth_monoid_morphism {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {E' : Type u_4} [normed_group E'] [normed_space 𝕜 E'] (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E') (G : Type u_5) [topological_space G] [charted_space E G] [monoid G] [has_continuous_mul G] [has_smooth_mul I G] (G' : Type u_6) [topological_space G'] [charted_space E' G'] [monoid G'] [has_continuous_mul G'] [has_smooth_mul I' G'] 
extends G →* G'
where
  smooth_to_fun : smooth I I' (monoid_hom.to_fun _to_monoid_hom)

protected instance smooth_add_monoid_morphism.has_zero {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {E' : Type u_4} [normed_group E'] [normed_space 𝕜 E'] {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'} {G : Type u_5} [topological_space G] [charted_space E G] [add_monoid G] [has_continuous_add G] [has_smooth_add I G] {G' : Type u_6} [topological_space G'] [charted_space E' G'] [add_monoid G'] [has_continuous_add G'] [has_smooth_add I' G'] : HasZero (smooth_add_monoid_morphism I I' G G') :=
  { zero := smooth_add_monoid_morphism.mk (add_monoid_hom.mk (add_monoid_hom.to_fun 0) sorry sorry) sorry }

protected instance smooth_monoid_morphism.inhabited {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {E' : Type u_4} [normed_group E'] [normed_space 𝕜 E'] {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'} {G : Type u_5} [topological_space G] [charted_space E G] [monoid G] [has_continuous_mul G] [has_smooth_mul I G] {G' : Type u_6} [topological_space G'] [charted_space E' G'] [monoid G'] [has_continuous_mul G'] [has_smooth_mul I' G'] : Inhabited (smooth_monoid_morphism I I' G G') :=
  { default := 1 }

protected instance smooth_add_monoid_morphism.has_coe_to_fun {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {E' : Type u_4} [normed_group E'] [normed_space 𝕜 E'] {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'} {G : Type u_5} [topological_space G] [charted_space E G] [add_monoid G] [has_continuous_add G] [has_smooth_add I G] {G' : Type u_6} [topological_space G'] [charted_space E' G'] [add_monoid G'] [has_continuous_add G'] [has_smooth_add I' G'] : has_coe_to_fun (smooth_add_monoid_morphism I I' G G') :=
  has_coe_to_fun.mk (fun (a : smooth_add_monoid_morphism I I' G G') => G → G')
    fun (a : smooth_add_monoid_morphism I I' G G') =>
      add_monoid_hom.to_fun (smooth_add_monoid_morphism.to_add_monoid_hom a)

/-- Sometimes one might want to define a smooth additive monoid `G` without having proved previously
that `G` is a topological additive monoid. In such case it is possible to use `has_smooth_add_core`
that does not require such instance, and then get a smooth additive monoid by invoking
`to_has_smooth_add`. -/
structure has_smooth_add_core {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (G : Type u_5) [Add G] [topological_space G] [charted_space H G] 
extends smooth_manifold_with_corners I G
where
  smooth_add : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p + prod.snd p

/-- Sometimes one might want to define a smooth monoid `G` without having proved previously that `G`
is a topological monoid. In such case it is possible to use `has_smooth_mul_core` that does not
require such instance, and then get a smooth monoid by invoking `to_has_smooth_mul`. -/
structure has_smooth_mul_core {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {H : Type u_3} [topological_space H] {E : Type u_4} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (G : Type u_5) [Mul G] [topological_space G] [charted_space H G] 
extends smooth_manifold_with_corners I G
where
  smooth_mul : smooth (model_with_corners.prod I I) I fun (p : G × G) => prod.fst p * prod.snd p

namespace has_smooth_mul_core


protected theorem to_has_continuous_mul {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E} {G : Type u_5} [topological_space G] [charted_space E G] [group G] (c : has_smooth_mul_core I G) : has_continuous_mul G :=
  has_continuous_mul.mk (times_cont_mdiff.continuous (smooth_mul c))

protected theorem Mathlib.has_smooth_add_core.to_has_smooth_add {𝕜 : Type u_2} [nondiscrete_normed_field 𝕜] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E} {G : Type u_5} [topological_space G] [charted_space E G] [add_group G] (c : has_smooth_add_core I G) : has_smooth_add I G :=
  has_smooth_add.mk smooth_manifold_with_corners.compatible (has_smooth_add_core.smooth_add c)

