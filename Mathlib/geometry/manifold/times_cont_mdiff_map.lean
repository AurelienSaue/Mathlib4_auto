/-
Copyright Β© 2020 NicolΓ² Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: NicolΓ² Cavalleri.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.times_cont_mdiff
import Mathlib.topology.continuous_map
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 u_7 l u_10 u_8 u_9 

namespace Mathlib

/-!
# Smooth bundled map

In this file we define the type `times_cont_mdiff_map` of `n` times continuously differentiable
bundled maps.
-/

/-- Bundled `n` times continuously differentiable maps. -/
structure times_cont_mdiff_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] (I : model_with_corners π E H) (I' : model_with_corners π E' H') (M : Type u_6) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_7) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top β) 
where
  to_fun : M β M'
  times_cont_mdiff_to_fun : times_cont_mdiff I I' n to_fun

/-- Bundled smooth maps. -/
def smooth_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] (I : model_with_corners π E H) (I' : model_with_corners π E' H') (M : Type u_6) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_7) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] :=
  times_cont_mdiff_map I I' M M' β€

namespace times_cont_mdiff_map


protected instance has_coe_to_fun {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} : has_coe_to_fun (times_cont_mdiff_map I I' M M' n) :=
  has_coe_to_fun.mk (fun (x : times_cont_mdiff_map I I' M M' n) => M β M') times_cont_mdiff_map.to_fun

protected instance continuous_map.has_coe {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} : has_coe (times_cont_mdiff_map I I' M M' n) (continuous_map M M') :=
  has_coe.mk fun (f : times_cont_mdiff_map I I' M M' n) => continuous_map.mk (times_cont_mdiff_map.to_fun f)

protected theorem times_cont_mdiff {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} (f : times_cont_mdiff_map I I' M M' n) : times_cont_mdiff I I' n βf :=
  times_cont_mdiff_map.times_cont_mdiff_to_fun f

protected theorem smooth {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (f : times_cont_mdiff_map I I' M M' β€) : smooth I I' βf :=
  times_cont_mdiff_map.times_cont_mdiff_to_fun f

theorem coe_inj {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} {f : times_cont_mdiff_map I I' M M' n} {g : times_cont_mdiff_map I I' M M' n} (h : βf = βg) : f = g := sorry

theorem ext {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} {f : times_cont_mdiff_map I I' M M' n} {g : times_cont_mdiff_map I I' M M' n} (h : β (x : M), coe_fn f x = coe_fn g x) : f = g := sorry

/-- The identity as a smooth map. -/
def id {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {n : with_top β} : times_cont_mdiff_map I I M M n :=
  mk id times_cont_mdiff_id

/-- The composition of smooth maps, as a smooth map. -/
def comp {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {E'' : Type u_8} [normed_group E''] [normed_space π E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners π E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {n : with_top β} (f : times_cont_mdiff_map I' I'' M' M'' n) (g : times_cont_mdiff_map I I' M M' n) : times_cont_mdiff_map I I'' M M'' n :=
  mk (fun (a : M) => coe_fn f (coe_fn g a)) sorry

@[simp] theorem comp_apply {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {E'' : Type u_8} [normed_group E''] [normed_space π E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners π E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {n : with_top β} (f : times_cont_mdiff_map I' I'' M' M'' n) (g : times_cont_mdiff_map I I' M M' n) (x : M) : coe_fn (comp f g) x = coe_fn f (coe_fn g x) :=
  rfl

protected instance inhabited {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} [Inhabited M'] : Inhabited (times_cont_mdiff_map I I' M M' n) :=
  { default := mk (fun (_x : M) => Inhabited.default) sorry }

/-- Constant map as a smooth map -/
def const {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners π E H} {I' : model_with_corners π E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top β} (y : M') : times_cont_mdiff_map I I' M M' n :=
  mk (fun (x : M) => y) times_cont_mdiff_const

end times_cont_mdiff_map


protected instance continuous_linear_map.has_coe_to_times_cont_mdiff_map {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] (n : with_top β) : has_coe (continuous_linear_map π E E')
  (times_cont_mdiff_map (model_with_corners_self π E) (model_with_corners_self π E') E E' n) :=
  has_coe.mk
    fun (f : continuous_linear_map π E E') =>
      times_cont_mdiff_map.mk (linear_map.to_fun (continuous_linear_map.to_linear_map f))
        (continuous_linear_map.times_cont_mdiff f)

