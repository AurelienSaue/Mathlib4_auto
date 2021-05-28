/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.geometry.manifold.times_cont_mdiff
import Mathlib.topology.continuous_map
import PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 u_7 l u_10 u_8 u_9 

namespace Mathlib

/-!
# Smooth bundled map

In this file we define the type `times_cont_mdiff_map` of `n` times continuously differentiable
bundled maps.
-/

/-- Bundled `n` times continuously differentiable maps. -/
structure times_cont_mdiff_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_6) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_7) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) 
where
  to_fun : M → M'
  times_cont_mdiff_to_fun : times_cont_mdiff I I' n to_fun

/-- Bundled smooth maps. -/
def smooth_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_6) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_7) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']  :=
  times_cont_mdiff_map I I' M M' ⊤

namespace times_cont_mdiff_map


protected instance has_coe_to_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} : has_coe_to_fun (times_cont_mdiff_map I I' M M' n) :=
  has_coe_to_fun.mk (fun (x : times_cont_mdiff_map I I' M M' n) => M → M') times_cont_mdiff_map.to_fun

protected instance continuous_map.has_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} : has_coe (times_cont_mdiff_map I I' M M' n) (continuous_map M M') :=
  has_coe.mk fun (f : times_cont_mdiff_map I I' M M' n) => continuous_map.mk (times_cont_mdiff_map.to_fun f)

protected theorem times_cont_mdiff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} (f : times_cont_mdiff_map I I' M M' n) : times_cont_mdiff I I' n ⇑f :=
  times_cont_mdiff_map.times_cont_mdiff_to_fun f

protected theorem smooth {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (f : times_cont_mdiff_map I I' M M' ⊤) : smooth I I' ⇑f :=
  times_cont_mdiff_map.times_cont_mdiff_to_fun f

theorem coe_inj {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} {f : times_cont_mdiff_map I I' M M' n} {g : times_cont_mdiff_map I I' M M' n} (h : ⇑f = ⇑g) : f = g := sorry

theorem ext {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} {f : times_cont_mdiff_map I I' M M' n} {g : times_cont_mdiff_map I I' M M' n} (h : ∀ (x : M), coe_fn f x = coe_fn g x) : f = g := sorry

/-- The identity as a smooth map. -/
def id {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {n : with_top ℕ} : times_cont_mdiff_map I I M M n :=
  mk id times_cont_mdiff_id

/-- The composition of smooth maps, as a smooth map. -/
def comp {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {n : with_top ℕ} (f : times_cont_mdiff_map I' I'' M' M'' n) (g : times_cont_mdiff_map I I' M M' n) : times_cont_mdiff_map I I'' M M'' n :=
  mk (fun (a : M) => coe_fn f (coe_fn g a)) sorry

@[simp] theorem comp_apply {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {E'' : Type u_8} [normed_group E''] [normed_space 𝕜 E''] {H'' : Type u_9} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''} {M'' : Type u_10} [topological_space M''] [charted_space H'' M''] [smooth_manifold_with_corners I'' M''] {n : with_top ℕ} (f : times_cont_mdiff_map I' I'' M' M'' n) (g : times_cont_mdiff_map I I' M M' n) (x : M) : coe_fn (comp f g) x = coe_fn f (coe_fn g x) :=
  rfl

protected instance inhabited {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} [Inhabited M'] : Inhabited (times_cont_mdiff_map I I' M M' n) :=
  { default := mk (fun (_x : M) => Inhabited.default) sorry }

/-- Constant map as a smooth map -/
def const {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {H' : Type u_5} [topological_space H'] {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'} {M : Type u_6} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] {M' : Type u_7} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] {n : with_top ℕ} (y : M') : times_cont_mdiff_map I I' M M' n :=
  mk (fun (x : M) => y) times_cont_mdiff_const

end times_cont_mdiff_map


protected instance continuous_linear_map.has_coe_to_times_cont_mdiff_map {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] (n : with_top ℕ) : has_coe (continuous_linear_map 𝕜 E E')
  (times_cont_mdiff_map (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') E E' n) :=
  has_coe.mk
    fun (f : continuous_linear_map 𝕜 E E') =>
      times_cont_mdiff_map.mk (linear_map.to_fun (continuous_linear_map.to_linear_map f))
        (continuous_linear_map.times_cont_mdiff f)

