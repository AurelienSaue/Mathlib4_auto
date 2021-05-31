/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.times_cont_mdiff_map
import Mathlib.PostPort

universes u_1 u_2 u_3 u_5 u_6 u_8 u_9 l u_10 u_4 u_7 

namespace Mathlib

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `times_diffeomorph I I' M M' n`:  `n`-times continuously differentiable diffeomorphism between
                                    `M` and `M'` with respect to I and I'
* `diffeomorph  I I' M M'` : smooth diffeomorphism between `M` and `M'` with respect to I and I'

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'` := `times_diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`   := `times_diffeomorph I J M N ⊤`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

-/

/--
`n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
structure times_diffeomorph {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) 
extends M ≃ M'
where
  times_cont_mdiff_to_fun : times_cont_mdiff I I' n (equiv.to_fun _to_equiv)
  times_cont_mdiff_inv_fun : times_cont_mdiff I' I n (equiv.inv_fun _to_equiv)

/-- A `diffeomorph` is just a smooth `times_diffeomorph`. -/
def diffeomorph {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] :=
  times_diffeomorph I I' M M' ⊤

namespace times_diffeomorph


protected instance has_coe_to_fun {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) : has_coe_to_fun (times_diffeomorph I I' M M' n) :=
  has_coe_to_fun.mk (fun (_x : times_diffeomorph I I' M M' n) => M → M')
    fun (e : times_diffeomorph I I' M M' n) => ⇑(times_diffeomorph.to_equiv e)

protected instance times_cont_mdiff_map.has_coe {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) : has_coe (times_diffeomorph I I' M M' n) (times_cont_mdiff_map I I' M M' n) :=
  has_coe.mk
    fun (Φ : times_diffeomorph I I' M M' n) => times_cont_mdiff_map.mk (⇑Φ) (times_diffeomorph.times_cont_mdiff_to_fun Φ)

protected theorem continuous {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) (h : times_diffeomorph I I' M M' n) : continuous ⇑h :=
  times_cont_mdiff.continuous (times_diffeomorph.times_cont_mdiff_to_fun h)

protected theorem times_cont_mdiff {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) (h : times_diffeomorph I I' M M' n) : times_cont_mdiff I I' n ⇑h :=
  times_diffeomorph.times_cont_mdiff_to_fun h

protected theorem smooth {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (h : times_diffeomorph I I' M M' ⊤) : smooth I I' ⇑h :=
  times_diffeomorph.times_cont_mdiff_to_fun h

theorem coe_eq_to_equiv {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (n : with_top ℕ) (h : times_diffeomorph I I' M M' n) (x : M) : coe_fn h x = coe_fn (times_diffeomorph.to_equiv h) x :=
  rfl

/-- Identity map as a diffeomorphism. -/
protected def refl {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_5} [topological_space H] (I : model_with_corners 𝕜 E H) (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (n : with_top ℕ) : times_diffeomorph I I M M n :=
  mk (equiv.mk (equiv.to_fun (equiv.refl M)) (equiv.inv_fun (equiv.refl M)) sorry sorry) times_cont_mdiff_id
    times_cont_mdiff_id

/-- Composition of two diffeomorphisms. -/
protected def trans {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] {H : Type u_5} [topological_space H] {H' : Type u_6} [topological_space H'] {G : Type u_7} [topological_space G] (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') (J : model_with_corners 𝕜 F G) (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (M' : Type u_9) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] (N : Type u_10) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N] (n : with_top ℕ) (h₁ : times_diffeomorph I I' M M' n) (h₂ : times_diffeomorph I' J M' N n) : times_diffeomorph I J M N n :=
  mk
    (equiv.mk (equiv.to_fun (equiv.trans (times_diffeomorph.to_equiv h₁) (times_diffeomorph.to_equiv h₂)))
      (equiv.inv_fun (equiv.trans (times_diffeomorph.to_equiv h₁) (times_diffeomorph.to_equiv h₂))) sorry sorry)
    sorry sorry

/-- Inverse of a diffeomorphism. -/
protected def symm {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {F : Type u_4} [normed_group F] [normed_space 𝕜 F] {H : Type u_5} [topological_space H] {G : Type u_7} [topological_space G] (I : model_with_corners 𝕜 E H) (J : model_with_corners 𝕜 F G) (M : Type u_8) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M] (N : Type u_10) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N] (n : with_top ℕ) (h : times_diffeomorph I J M N n) : times_diffeomorph J I N M n :=
  mk
    (equiv.mk (equiv.to_fun (equiv.symm (times_diffeomorph.to_equiv h)))
      (equiv.inv_fun (equiv.symm (times_diffeomorph.to_equiv h))) sorry sorry)
    (times_diffeomorph.times_cont_mdiff_inv_fun h) (times_diffeomorph.times_cont_mdiff_to_fun h)

