/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.algebra.lie_group
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 l 

namespace Mathlib

/-|
# Smooth structures

In this file we define smooth structures that build on Lie groups. We prefer using the term smooth
instead of Lie mainly because Lie ring has currently another use in mathematics.
-/

/-- A smooth semiring is a semiring where addition and multiplication are smooth. -/
class smooth_semiring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (R : Type u_4) [semiring R] [topological_space R] [topological_semiring R] [charted_space H R] 
extends has_smooth_add I R, has_smooth_mul I R
where

/-- A smooth ring is a ring where the ring operations are smooth. -/
class smooth_ring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H) (R : Type u_4) [ring R] [topological_space R] [topological_ring R] [charted_space H R] 
extends has_smooth_mul I R, lie_add_group I R
where

protected instance smooth_ring.to_smooth_semiring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {H : Type u_2} [topological_space H] {E : Type u_3} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H} {R : Type u_4} [ring R] [topological_space R] [topological_ring R] [charted_space H R] [t : smooth_ring I R] : smooth_semiring I R :=
  smooth_semiring.mk smooth_ring.compatible smooth_ring.smooth_add smooth_ring.smooth_mul

protected instance field_smooth_ring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] : smooth_ring (model_with_corners_self 𝕜 𝕜) 𝕜 := sorry

