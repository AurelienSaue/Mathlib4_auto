/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.geometry.manifold.algebra.structures
import Mathlib.geometry.manifold.times_cont_mdiff_map
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 u_5 u_6 u_7 

namespace Mathlib

/-!
# Algebraic structures over smooth functions

In this file, we define instances of algebraic structures over smooth functions.
-/

namespace smooth_map


protected instance has_add {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [Add G] [topological_space G] [has_continuous_add G] [charted_space H' G] [has_smooth_add I' G] : Add (times_cont_mdiff_map I I' N G ⊤) :=
  { add := fun (f g : times_cont_mdiff_map I I' N G ⊤) => times_cont_mdiff_map.mk (⇑f + ⇑g) sorry }

protected instance has_one {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [monoid G] [topological_space G] [charted_space H' G] [smooth_manifold_with_corners I' G] : HasOne (times_cont_mdiff_map I I' N G ⊤) :=
  { one := times_cont_mdiff_map.const 1 }

end smooth_map


/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

protected instance smooth_map_semigroup {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [semigroup G] [topological_space G] [has_continuous_mul G] [charted_space H' G] [has_smooth_mul I' G] : semigroup (times_cont_mdiff_map I I' N G ⊤) :=
  semigroup.mk Mul.mul sorry

protected instance smooth_map_add_monoid {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [add_monoid G] [topological_space G] [has_continuous_add G] [charted_space H' G] [has_smooth_add I' G] : add_monoid (times_cont_mdiff_map I I' N G ⊤) :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

protected instance smooth_map_comm_monoid {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [comm_monoid G] [topological_space G] [has_continuous_mul G] [charted_space H' G] [has_smooth_mul I' G] : comm_monoid (times_cont_mdiff_map I I' N G ⊤) :=
  comm_monoid.mk monoid.mul sorry monoid.one sorry sorry sorry

protected instance smooth_map_add_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [add_group G] [topological_space G] [topological_add_group G] [charted_space H' G] [smooth_manifold_with_corners I' G] [lie_add_group I' G] : add_group (times_cont_mdiff_map I I' N G ⊤) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry
    (fun (f : times_cont_mdiff_map I I' N G ⊤) => times_cont_mdiff_map.mk (fun (x : N) => -coe_fn f x) sorry)
    (sub_neg_monoid.sub._default add_monoid.add sorry add_monoid.zero sorry sorry
      fun (f : times_cont_mdiff_map I I' N G ⊤) => times_cont_mdiff_map.mk (fun (x : N) => -coe_fn f x) sorry)
    sorry

protected instance smooth_map_comm_group {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [comm_group G] [topological_space G] [topological_group G] [charted_space H' G] [lie_group I' G] : comm_group (times_cont_mdiff_map I I' N G ⊤) :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/

protected instance smooth_map_semiring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {R : Type u_7} [semiring R] [topological_space R] [topological_semiring R] [charted_space H' R] [smooth_semiring I' R] : semiring (times_cont_mdiff_map I I' N R ⊤) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry monoid.one sorry sorry
    sorry sorry sorry sorry

protected instance smooth_map_ring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {R : Type u_7} [ring R] [topological_space R] [topological_ring R] [charted_space H' R] [smooth_ring I' R] : ring (times_cont_mdiff_map I I' N R ⊤) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry

protected instance smooth_map_comm_ring {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {E' : Type u_3} [normed_group E'] [normed_space 𝕜 E'] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners 𝕜 E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {R : Type u_7} [comm_ring R] [topological_space R] [topological_ring R] [charted_space H' R] [smooth_ring I' R] : comm_ring (times_cont_mdiff_map I I' N R ⊤) :=
  comm_ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry sorry

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/

protected instance smooth_map_has_scalar {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space 𝕜 V] : has_scalar 𝕜 (times_cont_mdiff_map I (model_with_corners_self 𝕜 V) N V ⊤) :=
  has_scalar.mk
    fun (r : 𝕜) (f : times_cont_mdiff_map I (model_with_corners_self 𝕜 V) N V ⊤) => times_cont_mdiff_map.mk (r • ⇑f) sorry

protected instance smooth_map_semimodule {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space 𝕜 V] : vector_space 𝕜 (times_cont_mdiff_map I (model_with_corners_self 𝕜 V) N V ⊤) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/

/-- Smooth constant functions as a `ring_hom`. -/
def smooth_map.C {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {A : Type u_7} [normed_ring A] [normed_algebra 𝕜 A] [smooth_ring (model_with_corners_self 𝕜 A) A] : 𝕜 →+* times_cont_mdiff_map I (model_with_corners_self 𝕜 A) N A ⊤ :=
  ring_hom.mk (fun (c : 𝕜) => times_cont_mdiff_map.mk (fun (x : N) => coe_fn (algebra_map 𝕜 A) c) sorry) sorry sorry sorry
    sorry

protected instance times_cont_mdiff_map.algebra {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {A : Type u_7} [normed_ring A] [normed_algebra 𝕜 A] [smooth_ring (model_with_corners_self 𝕜 A) A] : algebra 𝕜 (times_cont_mdiff_map I (model_with_corners_self 𝕜 A) N A ⊤) :=
  algebra.mk smooth_map.C sorry sorry

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `𝕜`. -/

protected instance smooth_map_has_scalar' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space 𝕜 V] : has_scalar (times_cont_mdiff_map I (model_with_corners_self 𝕜 𝕜) N 𝕜 ⊤)
  (times_cont_mdiff_map I (model_with_corners_self 𝕜 V) N V ⊤) :=
  has_scalar.mk
    fun (f : times_cont_mdiff_map I (model_with_corners_self 𝕜 𝕜) N 𝕜 ⊤)
      (g : times_cont_mdiff_map I (model_with_corners_self 𝕜 V) N V ⊤) =>
      times_cont_mdiff_map.mk (fun (x : N) => coe_fn f x • coe_fn g x) sorry

protected instance smooth_map_module' {𝕜 : Type u_1} [nondiscrete_normed_field 𝕜] {E : Type u_2} [normed_group E] [normed_space 𝕜 E] {H : Type u_4} [topological_space H] {I : model_with_corners 𝕜 E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space 𝕜 V] : semimodule (times_cont_mdiff_map I (model_with_corners_self 𝕜 𝕜) N 𝕜 ⊤)
  (times_cont_mdiff_map I (model_with_corners_self 𝕜 V) N V ⊤) :=
  semimodule.mk sorry sorry

