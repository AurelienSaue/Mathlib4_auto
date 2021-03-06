/-
Copyright Β© 2020 NicolΓ² Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NicolΓ² Cavalleri
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


protected instance has_add {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [Add G] [topological_space G] [has_continuous_add G] [charted_space H' G] [has_smooth_add I' G] : Add (times_cont_mdiff_map I I' N G β€) :=
  { add := fun (f g : times_cont_mdiff_map I I' N G β€) => times_cont_mdiff_map.mk (βf + βg) sorry }

protected instance has_one {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [monoid G] [topological_space G] [charted_space H' G] [smooth_manifold_with_corners I' G] : HasOne (times_cont_mdiff_map I I' N G β€) :=
  { one := times_cont_mdiff_map.const 1 }

end smooth_map


/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

protected instance smooth_map_semigroup {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [semigroup G] [topological_space G] [has_continuous_mul G] [charted_space H' G] [has_smooth_mul I' G] : semigroup (times_cont_mdiff_map I I' N G β€) :=
  semigroup.mk Mul.mul sorry

protected instance smooth_map_add_monoid {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [add_monoid G] [topological_space G] [has_continuous_add G] [charted_space H' G] [has_smooth_add I' G] : add_monoid (times_cont_mdiff_map I I' N G β€) :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

protected instance smooth_map_comm_monoid {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [comm_monoid G] [topological_space G] [has_continuous_mul G] [charted_space H' G] [has_smooth_mul I' G] : comm_monoid (times_cont_mdiff_map I I' N G β€) :=
  comm_monoid.mk monoid.mul sorry monoid.one sorry sorry sorry

protected instance smooth_map_add_group {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [add_group G] [topological_space G] [topological_add_group G] [charted_space H' G] [smooth_manifold_with_corners I' G] [lie_add_group I' G] : add_group (times_cont_mdiff_map I I' N G β€) :=
  add_group.mk add_monoid.add sorry add_monoid.zero sorry sorry
    (fun (f : times_cont_mdiff_map I I' N G β€) => times_cont_mdiff_map.mk (fun (x : N) => -coe_fn f x) sorry)
    (sub_neg_monoid.sub._default add_monoid.add sorry add_monoid.zero sorry sorry
      fun (f : times_cont_mdiff_map I I' N G β€) => times_cont_mdiff_map.mk (fun (x : N) => -coe_fn f x) sorry)
    sorry

protected instance smooth_map_comm_group {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {G : Type u_7} [comm_group G] [topological_space G] [topological_group G] [charted_space H' G] [lie_group I' G] : comm_group (times_cont_mdiff_map I I' N G β€) :=
  comm_group.mk group.mul sorry group.one sorry sorry group.inv group.div sorry sorry

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/

protected instance smooth_map_semiring {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {R : Type u_7} [semiring R] [topological_space R] [topological_semiring R] [charted_space H' R] [smooth_semiring I' R] : semiring (times_cont_mdiff_map I I' N R β€) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry monoid.one sorry sorry
    sorry sorry sorry sorry

protected instance smooth_map_ring {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {R : Type u_7} [ring R] [topological_space R] [topological_ring R] [charted_space H' R] [smooth_ring I' R] : ring (times_cont_mdiff_map I I' N R β€) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry

protected instance smooth_map_comm_ring {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {E' : Type u_3} [normed_group E'] [normed_space π E'] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {H' : Type u_5} [topological_space H'] {I' : model_with_corners π E' H'} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {R : Type u_7} [comm_ring R] [topological_space R] [topological_ring R] [charted_space H' R] [smooth_ring I' R] : comm_ring (times_cont_mdiff_map I I' N R β€) :=
  comm_ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry semiring.mul
    sorry semiring.one sorry sorry sorry sorry sorry

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a vector space `M` over a normed
field `π` inherit a vector space structure.
-/

protected instance smooth_map_has_scalar {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space π V] : has_scalar π (times_cont_mdiff_map I (model_with_corners_self π V) N V β€) :=
  has_scalar.mk
    fun (r : π) (f : times_cont_mdiff_map I (model_with_corners_self π V) N V β€) => times_cont_mdiff_map.mk (r β’ βf) sorry

protected instance smooth_map_semimodule {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space π V] : vector_space π (times_cont_mdiff_map I (model_with_corners_self π V) N V β€) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `π`
inherit an algebra structure.
-/

/-- Smooth constant functions as a `ring_hom`. -/
def smooth_map.C {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {A : Type u_7} [normed_ring A] [normed_algebra π A] [smooth_ring (model_with_corners_self π A) A] : π β+* times_cont_mdiff_map I (model_with_corners_self π A) N A β€ :=
  ring_hom.mk (fun (c : π) => times_cont_mdiff_map.mk (fun (x : N) => coe_fn (algebra_map π A) c) sorry) sorry sorry sorry
    sorry

protected instance times_cont_mdiff_map.algebra {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {A : Type u_7} [normed_ring A] [normed_algebra π A] [smooth_ring (model_with_corners_self π A) A] : algebra π (times_cont_mdiff_map I (model_with_corners_self π A) N A β€) :=
  algebra.mk smooth_map.C sorry sorry

/-!
### Structure as module over scalar functions

If `V` is a module over `π`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `π`. -/

protected instance smooth_map_has_scalar' {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space π V] : has_scalar (times_cont_mdiff_map I (model_with_corners_self π π) N π β€)
  (times_cont_mdiff_map I (model_with_corners_self π V) N V β€) :=
  has_scalar.mk
    fun (f : times_cont_mdiff_map I (model_with_corners_self π π) N π β€)
      (g : times_cont_mdiff_map I (model_with_corners_self π V) N V β€) =>
      times_cont_mdiff_map.mk (fun (x : N) => coe_fn f x β’ coe_fn g x) sorry

protected instance smooth_map_module' {π : Type u_1} [nondiscrete_normed_field π] {E : Type u_2} [normed_group E] [normed_space π E] {H : Type u_4} [topological_space H] {I : model_with_corners π E H} {N : Type u_6} [topological_space N] [charted_space H N] [smooth_manifold_with_corners I N] {V : Type u_3} [normed_group V] [normed_space π V] : semimodule (times_cont_mdiff_map I (model_with_corners_self π π) N π β€)
  (times_cont_mdiff_map I (model_with_corners_self π V) N V β€) :=
  semimodule.mk sorry sorry

