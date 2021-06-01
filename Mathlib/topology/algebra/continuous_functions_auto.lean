/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.topology.algebra.module
import Mathlib.topology.continuous_map
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over continuous functions. Instances are
present both in the case of the subtype of continuous functions and the type of continuous bundled
functions. Both implementations have advantages and disadvantages, but many experienced people in
Zulip have expressed a preference towards continuous bundled maps, so when there is no particular
reason to use the subtype, continuous bundled functions should be used for the sake of uniformity.
-/

namespace continuous_functions


protected instance set_of.has_coe_to_fun {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] : has_coe_to_fun ↥(set_of fun (f : α → β) => continuous f) :=
  has_coe_to_fun.mk (fun (x : ↥(set_of fun (f : α → β) => continuous f)) => α → β) subtype.val

end continuous_functions


namespace continuous_map


protected instance has_mul {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [Mul β] [has_continuous_mul β] : Mul (continuous_map α β) :=
  { mul := fun (f g : continuous_map α β) => mk (⇑f * ⇑g) }

protected instance has_one {α : Type u_1} {β : Type u_2} [topological_space α] [topological_space β]
    [HasOne β] : HasOne (continuous_map α β) :=
  { one := const 1 }

end continuous_map


/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/

protected instance continuous_submonoid (α : Type u_1) (β : Type u_2) [topological_space α]
    [topological_space β] [monoid β] [has_continuous_mul β] :
    is_submonoid (set_of fun (f : α → β) => continuous f) :=
  is_submonoid.mk continuous_const
    fun (f g : α → β) (fc : f ∈ set_of fun (f : α → β) => continuous f)
      (gc : g ∈ set_of fun (f : α → β) => continuous f) =>
      continuous.comp has_continuous_mul.continuous_mul (continuous.prod_mk fc gc)

protected instance continuous_add_subgroup (α : Type u_1) (β : Type u_2) [topological_space α]
    [topological_space β] [add_group β] [topological_add_group β] :
    is_add_subgroup (set_of fun (f : α → β) => continuous f) :=
  is_add_subgroup.mk
    fun (f : (i : α) → (fun (ᾰ : α) => β) i) (fc : f ∈ set_of fun (f : α → β) => continuous f) =>
      continuous.comp continuous_neg fc

protected instance continuous_monoid {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [monoid β] [has_continuous_mul β] :
    monoid ↥(set_of fun (f : α → β) => continuous f) :=
  subtype.monoid

protected instance continuous_group {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [group β] [topological_group β] :
    group ↥(set_of fun (f : α → β) => continuous f) :=
  subtype.group

protected instance continuous_add_comm_group {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [add_comm_group β] [topological_add_group β] :
    add_comm_group ↥(set_of fun (f : α → β) => continuous f) :=
  subtype.add_comm_group

protected instance continuous_map_semigroup {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [semigroup β] [has_continuous_mul β] : semigroup (continuous_map α β) :=
  semigroup.mk Mul.mul sorry

protected instance continuous_map_add_monoid {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [add_monoid β] [has_continuous_add β] : add_monoid (continuous_map α β) :=
  add_monoid.mk add_semigroup.add sorry 0 sorry sorry

protected instance continuous_map_add_comm_monoid {α : Type u_1} {β : Type u_2}
    [topological_space α] [topological_space β] [add_comm_monoid β] [has_continuous_add β] :
    add_comm_monoid (continuous_map α β) :=
  add_comm_monoid.mk add_semigroup.add sorry 0 sorry sorry sorry

protected instance continuous_map_group {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [group β] [topological_group β] : group (continuous_map α β) :=
  group.mk monoid.mul sorry monoid.one sorry sorry
    (fun (f : continuous_map α β) => continuous_map.mk fun (x : α) => coe_fn f x⁻¹)
    (div_inv_monoid.div._default monoid.mul sorry monoid.one sorry sorry
      fun (f : continuous_map α β) => continuous_map.mk fun (x : α) => coe_fn f x⁻¹)
    sorry

protected instance continuous_map_add_comm_group {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [add_comm_group β] [topological_add_group β] :
    add_comm_group (continuous_map α β) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry
    sorry

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological ring `R` inherit
the structure of a ring.
-/

protected instance continuous_subring (α : Type u_1) (R : Type u_2) [topological_space α]
    [topological_space R] [ring R] [topological_ring R] :
    is_subring (set_of fun (f : α → R) => continuous f) :=
  is_subring.mk

protected instance continuous_ring {α : Type u_1} {R : Type u_2} [topological_space α]
    [topological_space R] [ring R] [topological_ring R] :
    ring ↥(set_of fun (f : α → R) => continuous f) :=
  subtype.ring

protected instance continuous_comm_ring {α : Type u_1} {R : Type u_2} [topological_space α]
    [topological_space R] [comm_ring R] [topological_ring R] :
    comm_ring ↥(set_of fun (f : α → R) => continuous f) :=
  subtype.comm_ring

protected instance continuous_map_semiring {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [semiring β] [topological_semiring β] : semiring (continuous_map α β) :=
  semiring.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry sorry monoid.mul sorry
    monoid.one sorry sorry sorry sorry sorry sorry

protected instance continuous_map_ring {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [ring β] [topological_ring β] : ring (continuous_map α β) :=
  ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry
    sorry semiring.mul sorry semiring.one sorry sorry sorry sorry

protected instance continuous_map_comm_ring {α : Type u_1} {β : Type u_2} [topological_space α]
    [topological_space β] [comm_ring β] [topological_ring β] : comm_ring (continuous_map α β) :=
  comm_ring.mk semiring.add sorry semiring.zero sorry sorry add_comm_group.neg add_comm_group.sub
    sorry sorry semiring.mul sorry semiring.one sorry sorry sorry sorry sorry

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological semimodule `M` over a
topological semiring `R` inherit the structure of a semimodule.
-/

protected instance continuous_has_scalar {α : Type u_1} [topological_space α] {R : Type u_2}
    [semiring R] [topological_space R] {M : Type u_3} [topological_space M] [add_comm_group M]
    [semimodule R M] [topological_semimodule R M] :
    has_scalar R ↥(set_of fun (f : α → M) => continuous f) :=
  has_scalar.mk
    fun (r : R) (f : ↥(set_of fun (f : α → M) => continuous f)) =>
      { val := r • ⇑f, property := sorry }

protected instance continuous_semimodule {α : Type u_1} [topological_space α] {R : Type u_2}
    [semiring R] [topological_space R] {M : Type u_3} [topological_space M] [add_comm_group M]
    [topological_add_group M] [semimodule R M] [topological_semimodule R M] :
    semimodule R ↥(set_of fun (f : α → M) => continuous f) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

protected instance continuous_map_has_scalar {α : Type u_1} [topological_space α] {R : Type u_2}
    [semiring R] [topological_space R] {M : Type u_3} [topological_space M] [add_comm_monoid M]
    [semimodule R M] [topological_semimodule R M] : has_scalar R (continuous_map α M) :=
  has_scalar.mk fun (r : R) (f : continuous_map α M) => continuous_map.mk (r • ⇑f)

protected instance continuous_map_semimodule {α : Type u_1} [topological_space α] {R : Type u_2}
    [semiring R] [topological_space R] {M : Type u_3} [topological_space M] [add_comm_monoid M]
    [has_continuous_add M] [semimodule R M] [topological_semimodule R M] :
    semimodule R (continuous_map α M) :=
  semimodule.mk sorry sorry

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `topological_semimodule` and a `topological_semiring`
(by now we require `topological_ring`: see TODO below).-/

/-- Continuous constant functions as a `ring_hom`. -/
def continuous.C {α : Type u_1} [topological_space α] {R : Type u_2} [comm_semiring R]
    {A : Type u_3} [topological_space A] [ring A] [algebra R A] [topological_ring A] :
    R →+* ↥(set_of fun (f : α → A) => continuous f) :=
  ring_hom.mk
    (fun (c : R) => { val := fun (x : α) => coe_fn (algebra_map R A) c, property := sorry }) sorry
    sorry sorry sorry

protected instance set_of.algebra {α : Type u_1} [topological_space α] {R : Type u_2}
    [comm_semiring R] {A : Type u_3} [topological_space A] [ring A] [algebra R A]
    [topological_ring A] [topological_space R] [topological_semimodule R A] :
    algebra R ↥(set_of fun (f : α → A) => continuous f) :=
  algebra.mk continuous.C sorry sorry

/- TODO: We are assuming `A` to be a ring and not a semiring just because there is not yet an
instance of semiring. In turn, we do not want to define yet an instance of semiring because there is
no `is_subsemiring` but only `subsemiring`, and it will make sense to change this when the whole
file will have no more `is_subobject`s but only `subobject`s. It does not make sense to change
it yet in this direction as `subring` does not exist yet, so everything is being blocked by
`subring`: afterwards everything will need to be updated to the new conventions of Mathlib.
Then the instance of `topological_ring` can also be removed, as it is below for `continuous_map`. -/

/-- Continuous constant functions as a `ring_hom`. -/
def continuous_map.C {α : Type u_1} [topological_space α] {R : Type u_2} [comm_semiring R]
    {A : Type u_3} [topological_space A] [semiring A] [algebra R A] [topological_semiring A] :
    R →+* continuous_map α A :=
  ring_hom.mk (fun (c : R) => continuous_map.mk fun (x : α) => coe_fn (algebra_map R A) c) sorry
    sorry sorry sorry

protected instance continuous_map_algebra {α : Type u_1} [topological_space α] {R : Type u_2}
    [comm_semiring R] {A : Type u_3} [topological_space A] [semiring A] [algebra R A]
    [topological_semiring A] [topological_space R] [topological_semimodule R A] :
    algebra R (continuous_map α A) :=
  algebra.mk continuous_map.C sorry sorry

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `M`. -/

protected instance continuous_has_scalar' {α : Type u_1} [topological_space α] {R : Type u_2}
    [semiring R] [topological_space R] {M : Type u_3} [topological_space M] [add_comm_group M]
    [semimodule R M] [topological_semimodule R M] :
    has_scalar ↥(set_of fun (f : α → R) => continuous f)
        ↥(set_of fun (f : α → M) => continuous f) :=
  has_scalar.mk
    fun (f : ↥(set_of fun (f : α → R) => continuous f))
      (g : ↥(set_of fun (f : α → M) => continuous f)) =>
      { val := fun (x : α) => coe_fn f x • coe_fn g x, property := sorry }

protected instance continuous_module' {α : Type u_1} [topological_space α] (R : Type u_2) [ring R]
    [topological_space R] [topological_ring R] (M : Type u_3) [topological_space M]
    [add_comm_group M] [topological_add_group M] [module R M] [topological_module R M] :
    module ↥(set_of fun (f : α → R) => continuous f) ↥(set_of fun (f : α → M) => continuous f) :=
  semimodule.of_core (semimodule.core.mk (has_scalar.mk has_scalar.smul) sorry sorry sorry sorry)

protected instance continuous_map_has_scalar' {α : Type u_1} [topological_space α] {R : Type u_2}
    [semiring R] [topological_space R] {M : Type u_3} [topological_space M] [add_comm_monoid M]
    [semimodule R M] [topological_semimodule R M] :
    has_scalar (continuous_map α R) (continuous_map α M) :=
  has_scalar.mk
    fun (f : continuous_map α R) (g : continuous_map α M) =>
      continuous_map.mk fun (x : α) => coe_fn f x • coe_fn g x

protected instance continuous_map_module' {α : Type u_1} [topological_space α] (R : Type u_2)
    [ring R] [topological_space R] [topological_ring R] (M : Type u_3) [topological_space M]
    [add_comm_monoid M] [has_continuous_add M] [semimodule R M] [topological_semimodule R M] :
    semimodule (continuous_map α R) (continuous_map α M) :=
  semimodule.mk sorry sorry

end Mathlib