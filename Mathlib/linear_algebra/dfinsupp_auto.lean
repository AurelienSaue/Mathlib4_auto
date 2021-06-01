/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.dfinsupp
import Mathlib.linear_algebra.basic
import Mathlib.PostPort

universes u_1 u_3 u_2 u_4 

namespace Mathlib

/-!
# Properties of the semimodule `Π₀ i, M i`

Given an indexed collection of `R`-semimodules `M i`, the `R`-semimodule structure on `Π₀ i, M i`
is defined in `data.dfinsupp`.

In this file we define `linear_map` versions of various maps:

* `dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lmk s : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `λ f, f i` as a linear map;

* `dfinsupp.lsum`: `dfinsupp.sum` or `dfinsupp.lift_add_hom` as a `linear_map`;

## Implementation notes

This file should try to mirror `linear_algebra.finsupp` where possible. The API of `finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, semimodule, linear algebra
-/

namespace dfinsupp


/-- `dfinsupp.mk` as a `linear_map`. -/
def lmk {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} [dec_ι : DecidableEq ι] [semiring R]
    [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (s : finset ι) :
    linear_map R ((i : ↥↑s) → M ↑i) (dfinsupp fun (i : ι) => M i) :=
  linear_map.mk (mk s) sorry sorry

/-- `dfinsupp.single` as a `linear_map` -/
def lsingle {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} [dec_ι : DecidableEq ι] [semiring R]
    [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) :
    linear_map R (M i) (dfinsupp fun (i : ι) => M i) :=
  linear_map.mk (single i) sorry sorry

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
theorem lhom_ext {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} {N : Type u_4}
    [dec_ι : DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M i)]
    [(i : ι) → semimodule R (M i)] [add_comm_monoid N] [semimodule R N]
    {φ : linear_map R (dfinsupp fun (i : ι) => M i) N}
    {ψ : linear_map R (dfinsupp fun (i : ι) => M i) N}
    (h : ∀ (i : ι) (x : M i), coe_fn φ (single i x) = coe_fn ψ (single i x)) : φ = ψ :=
  linear_map.to_add_monoid_hom_injective (add_hom_ext h)

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
theorem lhom_ext' {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} {N : Type u_4}
    [dec_ι : DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M i)]
    [(i : ι) → semimodule R (M i)] [add_comm_monoid N] [semimodule R N]
    {φ : linear_map R (dfinsupp fun (i : ι) => M i) N}
    {ψ : linear_map R (dfinsupp fun (i : ι) => M i) N}
    (h : ∀ (i : ι), linear_map.comp φ (lsingle i) = linear_map.comp ψ (lsingle i)) : φ = ψ :=
  lhom_ext fun (i : ι) => linear_map.congr_fun (h i)

/-- Interpret `λ (f : Π₀ i, M i), f i` as a linear map. -/
def lapply {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} [semiring R]
    [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) :
    linear_map R (dfinsupp fun (i : ι) => M i) (M i) :=
  linear_map.mk (fun (f : dfinsupp fun (i : ι) => M i) => coe_fn f i) sorry sorry

@[simp] theorem lmk_apply {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} [dec_ι : DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (s : finset ι)
    (x : (i : ↥↑s) → (fun (i : ι) => M i) ↑i) : coe_fn (lmk s) x = mk s x :=
  rfl

@[simp] theorem lsingle_apply {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3}
    [dec_ι : DecidableEq ι] [semiring R] [(i : ι) → add_comm_monoid (M i)]
    [(i : ι) → semimodule R (M i)] (i : ι) (x : M i) : coe_fn (lsingle i) x = single i x :=
  rfl

@[simp] theorem lapply_apply {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} [semiring R]
    [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι)
    (f : dfinsupp fun (i : ι) => M i) : coe_fn (lapply i) f = coe_fn f i :=
  rfl

/-- The `dfinsupp` version of `finsupp.lsum`. -/
def lsum {ι : Type u_1} {R : Type u_2} {M : ι → Type u_3} {N : Type u_4} [dec_ι : DecidableEq ι]
    [semiring R] [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)]
    [add_comm_monoid N] [semimodule R N] :
    ((i : ι) → linear_map R (M i) N) ≃+ linear_map R (dfinsupp fun (i : ι) => M i) N :=
  add_equiv.mk
    (fun (F : (i : ι) → linear_map R (M i) N) =>
      linear_map.mk ⇑(sum_add_hom fun (i : ι) => linear_map.to_add_monoid_hom (F i)) sorry sorry)
    (fun (F : linear_map R (dfinsupp fun (i : ι) => M i) N) (i : ι) =>
      linear_map.comp F (lsingle i))
    sorry sorry sorry

end Mathlib