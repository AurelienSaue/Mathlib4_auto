/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings, indexed by a discrete type.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.direct_sum
import Mathlib.linear_algebra.dfinsupp
import Mathlib.PostPort

universes u v w u₁ u_1 

namespace Mathlib

/-!
# Direct sum of modules over commutative rings, indexed by a discrete type.

This file provides constructors for finite direct sums of modules.
It provides a construction of the direct sum using the universal property and proves
its uniqueness.

## Implementation notes

All of this file assumes that
* `R` is a commutative ring,
* `ι` is a discrete type,
* `S` is a finite set in `ι`,
* `M` is a family of `R` semimodules indexed over `ι`.
-/

namespace direct_sum


protected instance semimodule {R : Type u} [semiring R] {ι : Type v} {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] : semimodule R (direct_sum ι fun (i : ι) => M i) :=
  dfinsupp.semimodule

theorem smul_apply {R : Type u} [semiring R] {ι : Type v} {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (b : R) (v : direct_sum ι fun (i : ι) => M i) (i : ι) : coe_fn (b • v) i = b • coe_fn v i :=
  dfinsupp.smul_apply b v i

/-- Create the direct sum given a family `M` of `R` semimodules indexed over `ι`. -/
def lmk (R : Type u) [semiring R] (ι : Type v) [dec_ι : DecidableEq ι] (M : ι → Type w) [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (s : finset ι) : linear_map R ((i : ↥↑s) → M (subtype.val i)) (direct_sum ι fun (i : ι) => M i) :=
  dfinsupp.lmk

/-- Inclusion of each component into the direct sum. -/
def lof (R : Type u) [semiring R] (ι : Type v) [dec_ι : DecidableEq ι] (M : ι → Type w) [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) : linear_map R (M i) (direct_sum ι fun (i : ι) => M i) :=
  dfinsupp.lsingle

theorem single_eq_lof (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) (b : M i) : dfinsupp.single i b = coe_fn (lof R ι M i) b :=
  rfl

/-- Scalar multiplication commutes with direct sums. -/
theorem mk_smul (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (s : finset ι) (c : R) (x : (i : ↥↑s) → M (subtype.val i)) : coe_fn (mk M s) (c • x) = c • coe_fn (mk M s) x :=
  linear_map.map_smul (lmk R ι M s) c x

/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
theorem of_smul (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) (c : R) (x : M i) : coe_fn (of M i) (c • x) = c • coe_fn (of M i) x :=
  linear_map.map_smul (lof R ι M i) c x

theorem support_smul {R : Type u} [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] [(i : ι) → (x : M i) → Decidable (x ≠ 0)] (c : R) (v : direct_sum ι fun (i : ι) => M i) : dfinsupp.support (c • v) ⊆ dfinsupp.support v :=
  dfinsupp.support_smul c v

/-- The linear map constructed using the universal property of the coproduct. -/
def to_module (R : Type u) [semiring R] (ι : Type v) [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (N : Type u₁) [add_comm_monoid N] [semimodule R N] (φ : (i : ι) → linear_map R (M i) N) : linear_map R (direct_sum ι fun (i : ι) => M i) N :=
  coe_fn dfinsupp.lsum φ

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp] theorem to_module_lof (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] {N : Type u₁} [add_comm_monoid N] [semimodule R N] {φ : (i : ι) → linear_map R (M i) N} (i : ι) (x : M i) : coe_fn (to_module R ι N φ) (coe_fn (lof R ι M i) x) = coe_fn (φ i) x :=
  to_add_monoid_of (fun (i : ι) => linear_map.to_add_monoid_hom (φ i)) i x

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
theorem to_module.unique (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] {N : Type u₁} [add_comm_monoid N] [semimodule R N] (ψ : linear_map R (direct_sum ι fun (i : ι) => M i) N) (f : direct_sum ι fun (i : ι) => M i) : coe_fn ψ f = coe_fn (to_module R ι N fun (i : ι) => linear_map.comp ψ (lof R ι M i)) f :=
  to_add_monoid.unique (linear_map.to_add_monoid_hom ψ) f

theorem to_module.ext (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] {N : Type u₁} [add_comm_monoid N] [semimodule R N] {ψ : linear_map R (direct_sum ι fun (i : ι) => M i) N} {ψ' : linear_map R (direct_sum ι fun (i : ι) => M i) N} (H : ∀ (i : ι), linear_map.comp ψ (lof R ι M i) = linear_map.comp ψ' (lof R ι M i)) (f : direct_sum ι fun (i : ι) => M i) : coe_fn ψ f = coe_fn ψ' f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn ψ f = coe_fn ψ' f)) (dfinsupp.lhom_ext' H))) (Eq.refl (coe_fn ψ' f))

/--
The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map.
-/
def lset_to_set (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (S : set ι) (T : set ι) (H : S ⊆ T) : linear_map R (direct_sum ↥S fun (i : ↥S) => M ↑i) (direct_sum ↥T fun (i : ↥T) => M ↑i) :=
  to_module R (↥S) (direct_sum ↥T fun (i : ↥T) => M ↑i)
    fun (i : ↥S) => lof R (↥T) (fun (i : Subtype T) => M ↑i) { val := ↑i, property := sorry }

/-- The natural linear equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def lid (R : Type u) [semiring R] (M : Type v) (ι : optParam (Type u_1) PUnit) [add_comm_monoid M] [semimodule R M] [unique ι] : linear_equiv R (direct_sum ι fun (_x : ι) => M) M :=
  linear_equiv.mk (add_equiv.to_fun (direct_sum.id M ι)) sorry sorry (add_equiv.inv_fun (direct_sum.id M ι)) sorry sorry

/-- The projection map onto one component, as a linear map. -/
def component (R : Type u) [semiring R] (ι : Type v) (M : ι → Type w) [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) : linear_map R (direct_sum ι fun (i : ι) => M i) (M i) :=
  dfinsupp.lapply i

theorem apply_eq_component (R : Type u) [semiring R] {ι : Type v} {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (f : direct_sum ι fun (i : ι) => M i) (i : ι) : coe_fn f i = coe_fn (component R ι M i) f :=
  rfl

theorem ext (R : Type u) [semiring R] {ι : Type v} {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] {f : direct_sum ι fun (i : ι) => M i} {g : direct_sum ι fun (i : ι) => M i} (h : ∀ (i : ι), coe_fn (component R ι M i) f = coe_fn (component R ι M i) g) : f = g :=
  dfinsupp.ext h

theorem ext_iff (R : Type u) [semiring R] {ι : Type v} {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] {f : direct_sum ι fun (i : ι) => M i} {g : direct_sum ι fun (i : ι) => M i} : f = g ↔ ∀ (i : ι), coe_fn (component R ι M i) f = coe_fn (component R ι M i) g := sorry

@[simp] theorem lof_apply (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) (b : M i) : coe_fn (coe_fn (lof R ι M i) b) i = b :=
  dfinsupp.single_eq_same

@[simp] theorem component.lof_self (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) (b : M i) : coe_fn (component R ι M i) (coe_fn (lof R ι M i) b) = b :=
  lof_apply R i b

theorem component.of (R : Type u) [semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : ι → Type w} [(i : ι) → add_comm_monoid (M i)] [(i : ι) → semimodule R (M i)] (i : ι) (j : ι) (b : M j) : coe_fn (component R ι M i) (coe_fn (lof R ι M j) b) =
  dite (j = i) (fun (h : j = i) => eq.rec_on h b) fun (h : ¬j = i) => 0 :=
  dfinsupp.single_apply

