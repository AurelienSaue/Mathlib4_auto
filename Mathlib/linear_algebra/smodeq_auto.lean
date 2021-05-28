/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.basic
import PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
# modular equivalence for submodule
-/

/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
def smodeq {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] (U : submodule R M) (x : M) (y : M)  :=
  submodule.quotient.mk x = submodule.quotient.mk y

protected theorem smodeq.def {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} {y : M} : smodeq U x y ↔ submodule.quotient.mk x = submodule.quotient.mk y :=
  iff.rfl

namespace smodeq


@[simp] theorem top {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {x : M} {y : M} : smodeq ⊤ x y :=
  iff.mpr (submodule.quotient.eq ⊤) submodule.mem_top

@[simp] theorem bot {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {x : M} {y : M} : smodeq ⊥ x y ↔ x = y := sorry

theorem mono {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U₁ : submodule R M} {U₂ : submodule R M} {x : M} {y : M} (HU : U₁ ≤ U₂) (hxy : smodeq U₁ x y) : smodeq U₂ x y :=
  iff.mpr (submodule.quotient.eq U₂) (HU (iff.mp (submodule.quotient.eq U₁) hxy))

theorem refl {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} : smodeq U x x :=
  Eq.refl (submodule.quotient.mk x)

theorem symm {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} {y : M} (hxy : smodeq U x y) : smodeq U y x :=
  Eq.symm hxy

theorem trans {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} {y : M} {z : M} (hxy : smodeq U x y) (hyz : smodeq U y z) : smodeq U x z :=
  Eq.trans hxy hyz

theorem add {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x₁ : M} {x₂ : M} {y₁ : M} {y₂ : M} (hxy₁ : smodeq U x₁ y₁) (hxy₂ : smodeq U x₂ y₂) : smodeq U (x₁ + x₂) (y₁ + y₂) := sorry

theorem smul {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} {y : M} (hxy : smodeq U x y) (c : R) : smodeq U (c • x) (c • y) := sorry

theorem zero {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} : smodeq U x 0 ↔ x ∈ U := sorry

theorem map {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {U : submodule R M} {x : M} {y : M} {N : Type u_3} [add_comm_group N] [module R N] (hxy : smodeq U x y) (f : linear_map R M N) : smodeq (submodule.map f U) (coe_fn f x) (coe_fn f y) :=
  iff.mpr (submodule.quotient.eq (submodule.map f U))
    (Eq.subst (linear_map.map_sub f x y) submodule.mem_map_of_mem (iff.mp (submodule.quotient.eq U) hxy))

theorem comap {R : Type u_1} [ring R] {M : Type u_2} [add_comm_group M] [module R M] {x : M} {y : M} {N : Type u_3} [add_comm_group N] [module R N] (V : submodule R N) {f : linear_map R M N} (hxy : smodeq V (coe_fn f x) (coe_fn f y)) : smodeq (submodule.comap f V) x y :=
  iff.mpr (submodule.quotient.eq (submodule.comap f V))
    ((fun (this : coe_fn f (x - y) ∈ V) => this)
      (Eq.symm (linear_map.map_sub f x y) ▸ iff.mp (submodule.quotient.eq V) hxy))

