/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.group.hom
import PostPort

universes u v w u_1 u_2 

namespace Mathlib

/-!
# Lift monoid homomorphisms to group homomorphisms of their units subgroups.
-/

namespace units


/-- The group homomorphism on units induced by a `monoid_hom`. -/
def map {M : Type u} {N : Type v} [monoid M] [monoid N] (f : M →* N) : units M →* units N :=
  monoid_hom.mk' (fun (u : units M) => mk (coe_fn f (val u)) (coe_fn f (inv u)) sorry sorry) sorry

@[simp] theorem coe_map {M : Type u} {N : Type v} [monoid M] [monoid N] (f : M →* N) (x : units M) : ↑(coe_fn (map f) x) = coe_fn f ↑x :=
  rfl

@[simp] theorem Mathlib.add_units.coe_map_neg {M : Type u} {N : Type v} [add_monoid M] [add_monoid N] (f : M →+ N) (u : add_units M) : ↑(-coe_fn (add_units.map f) u) = coe_fn f ↑(-u) :=
  rfl

@[simp] theorem map_comp {M : Type u} {N : Type v} {P : Type w} [monoid M] [monoid N] [monoid P] (f : M →* N) (g : N →* P) : map (monoid_hom.comp g f) = monoid_hom.comp (map g) (map f) :=
  rfl

@[simp] theorem map_id (M : Type u) [monoid M] : map (monoid_hom.id M) = monoid_hom.id (units M) :=
  monoid_hom.ext fun (x : units M) => ext (Eq.refl ↑(coe_fn (map (monoid_hom.id M)) x))

/-- Coercion `units M → M` as a monoid homomorphism. -/
def coe_hom (M : Type u) [monoid M] : units M →* M :=
  monoid_hom.mk coe coe_one coe_mul

@[simp] theorem coe_hom_apply {M : Type u} [monoid M] (x : units M) : coe_fn (coe_hom M) x = ↑x :=
  rfl

/-- If a map `g : M → units N` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
def lift_right {M : Type u} {N : Type v} [monoid M] [monoid N] (f : M →* N) (g : M → units N) (h : ∀ (x : M), ↑(g x) = coe_fn f x) : M →* units N :=
  monoid_hom.mk g sorry sorry

@[simp] theorem coe_lift_right {M : Type u} {N : Type v} [monoid M] [monoid N] {f : M →* N} {g : M → units N} (h : ∀ (x : M), ↑(g x) = coe_fn f x) (x : M) : ↑(coe_fn (lift_right f g h) x) = coe_fn f x :=
  h x

@[simp] theorem mul_lift_right_inv {M : Type u} {N : Type v} [monoid M] [monoid N] {f : M →* N} {g : M → units N} (h : ∀ (x : M), ↑(g x) = coe_fn f x) (x : M) : coe_fn f x * ↑(coe_fn (lift_right f g h) x⁻¹) = 1 := sorry

@[simp] theorem lift_right_inv_mul {M : Type u} {N : Type v} [monoid M] [monoid N] {f : M →* N} {g : M → units N} (h : ∀ (x : M), ↑(g x) = coe_fn f x) (x : M) : ↑(coe_fn (lift_right f g h) x⁻¹) * coe_fn f x = 1 := sorry

end units


namespace monoid_hom


/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.to_hom_units` is the corresponding monoid homomorphism from `G` to `units M`. -/
def Mathlib.add_monoid_hom.to_hom_units {G : Type u_1} {M : Type u_2} [add_group G] [add_monoid M] (f : G →+ M) : G →+ add_units M :=
  add_monoid_hom.mk (fun (g : G) => add_units.mk (coe_fn f g) (coe_fn f (-g)) sorry sorry) sorry sorry

@[simp] theorem coe_to_hom_units {G : Type u_1} {M : Type u_2} [group G] [monoid M] (f : G →* M) (g : G) : ↑(coe_fn (to_hom_units f) g) = coe_fn f g :=
  rfl

end monoid_hom


theorem is_unit.map {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) {x : M} (h : is_unit x) : is_unit (coe_fn f x) :=
  Exists.dcases_on h fun (y : units M) (h_h : ↑y = x) => Eq._oldrec (is_unit_unit (coe_fn (units.map f) y)) h_h

/-- If a homomorphism `f : M →* N` sends each element to an `is_unit`, then it can be lifted
to `f : M →* units N`. See also `units.lift_right` for a computable version. -/
def is_unit.lift_right {M : Type u_1} {N : Type u_2} [monoid M] [monoid N] (f : M →* N) (hf : ∀ (x : M), is_unit (coe_fn f x)) : M →* units N :=
  units.lift_right f (fun (x : M) => classical.some (hf x)) sorry

theorem is_add_unit.coe_lift_right {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (f : M →+ N) (hf : ∀ (x : M), is_add_unit (coe_fn f x)) (x : M) : ↑(coe_fn (is_add_unit.lift_right f hf) x) = coe_fn f x :=
  add_units.coe_lift_right (is_add_unit.lift_right._proof_1 f hf) x

@[simp] theorem is_add_unit.add_lift_right_neg {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (f : M →+ N) (h : ∀ (x : M), is_add_unit (coe_fn f x)) (x : M) : coe_fn f x + ↑(-coe_fn (is_add_unit.lift_right f h) x) = 0 :=
  add_units.add_lift_right_neg (fun (y : M) => classical.some_spec (h y)) x

@[simp] theorem is_add_unit.lift_right_neg_add {M : Type u_1} {N : Type u_2} [add_monoid M] [add_monoid N] (f : M →+ N) (h : ∀ (x : M), is_add_unit (coe_fn f x)) (x : M) : ↑(-coe_fn (is_add_unit.lift_right f h) x) + coe_fn f x = 0 :=
  add_units.lift_right_neg_add (fun (y : M) => classical.some_spec (h y)) x

