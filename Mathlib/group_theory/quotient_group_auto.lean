/-
Copyright (c) 2018 Kevin Buzzard and Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot.

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.group_theory.coset
import Mathlib.PostPort

universes u u_1 v 

namespace Mathlib

namespace quotient_group


-- Define the `div_inv_monoid` before the `group` structure,

-- to make sure we have `inv` fully defined before we show `mul_left_inv`.

-- TODO: is there a non-invasive way of defining this in one declaration?

protected instance Mathlib.quotient_add_group.div_inv_monoid {G : Type u} [add_group G]
    (N : add_subgroup G) [nN : add_subgroup.normal N] :
    sub_neg_monoid (quotient_add_group.quotient N) :=
  sub_neg_monoid.mk (quotient.map₂' Add.add sorry) sorry ↑0 sorry sorry
    (fun (a : quotient_add_group.quotient N) => quotient.lift_on' a (fun (a : G) => ↑(-a)) sorry)
    fun (a b : quotient_add_group.quotient N) =>
      quotient.map₂' Add.add sorry a (quotient.lift_on' b (fun (a : G) => ↑(-a)) sorry)

protected instance Mathlib.quotient_add_group.add_group {G : Type u} [add_group G]
    (N : add_subgroup G) [nN : add_subgroup.normal N] : add_group (quotient_add_group.quotient N) :=
  add_group.mk sub_neg_monoid.add sorry sub_neg_monoid.zero sorry sorry sub_neg_monoid.neg
    sub_neg_monoid.sub sorry

/-- The group homomorphism from `G` to `G/N`. -/
def mk' {G : Type u} [group G] (N : subgroup G) [nN : subgroup.normal N] : G →* quotient N :=
  monoid_hom.mk' mk sorry

@[simp] theorem Mathlib.quotient_add_group.ker_mk {G : Type u} [add_group G] (N : add_subgroup G)
    [nN : add_subgroup.normal N] : add_monoid_hom.ker (quotient_add_group.mk' N) = N :=
  sorry

-- for commutative groups we don't need normality assumption

protected instance Mathlib.quotient_add_group.add_comm_group {G : Type u_1} [add_comm_group G]
    (N : add_subgroup G) : add_comm_group (quotient_add_group.quotient N) :=
  add_comm_group.mk add_group.add sorry add_group.zero sorry sorry add_group.neg add_group.sub sorry
    sorry

@[simp] theorem Mathlib.quotient_add_group.coe_zero {G : Type u} [add_group G] (N : add_subgroup G)
    [nN : add_subgroup.normal N] : ↑0 = 0 :=
  rfl

@[simp] theorem coe_mul {G : Type u} [group G] (N : subgroup G) [nN : subgroup.normal N] (a : G)
    (b : G) : ↑(a * b) = ↑a * ↑b :=
  rfl

@[simp] theorem Mathlib.quotient_add_group.coe_neg {G : Type u} [add_group G] (N : add_subgroup G)
    [nN : add_subgroup.normal N] (a : G) : ↑(-a) = -↑a :=
  rfl

@[simp] theorem coe_pow {G : Type u} [group G] (N : subgroup G) [nN : subgroup.normal N] (a : G)
    (n : ℕ) : ↑(a ^ n) = ↑a ^ n :=
  monoid_hom.map_pow (mk' N) a n

@[simp] theorem coe_gpow {G : Type u} [group G] (N : subgroup G) [nN : subgroup.normal N] (a : G)
    (n : ℤ) : ↑(a ^ n) = ↑a ^ n :=
  monoid_hom.map_gpow (mk' N) a n

/-- A group homomorphism `φ : G →* H` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* H`. -/
def lift {G : Type u} [group G] (N : subgroup G) [nN : subgroup.normal N] {H : Type v} [group H]
    (φ : G →* H) (HN : ∀ (x : G), x ∈ N → coe_fn φ x = 1) : quotient N →* H :=
  monoid_hom.mk' (fun (q : quotient N) => quotient.lift_on' q ⇑φ sorry) sorry

@[simp] theorem Mathlib.quotient_add_group.lift_mk {G : Type u} [add_group G] (N : add_subgroup G)
    [nN : add_subgroup.normal N] {H : Type v} [add_group H] {φ : G →+ H}
    (HN : ∀ (x : G), x ∈ N → coe_fn φ x = 0) (g : G) :
    coe_fn (quotient_add_group.lift N φ HN) ↑g = coe_fn φ g :=
  rfl

@[simp] theorem lift_mk' {G : Type u} [group G] (N : subgroup G) [nN : subgroup.normal N]
    {H : Type v} [group H] {φ : G →* H} (HN : ∀ (x : G), x ∈ N → coe_fn φ x = 1) (g : G) :
    coe_fn (lift N φ HN) (mk g) = coe_fn φ g :=
  rfl

@[simp] theorem Mathlib.quotient_add_group.lift_quot_mk {G : Type u} [add_group G]
    (N : add_subgroup G) [nN : add_subgroup.normal N] {H : Type v} [add_group H] {φ : G →+ H}
    (HN : ∀ (x : G), x ∈ N → coe_fn φ x = 0) (g : G) :
    coe_fn (quotient_add_group.lift N φ HN) (Quot.mk setoid.r g) = coe_fn φ g :=
  rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
def Mathlib.quotient_add_group.map {G : Type u} [add_group G] (N : add_subgroup G)
    [nN : add_subgroup.normal N] {H : Type v} [add_group H] (M : add_subgroup H)
    [add_subgroup.normal M] (f : G →+ H) (h : N ≤ add_subgroup.comap f M) :
    quotient_add_group.quotient N →+ quotient_add_group.quotient M :=
  quotient_add_group.lift N (add_monoid_hom.comp (quotient_add_group.mk' M) f) sorry

/-- The induced map from the quotient by the kernel to the codomain. -/
def ker_lift {G : Type u} [group G] {H : Type v} [group H] (φ : G →* H) :
    quotient (monoid_hom.ker φ) →* H :=
  lift (monoid_hom.ker φ) φ sorry

@[simp] theorem ker_lift_mk {G : Type u} [group G] {H : Type v} [group H] (φ : G →* H) (g : G) :
    coe_fn (ker_lift φ) ↑g = coe_fn φ g :=
  lift_mk (monoid_hom.ker φ) (ker_lift._proof_1 φ) g

@[simp] theorem Mathlib.quotient_add_group.ker_lift_mk' {G : Type u} [add_group G] {H : Type v}
    [add_group H] (φ : G →+ H) (g : G) :
    coe_fn (quotient_add_group.ker_lift φ) (quotient_add_group.mk g) = coe_fn φ g :=
  quotient_add_group.lift_mk' (add_monoid_hom.ker φ) (quotient_add_group.ker_lift._proof_1 φ) g

theorem ker_lift_injective {G : Type u} [group G] {H : Type v} [group H] (φ : G →* H) :
    function.injective ⇑(ker_lift φ) :=
  sorry

-- Note that ker φ isn't definitionally ker (to_range φ)

-- so there is a bit of annoying code duplication here

/-- The induced map from the quotient by the kernel to the range. -/
def Mathlib.quotient_add_group.range_ker_lift {G : Type u} [add_group G] {H : Type v} [add_group H]
    (φ : G →+ H) :
    quotient_add_group.quotient (add_monoid_hom.ker φ) →+ ↥(add_monoid_hom.range φ) :=
  quotient_add_group.lift (add_monoid_hom.ker φ) (add_monoid_hom.to_range φ) sorry

theorem range_ker_lift_injective {G : Type u} [group G] {H : Type v} [group H] (φ : G →* H) :
    function.injective ⇑(range_ker_lift φ) :=
  sorry

theorem Mathlib.quotient_add_group.range_ker_lift_surjective {G : Type u} [add_group G] {H : Type v}
    [add_group H] (φ : G →+ H) : function.surjective ⇑(quotient_add_group.range_ker_lift φ) :=
  sorry

/-- The first isomorphism theorem (a definition): the canonical isomorphism between
`G/(ker φ)` to `range φ`. -/
def Mathlib.quotient_add_group.quotient_ker_equiv_range {G : Type u} [add_group G] {H : Type v}
    [add_group H] (φ : G →+ H) :
    quotient_add_group.quotient (add_monoid_hom.ker φ) ≃+ ↥(add_monoid_hom.range φ) :=
  add_equiv.of_bijective (quotient_add_group.range_ker_lift φ) sorry

/-- The canonical isomorphism `G/(ker φ) ≃* H` induced by a surjection `φ : G →* H`. -/
def Mathlib.quotient_add_group.quotient_ker_equiv_of_surjective {G : Type u} [add_group G]
    {H : Type v} [add_group H] (φ : G →+ H) (hφ : function.surjective ⇑φ) :
    quotient_add_group.quotient (add_monoid_hom.ker φ) ≃+ H :=
  add_equiv.of_bijective (quotient_add_group.ker_lift φ) sorry

end Mathlib