/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.equiv.mul_add_aut
import Mathlib.logic.function.basic
import Mathlib.group_theory.subgroup
import PostPort

universes u_1 u_2 l u_3 u_4 u_5 

namespace Mathlib

/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`φ` from `G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* N ⋊[φ] G` and
`inr : G →* N ⋊[φ] G`, and `lift` can be used to define maps `N ⋊[φ] G →* H`
out of the semidirect product given maps `f₁ : N →* H` and `f₂ : G →* H` that satisfy the
condition `∀ n g, f₁ (φ g n) = f₂ g * f₁ n * f₂ g⁻¹`

## Notation

This file introduces the global notation `N ⋊[φ] G` for `semidirect_product N G φ`

## Tags
group, semidirect product
-/

/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
structure semidirect_product (N : Type u_1) (G : Type u_2) [group N] [group G] (φ : G →* mul_aut N) 
where
  left : N
  right : G

namespace semidirect_product


protected instance group {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : group (semidirect_product N G φ) :=
  group.mk mul_aux mul_assoc_aux one_aux one_mul_aux mul_one_aux inv_aux
    (div_inv_monoid.div._default mul_aux mul_assoc_aux one_aux one_mul_aux mul_one_aux inv_aux) mul_left_inv_aux

protected instance inhabited {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : Inhabited (semidirect_product N G φ) :=
  { default := 1 }

@[simp] theorem one_left {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : left 1 = 1 :=
  rfl

@[simp] theorem one_right {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : right 1 = 1 :=
  rfl

@[simp] theorem inv_left {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (a : semidirect_product N G φ) : left (a⁻¹) = coe_fn (coe_fn φ (right a⁻¹)) (left a⁻¹) :=
  rfl

@[simp] theorem inv_right {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (a : semidirect_product N G φ) : right (a⁻¹) = (right a⁻¹) :=
  rfl

@[simp] theorem mul_left {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (a : semidirect_product N G φ) (b : semidirect_product N G φ) : left (a * b) = left a * coe_fn (coe_fn φ (right a)) (left b) :=
  rfl

@[simp] theorem mul_right {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (a : semidirect_product N G φ) (b : semidirect_product N G φ) : right (a * b) = right a * right b :=
  rfl

/-- The canonical map `N →* N ⋊[φ] G` sending `n` to `⟨n, 1⟩` -/
def inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : N →* semidirect_product N G φ :=
  monoid_hom.mk (fun (n : N) => mk n 1) sorry sorry

@[simp] theorem left_inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (n : N) : left (coe_fn inl n) = n :=
  rfl

@[simp] theorem right_inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (n : N) : right (coe_fn inl n) = 1 :=
  rfl

theorem inl_injective {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : function.injective ⇑inl :=
  iff.mpr function.injective_iff_has_left_inverse (Exists.intro left left_inl)

@[simp] theorem inl_inj {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {n₁ : N} {n₂ : N} : coe_fn inl n₁ = coe_fn inl n₂ ↔ n₁ = n₂ :=
  function.injective.eq_iff inl_injective

/-- The canonical map `G →* N ⋊[φ] G` sending `g` to `⟨1, g⟩` -/
def inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : G →* semidirect_product N G φ :=
  monoid_hom.mk (fun (g : G) => mk 1 g) sorry sorry

@[simp] theorem left_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (g : G) : left (coe_fn inr g) = 1 :=
  rfl

@[simp] theorem right_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (g : G) : right (coe_fn inr g) = g :=
  rfl

theorem inr_injective {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : function.injective ⇑inr :=
  iff.mpr function.injective_iff_has_left_inverse (Exists.intro right right_inr)

@[simp] theorem inr_inj {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {g₁ : G} {g₂ : G} : coe_fn inr g₁ = coe_fn inr g₂ ↔ g₁ = g₂ :=
  function.injective.eq_iff inr_injective

theorem inl_aut {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (g : G) (n : N) : coe_fn inl (coe_fn (coe_fn φ g) n) = coe_fn inr g * coe_fn inl n * coe_fn inr (g⁻¹) := sorry

theorem inl_aut_inv {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (g : G) (n : N) : coe_fn inl (coe_fn (coe_fn φ g⁻¹) n) = coe_fn inr (g⁻¹) * coe_fn inl n * coe_fn inr g := sorry

@[simp] theorem mk_eq_inl_mul_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (g : G) (n : N) : mk n g = coe_fn inl n * coe_fn inr g := sorry

@[simp] theorem inl_left_mul_inr_right {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (x : semidirect_product N G φ) : coe_fn inl (left x) * coe_fn inr (right x) = x := sorry

/-- The canonical projection map `N ⋊[φ] G →* G`, as a group hom. -/
def right_hom {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : semidirect_product N G φ →* G :=
  monoid_hom.mk right sorry sorry

@[simp] theorem right_hom_eq_right {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : ⇑right_hom = right :=
  rfl

@[simp] theorem right_hom_comp_inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : monoid_hom.comp right_hom inl = 1 := sorry

@[simp] theorem right_hom_comp_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : monoid_hom.comp right_hom inr = monoid_hom.id G := sorry

@[simp] theorem right_hom_inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (n : N) : coe_fn right_hom (coe_fn inl n) = 1 := sorry

@[simp] theorem right_hom_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} (g : G) : coe_fn right_hom (coe_fn inr g) = g := sorry

theorem right_hom_surjective {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : function.surjective ⇑right_hom :=
  iff.mpr function.surjective_iff_has_right_inverse (Exists.intro (⇑inr) right_hom_inr)

theorem range_inl_eq_ker_right_hom {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} : monoid_hom.range inl = monoid_hom.ker right_hom := sorry

/-- Define a group hom `N ⋊[φ] G →* H`, by defining maps `N →* H` and `G →* H`  -/
def lift {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} (f₁ : N →* H) (f₂ : G →* H) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn f₂ g))) f₁) : semidirect_product N G φ →* H :=
  monoid_hom.mk (fun (a : semidirect_product N G φ) => coe_fn f₁ (left a) * coe_fn f₂ (right a)) sorry sorry

@[simp] theorem lift_inl {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} (f₁ : N →* H) (f₂ : G →* H) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn f₂ g))) f₁) (n : N) : coe_fn (lift f₁ f₂ h) (coe_fn inl n) = coe_fn f₁ n := sorry

@[simp] theorem lift_comp_inl {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} (f₁ : N →* H) (f₂ : G →* H) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn f₂ g))) f₁) : monoid_hom.comp (lift f₁ f₂ h) inl = f₁ := sorry

@[simp] theorem lift_inr {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} (f₁ : N →* H) (f₂ : G →* H) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn f₂ g))) f₁) (g : G) : coe_fn (lift f₁ f₂ h) (coe_fn inr g) = coe_fn f₂ g := sorry

@[simp] theorem lift_comp_inr {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} (f₁ : N →* H) (f₂ : G →* H) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn f₂ g))) f₁) : monoid_hom.comp (lift f₁ f₂ h) inr = f₂ := sorry

theorem lift_unique {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} (F : semidirect_product N G φ →* H) : F =
  lift (monoid_hom.comp F inl) (monoid_hom.comp F inr)
    fun (_x : G) =>
      monoid_hom.ext
        fun (x : N) =>
          eq.mpr
            (id
              (Eq.trans
                (Eq.trans
                  (Eq.trans
                    ((fun (a a_1 : H) (e_1 : a = a_1) (ᾰ ᾰ_1 : H) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                      (coe_fn (monoid_hom.comp (monoid_hom.comp F inl) (mul_equiv.to_monoid_hom (coe_fn φ _x))) x)
                      (coe_fn F (coe_fn inr _x) * coe_fn F (coe_fn inl x) * (coe_fn F (coe_fn inr _x)⁻¹))
                      (Eq.trans
                        (Eq.trans
                          (Eq.trans
                            (Eq.trans
                              (Eq.trans
                                (Eq.trans
                                  (congr_fun
                                    (monoid_hom.coe_comp (monoid_hom.comp F inl)
                                      (mul_equiv.to_monoid_hom (coe_fn φ _x)))
                                    x)
                                  ((fun (f f_1 : N → H) (e_1 : f = f_1) (g g_1 : N → N) (e_2 : g = g_1) (ᾰ ᾰ_1 : N)
                                      (e_3 : ᾰ = ᾰ_1) => congr (congr (congr_arg function.comp e_1) e_2) e_3)
                                    (⇑(monoid_hom.comp F inl)) (⇑F ∘ ⇑inl) (monoid_hom.coe_comp F inl)
                                    (⇑(mul_equiv.to_monoid_hom (coe_fn φ _x))) (⇑(coe_fn φ _x))
                                    (mul_equiv.coe_to_monoid_hom (coe_fn φ _x)) x x (Eq.refl x)))
                                (function.comp_app (⇑F ∘ ⇑inl) (⇑(coe_fn φ _x)) x))
                              (function.comp_app (⇑F) (⇑inl) (coe_fn (coe_fn φ _x) x)))
                            ((fun (x x_1 : semidirect_product N G φ →* H) (e_1 : x = x_1)
                                (ᾰ ᾰ_1 : semidirect_product N G φ) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg coe_fn e_1) e_2)
                              F F (Eq.refl F) (coe_fn inl (coe_fn (coe_fn φ _x) x))
                              (coe_fn inr _x * coe_fn inl x * (coe_fn inr _x⁻¹))
                              (Eq.trans (inl_aut _x x)
                                ((fun (ᾰ ᾰ_1 : semidirect_product N G φ) (e_2 : ᾰ = ᾰ_1)
                                    (ᾰ_2 ᾰ_3 : semidirect_product N G φ) (e_3 : ᾰ_2 = ᾰ_3) =>
                                    congr (congr_arg Mul.mul e_2) e_3)
                                  (coe_fn inr _x * coe_fn inl x) (coe_fn inr _x * coe_fn inl x)
                                  (Eq.refl (coe_fn inr _x * coe_fn inl x)) (coe_fn inr (_x⁻¹)) (coe_fn inr _x⁻¹)
                                  (monoid_hom.map_inv inr _x)))))
                          (monoid_hom.map_mul_inv F (coe_fn inr _x * coe_fn inl x) (coe_fn inr _x)))
                        ((fun (ᾰ ᾰ_1 : H) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : H) (e_3 : ᾰ_2 = ᾰ_3) =>
                            congr (congr_arg Mul.mul e_2) e_3)
                          (coe_fn F (coe_fn inr _x * coe_fn inl x)) (coe_fn F (coe_fn inr _x) * coe_fn F (coe_fn inl x))
                          (monoid_hom.map_mul F (coe_fn inr _x) (coe_fn inl x)) (coe_fn F (coe_fn inr _x)⁻¹)
                          (coe_fn F (coe_fn inr _x)⁻¹) (Eq.refl (coe_fn F (coe_fn inr _x)⁻¹))))
                      (coe_fn
                        (monoid_hom.comp
                          (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn (monoid_hom.comp F inr) _x)))
                          (monoid_hom.comp F inl))
                        x)
                      (coe_fn F (coe_fn inr _x) * coe_fn F (coe_fn inl x) * (coe_fn F (coe_fn inr _x)⁻¹))
                      (Eq.trans
                        (Eq.trans
                          (Eq.trans
                            (Eq.trans
                              (Eq.trans
                                ((fun (x x_1 : N →* H) (e_1 : x = x_1) (ᾰ ᾰ_1 : N) (e_2 : ᾰ = ᾰ_1) =>
                                    congr (congr_arg coe_fn e_1) e_2)
                                  (monoid_hom.comp
                                    (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn (monoid_hom.comp F inr) _x)))
                                    (monoid_hom.comp F inl))
                                  (monoid_hom.comp
                                    (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x))))
                                    (monoid_hom.comp F inl))
                                  ((fun (hnp hnp_1 : H →* H) (e_1 : hnp = hnp_1) (hmn hmn_1 : N →* H)
                                      (e_2 : hmn = hmn_1) => congr (congr_arg monoid_hom.comp e_1) e_2)
                                    (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn (monoid_hom.comp F inr) _x)))
                                    (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x))))
                                    ((fun (h h_1 : H ≃* H) (e_1 : h = h_1) => congr_arg mul_equiv.to_monoid_hom e_1)
                                      (coe_fn mul_aut.conj (coe_fn (monoid_hom.comp F inr) _x))
                                      (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x)))
                                      ((fun (x x_1 : H →* mul_aut H) (e_1 : x = x_1) (ᾰ ᾰ_1 : H) (e_2 : ᾰ = ᾰ_1) =>
                                          congr (congr_arg coe_fn e_1) e_2)
                                        mul_aut.conj mul_aut.conj (Eq.refl mul_aut.conj)
                                        (coe_fn (monoid_hom.comp F inr) _x) (coe_fn F (coe_fn inr _x))
                                        (Eq.trans (congr_fun (monoid_hom.coe_comp F inr) _x)
                                          (function.comp_app (⇑F) (⇑inr) _x))))
                                    (monoid_hom.comp F inl) (monoid_hom.comp F inl) (Eq.refl (monoid_hom.comp F inl)))
                                  x x (Eq.refl x))
                                (congr_fun
                                  (monoid_hom.coe_comp
                                    (mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x))))
                                    (monoid_hom.comp F inl))
                                  x))
                              ((fun (f f_1 : H → H) (e_1 : f = f_1) (g g_1 : N → H) (e_2 : g = g_1) (ᾰ ᾰ_1 : N)
                                  (e_3 : ᾰ = ᾰ_1) => congr (congr (congr_arg function.comp e_1) e_2) e_3)
                                (⇑(mul_equiv.to_monoid_hom (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x)))))
                                (⇑(coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x))))
                                (mul_equiv.coe_to_monoid_hom (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x))))
                                (⇑(monoid_hom.comp F inl)) (⇑F ∘ ⇑inl) (monoid_hom.coe_comp F inl) x x (Eq.refl x)))
                            (function.comp_app (⇑(coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x)))) (⇑F ∘ ⇑inl) x))
                          ((fun (x x_1 : H ≃* H) (e_1 : x = x_1) (ᾰ ᾰ_1 : H) (e_2 : ᾰ = ᾰ_1) =>
                              congr (congr_arg coe_fn e_1) e_2)
                            (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x)))
                            (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x)))
                            (Eq.refl (coe_fn mul_aut.conj (coe_fn F (coe_fn inr _x)))) (function.comp (⇑F) (⇑inl) x)
                            (coe_fn F (coe_fn inl x)) (function.comp_app (⇑F) (⇑inl) x)))
                        (mul_aut.conj_apply (coe_fn F (coe_fn inr _x)) (coe_fn F (coe_fn inl x)))))
                    (propext (mul_left_inj (coe_fn F (coe_fn inr _x)⁻¹))))
                  (propext (mul_left_inj (coe_fn F (coe_fn inl x)))))
                (propext (eq_self_iff_true (coe_fn F (coe_fn inr _x))))))
            trivial := sorry

/-- Two maps out of the semidirect product are equal if they're equal after composition
  with both `inl` and `inr` -/
theorem hom_ext {N : Type u_1} {G : Type u_2} {H : Type u_3} [group N] [group G] [group H] {φ : G →* mul_aut N} {f : semidirect_product N G φ →* H} {g : semidirect_product N G φ →* H} (hl : monoid_hom.comp f inl = monoid_hom.comp g inl) (hr : monoid_hom.comp f inr = monoid_hom.comp g inr) : f = g := sorry

/-- Define a map from `N ⋊[φ] G` to `N₁ ⋊[φ₁] G₁` given maps `N →* N₁` and `G →* G₁` that
  satisfy a commutativity condition `∀ n g, f₁ (φ g n) = φ₁ (f₂ g) (f₁ n)`.  -/
def map {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) : semidirect_product N G φ →* semidirect_product N₁ G₁ φ₁ :=
  monoid_hom.mk (fun (x : semidirect_product N G φ) => mk (coe_fn f₁ (left x)) (coe_fn f₂ (right x))) sorry sorry

@[simp] theorem map_left {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) (g : semidirect_product N G φ) : left (coe_fn (map f₁ f₂ h) g) = coe_fn f₁ (left g) :=
  rfl

@[simp] theorem map_right {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) (g : semidirect_product N G φ) : right (coe_fn (map f₁ f₂ h) g) = coe_fn f₂ (right g) :=
  rfl

@[simp] theorem right_hom_comp_map {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) : monoid_hom.comp right_hom (map f₁ f₂ h) = monoid_hom.comp f₂ right_hom :=
  rfl

@[simp] theorem map_inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) (n : N) : coe_fn (map f₁ f₂ h) (coe_fn inl n) = coe_fn inl (coe_fn f₁ n) := sorry

@[simp] theorem map_comp_inl {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) : monoid_hom.comp (map f₁ f₂ h) inl = monoid_hom.comp inl f₁ := sorry

@[simp] theorem map_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) (g : G) : coe_fn (map f₁ f₂ h) (coe_fn inr g) = coe_fn inr (coe_fn f₂ g) := sorry

@[simp] theorem map_comp_inr {N : Type u_1} {G : Type u_2} [group N] [group G] {φ : G →* mul_aut N} {N₁ : Type u_4} {G₁ : Type u_5} [group N₁] [group G₁] {φ₁ : G₁ →* mul_aut N₁} (f₁ : N →* N₁) (f₂ : G →* G₁) (h : ∀ (g : G),
  monoid_hom.comp f₁ (mul_equiv.to_monoid_hom (coe_fn φ g)) =
    monoid_hom.comp (mul_equiv.to_monoid_hom (coe_fn φ₁ (coe_fn f₂ g))) f₁) : monoid_hom.comp (map f₁ f₂ h) inr = monoid_hom.comp inr f₂ := sorry

