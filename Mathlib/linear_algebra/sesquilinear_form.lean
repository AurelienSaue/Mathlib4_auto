/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.module.basic
import Mathlib.ring_theory.ring_invo
import Mathlib.PostPort

universes u v l u_1 u_2 

namespace Mathlib

/-!
# Sesquilinear form

This file defines a sesquilinear form over a module. The definition requires a ring antiautomorphism
on the scalar ring. Basic ideas such as
orthogonality are also introduced.

A sesquilinear form on an `R`-module `M`, is a function from `M × M` to `R`, that is linear in the
first argument and antilinear in the second, with respect to an antiautomorphism on `R` (an
antiisomorphism from `R` to `R`).

## Notations

Given any term `S` of type `sesq_form`, due to a coercion, can use the notation `S x y` to
refer to the function field, ie. `S x y = S.sesq x y`.

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/

/-- A sesquilinear form over a module  -/
structure sesq_form (R : Type u) (M : Type v) [ring R] (I : R ≃+* (Rᵒᵖ)) [add_comm_group M] [module R M] 
where
  sesq : M → M → R
  sesq_add_left : ∀ (x y z : M), sesq (x + y) z = sesq x z + sesq y z
  sesq_smul_left : ∀ (a : R) (x y : M), sesq (a • x) y = a * sesq x y
  sesq_add_right : ∀ (x y z : M), sesq x (y + z) = sesq x y + sesq x z
  sesq_smul_right : ∀ (a : R) (x y : M), sesq x (a • y) = opposite.unop (coe_fn I a) * sesq x y

namespace sesq_form


protected instance has_coe_to_fun {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} : has_coe_to_fun (sesq_form R M I) :=
  has_coe_to_fun.mk (fun (S : sesq_form R M I) => M → M → R) fun (S : sesq_form R M I) => sesq S

theorem add_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) (y : M) (z : M) : coe_fn S (x + y) z = coe_fn S x z + coe_fn S y z :=
  sesq_add_left S x y z

theorem smul_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (a : R) (x : M) (y : M) : coe_fn S (a • x) y = a * coe_fn S x y :=
  sesq_smul_left S a x y

theorem add_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) (y : M) (z : M) : coe_fn S x (y + z) = coe_fn S x y + coe_fn S x z :=
  sesq_add_right S x y z

theorem smul_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (a : R) (x : M) (y : M) : coe_fn S x (a • y) = opposite.unop (coe_fn I a) * coe_fn S x y :=
  sesq_smul_right S a x y

theorem zero_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) : coe_fn S 0 x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn S 0 x = 0)) (Eq.symm (zero_smul R 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn S (0 • 0) x = 0)) (smul_left 0 0 x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 * coe_fn S 0 x = 0)) (zero_mul (coe_fn S 0 x)))) (Eq.refl 0)))

theorem zero_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) : coe_fn S x 0 = 0 := sorry

theorem neg_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) (y : M) : coe_fn S (-x) y = -coe_fn S x y := sorry

theorem neg_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) (y : M) : coe_fn S x (-y) = -coe_fn S x y := sorry

theorem sub_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) (y : M) (z : M) : coe_fn S (x - y) z = coe_fn S x z - coe_fn S y z := sorry

theorem sub_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) (y : M) (z : M) : coe_fn S x (y - z) = coe_fn S x y - coe_fn S x z := sorry

theorem ext {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} {D : sesq_form R M I} (H : ∀ (x y : M), coe_fn S x y = coe_fn D x y) : S = D := sorry

protected instance add_comm_group {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} : add_comm_group (sesq_form R M I) :=
  add_comm_group.mk
    (fun (S D : sesq_form R M I) => mk (fun (x y : M) => coe_fn S x y + coe_fn D x y) sorry sorry sorry sorry) sorry
    (mk (fun (x y : M) => 0) sorry sorry sorry sorry) sorry sorry
    (fun (S : sesq_form R M I) => mk (fun (x y : M) => -sesq S x y) sorry sorry sorry sorry)
    (add_group.sub._default
      (fun (S D : sesq_form R M I) => mk (fun (x y : M) => coe_fn S x y + coe_fn D x y) sorry sorry sorry sorry) sorry
      (mk (fun (x y : M) => 0) sorry sorry sorry sorry) sorry sorry
      fun (S : sesq_form R M I) => mk (fun (x y : M) => -sesq S x y) sorry sorry sorry sorry)
    sorry sorry

protected instance inhabited {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} : Inhabited (sesq_form R M I) :=
  { default := 0 }

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} (S : sesq_form R M I) (x : M) (y : M) :=
  coe_fn S x y = 0

theorem ortho_zero {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (x : M) : is_ortho S 0 x :=
  zero_left x

theorem is_add_monoid_hom_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} (S : sesq_form R M I) (x : M) : is_add_monoid_hom fun (z : M) => coe_fn S z x :=
  is_add_monoid_hom.mk (zero_left x)

theorem is_add_monoid_hom_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} (S : sesq_form R M I) (x : M) : is_add_monoid_hom fun (z : M) => coe_fn S x z :=
  is_add_monoid_hom.mk (zero_right x)

theorem map_sum_left {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {α : Type u_1} (S : sesq_form R M I) (t : finset α) (g : α → M) (w : M) : coe_fn S (finset.sum t fun (i : α) => g i) w = finset.sum t fun (i : α) => coe_fn S (g i) w :=
  Eq.symm (finset.sum_hom t fun (z : M) => coe_fn S z w)

theorem map_sum_right {R : Type u} {M : Type v} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {α : Type u_1} (S : sesq_form R M I) (t : finset α) (g : α → M) (w : M) : coe_fn S w (finset.sum t fun (i : α) => g i) = finset.sum t fun (i : α) => coe_fn S w (g i) :=
  Eq.symm (finset.sum_hom t fun (z : M) => coe_fn S w z)

protected instance to_module {R : Type u_1} [comm_ring R] {M : Type v} [add_comm_group M] [module R M] {J : R ≃+* (Rᵒᵖ)} : module R (sesq_form R M J) :=
  semimodule.mk sorry sorry

theorem ortho_smul_left {R : Type u_1} [domain R] {M : Type v} [add_comm_group M] [module R M] {K : R ≃+* (Rᵒᵖ)} {G : sesq_form R M K} {x : M} {y : M} {a : R} (ha : a ≠ 0) : is_ortho G x y ↔ is_ortho G (a • x) y := sorry

theorem ortho_smul_right {R : Type u_1} [domain R] {M : Type v} [add_comm_group M] [module R M] {K : R ≃+* (Rᵒᵖ)} {G : sesq_form R M K} {x : M} {y : M} {a : R} (ha : a ≠ 0) : is_ortho G x y ↔ is_ortho G x (a • y) := sorry

end sesq_form


namespace refl_sesq_form


/-- The proposition that a sesquilinear form is reflexive -/
def is_refl {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} (S : sesq_form R M I) :=
  ∀ (x y : M), coe_fn S x y = 0 → coe_fn S y x = 0

theorem eq_zero {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_refl S) {x : M} {y : M} : coe_fn S x y = 0 → coe_fn S y x = 0 :=
  H x y

theorem ortho_sym {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_refl S) {x : M} {y : M} : sesq_form.is_ortho S x y ↔ sesq_form.is_ortho S y x :=
  { mp := eq_zero H, mpr := eq_zero H }

end refl_sesq_form


namespace sym_sesq_form


/-- The proposition that a sesquilinear form is symmetric -/
def is_sym {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} (S : sesq_form R M I) :=
  ∀ (x y : M), opposite.unop (coe_fn I (coe_fn S x y)) = coe_fn S y x

theorem sym {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_sym S) (x : M) (y : M) : opposite.unop (coe_fn I (coe_fn S x y)) = coe_fn S y x :=
  H x y

theorem is_refl {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_sym S) : refl_sesq_form.is_refl S := sorry

theorem ortho_sym {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_sym S) {x : M} {y : M} : sesq_form.is_ortho S x y ↔ sesq_form.is_ortho S y x :=
  refl_sesq_form.ortho_sym (is_refl H)

end sym_sesq_form


namespace alt_sesq_form


/-- The proposition that a sesquilinear form is alternating -/
def is_alt {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} (S : sesq_form R M I) :=
  ∀ (x : M), coe_fn S x x = 0

theorem self_eq_zero {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_alt S) (x : M) : coe_fn S x x = 0 :=
  H x

theorem neg {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {I : R ≃+* (Rᵒᵖ)} {S : sesq_form R M I} (H : is_alt S) (x : M) (y : M) : -coe_fn S x y = coe_fn S y x := sorry

