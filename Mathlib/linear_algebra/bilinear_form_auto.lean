/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.matrix
import Mathlib.linear_algebra.tensor_product
import Mathlib.linear_algebra.nonsingular_inverse
import PostPort

universes u v l u_1 w u_2 u_3 u_4 u_5 

namespace Mathlib

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive,
symmetric and alternating bilinear forms. Adjoints of linear maps
with respect to a bilinear form are also introduced.

A bilinear form on an R-(semi)module M, is a function from M x M to R,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

## Notations

Given any term B of type bilin_form, due to a coercion, can use
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.

In this file we use the following type variables:
 - `M`, `M'`, ... are semimodules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are semimodules over the commutative semiring `R₂`
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

/-- `bilin_form R M` is the type of `R`-bilinear functions `M → M → R`. -/
structure bilin_form (R : Type u) (M : Type v) [semiring R] [add_comm_monoid M] [semimodule R M] 
where
  bilin : M → M → R
  bilin_add_left : ∀ (x y z : M), bilin (x + y) z = bilin x z + bilin y z
  bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * bilin x y
  bilin_add_right : ∀ (x y z : M), bilin x (y + z) = bilin x y + bilin x z
  bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * bilin x y

namespace bilin_form


protected instance has_coe_to_fun {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : has_coe_to_fun (bilin_form R M) :=
  has_coe_to_fun.mk (fun (B : bilin_form R M) => M → M → R) fun (B : bilin_form R M) => bilin B

@[simp] theorem coe_fn_mk {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (f : M → M → R) (h₁ : ∀ (x y z : M), f (x + y) z = f x z + f y z) (h₂ : ∀ (a : R) (x y : M), f (a • x) y = a * f x y) (h₃ : ∀ (x y z : M), f x (y + z) = f x y + f x z) (h₄ : ∀ (a : R) (x y : M), f x (a • y) = a * f x y) : ⇑(mk f h₁ h₂ h₃ h₄) = f :=
  rfl

theorem coe_fn_congr {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {x : M} {x' : M} {y : M} {y' : M} : x = x' → y = y' → coe_fn B x y = coe_fn B x' y' := sorry

@[simp] theorem add_left {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (x : M) (y : M) (z : M) : coe_fn B (x + y) z = coe_fn B x z + coe_fn B y z :=
  bilin_add_left B x y z

@[simp] theorem smul_left {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (a : R) (x : M) (y : M) : coe_fn B (a • x) y = a * coe_fn B x y :=
  bilin_smul_left B a x y

@[simp] theorem add_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (x : M) (y : M) (z : M) : coe_fn B x (y + z) = coe_fn B x y + coe_fn B x z :=
  bilin_add_right B x y z

@[simp] theorem smul_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (a : R) (x : M) (y : M) : coe_fn B x (a • y) = a * coe_fn B x y :=
  bilin_smul_right B a x y

@[simp] theorem zero_left {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (x : M) : coe_fn B 0 x = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn B 0 x = 0)) (Eq.symm (zero_smul R 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn B (0 • 0) x = 0)) (smul_left 0 0 x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 * coe_fn B 0 x = 0)) (zero_mul (coe_fn B 0 x)))) (Eq.refl 0)))

@[simp] theorem zero_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (x : M) : coe_fn B x 0 = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn B x 0 = 0)) (Eq.symm (zero_smul R 0))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn B x (0 • 0) = 0)) (smul_right 0 x 0)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (0 * coe_fn B x 0 = 0)) (zero_mul (coe_fn B x 0)))) (Eq.refl 0)))

@[simp] theorem neg_left {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} (x : M₁) (y : M₁) : coe_fn B₁ (-x) y = -coe_fn B₁ x y := sorry

@[simp] theorem neg_right {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} (x : M₁) (y : M₁) : coe_fn B₁ x (-y) = -coe_fn B₁ x y := sorry

@[simp] theorem sub_left {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} (x : M₁) (y : M₁) (z : M₁) : coe_fn B₁ (x - y) z = coe_fn B₁ x z - coe_fn B₁ y z := sorry

@[simp] theorem sub_right {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} (x : M₁) (y : M₁) (z : M₁) : coe_fn B₁ x (y - z) = coe_fn B₁ x y - coe_fn B₁ x z := sorry

theorem ext {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {D : bilin_form R M} (H : ∀ (x y : M), coe_fn B x y = coe_fn D x y) : B = D := sorry

protected instance add_comm_monoid {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : add_comm_monoid (bilin_form R M) :=
  add_comm_monoid.mk
    (fun (B D : bilin_form R M) => mk (fun (x y : M) => coe_fn B x y + coe_fn D x y) sorry sorry sorry sorry) sorry
    (mk (fun (x y : M) => 0) sorry sorry sorry sorry) sorry sorry sorry

protected instance add_comm_group {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] : add_comm_group (bilin_form R₁ M₁) :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry
    (fun (B : bilin_form R₁ M₁) => mk (fun (x y : M₁) => -bilin B x y) sorry sorry sorry sorry)
    (add_group.sub._default add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry
      fun (B : bilin_form R₁ M₁) => mk (fun (x y : M₁) => -bilin B x y) sorry sorry sorry sorry)
    sorry sorry

@[simp] theorem add_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {D : bilin_form R M} (x : M) (y : M) : coe_fn (B + D) x y = coe_fn B x y + coe_fn D x y :=
  rfl

@[simp] theorem neg_apply {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} (x : M₁) (y : M₁) : coe_fn (-B₁) x y = -coe_fn B₁ x y :=
  rfl

protected instance inhabited {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] : Inhabited (bilin_form R M) :=
  { default := 0 }

protected instance semimodule {M : Type v} [add_comm_monoid M] {R : Type u_1} [comm_semiring R] [semimodule R M] : semimodule R (bilin_form R M) :=
  semimodule.mk sorry sorry

@[simp] theorem smul_apply {M : Type v} [add_comm_monoid M] {R : Type u_1} [comm_semiring R] [semimodule R M] (B : bilin_form R M) (a : R) (x : M) (y : M) : coe_fn (a • B) x y = a • coe_fn B x y :=
  rfl

end bilin_form


/-- A map with two arguments that is linear in both is a bilinear form.

This is an auxiliary definition for the full linear equivalence `linear_map.to_bilin`.
-/
def linear_map.to_bilin_aux {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (f : linear_map R₂ M₂ (linear_map R₂ M₂ R₂)) : bilin_form R₂ M₂ :=
  bilin_form.mk (fun (x y : M₂) => coe_fn (coe_fn f x) y) sorry sorry sorry sorry

/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/
def linear_map.to_bilin {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] : linear_equiv R₂ (linear_map R₂ M₂ (linear_map R₂ M₂ R₂)) (bilin_form R₂ M₂) :=
  linear_equiv.mk linear_map.to_bilin_aux sorry sorry
    (fun (F : bilin_form R₂ M₂) => linear_map.mk₂ R₂ ⇑F sorry sorry sorry sorry) sorry sorry

/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/
def bilin_form.to_lin {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] : linear_equiv R₂ (bilin_form R₂ M₂) (linear_map R₂ M₂ (linear_map R₂ M₂ R₂)) :=
  linear_equiv.symm linear_map.to_bilin

@[simp] theorem linear_map.to_bilin_aux_eq {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (f : linear_map R₂ M₂ (linear_map R₂ M₂ R₂)) : linear_map.to_bilin_aux f = coe_fn linear_map.to_bilin f :=
  rfl

@[simp] theorem linear_map.to_bilin_symm {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] : linear_equiv.symm linear_map.to_bilin = bilin_form.to_lin :=
  rfl

@[simp] theorem bilin_form.to_lin_symm {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] : linear_equiv.symm bilin_form.to_lin = linear_map.to_bilin :=
  linear_equiv.symm_symm linear_map.to_bilin

@[simp] theorem to_linear_map_apply {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {B₂ : bilin_form R₂ M₂} (x : M₂) : ⇑(coe_fn (coe_fn bilin_form.to_lin B₂) x) = coe_fn B₂ x :=
  rfl

@[simp] theorem map_sum_left {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {B₂ : bilin_form R₂ M₂} {α : Type u_1} (t : finset α) (g : α → M₂) (w : M₂) : coe_fn B₂ (finset.sum t fun (i : α) => g i) w = finset.sum t fun (i : α) => coe_fn B₂ (g i) w := sorry

@[simp] theorem map_sum_right {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {B₂ : bilin_form R₂ M₂} {α : Type u_1} (t : finset α) (w : M₂) (g : α → M₂) : coe_fn B₂ w (finset.sum t fun (i : α) => g i) = finset.sum t fun (i : α) => coe_fn B₂ w (g i) := sorry

namespace bilin_form


/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {M' : Type w} [add_comm_monoid M'] [semimodule R M'] (B : bilin_form R M') (l : linear_map R M M') (r : linear_map R M M') : bilin_form R M :=
  mk (fun (x y : M) => coe_fn B (coe_fn l x) (coe_fn r y)) sorry sorry sorry sorry

/-- Apply a linear map to the left argument of a bilinear form. -/
def comp_left {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (f : linear_map R M M) : bilin_form R M :=
  comp B f linear_map.id

/-- Apply a linear map to the right argument of a bilinear form. -/
def comp_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (f : linear_map R M M) : bilin_form R M :=
  comp B linear_map.id f

theorem comp_comp {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {M' : Type w} [add_comm_monoid M'] [semimodule R M'] {M'' : Type u_1} [add_comm_monoid M''] [semimodule R M''] (B : bilin_form R M'') (l : linear_map R M M') (r : linear_map R M M') (l' : linear_map R M' M'') (r' : linear_map R M' M'') : comp (comp B l' r') l r = comp B (linear_map.comp l' l) (linear_map.comp r' r) :=
  rfl

@[simp] theorem comp_left_comp_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (l : linear_map R M M) (r : linear_map R M M) : comp_right (comp_left B l) r = comp B l r :=
  rfl

@[simp] theorem comp_right_comp_left {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (l : linear_map R M M) (r : linear_map R M M) : comp_left (comp_right B r) l = comp B l r :=
  rfl

@[simp] theorem comp_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {M' : Type w} [add_comm_monoid M'] [semimodule R M'] (B : bilin_form R M') (l : linear_map R M M') (r : linear_map R M M') (v : M) (w : M) : coe_fn (comp B l r) v w = coe_fn B (coe_fn l v) (coe_fn r w) :=
  rfl

@[simp] theorem comp_left_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (f : linear_map R M M) (v : M) (w : M) : coe_fn (comp_left B f) v w = coe_fn B (coe_fn f v) w :=
  rfl

@[simp] theorem comp_right_apply {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (f : linear_map R M M) (v : M) (w : M) : coe_fn (comp_right B f) v w = coe_fn B v (coe_fn f w) :=
  rfl

theorem comp_injective {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {M' : Type w} [add_comm_monoid M'] [semimodule R M'] (B₁ : bilin_form R M') (B₂ : bilin_form R M') (l : linear_map R M M') (r : linear_map R M M') (hₗ : function.surjective ⇑l) (hᵣ : function.surjective ⇑r) : comp B₁ l r = comp B₂ l r ↔ B₁ = B₂ := sorry

/-- Apply a linear equivalence on the arguments of a bilinear form. -/
def congr {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {M₂' : Type u_1} [add_comm_monoid M₂'] [semimodule R₂ M₂'] (e : linear_equiv R₂ M₂ M₂') : linear_equiv R₂ (bilin_form R₂ M₂) (bilin_form R₂ M₂') :=
  linear_equiv.mk (fun (B : bilin_form R₂ M₂) => comp B ↑(linear_equiv.symm e) ↑(linear_equiv.symm e)) sorry sorry
    (fun (B : bilin_form R₂ M₂') => comp B ↑e ↑e) sorry sorry

@[simp] theorem congr_apply {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {M₂' : Type u_1} [add_comm_monoid M₂'] [semimodule R₂ M₂'] (e : linear_equiv R₂ M₂ M₂') (B : bilin_form R₂ M₂) (x : M₂') (y : M₂') : coe_fn (coe_fn (congr e) B) x y = coe_fn B (coe_fn (linear_equiv.symm e) x) (coe_fn (linear_equiv.symm e) y) :=
  rfl

@[simp] theorem congr_symm {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {M₂' : Type u_1} [add_comm_monoid M₂'] [semimodule R₂ M₂'] (e : linear_equiv R₂ M₂ M₂') : linear_equiv.symm (congr e) = congr (linear_equiv.symm e) := sorry

theorem congr_comp {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {M₂' : Type u_1} [add_comm_monoid M₂'] [semimodule R₂ M₂'] {M₂'' : Type u_2} [add_comm_monoid M₂''] [semimodule R₂ M₂''] (e : linear_equiv R₂ M₂ M₂') (B : bilin_form R₂ M₂) (l : linear_map R₂ M₂'' M₂') (r : linear_map R₂ M₂'' M₂') : comp (coe_fn (congr e) B) l r =
  comp B (linear_map.comp (↑(linear_equiv.symm e)) l) (linear_map.comp (↑(linear_equiv.symm e)) r) :=
  rfl

theorem comp_congr {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {M₂' : Type u_1} [add_comm_monoid M₂'] [semimodule R₂ M₂'] {M₂'' : Type u_2} [add_comm_monoid M₂''] [semimodule R₂ M₂''] (e : linear_equiv R₂ M₂' M₂'') (B : bilin_form R₂ M₂) (l : linear_map R₂ M₂' M₂) (r : linear_map R₂ M₂' M₂) : coe_fn (congr e) (comp B l r) =
  comp B (linear_map.comp l ↑(linear_equiv.symm e)) (linear_map.comp r ↑(linear_equiv.symm e)) :=
  rfl

/-- `lin_mul_lin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def lin_mul_lin {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (f : linear_map R₂ M₂ R₂) (g : linear_map R₂ M₂ R₂) : bilin_form R₂ M₂ :=
  mk (fun (x y : M₂) => coe_fn f x * coe_fn g y) sorry sorry sorry sorry

@[simp] theorem lin_mul_lin_apply {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {f : linear_map R₂ M₂ R₂} {g : linear_map R₂ M₂ R₂} (x : M₂) (y : M₂) : coe_fn (lin_mul_lin f g) x y = coe_fn f x * coe_fn g y :=
  rfl

@[simp] theorem lin_mul_lin_comp {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {M₂' : Type u_1} [add_comm_monoid M₂'] [semimodule R₂ M₂'] {f : linear_map R₂ M₂ R₂} {g : linear_map R₂ M₂ R₂} (l : linear_map R₂ M₂' M₂) (r : linear_map R₂ M₂' M₂) : comp (lin_mul_lin f g) l r = lin_mul_lin (linear_map.comp f l) (linear_map.comp g r) :=
  rfl

@[simp] theorem lin_mul_lin_comp_left {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {f : linear_map R₂ M₂ R₂} {g : linear_map R₂ M₂ R₂} (l : linear_map R₂ M₂ M₂) : comp_left (lin_mul_lin f g) l = lin_mul_lin (linear_map.comp f l) g :=
  rfl

@[simp] theorem lin_mul_lin_comp_right {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {f : linear_map R₂ M₂ R₂} {g : linear_map R₂ M₂ R₂} (r : linear_map R₂ M₂ M₂) : comp_right (lin_mul_lin f g) r = lin_mul_lin f (linear_map.comp g r) :=
  rfl

/-- The proposition that two elements of a bilinear form space are orthogonal -/
def is_ortho {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (x : M) (y : M)  :=
  coe_fn B x y = 0

theorem ortho_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (x : M) : is_ortho B 0 x :=
  zero_left x

@[simp] theorem is_ortho_smul_left {R₄ : Type u_2} {M₄ : Type u_3} [domain R₄] [add_comm_group M₄] [module R₄ M₄] {G : bilin_form R₄ M₄} {x : M₄} {y : M₄} {a : R₄} (ha : a ≠ 0) : is_ortho G (a • x) y ↔ is_ortho G x y := sorry

@[simp] theorem is_ortho_smul_right {R₄ : Type u_2} {M₄ : Type u_3} [domain R₄] [add_comm_group M₄] [module R₄ M₄] {G : bilin_form R₄ M₄} {x : M₄} {y : M₄} {a : R₄} (ha : a ≠ 0) : is_ortho G x (a • y) ↔ is_ortho G x y := sorry

/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
theorem ext_basis {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {B₃ : bilin_form R₃ M₃} {F₃ : bilin_form R₃ M₃} {ι : Type u_2} {b : ι → M₃} (hb : is_basis R₃ b) (h : ∀ (i j : ι), coe_fn B₃ (b i) (b j) = coe_fn F₃ (b i) (b j)) : B₃ = F₃ :=
  linear_equiv.injective to_lin (is_basis.ext hb fun (i : ι) => is_basis.ext hb fun (j : ι) => h i j)

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
theorem sum_repr_mul_repr_mul {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {B₃ : bilin_form R₃ M₃} {ι : Type u_2} {b : ι → M₃} (hb : is_basis R₃ b) (x : M₃) (y : M₃) : (finsupp.sum (coe_fn (is_basis.repr hb) x)
    fun (i : ι) (xi : R₃) =>
      finsupp.sum (coe_fn (is_basis.repr hb) y) fun (j : ι) (yj : R₃) => xi • yj • coe_fn B₃ (b i) (b j)) =
  coe_fn B₃ x y := sorry

end bilin_form


/-- The map from `matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def matrix.to_bilin'_aux {R₂ : Type u} [comm_semiring R₂] {n : Type u_1} [fintype n] (M : matrix n n R₂) : bilin_form R₂ (n → R₂) :=
  bilin_form.mk
    (fun (v w : n → R₂) => finset.sum finset.univ fun (i : n) => finset.sum finset.univ fun (j : n) => v i * M i j * w j)
    sorry sorry sorry sorry

theorem matrix.to_bilin'_aux_std_basis {R₂ : Type u} [comm_semiring R₂] {n : Type u_1} [fintype n] [DecidableEq n] (M : matrix n n R₂) (i : n) (j : n) : coe_fn (matrix.to_bilin'_aux M) (coe_fn (linear_map.std_basis R₂ (fun (ᾰ : n) => R₂) i) 1)
    (coe_fn (linear_map.std_basis R₂ (fun (ᾰ : n) => R₂) j) 1) =
  M i j := sorry

/-- The linear map from bilinear forms to `matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def bilin_form.to_matrix_aux {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {n : Type u_1} [fintype n] (b : n → M₂) : linear_map R₂ (bilin_form R₂ M₂) (matrix n n R₂) :=
  linear_map.mk (fun (B : bilin_form R₂ M₂) (i j : n) => coe_fn B (b i) (b j)) sorry sorry

theorem to_bilin'_aux_to_matrix_aux {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B₃ : bilin_form R₃ (n → R₃)) : matrix.to_bilin'_aux
    (coe_fn (bilin_form.to_matrix_aux fun (j : n) => coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) j) 1) B₃) =
  B₃ := sorry

/-! ### `to_matrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₃`.
-/

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def bilin_form.to_matrix' {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] : linear_equiv R₃ (bilin_form R₃ (n → R₃)) (matrix n n R₃) :=
  linear_equiv.mk
    (linear_map.to_fun (bilin_form.to_matrix_aux fun (j : n) => coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) j) 1))
    sorry sorry matrix.to_bilin'_aux sorry sorry

@[simp] theorem bilin_form.to_matrix_aux_std_basis {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) : coe_fn (bilin_form.to_matrix_aux fun (j : n) => coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) j) 1) B =
  coe_fn bilin_form.to_matrix' B :=
  rfl

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def matrix.to_bilin' {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] : linear_equiv R₃ (matrix n n R₃) (bilin_form R₃ (n → R₃)) :=
  linear_equiv.symm bilin_form.to_matrix'

@[simp] theorem matrix.to_bilin'_aux_eq {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (M : matrix n n R₃) : matrix.to_bilin'_aux M = coe_fn matrix.to_bilin' M :=
  rfl

theorem matrix.to_bilin'_apply {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (M : matrix n n R₃) (x : n → R₃) (y : n → R₃) : coe_fn (coe_fn matrix.to_bilin' M) x y =
  finset.sum finset.univ fun (i : n) => finset.sum finset.univ fun (j : n) => x i * M i j * y j :=
  rfl

@[simp] theorem matrix.to_bilin'_std_basis {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (M : matrix n n R₃) (i : n) (j : n) : coe_fn (coe_fn matrix.to_bilin' M) (coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) i) 1)
    (coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) j) 1) =
  M i j :=
  matrix.to_bilin'_aux_std_basis M i j

@[simp] theorem bilin_form.to_matrix'_symm {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] : linear_equiv.symm bilin_form.to_matrix' = matrix.to_bilin' :=
  rfl

@[simp] theorem matrix.to_bilin'_symm {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] : linear_equiv.symm matrix.to_bilin' = bilin_form.to_matrix' :=
  linear_equiv.symm_symm bilin_form.to_matrix'

@[simp] theorem matrix.to_bilin'_to_matrix' {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) : coe_fn matrix.to_bilin' (coe_fn bilin_form.to_matrix' B) = B :=
  linear_equiv.apply_symm_apply matrix.to_bilin' B

@[simp] theorem bilin_form.to_matrix'_to_bilin' {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (M : matrix n n R₃) : coe_fn bilin_form.to_matrix' (coe_fn matrix.to_bilin' M) = M :=
  linear_equiv.apply_symm_apply bilin_form.to_matrix' M

@[simp] theorem bilin_form.to_matrix'_apply {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) (i : n) (j : n) : coe_fn bilin_form.to_matrix' B i j =
  coe_fn B (coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) i) 1)
    (coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) j) 1) :=
  rfl

@[simp] theorem bilin_form.to_matrix'_comp {R₃ : Type u} [comm_ring R₃] {n : Type u_1} {o : Type u_2} [fintype n] [fintype o] [DecidableEq n] [DecidableEq o] (B : bilin_form R₃ (n → R₃)) (l : linear_map R₃ (o → R₃) (n → R₃)) (r : linear_map R₃ (o → R₃) (n → R₃)) : coe_fn bilin_form.to_matrix' (bilin_form.comp B l r) =
  matrix.mul (matrix.mul (matrix.transpose (coe_fn linear_map.to_matrix' l)) (coe_fn bilin_form.to_matrix' B))
    (coe_fn linear_map.to_matrix' r) := sorry

theorem bilin_form.to_matrix'_comp_left {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) (f : linear_map R₃ (n → R₃) (n → R₃)) : coe_fn bilin_form.to_matrix' (bilin_form.comp_left B f) =
  matrix.mul (matrix.transpose (coe_fn linear_map.to_matrix' f)) (coe_fn bilin_form.to_matrix' B) := sorry

theorem bilin_form.to_matrix'_comp_right {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) (f : linear_map R₃ (n → R₃) (n → R₃)) : coe_fn bilin_form.to_matrix' (bilin_form.comp_right B f) =
  matrix.mul (coe_fn bilin_form.to_matrix' B) (coe_fn linear_map.to_matrix' f) := sorry

theorem bilin_form.mul_to_matrix'_mul {R₃ : Type u} [comm_ring R₃] {n : Type u_1} {o : Type u_2} [fintype n] [fintype o] [DecidableEq n] [DecidableEq o] (B : bilin_form R₃ (n → R₃)) (M : matrix o n R₃) (N : matrix n o R₃) : matrix.mul (matrix.mul M (coe_fn bilin_form.to_matrix' B)) N =
  coe_fn bilin_form.to_matrix'
    (bilin_form.comp B (coe_fn matrix.to_lin' (matrix.transpose M)) (coe_fn matrix.to_lin' N)) := sorry

theorem bilin_form.mul_to_matrix' {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) (M : matrix n n R₃) : matrix.mul M (coe_fn bilin_form.to_matrix' B) =
  coe_fn bilin_form.to_matrix' (bilin_form.comp_left B (coe_fn matrix.to_lin' (matrix.transpose M))) := sorry

theorem bilin_form.to_matrix'_mul {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] (B : bilin_form R₃ (n → R₃)) (M : matrix n n R₃) : matrix.mul (coe_fn bilin_form.to_matrix' B) M =
  coe_fn bilin_form.to_matrix' (bilin_form.comp_right B (coe_fn matrix.to_lin' M)) := sorry

theorem matrix.to_bilin'_comp {R₃ : Type u} [comm_ring R₃] {n : Type u_1} {o : Type u_2} [fintype n] [fintype o] [DecidableEq n] [DecidableEq o] (M : matrix n n R₃) (P : matrix n o R₃) (Q : matrix n o R₃) : bilin_form.comp (coe_fn matrix.to_bilin' M) (coe_fn matrix.to_lin' P) (coe_fn matrix.to_lin' Q) =
  coe_fn matrix.to_bilin' (matrix.mul (matrix.mul (matrix.transpose P) M) Q) := sorry

/-! ### `to_matrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/

/-- `bilin_form.to_matrix hb` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `hb` is an `R`-basis for `M`. -/
def bilin_form.to_matrix {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) : linear_equiv R₃ (bilin_form R₃ M₃) (matrix n n R₃) :=
  linear_equiv.trans (bilin_form.congr (is_basis.equiv_fun hb)) bilin_form.to_matrix'

/-- `bilin_form.to_matrix hb` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `hb` is an `R`-basis for `M`. -/
def matrix.to_bilin {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) : linear_equiv R₃ (matrix n n R₃) (bilin_form R₃ M₃) :=
  linear_equiv.symm (bilin_form.to_matrix hb)

@[simp] theorem is_basis.equiv_fun_symm_std_basis {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (i : n) : coe_fn (linear_equiv.symm (is_basis.equiv_fun hb)) (coe_fn (linear_map.std_basis R₃ (fun (ᾰ : n) => R₃) i) 1) = b i := sorry

@[simp] theorem bilin_form.to_matrix_apply {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) (i : n) (j : n) : coe_fn (bilin_form.to_matrix hb) B i j = coe_fn B (b i) (b j) := sorry

@[simp] theorem matrix.to_bilin_apply {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (M : matrix n n R₃) (x : M₃) (y : M₃) : coe_fn (coe_fn (matrix.to_bilin hb) M) x y =
  finset.sum finset.univ
    fun (i : n) =>
      finset.sum finset.univ
        fun (j : n) => coe_fn (coe_fn (is_basis.repr hb) x) i * M i j * coe_fn (coe_fn (is_basis.repr hb) y) j := sorry

-- Not a `simp` lemma since `bilin_form.to_matrix` needs an extra argument

theorem bilinear_form.to_matrix_aux_eq {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) : coe_fn (bilin_form.to_matrix_aux b) B = coe_fn (bilin_form.to_matrix hb) B := sorry

@[simp] theorem bilin_form.to_matrix_symm {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) : linear_equiv.symm (bilin_form.to_matrix hb) = matrix.to_bilin hb :=
  rfl

@[simp] theorem matrix.to_bilin_symm {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) : linear_equiv.symm (matrix.to_bilin hb) = bilin_form.to_matrix hb :=
  linear_equiv.symm_symm (bilin_form.to_matrix hb)

theorem matrix.to_bilin_is_basis_fun {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] : matrix.to_bilin (pi.is_basis_fun R₃ n) = matrix.to_bilin' := sorry

theorem bilin_form.to_matrix_is_basis_fun {R₃ : Type u} [comm_ring R₃] {n : Type u_1} [fintype n] [DecidableEq n] : bilin_form.to_matrix (pi.is_basis_fun R₃ n) = bilin_form.to_matrix' := sorry

@[simp] theorem matrix.to_bilin_to_matrix {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) : coe_fn (matrix.to_bilin hb) (coe_fn (bilin_form.to_matrix hb) B) = B :=
  linear_equiv.apply_symm_apply (matrix.to_bilin hb) B

@[simp] theorem bilin_form.to_matrix_to_bilin {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (M : matrix n n R₃) : coe_fn (bilin_form.to_matrix hb) (coe_fn (matrix.to_bilin hb) M) = M :=
  linear_equiv.apply_symm_apply (bilin_form.to_matrix hb) M

-- Cannot be a `simp` lemma because `hb` must be inferred.

theorem bilin_form.to_matrix_comp {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} {o : Type u_2} [fintype n] [fintype o] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) {M₃' : Type u_3} [add_comm_group M₃'] [module R₃ M₃'] {c : o → M₃'} (hc : is_basis R₃ c) [DecidableEq o] (B : bilin_form R₃ M₃) (l : linear_map R₃ M₃' M₃) (r : linear_map R₃ M₃' M₃) : coe_fn (bilin_form.to_matrix hc) (bilin_form.comp B l r) =
  matrix.mul
    (matrix.mul (matrix.transpose (coe_fn (linear_map.to_matrix hc hb) l)) (coe_fn (bilin_form.to_matrix hb) B))
    (coe_fn (linear_map.to_matrix hc hb) r) := sorry

theorem bilin_form.to_matrix_comp_left {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) (f : linear_map R₃ M₃ M₃) : coe_fn (bilin_form.to_matrix hb) (bilin_form.comp_left B f) =
  matrix.mul (matrix.transpose (coe_fn (linear_map.to_matrix hb hb) f)) (coe_fn (bilin_form.to_matrix hb) B) := sorry

theorem bilin_form.to_matrix_comp_right {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) (f : linear_map R₃ M₃ M₃) : coe_fn (bilin_form.to_matrix hb) (bilin_form.comp_right B f) =
  matrix.mul (coe_fn (bilin_form.to_matrix hb) B) (coe_fn (linear_map.to_matrix hb hb) f) := sorry

theorem bilin_form.mul_to_matrix_mul {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} {o : Type u_2} [fintype n] [fintype o] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) {M₃' : Type u_3} [add_comm_group M₃'] [module R₃ M₃'] {c : o → M₃'} (hc : is_basis R₃ c) [DecidableEq o] (B : bilin_form R₃ M₃) (M : matrix o n R₃) (N : matrix n o R₃) : matrix.mul (matrix.mul M (coe_fn (bilin_form.to_matrix hb) B)) N =
  coe_fn (bilin_form.to_matrix hc)
    (bilin_form.comp B (coe_fn (matrix.to_lin hc hb) (matrix.transpose M)) (coe_fn (matrix.to_lin hc hb) N)) := sorry

theorem bilin_form.mul_to_matrix {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) (M : matrix n n R₃) : matrix.mul M (coe_fn (bilin_form.to_matrix hb) B) =
  coe_fn (bilin_form.to_matrix hb) (bilin_form.comp_left B (coe_fn (matrix.to_lin hb hb) (matrix.transpose M))) := sorry

theorem bilin_form.to_matrix_mul {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} [fintype n] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) (B : bilin_form R₃ M₃) (M : matrix n n R₃) : matrix.mul (coe_fn (bilin_form.to_matrix hb) B) M =
  coe_fn (bilin_form.to_matrix hb) (bilin_form.comp_right B (coe_fn (matrix.to_lin hb hb) M)) := sorry

theorem matrix.to_bilin_comp {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type u_1} {o : Type u_2} [fintype n] [fintype o] [DecidableEq n] {b : n → M₃} (hb : is_basis R₃ b) {M₃' : Type u_3} [add_comm_group M₃'] [module R₃ M₃'] {c : o → M₃'} (hc : is_basis R₃ c) [DecidableEq o] (M : matrix n n R₃) (P : matrix n o R₃) (Q : matrix n o R₃) : bilin_form.comp (coe_fn (matrix.to_bilin hb) M) (coe_fn (matrix.to_lin hc hb) P) (coe_fn (matrix.to_lin hc hb) Q) =
  coe_fn (matrix.to_bilin hc) (matrix.mul (matrix.mul (matrix.transpose P) M) Q) := sorry

namespace refl_bilin_form


/-- The proposition that a bilinear form is reflexive -/
def is_refl {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M)  :=
  ∀ (x y : M), coe_fn B x y = 0 → coe_fn B y x = 0

theorem eq_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (H : is_refl B) {x : M} {y : M} : coe_fn B x y = 0 → coe_fn B y x = 0 :=
  H x y

theorem ortho_sym {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (H : is_refl B) {x : M} {y : M} : bilin_form.is_ortho B x y ↔ bilin_form.is_ortho B y x :=
  { mp := eq_zero H, mpr := eq_zero H }

end refl_bilin_form


namespace sym_bilin_form


/-- The proposition that a bilinear form is symmetric -/
def is_sym {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M)  :=
  ∀ (x y : M), coe_fn B x y = coe_fn B y x

theorem sym {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (H : is_sym B) (x : M) (y : M) : coe_fn B x y = coe_fn B y x :=
  H x y

theorem is_refl {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (H : is_sym B) : refl_bilin_form.is_refl B :=
  fun (x y : M) (H1 : coe_fn B x y = 0) => H x y ▸ H1

theorem ortho_sym {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (H : is_sym B) {x : M} {y : M} : bilin_form.is_ortho B x y ↔ bilin_form.is_ortho B y x :=
  refl_bilin_form.ortho_sym (is_refl H)

end sym_bilin_form


namespace alt_bilin_form


/-- The proposition that a bilinear form is alternating -/
def is_alt {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M)  :=
  ∀ (x : M), coe_fn B x x = 0

theorem self_eq_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (H : is_alt B) (x : M) : coe_fn B x x = 0 :=
  H x

theorem neg {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} (H : is_alt B₁) (x : M₁) (y : M₁) : -coe_fn B₁ x y = coe_fn B₁ y x := sorry

end alt_bilin_form


namespace bilin_form


/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def is_adjoint_pair {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) {M' : Type u_1} [add_comm_monoid M'] [semimodule R M'] (B' : bilin_form R M') (f : linear_map R M M') (g : linear_map R M' M)  :=
  ∀ {x : M} {y : M'}, coe_fn B' (coe_fn f x) y = coe_fn B x (coe_fn g y)

theorem is_adjoint_pair.eq {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {M' : Type u_1} [add_comm_monoid M'] [semimodule R M'] {B' : bilin_form R M'} {f : linear_map R M M'} {g : linear_map R M' M} (h : is_adjoint_pair B B' f g) {x : M} {y : M'} : coe_fn B' (coe_fn f x) y = coe_fn B x (coe_fn g y) :=
  h

theorem is_adjoint_pair_iff_comp_left_eq_comp_right {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} (F : bilin_form R M) (f : module.End R M) (g : module.End R M) : is_adjoint_pair B F f g ↔ comp_left F f = comp_right B g := sorry

theorem is_adjoint_pair_zero {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {M' : Type u_1} [add_comm_monoid M'] [semimodule R M'] {B' : bilin_form R M'} : is_adjoint_pair B B' 0 0 := sorry

theorem is_adjoint_pair_id {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} : is_adjoint_pair B B 1 1 :=
  fun (x y : M) => rfl

theorem is_adjoint_pair.add {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {M' : Type u_1} [add_comm_monoid M'] [semimodule R M'] {B' : bilin_form R M'} {f : linear_map R M M'} {f' : linear_map R M M'} {g : linear_map R M' M} {g' : linear_map R M' M} (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B B' f' g') : is_adjoint_pair B B' (f + f') (g + g') := sorry

theorem is_adjoint_pair.sub {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] {B₁ : bilin_form R₁ M₁} {M₁' : Type u_2} [add_comm_group M₁'] [module R₁ M₁'] {B₁' : bilin_form R₁ M₁'} {f₁ : linear_map R₁ M₁ M₁'} {f₁' : linear_map R₁ M₁ M₁'} {g₁ : linear_map R₁ M₁' M₁} {g₁' : linear_map R₁ M₁' M₁} (h : is_adjoint_pair B₁ B₁' f₁ g₁) (h' : is_adjoint_pair B₁ B₁' f₁' g₁') : is_adjoint_pair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := sorry

theorem is_adjoint_pair.smul {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] {B₂ : bilin_form R₂ M₂} {M₂' : Type u_3} [add_comm_monoid M₂'] [semimodule R₂ M₂'] {B₂' : bilin_form R₂ M₂'} {f₂ : linear_map R₂ M₂ M₂'} {g₂ : linear_map R₂ M₂' M₂} (c : R₂) (h : is_adjoint_pair B₂ B₂' f₂ g₂) : is_adjoint_pair B₂ B₂' (c • f₂) (c • g₂) := sorry

theorem is_adjoint_pair.comp {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {M' : Type u_1} [add_comm_monoid M'] [semimodule R M'] {B' : bilin_form R M'} {f : linear_map R M M'} {g : linear_map R M' M} {M'' : Type u_4} [add_comm_monoid M''] [semimodule R M''] (B'' : bilin_form R M'') {f' : linear_map R M' M''} {g' : linear_map R M'' M'} (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B' B'' f' g') : is_adjoint_pair B B'' (linear_map.comp f' f) (linear_map.comp g g') := sorry

theorem is_adjoint_pair.mul {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] {B : bilin_form R M} {f : module.End R M} {g : module.End R M} {f' : module.End R M} {g' : module.End R M} (h : is_adjoint_pair B B f g) (h' : is_adjoint_pair B B f' g') : is_adjoint_pair B B (f * f') (g' * g) := sorry

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def is_pair_self_adjoint {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (F : bilin_form R M) (f : module.End R M)  :=
  is_adjoint_pair B F f f

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def is_pair_self_adjoint_submodule {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (B₂ : bilin_form R₂ M₂) (F₂ : bilin_form R₂ M₂) : submodule R₂ (module.End R₂ M₂) :=
  submodule.mk (set_of fun (f : module.End R₂ M₂) => is_pair_self_adjoint B₂ F₂ f) sorry sorry sorry

@[simp] theorem mem_is_pair_self_adjoint_submodule {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (B₂ : bilin_form R₂ M₂) (F₂ : bilin_form R₂ M₂) (f : module.End R₂ M₂) : f ∈ is_pair_self_adjoint_submodule B₂ F₂ ↔ is_pair_self_adjoint B₂ F₂ f :=
  iff.refl (f ∈ is_pair_self_adjoint_submodule B₂ F₂)

theorem is_pair_self_adjoint_equiv {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {M₃' : Type u_5} [add_comm_group M₃'] [module R₃ M₃'] (B₃ : bilin_form R₃ M₃) (F₃ : bilin_form R₃ M₃) (e : linear_equiv R₃ M₃' M₃) (f : module.End R₃ M₃) : is_pair_self_adjoint B₃ F₃ f ↔
  is_pair_self_adjoint (comp B₃ ↑e ↑e) (comp F₃ ↑e ↑e) (coe_fn (linear_equiv.conj (linear_equiv.symm e)) f) := sorry

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def is_self_adjoint {R : Type u} {M : Type v} [semiring R] [add_comm_monoid M] [semimodule R M] (B : bilin_form R M) (f : module.End R M)  :=
  is_adjoint_pair B B f f

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def is_skew_adjoint {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] (B₁ : bilin_form R₁ M₁) (f : module.End R₁ M₁)  :=
  is_adjoint_pair B₁ B₁ f (-f)

theorem is_skew_adjoint_iff_neg_self_adjoint {R₁ : Type u} {M₁ : Type v} [ring R₁] [add_comm_group M₁] [module R₁ M₁] (B₁ : bilin_form R₁ M₁) (f : module.End R₁ M₁) : is_skew_adjoint B₁ f ↔ is_adjoint_pair (-B₁) B₁ f f := sorry

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def self_adjoint_submodule {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (B₂ : bilin_form R₂ M₂) : submodule R₂ (module.End R₂ M₂) :=
  is_pair_self_adjoint_submodule B₂ B₂

@[simp] theorem mem_self_adjoint_submodule {R₂ : Type u} {M₂ : Type v} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂] (B₂ : bilin_form R₂ M₂) (f : module.End R₂ M₂) : f ∈ self_adjoint_submodule B₂ ↔ is_self_adjoint B₂ f :=
  iff.rfl

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skew_adjoint_submodule {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] (B₃ : bilin_form R₃ M₃) : submodule R₃ (module.End R₃ M₃) :=
  is_pair_self_adjoint_submodule (-B₃) B₃

@[simp] theorem mem_skew_adjoint_submodule {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] (B₃ : bilin_form R₃ M₃) (f : module.End R₃ M₃) : f ∈ skew_adjoint_submodule B₃ ↔ is_skew_adjoint B₃ f := sorry

end bilin_form


/-- The condition for the square matrices `A`, `A'` to be an adjoint pair with respect to the square
matrices `J`, `J₃`. -/
def matrix.is_adjoint_pair {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (J₃ : matrix n n R₃) (A : matrix n n R₃) (A' : matrix n n R₃)  :=
  matrix.mul (matrix.transpose A) J₃ = matrix.mul J A'

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def matrix.is_self_adjoint {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (A : matrix n n R₃)  :=
  matrix.is_adjoint_pair J J A A

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def matrix.is_skew_adjoint {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (A : matrix n n R₃)  :=
  matrix.is_adjoint_pair J J A (-A)

@[simp] theorem is_adjoint_pair_to_bilin' {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (J₃ : matrix n n R₃) (A : matrix n n R₃) (A' : matrix n n R₃) [DecidableEq n] : bilin_form.is_adjoint_pair (coe_fn matrix.to_bilin' J) (coe_fn matrix.to_bilin' J₃) (coe_fn matrix.to_lin' A)
    (coe_fn matrix.to_lin' A') ↔
  matrix.is_adjoint_pair J J₃ A A' := sorry

@[simp] theorem is_adjoint_pair_to_bilin {R₃ : Type u} {M₃ : Type v} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃] {n : Type w} [fintype n] {b : n → M₃} (hb : is_basis R₃ b) (J : matrix n n R₃) (J₃ : matrix n n R₃) (A : matrix n n R₃) (A' : matrix n n R₃) [DecidableEq n] : bilin_form.is_adjoint_pair (coe_fn (matrix.to_bilin hb) J) (coe_fn (matrix.to_bilin hb) J₃)
    (coe_fn (matrix.to_lin hb hb) A) (coe_fn (matrix.to_lin hb hb) A') ↔
  matrix.is_adjoint_pair J J₃ A A' := sorry

theorem matrix.is_adjoint_pair_equiv {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (A : matrix n n R₃) (A' : matrix n n R₃) [DecidableEq n] (P : matrix n n R₃) (h : is_unit P) : matrix.is_adjoint_pair (matrix.mul (matrix.mul (matrix.transpose P) J) P)
    (matrix.mul (matrix.mul (matrix.transpose P) J) P) A A' ↔
  matrix.is_adjoint_pair J J (matrix.mul (matrix.mul P A) (P⁻¹)) (matrix.mul (matrix.mul P A') (P⁻¹)) := sorry

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pair_self_adjoint_matrices_submodule {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (J₃ : matrix n n R₃) [DecidableEq n] : submodule R₃ (matrix n n R₃) :=
  submodule.map (↑linear_map.to_matrix')
    (bilin_form.is_pair_self_adjoint_submodule (coe_fn matrix.to_bilin' J) (coe_fn matrix.to_bilin' J₃))

@[simp] theorem mem_pair_self_adjoint_matrices_submodule {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (J₃ : matrix n n R₃) (A : matrix n n R₃) [DecidableEq n] : A ∈ pair_self_adjoint_matrices_submodule J J₃ ↔ matrix.is_adjoint_pair J J₃ A A := sorry

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def self_adjoint_matrices_submodule {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) [DecidableEq n] : submodule R₃ (matrix n n R₃) :=
  pair_self_adjoint_matrices_submodule J J

@[simp] theorem mem_self_adjoint_matrices_submodule {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (A : matrix n n R₃) [DecidableEq n] : A ∈ self_adjoint_matrices_submodule J ↔ matrix.is_self_adjoint J A := sorry

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skew_adjoint_matrices_submodule {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) [DecidableEq n] : submodule R₃ (matrix n n R₃) :=
  pair_self_adjoint_matrices_submodule (-J) J

@[simp] theorem mem_skew_adjoint_matrices_submodule {R₃ : Type u} [comm_ring R₃] {n : Type w} [fintype n] (J : matrix n n R₃) (A : matrix n n R₃) [DecidableEq n] : A ∈ skew_adjoint_matrices_submodule J ↔ matrix.is_skew_adjoint J A := sorry

