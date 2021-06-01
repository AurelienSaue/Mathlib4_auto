/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.invertible
import Mathlib.linear_algebra.bilinear_form
import Mathlib.linear_algebra.determinant
import Mathlib.linear_algebra.special_linear_group
import Mathlib.PostPort

universes u v l u_1 w u_2 u_3 

namespace Mathlib

/-!
# Quadratic forms

This file defines quadratic forms over a `R`-module `M`.
A quadratic form is a map `Q : M → R` such that
  (`to_fun_smul`) `Q (a • x) = a * a * Q x`
  (`polar_...`) The map `polar Q := λ x y, Q (x + y) - Q x - Q y` is bilinear.
They come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `quadratic_form.associated`: associated bilinear form
 * `quadratic_form.pos_def`: positive definite quadratic forms
 * `quadratic_form.anisotropic`: anisotropic quadratic forms
 * `quadratic_form.discr`: discriminant of a quadratic form

## Main statements

 * `quadratic_form.associated_left_inverse`,
 * `quadratic_form.associated_right_inverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms

## Notation

In this file, the variable `R` is used when a `ring` structure is sufficient and
`R₁` is used when specifically a `comm_ring` is required. This allows us to keep
`[module R M]` and `[module R₁ M]` assumptions in the variables without
confusion between `*` from `ring` and `*` from `comm_ring`.


## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/

namespace quadratic_form


/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.d

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar {R : Type u} {M : Type v} [add_comm_group M] [ring R] (f : M → R) (x : M) (y : M) : R :=
  f (x + y) - f x - f y

theorem polar_add {R : Type u} {M : Type v} [add_comm_group M] [ring R] (f : M → R) (g : M → R)
    (x : M) (y : M) : polar (f + g) x y = polar f x y + polar g x y :=
  sorry

theorem polar_neg {R : Type u} {M : Type v} [add_comm_group M] [ring R] (f : M → R) (x : M)
    (y : M) : polar (-f) x y = -polar f x y :=
  sorry

theorem polar_smul {R : Type u} {M : Type v} [add_comm_group M] [ring R] (f : M → R) (s : R) (x : M)
    (y : M) : polar (s • f) x y = s * polar f x y :=
  sorry

theorem polar_comm {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁] (f : M → R₁) (x : M)
    (y : M) : polar f x y = polar f y x :=
  sorry

end quadratic_form


/-- A quadratic form over a module. -/
structure quadratic_form (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M]
    extends
      quadratic_form.to_fun #1 #0 R M _inst_6 _inst_7 (_inst_8 • to_fun) =
        _inst_8 * _inst_8 * quadratic_form.to_fun #1 #0 R M _inst_6 _inst_7 to_fun
    where
  to_fun : M → R
  to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x
  polar_add_left' :
    ∀ (x x' y : M),
      quadratic_form.polar to_fun (x + x') y =
        quadratic_form.polar to_fun x y + quadratic_form.polar to_fun x' y
  polar_smul_left' :
    ∀ (a : R) (x y : M), quadratic_form.polar to_fun (a • x) y = a • quadratic_form.polar to_fun x y
  polar_add_right' :
    ∀ (x y y' : M),
      quadratic_form.polar to_fun x (y + y') =
        quadratic_form.polar to_fun x y + quadratic_form.polar to_fun x y'
  polar_smul_right' :
    ∀ (a : R) (x y : M), quadratic_form.polar to_fun x (a • y) = a • quadratic_form.polar to_fun x y

namespace quadratic_form


protected instance has_coe_to_fun {R : Type u} {M : Type v} [add_comm_group M] [ring R]
    [module R M] : has_coe_to_fun (quadratic_form R M) :=
  has_coe_to_fun.mk (fun (B : quadratic_form R M) => M → R) fun (B : quadratic_form R M) => to_fun B

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp] theorem to_fun_eq_apply {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} : to_fun Q = ⇑Q :=
  rfl

@[simp] theorem polar_add_left {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (x' : M) (y : M) :
    polar (⇑Q) (x + x') y = polar (⇑Q) x y + polar (⇑Q) x' y :=
  polar_add_left' Q x x' y

@[simp] theorem polar_smul_left {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (a : R) (x : M) (y : M) : polar (⇑Q) (a • x) y = a * polar (⇑Q) x y :=
  polar_smul_left' Q a x y

@[simp] theorem polar_neg_left {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (y : M) : polar (⇑Q) (-x) y = -polar (⇑Q) x y :=
  sorry

@[simp] theorem polar_sub_left {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (x' : M) (y : M) :
    polar (⇑Q) (x - x') y = polar (⇑Q) x y - polar (⇑Q) x' y :=
  sorry

@[simp] theorem polar_add_right {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (y : M) (y' : M) :
    polar (⇑Q) x (y + y') = polar (⇑Q) x y + polar (⇑Q) x y' :=
  polar_add_right' Q x y y'

@[simp] theorem polar_smul_right {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (a : R) (x : M) (y : M) : polar (⇑Q) x (a • y) = a * polar (⇑Q) x y :=
  polar_smul_right' Q a x y

@[simp] theorem polar_neg_right {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (y : M) : polar (⇑Q) x (-y) = -polar (⇑Q) x y :=
  sorry

@[simp] theorem polar_sub_right {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (y : M) (y' : M) :
    polar (⇑Q) x (y - y') = polar (⇑Q) x y - polar (⇑Q) x y' :=
  sorry

theorem map_smul {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (a : R) (x : M) : coe_fn Q (a • x) = a * a * coe_fn Q x :=
  to_fun_smul Q a x

theorem map_add_self {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) : coe_fn Q (x + x) = bit0 (bit0 1) * coe_fn Q x :=
  sorry

@[simp] theorem map_zero {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} : coe_fn Q 0 = 0 :=
  sorry

@[simp] theorem map_neg {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) : coe_fn Q (-x) = coe_fn Q x :=
  sorry

theorem map_sub {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} (x : M) (y : M) : coe_fn Q (x - y) = coe_fn Q (y - x) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn Q (x - y) = coe_fn Q (y - x))) (Eq.symm (neg_sub y x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn Q (-(y - x)) = coe_fn Q (y - x))) (map_neg (y - x))))
      (Eq.refl (coe_fn Q (y - x))))

theorem ext {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {Q : quadratic_form R M} {Q' : quadratic_form R M} (H : ∀ (x : M), coe_fn Q x = coe_fn Q' x) :
    Q = Q' :=
  sorry

protected instance has_zero {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M] :
    HasZero (quadratic_form R M) :=
  { zero := mk (fun (x : M) => 0) sorry sorry sorry sorry sorry }

@[simp] theorem zero_apply {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (x : M) : coe_fn 0 x = 0 :=
  rfl

protected instance inhabited {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M] :
    Inhabited (quadratic_form R M) :=
  { default := 0 }

protected instance has_add {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M] :
    Add (quadratic_form R M) :=
  { add := fun (Q Q' : quadratic_form R M) => mk (⇑Q + ⇑Q') sorry sorry sorry sorry sorry }

@[simp] theorem coe_fn_add {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) (Q' : quadratic_form R M) : ⇑(Q + Q') = ⇑Q + ⇑Q' :=
  rfl

@[simp] theorem add_apply {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) (Q' : quadratic_form R M) (x : M) :
    coe_fn (Q + Q') x = coe_fn Q x + coe_fn Q' x :=
  rfl

protected instance has_neg {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M] :
    Neg (quadratic_form R M) :=
  { neg := fun (Q : quadratic_form R M) => mk (-⇑Q) sorry sorry sorry sorry sorry }

@[simp] theorem coe_fn_neg {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) : ⇑(-Q) = -⇑Q :=
  rfl

@[simp] theorem neg_apply {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) (x : M) : coe_fn (-Q) x = -coe_fn Q x :=
  rfl

protected instance has_scalar {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] : has_scalar R₁ (quadratic_form R₁ M) :=
  has_scalar.mk fun (a : R₁) (Q : quadratic_form R₁ M) => mk (a • ⇑Q) sorry sorry sorry sorry sorry

@[simp] theorem coe_fn_smul {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] (a : R₁) (Q : quadratic_form R₁ M) : ⇑(a • Q) = a • ⇑Q :=
  rfl

@[simp] theorem smul_apply {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] (a : R₁) (Q : quadratic_form R₁ M) (x : M) : coe_fn (a • Q) x = a * coe_fn Q x :=
  rfl

protected instance add_comm_group {R : Type u} {M : Type v} [add_comm_group M] [ring R]
    [module R M] : add_comm_group (quadratic_form R M) :=
  add_comm_group.mk Add.add sorry 0 sorry sorry Neg.neg
    (add_group.sub._default Add.add sorry 0 sorry sorry Neg.neg) sorry sorry

protected instance module {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] : module R₁ (quadratic_form R₁ M) :=
  semimodule.mk sorry sorry

/-- Compose the quadratic form with a linear function. -/
def comp {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M] {N : Type v}
    [add_comm_group N] [module R N] (Q : quadratic_form R N) (f : linear_map R M N) :
    quadratic_form R M :=
  mk (fun (x : M) => coe_fn Q (coe_fn f x)) sorry sorry sorry sorry sorry

@[simp] theorem comp_apply {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {N : Type v} [add_comm_group N] [module R N] (Q : quadratic_form R N) (f : linear_map R M N)
    (x : M) : coe_fn (comp Q f) x = coe_fn Q (coe_fn f x) :=
  rfl

/-- Create a quadratic form in a commutative ring by proving only one side of the bilinearity. -/
def mk_left {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁] [module R₁ M] (f : M → R₁)
    (to_fun_smul : ∀ (a : R₁) (x : M), f (a • x) = a * a * f x)
    (polar_add_left : ∀ (x x' y : M), polar f (x + x') y = polar f x y + polar f x' y)
    (polar_smul_left : ∀ (a : R₁) (x y : M), polar f (a • x) y = a * polar f x y) :
    quadratic_form R₁ M :=
  mk f to_fun_smul polar_add_left polar_smul_left sorry sorry

/-- The product of linear forms is a quadratic form. -/
def lin_mul_lin {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁] [module R₁ M]
    (f : linear_map R₁ M R₁) (g : linear_map R₁ M R₁) : quadratic_form R₁ M :=
  mk_left (⇑f * ⇑g) sorry sorry sorry

@[simp] theorem lin_mul_lin_apply {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] (f : linear_map R₁ M R₁) (g : linear_map R₁ M R₁) (x : M) :
    coe_fn (lin_mul_lin f g) x = coe_fn f x * coe_fn g x :=
  rfl

@[simp] theorem add_lin_mul_lin {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] (f : linear_map R₁ M R₁) (g : linear_map R₁ M R₁) (h : linear_map R₁ M R₁) :
    lin_mul_lin (f + g) h = lin_mul_lin f h + lin_mul_lin g h :=
  ext fun (x : M) => add_mul (coe_fn f x) (coe_fn g x) (coe_fn h x)

@[simp] theorem lin_mul_lin_add {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] (f : linear_map R₁ M R₁) (g : linear_map R₁ M R₁) (h : linear_map R₁ M R₁) :
    lin_mul_lin f (g + h) = lin_mul_lin f g + lin_mul_lin f h :=
  ext fun (x : M) => mul_add (coe_fn f x) (coe_fn g x) (coe_fn h x)

@[simp] theorem lin_mul_lin_comp {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] {N : Type v} [add_comm_group N] [module R₁ N] (f : linear_map R₁ M R₁)
    (g : linear_map R₁ M R₁) (h : linear_map R₁ N M) :
    comp (lin_mul_lin f g) h = lin_mul_lin (linear_map.comp f h) (linear_map.comp g h) :=
  rfl

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj {R₁ : Type u} [comm_ring R₁] {n : Type u_1} (i : n) (j : n) : quadratic_form R₁ (n → R₁) :=
  lin_mul_lin (linear_map.proj i) (linear_map.proj j)

@[simp] theorem proj_apply {R₁ : Type u} [comm_ring R₁] {n : Type u_1} (i : n) (j : n)
    (x : n → R₁) : coe_fn (proj i j) x = x i * x j :=
  rfl

end quadratic_form


/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/

namespace bilin_form


theorem polar_to_quadratic_form {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    {B : bilin_form R M} (x : M) (y : M) :
    quadratic_form.polar (fun (x : M) => coe_fn B x x) x y = coe_fn B x y + coe_fn B y x :=
  sorry

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def to_quadratic_form {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (B : bilin_form R M) : quadratic_form R M :=
  quadratic_form.mk (fun (x : M) => coe_fn B x x) sorry sorry sorry sorry sorry

@[simp] theorem to_quadratic_form_apply {R : Type u} {M : Type v} [add_comm_group M] [ring R]
    [module R M] (B : bilin_form R M) (x : M) : coe_fn (to_quadratic_form B) x = coe_fn B x x :=
  rfl

end bilin_form


namespace quadratic_form


/-- `associated` is the linear map that sends a quadratic form to its associated
symmetric bilinear form -/
def associated {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁] [module R₁ M]
    [invertible (bit0 1)] : linear_map R₁ (quadratic_form R₁ M) (bilin_form R₁ M) :=
  linear_map.mk
    (fun (Q : quadratic_form R₁ M) =>
      bilin_form.mk (fun (x y : M) => ⅟ * polar (⇑Q) x y) sorry sorry sorry sorry)
    sorry sorry

@[simp] theorem associated_apply {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] [invertible (bit0 1)] {Q : quadratic_form R₁ M} (x : M) (y : M) :
    coe_fn (coe_fn associated Q) x y = ⅟ * (coe_fn Q (x + y) - coe_fn Q x - coe_fn Q y) :=
  rfl

theorem associated_is_sym {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁] [module R₁ M]
    [invertible (bit0 1)] {Q : quadratic_form R₁ M} : sym_bilin_form.is_sym (coe_fn associated Q) :=
  sorry

@[simp] theorem associated_comp {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] [invertible (bit0 1)] {Q : quadratic_form R₁ M} {N : Type v} [add_comm_group N]
    [module R₁ N] (f : linear_map R₁ N M) :
    coe_fn associated (comp Q f) = bilin_form.comp (coe_fn associated Q) f f :=
  sorry

@[simp] theorem associated_lin_mul_lin {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] [invertible (bit0 1)] (f : linear_map R₁ M R₁) (g : linear_map R₁ M R₁) :
    coe_fn associated (lin_mul_lin f g) =
        ⅟ • (bilin_form.lin_mul_lin f g + bilin_form.lin_mul_lin g f) :=
  sorry

theorem associated_to_quadratic_form {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] [invertible (bit0 1)] (B : bilin_form R₁ M) (x : M) (y : M) :
    coe_fn (coe_fn associated (bilin_form.to_quadratic_form B)) x y =
        ⅟ * (coe_fn B x y + coe_fn B y x) :=
  sorry

theorem associated_left_inverse {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] [invertible (bit0 1)] {B₁ : bilin_form R₁ M} (h : sym_bilin_form.is_sym B₁) :
    coe_fn associated (bilin_form.to_quadratic_form B₁) = B₁ :=
  sorry

theorem associated_right_inverse {M : Type v} [add_comm_group M] {R₁ : Type u} [comm_ring R₁]
    [module R₁ M] [invertible (bit0 1)] {Q : quadratic_form R₁ M} :
    bilin_form.to_quadratic_form (coe_fn associated Q) = Q :=
  sorry

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def anisotropic {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) :=
  ∀ (x : M), coe_fn Q x = 0 → x = 0

theorem not_anisotropic_iff_exists {R : Type u} {M : Type v} [add_comm_group M] [ring R]
    [module R M] (Q : quadratic_form R M) :
    ¬anisotropic Q ↔ ∃ (x : M), ∃ (H : x ≠ 0), coe_fn Q x = 0 :=
  sorry

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def pos_def {M : Type v} [add_comm_group M] {R₂ : Type u} [ordered_ring R₂] [module R₂ M]
    (Q₂ : quadratic_form R₂ M) :=
  ∀ (x : M), x ≠ 0 → 0 < coe_fn Q₂ x

theorem pos_def.smul {M : Type v} [add_comm_group M] {R : Type u_1} [linear_ordered_comm_ring R]
    [module R M] {Q : quadratic_form R M} (h : pos_def Q) {a : R} (a_pos : 0 < a) :
    pos_def (a • Q) :=
  fun (x : M) (hx : x ≠ 0) => mul_pos a_pos (h x hx)

theorem pos_def.add {M : Type v} [add_comm_group M] {R₂ : Type u} [ordered_ring R₂] [module R₂ M]
    (Q : quadratic_form R₂ M) (Q' : quadratic_form R₂ M) (hQ : pos_def Q) (hQ' : pos_def Q') :
    pos_def (Q + Q') :=
  fun (x : M) (hx : x ≠ 0) => add_pos (hQ x hx) (hQ' x hx)

theorem lin_mul_lin_self_pos_def {M : Type v} [add_comm_group M] {R : Type u_1}
    [linear_ordered_comm_ring R] [module R M] (f : linear_map R M R) (hf : linear_map.ker f = ⊥) :
    pos_def (lin_mul_lin f f) :=
  sorry

end quadratic_form


/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def matrix.to_quadratic_form' {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n] [DecidableEq n]
    (M : matrix n n R₁) : quadratic_form R₁ (n → R₁) :=
  bilin_form.to_quadratic_form (coe_fn matrix.to_bilin' M)

/-- A matrix representation of the quadratic form. -/
def quadratic_form.to_matrix' {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n] [DecidableEq n]
    [invertible (bit0 1)] (Q : quadratic_form R₁ (n → R₁)) : matrix n n R₁ :=
  coe_fn bilin_form.to_matrix' (coe_fn quadratic_form.associated Q)

theorem quadratic_form.to_matrix'_smul {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n]
    [DecidableEq n] [invertible (bit0 1)] (a : R₁) (Q : quadratic_form R₁ (n → R₁)) :
    quadratic_form.to_matrix' (a • Q) = a • quadratic_form.to_matrix' Q :=
  sorry

namespace quadratic_form


@[simp] theorem to_matrix'_comp {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n]
    [DecidableEq n] [invertible (bit0 1)] {m : Type w} [DecidableEq m] [fintype m]
    (Q : quadratic_form R₁ (m → R₁)) (f : linear_map R₁ (n → R₁) (m → R₁)) :
    to_matrix' (comp Q f) =
        matrix.mul (matrix.mul (matrix.transpose (coe_fn linear_map.to_matrix' f)) (to_matrix' Q))
          (coe_fn linear_map.to_matrix' f) :=
  sorry

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n] [DecidableEq n]
    [invertible (bit0 1)] (Q : quadratic_form R₁ (n → R₁)) : R₁ :=
  matrix.det (to_matrix' Q)

theorem discr_smul {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n] [DecidableEq n]
    [invertible (bit0 1)] {Q : quadratic_form R₁ (n → R₁)} (a : R₁) :
    discr (a • Q) = a ^ fintype.card n * discr Q :=
  sorry

theorem discr_comp {R₁ : Type u} [comm_ring R₁] {n : Type w} [fintype n] [DecidableEq n]
    [invertible (bit0 1)] {Q : quadratic_form R₁ (n → R₁)} (f : linear_map R₁ (n → R₁) (n → R₁)) :
    discr (comp Q f) =
        matrix.det (coe_fn linear_map.to_matrix' f) * matrix.det (coe_fn linear_map.to_matrix' f) *
          discr Q :=
  sorry

end quadratic_form


namespace quadratic_form


/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
structure isometry {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] (Q₁ : quadratic_form R M₁)
    (Q₂ : quadratic_form R M₂)
    extends linear_equiv R M₁ M₂ where
  map_app' : ∀ (m : M₁), coe_fn Q₂ (linear_equiv.to_fun _to_linear_equiv m) = coe_fn Q₁ m

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometry between them:
a linear equivalence that transforms one quadratic form into the other. -/
def equivalent {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] (Q₁ : quadratic_form R M₁)
    (Q₂ : quadratic_form R M₂) :=
  Nonempty (isometry Q₁ Q₂)

namespace isometry


protected instance linear_equiv.has_coe {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2}
    [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] {Q₁ : quadratic_form R M₁}
    {Q₂ : quadratic_form R M₂} : has_coe (isometry Q₁ Q₂) (linear_equiv R M₁ M₂) :=
  has_coe.mk to_linear_equiv

protected instance has_coe_to_fun {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2}
    [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] {Q₁ : quadratic_form R M₁}
    {Q₂ : quadratic_form R M₂} : has_coe_to_fun (isometry Q₁ Q₂) :=
  has_coe_to_fun.mk (fun (_x : isometry Q₁ Q₂) => M₁ → M₂) fun (f : isometry Q₁ Q₂) => ⇑↑f

@[simp] theorem map_app {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {Q₁ : quadratic_form R M₁}
    {Q₂ : quadratic_form R M₂} (f : isometry Q₁ Q₂) (m : M₁) :
    coe_fn Q₂ (coe_fn f m) = coe_fn Q₁ m :=
  map_app' f m

/-- The identity isometry from a quadratic form to itself. -/
def refl {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) : isometry Q Q :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.refl R M)) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.refl R M)) sorry sorry)
    sorry

/-- The inverse isometry of an isometry between two quadratic forms. -/
def symm {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {Q₁ : quadratic_form R M₁}
    {Q₂ : quadratic_form R M₂} (f : isometry Q₁ Q₂) : isometry Q₂ Q₁ :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.symm ↑f)) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.symm ↑f)) sorry sorry)
    sorry

/-- The composition of two isometries between quadratic forms. -/
def trans {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} {M₃ : Type u_3} [add_comm_group M₁]
    [add_comm_group M₂] [add_comm_group M₃] [module R M₁] [module R M₂] [module R M₃]
    {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}
    (f : isometry Q₁ Q₂) (g : isometry Q₂ Q₃) : isometry Q₁ Q₃ :=
  mk
    (linear_equiv.mk (linear_equiv.to_fun (linear_equiv.trans ↑f ↑g)) sorry sorry
      (linear_equiv.inv_fun (linear_equiv.trans ↑f ↑g)) sorry sorry)
    sorry

end isometry


namespace equivalent


theorem refl {R : Type u} {M : Type v} [add_comm_group M] [ring R] [module R M]
    (Q : quadratic_form R M) : equivalent Q Q :=
  Nonempty.intro (isometry.refl Q)

theorem symm {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} [add_comm_group M₁]
    [add_comm_group M₂] [module R M₁] [module R M₂] {Q₁ : quadratic_form R M₁}
    {Q₂ : quadratic_form R M₂} (h : equivalent Q₁ Q₂) : equivalent Q₂ Q₁ :=
  nonempty.elim h fun (f : isometry Q₁ Q₂) => Nonempty.intro (isometry.symm f)

theorem trans {R : Type u} [ring R] {M₁ : Type u_1} {M₂ : Type u_2} {M₃ : Type u_3}
    [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₃] [module R M₁] [module R M₂]
    [module R M₃] {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}
    (h : equivalent Q₁ Q₂) (h' : equivalent Q₂ Q₃) : equivalent Q₁ Q₃ :=
  nonempty.elim h'
    (nonempty.elim h
      fun (f : isometry Q₁ Q₂) (g : isometry Q₂ Q₃) => Nonempty.intro (isometry.trans f g))

end Mathlib