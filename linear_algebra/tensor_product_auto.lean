/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.group_theory.congruence
import Mathlib.linear_algebra.basic
import PostPort

universes u_1 u_4 u_3 u_2 u_5 l u_6 u_7 u_8 u_9 

namespace Mathlib

/-!
# Tensor product of semimodules over commutative semirings.

This file constructs the tensor product of semimodules over commutative semirings. Given a semiring
`R` and semimodules over it `M` and `N`, the standard construction of the tensor product is
`tensor_product R M N`. It is also a semimodule over `R`.

It comes with a canonical bilinear map `M → N → tensor_product R M N`.

Given any bilinear map `M → N → P`, there is a unique linear map `tensor_product R M N → P` whose
composition with the canonical bilinear map `M → N → tensor_product R M N` is the given bilinear
map `M → N → P`.

We start by proving basic lemmas about bilinear maps.

## Notations

This file uses the localized notation `M ⊗ N` and `M ⊗[R] N` for `tensor_product R M N`, as well
as `m ⊗ₜ n` and `m ⊗ₜ[R] n` for `tensor_product.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

namespace linear_map


/-- Create a bilinear map from a function that is linear in each component. -/
def mk₂ (R : Type u_1) [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : M → N → P) (H1 : ∀ (m₁ m₂ : M) (n : N), f (m₁ + m₂) n = f m₁ n + f m₂ n) (H2 : ∀ (c : R) (m : M) (n : N), f (c • m) n = c • f m n) (H3 : ∀ (m : M) (n₁ n₂ : N), f m (n₁ + n₂) = f m n₁ + f m n₂) (H4 : ∀ (c : R) (m : M) (n : N), f m (c • n) = c • f m n) : linear_map R M (linear_map R N P) :=
  mk (fun (m : M) => mk (f m) (H3 m) sorry) sorry sorry

@[simp] theorem mk₂_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : M → N → P) {H1 : ∀ (m₁ m₂ : M) (n : N), f (m₁ + m₂) n = f m₁ n + f m₂ n} {H2 : ∀ (c : R) (m : M) (n : N), f (c • m) n = c • f m n} {H3 : ∀ (m : M) (n₁ n₂ : N), f m (n₁ + n₂) = f m n₁ + f m n₂} {H4 : ∀ (c : R) (m : M) (n : N), f m (c • n) = c • f m n} (m : M) (n : N) : coe_fn (coe_fn (mk₂ R f H1 H2 H3 H4) m) n = f m n :=
  rfl

theorem ext₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {f : linear_map R M (linear_map R N P)} {g : linear_map R M (linear_map R N P)} (H : ∀ (m : M) (n : N), coe_fn (coe_fn f m) n = coe_fn (coe_fn g m) n) : f = g :=
  ext fun (m : M) => ext fun (n : N) => H m n

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def flip {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) : linear_map R N (linear_map R M P) :=
  mk₂ R (fun (n : N) (m : M) => coe_fn (coe_fn f m) n) sorry sorry sorry sorry

@[simp] theorem flip_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (m : M) (n : N) : coe_fn (coe_fn (flip f) n) m = coe_fn (coe_fn f m) n :=
  rfl

theorem flip_inj {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {f : linear_map R M (linear_map R N P)} {g : linear_map R M (linear_map R N P)} (H : flip f = flip g) : f = g := sorry

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map `M → N → P`,
change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def lflip (R : Type u_1) [comm_semiring R] (M : Type u_2) (N : Type u_3) (P : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_map R (linear_map R M (linear_map R N P)) (linear_map R N (linear_map R M P)) :=
  mk flip sorry sorry

@[simp] theorem lflip_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (m : M) (n : N) : coe_fn (coe_fn (coe_fn (lflip R M N P) f) n) m = coe_fn (coe_fn f m) n :=
  rfl

theorem map_zero₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (y : N) : coe_fn (coe_fn f 0) y = 0 :=
  map_zero (coe_fn (flip f) y)

theorem map_neg₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_group M] [add_comm_monoid N] [add_comm_group P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (x : M) (y : N) : coe_fn (coe_fn f (-x)) y = -coe_fn (coe_fn f x) y :=
  map_neg (coe_fn (flip f) y) x

theorem map_sub₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_group M] [add_comm_monoid N] [add_comm_group P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (x : M) (y : M) (z : N) : coe_fn (coe_fn f (x - y)) z = coe_fn (coe_fn f x) z - coe_fn (coe_fn f y) z :=
  map_sub (coe_fn (flip f) z) x y

theorem map_add₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (x₁ : M) (x₂ : M) (y : N) : coe_fn (coe_fn f (x₁ + x₂)) y = coe_fn (coe_fn f x₁) y + coe_fn (coe_fn f x₂) y :=
  map_add (coe_fn (flip f) y) x₁ x₂

theorem map_smul₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (r : R) (x : M) (y : N) : coe_fn (coe_fn f (r • x)) y = r • coe_fn (coe_fn f x) y :=
  map_smul (coe_fn (flip f) y) r x

/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def lcomp (R : Type u_1) [comm_semiring R] {M : Type u_2} {N : Type u_3} (P : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M N) : linear_map R (linear_map R N P) (linear_map R M P) :=
  flip (comp (flip id) f)

@[simp] theorem lcomp_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M N) (g : linear_map R N P) (x : M) : coe_fn (coe_fn (lcomp R P f) g) x = coe_fn g (coe_fn f x) :=
  rfl

/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def llcomp (R : Type u_1) [comm_semiring R] (M : Type u_2) (N : Type u_3) (P : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_map R (linear_map R N P) (linear_map R (linear_map R M N) (linear_map R M P)) :=
  flip (mk (lcomp R P) sorry sorry)

@[simp] theorem llcomp_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (g : linear_map R M N) (x : M) : coe_fn (coe_fn (coe_fn (llcomp R M N P) f) g) x = coe_fn f (coe_fn g x) :=
  rfl

/-- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`. -/
def compl₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} {Q : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M (linear_map R N P)) (g : linear_map R Q N) : linear_map R M (linear_map R Q P) :=
  comp (lcomp R P g) f

@[simp] theorem compl₂_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} {Q : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M (linear_map R N P)) (g : linear_map R Q N) (m : M) (q : Q) : coe_fn (coe_fn (compl₂ f g) m) q = coe_fn (coe_fn f m) (coe_fn g q) :=
  rfl

/-- Composing a linear map `P → Q` and a bilinear map `M × N → P` to
form a bilinear map `M → N → Q`. -/
def compr₂ {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} {Q : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M (linear_map R N P)) (g : linear_map R P Q) : linear_map R M (linear_map R N Q) :=
  comp (coe_fn (llcomp R N P Q) g) f

@[simp] theorem compr₂_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} {Q : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M (linear_map R N P)) (g : linear_map R P Q) (m : M) (n : N) : coe_fn (coe_fn (compr₂ f g) m) n = coe_fn g (coe_fn (coe_fn f m) n) :=
  rfl

/-- Scalar multiplication as a bilinear map `R → M → M`. -/
def lsmul (R : Type u_1) [comm_semiring R] (M : Type u_2) [add_comm_monoid M] [semimodule R M] : linear_map R R (linear_map R M M) :=
  mk₂ R has_scalar.smul sorry sorry sorry sorry

@[simp] theorem lsmul_apply {R : Type u_1} [comm_semiring R] {M : Type u_2} [add_comm_monoid M] [semimodule R M] (r : R) (m : M) : coe_fn (coe_fn (lsmul R M) r) m = r • m :=
  rfl

end linear_map


namespace tensor_product


-- open free_add_monoid

/-- The relation on `free_add_monoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : free_add_monoid (M × N) → free_add_monoid (M × N) → Prop
where
| of_zero_left : ∀ (n : N), eqv R M N (free_add_monoid.of (0, n)) 0
| of_zero_right : ∀ (m : M), eqv R M N (free_add_monoid.of (m, 0)) 0
| of_add_left : ∀ (m₁ m₂ : M) (n : N),
  eqv R M N (free_add_monoid.of (m₁, n) + free_add_monoid.of (m₂, n)) (free_add_monoid.of (m₁ + m₂, n))
| of_add_right : ∀ (m : M) (n₁ n₂ : N),
  eqv R M N (free_add_monoid.of (m, n₁) + free_add_monoid.of (m, n₂)) (free_add_monoid.of (m, n₁ + n₂))
| of_smul : ∀ (r : R) (m : M) (n : N), eqv R M N (free_add_monoid.of (r • m, n)) (free_add_monoid.of (m, r • n))
| add_comm : ∀ (x y : free_add_monoid (M × N)), eqv R M N (x + y) (y + x)

end tensor_product


/-- The tensor product of two semimodules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open_locale tensor_product`. -/
def tensor_product (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N]  :=
  add_con.quotient (add_con_gen sorry)

namespace tensor_product


protected instance add_comm_monoid {R : Type u_1} [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : add_comm_monoid (tensor_product R M N) :=
  add_comm_monoid.mk add_monoid.add sorry add_monoid.zero sorry sorry sorry

protected instance inhabited {R : Type u_1} [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : Inhabited (tensor_product R M N) :=
  { default := 0 }

/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open_locale tensor_product`. -/
def tmul (R : Type u_1) [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) (n : N) : tensor_product R M N :=
  coe_fn (add_con.mk' (add_con_gen (eqv R M N))) (free_add_monoid.of (m, n))

protected theorem induction_on {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] {C : tensor_product R M N → Prop} (z : tensor_product R M N) (C0 : C 0) (C1 : ∀ {x : M} {y : N}, C (tmul R x y)) (Cp : ∀ {x y : tensor_product R M N}, C x → C y → C (x + y)) : C z := sorry

@[simp] theorem zero_tmul {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (n : N) : tmul R 0 n = 0 :=
  quotient.sound' (add_con_gen.rel.of (free_add_monoid.of (0, n)) 0 (eqv.of_zero_left n))

theorem add_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m₁ : M) (m₂ : M) (n : N) : tmul R (m₁ + m₂) n = tmul R m₁ n + tmul R m₂ n := sorry

@[simp] theorem tmul_zero {R : Type u_1} [comm_semiring R] {M : Type u_3} (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) : tmul R m 0 = 0 :=
  quotient.sound' (add_con_gen.rel.of (free_add_monoid.of (m, 0)) 0 (eqv.of_zero_right m))

theorem tmul_add {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) (n₁ : N) (n₂ : N) : tmul R m (n₁ + n₂) = tmul R m n₁ + tmul R m n₂ := sorry

/--
A typeclass for `has_scalar` structures which can be moved across a tensor product.

This typeclass is generated automatically from a `is_scalar_tower` instance, but exists so that
we can also add an instance for `add_comm_group.int_module`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `semimodule R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `tensor_product.smul_tmul`, `tensor_product.smul_tmul'`, or `tensor_product.tmul_smul` is
used.
-/
class compatible_smul (R : Type u_1) [comm_semiring R] (R' : Type u_2) [comm_semiring R'] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] 
where
  smul_tmul : ∀ (r : R') (m : M) (n : N), tmul R (r • m) n = tmul R m (r • n)

/-- Note that this provides the default `compatible_smul R R M N` instance through
`mul_action.is_scalar_tower.left`. -/
protected instance compatible_smul.is_scalar_tower {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [has_scalar R' R] [is_scalar_tower R' R M] [is_scalar_tower R' R N] : compatible_smul R R' M N :=
  compatible_smul.mk sorry

/-- `smul` can be moved from one side of the product to the other .-/
theorem smul_tmul {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [compatible_smul R R' M N] (r : R') (m : M) (n : N) : tmul R (r • m) n = tmul R m (r • n) :=
  compatible_smul.smul_tmul r m n

/-- Auxiliary function to defining scalar multiplication on tensor product. -/
def smul.aux {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] {R' : Type u_2} [has_scalar R' M] (r : R') : free_add_monoid (M × N) →+ tensor_product R M N :=
  coe_fn free_add_monoid.lift fun (p : M × N) => tmul R (r • prod.fst p) (prod.snd p)

theorem smul.aux_of {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] {R' : Type u_2} [has_scalar R' M] (r : R') (m : M) (n : N) : coe_fn (smul.aux r) (free_add_monoid.of (m, n)) = tmul R (r • m) n :=
  rfl

-- Most of the time we want the instance below this one, which is easier for typeclass resolution

-- to find. The `unused_arguments` is from one of the two comm_classes - while we only make use

-- of one, it makes sense to make the API symmetric.

protected instance has_scalar' {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [smul_comm_class R R' M] [smul_comm_class R R' N] : has_scalar R' (tensor_product R M N) :=
  has_scalar.mk fun (r : R') => ⇑(add_con.lift (add_con_gen (eqv R M N)) (smul.aux r) sorry)

protected instance has_scalar {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : has_scalar R (tensor_product R M N) :=
  tensor_product.has_scalar'

protected theorem smul_zero {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [smul_comm_class R R' M] [smul_comm_class R R' N] (r : R') : r • 0 = 0 :=
  add_monoid_hom.map_zero (add_con.lift (add_con_gen (eqv R M N)) (smul.aux r) (has_scalar'._proof_1 r))

protected theorem smul_add {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [smul_comm_class R R' M] [smul_comm_class R R' N] (r : R') (x : tensor_product R M N) (y : tensor_product R M N) : r • (x + y) = r • x + r • y :=
  add_monoid_hom.map_add (add_con.lift (add_con_gen (eqv R M N)) (smul.aux r) (has_scalar'._proof_1 r)) x y

-- Most of the time we want the instance below this one, which is easier for typeclass resolution

-- to find.

protected instance semimodule' {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [smul_comm_class R R' M] [smul_comm_class R R' N] : semimodule R' (tensor_product R M N) :=
  (fun (this : ∀ (r : R') (m : M) (n : N), r • tmul R m n = tmul R (r • m) n) => semimodule.mk sorry sorry) sorry

protected instance semimodule {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : semimodule R (tensor_product R M N) :=
  tensor_product.semimodule'

-- note that we don't actually need `compatible_smul` here, but we include it for symmetry

-- with `tmul_smul` to avoid exposing our asymmetric definition.

theorem smul_tmul' {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [smul_comm_class R R' M] [smul_comm_class R R' N] [compatible_smul R R' M N] (r : R') (m : M) (n : N) : r • tmul R m n = tmul R (r • m) n :=
  rfl

@[simp] theorem tmul_smul {R : Type u_1} [comm_semiring R] {R' : Type u_2} [comm_semiring R'] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] [semimodule R' M] [semimodule R' N] [smul_comm_class R R' M] [smul_comm_class R R' N] [compatible_smul R R' M N] (r : R') (x : M) (y : N) : tmul R x (r • y) = r • tmul R x y :=
  Eq.symm (smul_tmul r x y)

/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
def mk (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : linear_map R M (linear_map R N (tensor_product R M N)) :=
  linear_map.mk₂ R (fun (_x : M) (_y : N) => tmul R _x _y) add_tmul sorry tmul_add sorry

@[simp] theorem mk_apply {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) (n : N) : coe_fn (coe_fn (mk R M N) m) n = tmul R m n :=
  rfl

theorem ite_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] : tmul R (ite P x₁ 0) x₂ = ite P (tmul R x₁ x₂) 0 := sorry

theorem tmul_ite {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] : tmul R x₁ (ite P x₂ 0) = ite P (tmul R x₁ x₂) 0 := sorry

theorem sum_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] {α : Type u_2} (s : finset α) (m : α → M) (n : N) : tmul R (finset.sum s fun (a : α) => m a) n = finset.sum s fun (a : α) => tmul R (m a) n := sorry

theorem tmul_sum {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) {α : Type u_2} (s : finset α) (n : α → N) : tmul R m (finset.sum s fun (a : α) => n a) = finset.sum s fun (a : α) => tmul R m (n a) := sorry

/-- Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift_aux {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) : tensor_product R M N →+ P :=
  add_con.lift (add_con_gen (eqv R M N))
    (coe_fn free_add_monoid.lift fun (p : M × N) => coe_fn (coe_fn f (prod.fst p)) (prod.snd p)) sorry

theorem lift_aux_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (m : M) (n : N) : coe_fn (lift_aux f) (tmul R m n) = coe_fn (coe_fn f m) n :=
  zero_add ((fun (p : M × N) => coe_fn (coe_fn f (prod.fst p)) (prod.snd p)) (m, n))

@[simp] theorem lift_aux.smul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {f : linear_map R M (linear_map R N P)} (r : R) (x : tensor_product R M N) : coe_fn (lift_aux f) (r • x) = r • coe_fn (lift_aux f) x := sorry

/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) : linear_map R (tensor_product R M N) P :=
  linear_map.mk (add_monoid_hom.to_fun (lift_aux f)) sorry lift_aux.smul

@[simp] theorem lift.tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {f : linear_map R M (linear_map R N P)} (x : M) (y : N) : coe_fn (lift f) (tmul R x y) = coe_fn (coe_fn f x) y :=
  zero_add ((fun (p : M × N) => coe_fn (coe_fn f (prod.fst p)) (prod.snd p)) (x, y))

@[simp] theorem lift.tmul' {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {f : linear_map R M (linear_map R N P)} (x : M) (y : N) : linear_map.to_fun (lift f) (tmul R x y) = coe_fn (coe_fn f x) y :=
  lift.tmul x y

theorem ext {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {g : linear_map R (tensor_product R M N) P} {h : linear_map R (tensor_product R M N) P} (H : ∀ (x : M) (y : N), coe_fn g (tmul R x y) = coe_fn h (tmul R x y)) : g = h := sorry

theorem lift.unique {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {f : linear_map R M (linear_map R N P)} {g : linear_map R (tensor_product R M N) P} (H : ∀ (x : M) (y : N), coe_fn g (tmul R x y) = coe_fn (coe_fn f x) y) : g = lift f := sorry

theorem lift_mk {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : lift (mk R M N) = linear_map.id :=
  Eq.symm (lift.unique fun (x : M) (y : N) => rfl)

theorem lift_compr₂ {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] {f : linear_map R M (linear_map R N P)} (g : linear_map R P Q) : lift (linear_map.compr₂ f g) = linear_map.comp g (lift f) := sorry

theorem lift_mk_compr₂ {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R (tensor_product R M N) P) : lift (linear_map.compr₂ (mk R M N) f) = f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (lift (linear_map.compr₂ (mk R M N) f) = f)) (lift_compr₂ f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (linear_map.comp f (lift (mk R M N)) = f)) lift_mk))
      (eq.mpr (id (Eq._oldrec (Eq.refl (linear_map.comp f linear_map.id = f)) (linear_map.comp_id f))) (Eq.refl f)))

theorem mk_compr₂_inj {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] {g : linear_map R (tensor_product R M N) P} {h : linear_map R (tensor_product R M N) P} (H : linear_map.compr₂ (mk R M N) g = linear_map.compr₂ (mk R M N) h) : g = h :=
  eq.mpr (id (Eq._oldrec (Eq.refl (g = h)) (Eq.symm (lift_mk_compr₂ g))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (lift (linear_map.compr₂ (mk R M N) g) = h)) H))
      (eq.mpr (id (Eq._oldrec (Eq.refl (lift (linear_map.compr₂ (mk R M N) h) = h)) (lift_mk_compr₂ h))) (Eq.refl h)))

/-- Linearly constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurry (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) (P : Type u_5) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_map R (linear_map R M (linear_map R N P)) (linear_map R (tensor_product R M N) P) :=
  linear_map.flip
    (lift (linear_map.comp (linear_map.lflip R (linear_map R M (linear_map R N P)) N P) (linear_map.flip linear_map.id)))

@[simp] theorem uncurry_apply {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R M (linear_map R N P)) (m : M) (n : N) : coe_fn (coe_fn (uncurry R M N P) f) (tmul R m n) = coe_fn (coe_fn f m) n := sorry

/-- A linear equivalence constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift.equiv (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) (P : Type u_5) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_equiv R (linear_map R M (linear_map R N P)) (linear_map R (tensor_product R M N) P) :=
  linear_equiv.mk (linear_map.to_fun (uncurry R M N P)) sorry sorry
    (fun (f : linear_map R (tensor_product R M N) P) => linear_map.compr₂ (mk R M N) f) sorry sorry

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def lcurry (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) (P : Type u_5) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_map R (linear_map R (tensor_product R M N) P) (linear_map R M (linear_map R N P)) :=
  ↑(linear_equiv.symm (lift.equiv R M N P))

@[simp] theorem lcurry_apply {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R (tensor_product R M N) P) (m : M) (n : N) : coe_fn (coe_fn (coe_fn (lcurry R M N P) f) m) n = coe_fn f (tmul R m n) :=
  rfl

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def curry {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R (tensor_product R M N) P) : linear_map R M (linear_map R N P) :=
  coe_fn (lcurry R M N P) f

@[simp] theorem curry_apply {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R (tensor_product R M N) P) (m : M) (n : N) : coe_fn (coe_fn (curry f) m) n = coe_fn f (tmul R m n) :=
  rfl

theorem ext_threefold {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] {g : linear_map R (tensor_product R (tensor_product R M N) P) Q} {h : linear_map R (tensor_product R (tensor_product R M N) P) Q} (H : ∀ (x : M) (y : N) (z : P), coe_fn g (tmul R (tmul R x y) z) = coe_fn h (tmul R (tmul R x y) z)) : g = h := sorry

-- We'll need this one for checking the pentagon identity!

theorem ext_fourfold {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} {S : Type u_7} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S] {g : linear_map R (tensor_product R (tensor_product R (tensor_product R M N) P) Q) S} {h : linear_map R (tensor_product R (tensor_product R (tensor_product R M N) P) Q) S} (H : ∀ (w : M) (x : N) (y : P) (z : Q),
  coe_fn g (tmul R (tmul R (tmul R w x) y) z) = coe_fn h (tmul R (tmul R (tmul R w x) y) z)) : g = h := sorry

/--
The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
protected def lid (R : Type u_1) [comm_semiring R] (M : Type u_3) [add_comm_monoid M] [semimodule R M] : linear_equiv R (tensor_product R R M) M :=
  linear_equiv.of_linear (lift (linear_map.lsmul R M)) (coe_fn (mk R R M) 1) sorry sorry

@[simp] theorem lid_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} [add_comm_monoid M] [semimodule R M] (m : M) (r : R) : coe_fn (tensor_product.lid R M) (tmul R r m) = r • m := sorry

@[simp] theorem lid_symm_apply {R : Type u_1} [comm_semiring R] {M : Type u_3} [add_comm_monoid M] [semimodule R M] (m : M) : coe_fn (linear_equiv.symm (tensor_product.lid R M)) m = tmul R 1 m :=
  rfl

/--
The tensor product of modules is commutative, up to linear equivalence.
-/
protected def comm (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : linear_equiv R (tensor_product R M N) (tensor_product R N M) :=
  linear_equiv.of_linear (lift (linear_map.flip (mk R N M))) (lift (linear_map.flip (mk R M N))) sorry sorry

@[simp] theorem comm_tmul (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) (n : N) : coe_fn (tensor_product.comm R M N) (tmul R m n) = tmul R n m :=
  rfl

@[simp] theorem comm_symm_tmul (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] (m : M) (n : N) : coe_fn (linear_equiv.symm (tensor_product.comm R M N)) (tmul R n m) = tmul R m n :=
  rfl

/--
The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
protected def rid (R : Type u_1) [comm_semiring R] (M : Type u_3) [add_comm_monoid M] [semimodule R M] : linear_equiv R (tensor_product R M R) M :=
  linear_equiv.trans (tensor_product.comm R M R) (tensor_product.lid R M)

@[simp] theorem rid_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} [add_comm_monoid M] [semimodule R M] (m : M) (r : R) : coe_fn (tensor_product.rid R M) (tmul R m r) = r • m := sorry

@[simp] theorem rid_symm_apply {R : Type u_1} [comm_semiring R] {M : Type u_3} [add_comm_monoid M] [semimodule R M] (m : M) : coe_fn (linear_equiv.symm (tensor_product.rid R M)) m = tmul R m 1 :=
  rfl

/-- The associator for tensor product of R-modules, as a linear equivalence. -/
protected def assoc (R : Type u_1) [comm_semiring R] (M : Type u_3) (N : Type u_4) (P : Type u_5) [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_equiv R (tensor_product R (tensor_product R M N) P) (tensor_product R M (tensor_product R N P)) :=
  linear_equiv.of_linear
    (lift
      (lift (linear_map.comp (lcurry R N P (tensor_product R M (tensor_product R N P))) (mk R M (tensor_product R N P)))))
    (lift
      (linear_map.comp (uncurry R N P (tensor_product R (tensor_product R M N) P))
        (curry (mk R (tensor_product R M N) P))))
    sorry sorry

@[simp] theorem assoc_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (m : M) (n : N) (p : P) : coe_fn (tensor_product.assoc R M N P) (tmul R (tmul R m n) p) = tmul R m (tmul R n p) :=
  rfl

@[simp] theorem assoc_symm_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (m : M) (n : N) (p : P) : coe_fn (linear_equiv.symm (tensor_product.assoc R M N P)) (tmul R m (tmul R n p)) = tmul R (tmul R m n) p :=
  rfl

/-- The tensor product of a pair of linear maps between modules. -/
def map {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M P) (g : linear_map R N Q) : linear_map R (tensor_product R M N) (tensor_product R P Q) :=
  lift (linear_map.comp (linear_map.compl₂ (mk R P Q) g) f)

@[simp] theorem map_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M P) (g : linear_map R N Q) (m : M) (n : N) : coe_fn (map f g) (tmul R m n) = tmul R (coe_fn f m) (coe_fn g n) :=
  rfl

theorem map_comp {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] {P' : Type u_8} {Q' : Type u_9} [add_comm_monoid P'] [semimodule R P'] [add_comm_monoid Q'] [semimodule R Q'] (f₂ : linear_map R P P') (f₁ : linear_map R M P) (g₂ : linear_map R Q Q') (g₁ : linear_map R N Q) : map (linear_map.comp f₂ f₁) (linear_map.comp g₂ g₁) = linear_map.comp (map f₂ g₂) (map f₁ g₁) := sorry

theorem lift_comp_map {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] {Q' : Type u_9} [add_comm_monoid Q'] [semimodule R Q'] (i : linear_map R P (linear_map R Q Q')) (f : linear_map R M P) (g : linear_map R N Q) : linear_map.comp (lift i) (map f g) = lift (linear_map.compl₂ (linear_map.comp i f) g) := sorry

/-- If `M` and `P` are linearly equivalent and `N` and `Q` are linearly equivalent
then `M ⊗ N` and `P ⊗ Q` are linearly equivalent. -/
def congr {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_equiv R M P) (g : linear_equiv R N Q) : linear_equiv R (tensor_product R M N) (tensor_product R P Q) :=
  linear_equiv.of_linear (map ↑f ↑g) (map ↑(linear_equiv.symm f) ↑(linear_equiv.symm g)) sorry sorry

@[simp] theorem congr_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_equiv R M P) (g : linear_equiv R N Q) (m : M) (n : N) : coe_fn (congr f g) (tmul R m n) = tmul R (coe_fn f m) (coe_fn g n) :=
  rfl

@[simp] theorem congr_symm_tmul {R : Type u_1} [comm_semiring R] {M : Type u_3} {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_equiv R M P) (g : linear_equiv R N Q) (p : P) (q : Q) : coe_fn (linear_equiv.symm (congr f g)) (tmul R p q) =
  tmul R (coe_fn (linear_equiv.symm f) p) (coe_fn (linear_equiv.symm g) q) :=
  rfl

end tensor_product


namespace linear_map


/-- `ltensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map induced by `f : N →ₗ P`. -/
def ltensor {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) : linear_map R (tensor_product R M N) (tensor_product R M P) :=
  tensor_product.map id f

/-- `rtensor f M : N₁ ⊗ M →ₗ N₂ ⊗ M` is the natural linear map induced by `f : N₁ →ₗ N₂`. -/
def rtensor {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) : linear_map R (tensor_product R N M) (tensor_product R P M) :=
  tensor_product.map f id

@[simp] theorem ltensor_tmul {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (m : M) (n : N) : coe_fn (ltensor M f) (tensor_product.tmul R m n) = tensor_product.tmul R m (coe_fn f n) :=
  rfl

@[simp] theorem rtensor_tmul {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (m : M) (n : N) : coe_fn (rtensor M f) (tensor_product.tmul R n m) = tensor_product.tmul R (coe_fn f n) m :=
  rfl

/-- `ltensor_hom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def ltensor_hom {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_map R (linear_map R N P) (linear_map R (tensor_product R M N) (tensor_product R M P)) :=
  mk (ltensor M) sorry sorry

/-- `rtensor_hom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def rtensor_hom {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : linear_map R (linear_map R N P) (linear_map R (tensor_product R N M) (tensor_product R P M)) :=
  mk (fun (f : linear_map R N P) => rtensor M f) sorry sorry

@[simp] theorem coe_ltensor_hom {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : ⇑(ltensor_hom M) = ltensor M :=
  rfl

@[simp] theorem coe_rtensor_hom {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : ⇑(rtensor_hom M) = rtensor M :=
  rfl

@[simp] theorem ltensor_add {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (g : linear_map R N P) : ltensor M (f + g) = ltensor M f + ltensor M g :=
  map_add (ltensor_hom M) f g

@[simp] theorem rtensor_add {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (g : linear_map R N P) : rtensor M (f + g) = rtensor M f + rtensor M g :=
  map_add (rtensor_hom M) f g

@[simp] theorem ltensor_zero {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : ltensor M 0 = 0 :=
  map_zero (ltensor_hom M)

@[simp] theorem rtensor_zero {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] : rtensor M 0 = 0 :=
  map_zero (rtensor_hom M)

@[simp] theorem ltensor_smul {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (r : R) (f : linear_map R N P) : ltensor M (r • f) = r • ltensor M f :=
  map_smul (ltensor_hom M) r f

@[simp] theorem rtensor_smul {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [semimodule R M] [semimodule R N] [semimodule R P] (r : R) (f : linear_map R N P) : rtensor M (r • f) = r • rtensor M f :=
  map_smul (rtensor_hom M) r f

theorem ltensor_comp {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (g : linear_map R P Q) (f : linear_map R N P) : ltensor M (comp g f) = comp (ltensor M g) (ltensor M f) := sorry

theorem rtensor_comp {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (g : linear_map R P Q) (f : linear_map R N P) : rtensor M (comp g f) = comp (rtensor M g) (rtensor M f) := sorry

@[simp] theorem ltensor_id {R : Type u_1} [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : ltensor M id = id := sorry

@[simp] theorem rtensor_id {R : Type u_1} [comm_semiring R] (M : Type u_3) (N : Type u_4) [add_comm_monoid M] [add_comm_monoid N] [semimodule R M] [semimodule R N] : rtensor M id = id := sorry

@[simp] theorem ltensor_comp_rtensor {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M P) (g : linear_map R N Q) : comp (ltensor P g) (rtensor N f) = tensor_product.map f g := sorry

@[simp] theorem rtensor_comp_ltensor {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] (f : linear_map R M P) (g : linear_map R N Q) : comp (rtensor Q f) (ltensor M g) = tensor_product.map f g := sorry

@[simp] theorem map_comp_rtensor {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} {S : Type u_7} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S] (f : linear_map R M P) (g : linear_map R N Q) (f' : linear_map R S M) : comp (tensor_product.map f g) (rtensor N f') = tensor_product.map (comp f f') g := sorry

@[simp] theorem map_comp_ltensor {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} {S : Type u_7} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S] (f : linear_map R M P) (g : linear_map R N Q) (g' : linear_map R S N) : comp (tensor_product.map f g) (ltensor M g') = tensor_product.map f (comp g g') := sorry

@[simp] theorem rtensor_comp_map {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} {S : Type u_7} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S] (f' : linear_map R P S) (f : linear_map R M P) (g : linear_map R N Q) : comp (rtensor Q f') (tensor_product.map f g) = tensor_product.map (comp f' f) g := sorry

@[simp] theorem ltensor_comp_map {R : Type u_1} [comm_semiring R] (M : Type u_3) {N : Type u_4} {P : Type u_5} {Q : Type u_6} {S : Type u_7} [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S] [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S] (g' : linear_map R Q S) (f : linear_map R M P) (g : linear_map R N Q) : comp (ltensor P g') (tensor_product.map f g) = tensor_product.map f (comp g' g) := sorry

end linear_map


namespace tensor_product


/-- Auxiliary function to defining negation multiplication on tensor product. -/
def neg.aux (R : Type u_1) [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] : free_add_monoid (M × N) →+ tensor_product R M N :=
  coe_fn free_add_monoid.lift fun (p : M × N) => tmul R (-prod.fst p) (prod.snd p)

theorem neg.aux_of {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] (m : M) (n : N) : coe_fn (neg.aux R) (free_add_monoid.of (m, n)) = tmul R (-m) n :=
  rfl

protected instance has_neg {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] : Neg (tensor_product R M N) :=
  { neg := ⇑(add_con.lift (add_con_gen (eqv R M N)) (neg.aux R) sorry) }

protected instance add_comm_group {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] : add_comm_group (tensor_product R M N) :=
  add_comm_group.mk add_comm_monoid.add sorry add_comm_monoid.zero sorry sorry Neg.neg
    (fun (_x _x_1 : tensor_product R M N) => add_semigroup.add _x (-_x_1)) sorry sorry

theorem neg_tmul {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] (m : M) (n : N) : tmul R (-m) n = -tmul R m n :=
  rfl

theorem tmul_neg {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] (m : M) (n : N) : tmul R m (-n) = -tmul R m n :=
  linear_map.map_neg (coe_fn (mk R M N) m) n

theorem tmul_sub {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] (m : M) (n₁ : N) (n₂ : N) : tmul R m (n₁ - n₂) = tmul R m n₁ - tmul R m n₂ :=
  linear_map.map_sub (coe_fn (mk R M N) m) n₁ n₂

theorem sub_tmul {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] (m₁ : M) (m₂ : M) (n : N) : tmul R (m₁ - m₂) n = tmul R m₁ n - tmul R m₂ n :=
  linear_map.map_sub₂ (mk R M N) m₁ m₂ n

/--
While the tensor product will automatically inherit a ℤ-module structure from
`add_comm_group.int_module`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-module` instance provided by `tensor_product.semimodule'`.

When `R` is a `ring` we get the required `tensor_product.compatible_smul` instance through
`is_scalar_tower`, but when it is only a `semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
protected instance compatible_smul.int {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N] [semimodule ℤ M] [semimodule ℤ N] : compatible_smul R ℤ M N :=
  compatible_smul.mk sorry

end tensor_product


namespace linear_map


@[simp] theorem ltensor_sub {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_group M] [add_comm_group N] [add_comm_group P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (g : linear_map R N P) : ltensor M (f - g) = ltensor M f - ltensor M g := sorry

@[simp] theorem rtensor_sub {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_group M] [add_comm_group N] [add_comm_group P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) (g : linear_map R N P) : rtensor M (f - g) = rtensor M f - rtensor M g := sorry

@[simp] theorem ltensor_neg {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_group M] [add_comm_group N] [add_comm_group P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) : ltensor M (-f) = -ltensor M f := sorry

@[simp] theorem rtensor_neg {R : Type u_1} [comm_semiring R] {M : Type u_2} {N : Type u_3} {P : Type u_4} [add_comm_group M] [add_comm_group N] [add_comm_group P] [semimodule R M] [semimodule R N] [semimodule R P] (f : linear_map R N P) : rtensor M (-f) = -rtensor M f := sorry

