/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.linear_algebra.tensor_product
import Mathlib.algebra.algebra.basic
import PostPort

universes u v₁ v₂ v₃ v₄ 

namespace Mathlib

/-!
# The tensor product of R-algebras

We construct the R-algebra structure on `A ⊗[R] B`, when `A` and `B` are both `R`-algebras,
and provide the structure isomorphisms

* `R ⊗[R] A ≃ₐ[R] A`
* `A ⊗[R] R ≃ₐ[R] A`
* `A ⊗[R] B ≃ₐ[R] B ⊗[R] A`

The code for
* `((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`
is written and compiles, but takes longer than the `-T100000` time limit,
so is currently commented out.
-/

namespace algebra


namespace tensor_product


/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mul_aux {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (a₁ : A) (b₁ : B) : linear_map R (tensor_product R A B) (tensor_product R A B) :=
  tensor_product.lift
    (linear_map.mk (fun (a₂ : A) => linear_map.mk (fun (b₂ : B) => tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) sorry sorry)
      sorry sorry)

@[simp] theorem mul_aux_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) : coe_fn (mul_aux a₁ b₁) (tensor_product.tmul R a₂ b₂) = tensor_product.tmul R (a₁ * a₂) (b₁ * b₂) :=
  rfl

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : linear_map R (tensor_product R A B) (linear_map R (tensor_product R A B) (tensor_product R A B)) :=
  tensor_product.lift
    (linear_map.mk (fun (a₁ : A) => linear_map.mk (fun (b₁ : B) => mul_aux a₁ b₁) sorry sorry) sorry sorry)

@[simp] theorem mul_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) : coe_fn (coe_fn mul (tensor_product.tmul R a₁ b₁)) (tensor_product.tmul R a₂ b₂) =
  tensor_product.tmul R (a₁ * a₂) (b₁ * b₂) :=
  rfl

theorem mul_assoc' {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (mul : linear_map R (tensor_product R A B) (linear_map R (tensor_product R A B) (tensor_product R A B))) (h : ∀ (a₁ a₂ a₃ : A) (b₁ b₂ b₃ : B),
  coe_fn (coe_fn mul (coe_fn (coe_fn mul (tensor_product.tmul R a₁ b₁)) (tensor_product.tmul R a₂ b₂)))
      (tensor_product.tmul R a₃ b₃) =
    coe_fn (coe_fn mul (tensor_product.tmul R a₁ b₁))
      (coe_fn (coe_fn mul (tensor_product.tmul R a₂ b₂)) (tensor_product.tmul R a₃ b₃))) (x : tensor_product R A B) (y : tensor_product R A B) (z : tensor_product R A B) : coe_fn (coe_fn mul (coe_fn (coe_fn mul x) y)) z = coe_fn (coe_fn mul x) (coe_fn (coe_fn mul y) z) := sorry

theorem mul_assoc {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (x : tensor_product R A B) (y : tensor_product R A B) (z : tensor_product R A B) : coe_fn (coe_fn mul (coe_fn (coe_fn mul x) y)) z = coe_fn (coe_fn mul x) (coe_fn (coe_fn mul y) z) := sorry

theorem one_mul {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (x : tensor_product R A B) : coe_fn (coe_fn mul (tensor_product.tmul R 1 1)) x = x := sorry

theorem mul_one {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (x : tensor_product R A B) : coe_fn (coe_fn mul x) (tensor_product.tmul R 1 1) = x := sorry

protected instance tensor_product.semiring {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : semiring (tensor_product R A B) :=
  semiring.mk Add.add sorry 0 sorry sorry sorry (fun (a b : tensor_product R A B) => coe_fn (coe_fn mul a) b) mul_assoc
    (tensor_product.tmul R 1 1) one_mul mul_one sorry sorry sorry sorry

theorem one_def {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : 1 = tensor_product.tmul R 1 1 :=
  rfl

@[simp] theorem tmul_mul_tmul {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) : tensor_product.tmul R a₁ b₁ * tensor_product.tmul R a₂ b₂ = tensor_product.tmul R (a₁ * a₂) (b₁ * b₂) :=
  rfl

@[simp] theorem tmul_pow {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (a : A) (b : B) (k : ℕ) : tensor_product.tmul R a b ^ k = tensor_product.tmul R (a ^ k) (b ^ k) := sorry

/--
The algebra map `R →+* (A ⊗[R] B)` giving `A ⊗[R] B` the structure of an `R`-algebra.
-/
def tensor_algebra_map {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : R →+* tensor_product R A B :=
  ring_hom.mk (fun (r : R) => tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) sorry sorry sorry sorry

protected instance tensor_product.algebra {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : algebra R (tensor_product R A B) :=
  mk (ring_hom.mk (ring_hom.to_fun tensor_algebra_map) sorry sorry sorry sorry) sorry sorry

@[simp] theorem algebra_map_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (r : R) : coe_fn (algebra_map R (tensor_product R A B)) r = tensor_product.tmul R (coe_fn (algebra_map R A) r) 1 :=
  rfl

theorem ext {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {g : alg_hom R (tensor_product R A B) C} {h : alg_hom R (tensor_product R A B) C} (H : ∀ (a : A) (b : B), coe_fn g (tensor_product.tmul R a b) = coe_fn h (tensor_product.tmul R a b)) : g = h := sorry

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def include_left {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : alg_hom R A (tensor_product R A B) :=
  alg_hom.mk (fun (a : A) => tensor_product.tmul R a 1) sorry sorry sorry sorry sorry

@[simp] theorem include_left_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (a : A) : coe_fn include_left a = tensor_product.tmul R a 1 :=
  rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
def include_right {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] : alg_hom R B (tensor_product R A B) :=
  alg_hom.mk (fun (b : B) => tensor_product.tmul R 1 b) sorry sorry sorry sorry sorry

@[simp] theorem include_right_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] (b : B) : coe_fn include_right b = tensor_product.tmul R 1 b :=
  rfl

protected instance tensor_product.ring {R : Type u} [comm_ring R] {A : Type v₁} [ring A] [algebra R A] {B : Type v₂} [ring B] [algebra R B] : ring (tensor_product R A B) :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    semiring.mul sorry semiring.one sorry sorry sorry sorry

protected instance tensor_product.comm_ring {R : Type u} [comm_ring R] {A : Type v₁} [comm_ring A] [algebra R A] {B : Type v₂} [comm_ring B] [algebra R B] : comm_ring (tensor_product R A B) :=
  comm_ring.mk ring.add sorry ring.zero sorry sorry ring.neg ring.sub sorry sorry ring.mul sorry ring.one sorry sorry
    sorry sorry sorry

/--
Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
/--
Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/

/--
Build an algebra morphism from a linear map out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_hom_of_linear_map_tensor_product {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] (f : linear_map R (tensor_product R A B) C) (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
  coe_fn f (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) =
    coe_fn f (tensor_product.tmul R a₁ b₁) * coe_fn f (tensor_product.tmul R a₂ b₂)) (w₂ : ∀ (r : R), coe_fn f (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) = coe_fn (algebra_map R C) r) : alg_hom R (tensor_product R A B) C :=
  alg_hom.mk (linear_map.to_fun f) sorry sorry sorry sorry sorry

@[simp] theorem alg_hom_of_linear_map_tensor_product_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] (f : linear_map R (tensor_product R A B) C) (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
  coe_fn f (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) =
    coe_fn f (tensor_product.tmul R a₁ b₁) * coe_fn f (tensor_product.tmul R a₂ b₂)) (w₂ : ∀ (r : R), coe_fn f (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) = coe_fn (algebra_map R C) r) (x : tensor_product R A B) : coe_fn (alg_hom_of_linear_map_tensor_product f w₁ w₂) x = coe_fn f x :=
  rfl

/--
Build an algebra equivalence from a linear equivalence out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_equiv_of_linear_equiv_tensor_product {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] (f : linear_equiv R (tensor_product R A B) C) (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
  coe_fn f (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) =
    coe_fn f (tensor_product.tmul R a₁ b₁) * coe_fn f (tensor_product.tmul R a₂ b₂)) (w₂ : ∀ (r : R), coe_fn f (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) = coe_fn (algebra_map R C) r) : alg_equiv R (tensor_product R A B) C :=
  alg_equiv.mk (alg_hom.to_fun (alg_hom_of_linear_map_tensor_product (↑f) w₁ w₂)) (linear_equiv.inv_fun f) sorry sorry
    sorry sorry sorry

@[simp] theorem alg_equiv_of_linear_equiv_tensor_product_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] (f : linear_equiv R (tensor_product R A B) C) (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
  coe_fn f (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) =
    coe_fn f (tensor_product.tmul R a₁ b₁) * coe_fn f (tensor_product.tmul R a₂ b₂)) (w₂ : ∀ (r : R), coe_fn f (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) = coe_fn (algebra_map R C) r) (x : tensor_product R A B) : coe_fn (alg_equiv_of_linear_equiv_tensor_product f w₁ w₂) x = coe_fn f x :=
  rfl

/--
Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_equiv_of_linear_equiv_triple_tensor_product {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : linear_equiv R (tensor_product R (tensor_product R A B) C) D) (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
  coe_fn f (tensor_product.tmul R (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) (c₁ * c₂)) =
    coe_fn f (tensor_product.tmul R (tensor_product.tmul R a₁ b₁) c₁) *
      coe_fn f (tensor_product.tmul R (tensor_product.tmul R a₂ b₂) c₂)) (w₂ : ∀ (r : R),
  coe_fn f (tensor_product.tmul R (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) 1) = coe_fn (algebra_map R D) r) : alg_equiv R (tensor_product R (tensor_product R A B) C) D :=
  alg_equiv.mk (⇑f) (linear_equiv.inv_fun f) sorry sorry sorry sorry sorry

@[simp] theorem alg_equiv_of_linear_equiv_triple_tensor_product_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : linear_equiv R (tensor_product R (tensor_product R A B) C) D) (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
  coe_fn f (tensor_product.tmul R (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) (c₁ * c₂)) =
    coe_fn f (tensor_product.tmul R (tensor_product.tmul R a₁ b₁) c₁) *
      coe_fn f (tensor_product.tmul R (tensor_product.tmul R a₂ b₂) c₂)) (w₂ : ∀ (r : R),
  coe_fn f (tensor_product.tmul R (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) 1) = coe_fn (algebra_map R D) r) (x : tensor_product R (tensor_product R A B) C) : coe_fn (alg_equiv_of_linear_equiv_triple_tensor_product f w₁ w₂) x = coe_fn f x :=
  rfl

/--
The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def lid (R : Type u) [comm_semiring R] (A : Type v₁) [semiring A] [algebra R A] : alg_equiv R (tensor_product R R A) A :=
  alg_equiv_of_linear_equiv_tensor_product (tensor_product.lid R A) sorry sorry

@[simp] theorem lid_tmul (R : Type u) [comm_semiring R] (A : Type v₁) [semiring A] [algebra R A] (r : R) (a : A) : coe_fn (tensor_product.lid R A) (tensor_product.tmul R r a) = r • a := sorry

/--
The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def rid (R : Type u) [comm_semiring R] (A : Type v₁) [semiring A] [algebra R A] : alg_equiv R (tensor_product R A R) A :=
  alg_equiv_of_linear_equiv_tensor_product (tensor_product.rid R A) sorry sorry

@[simp] theorem rid_tmul (R : Type u) [comm_semiring R] (A : Type v₁) [semiring A] [algebra R A] (r : R) (a : A) : coe_fn (tensor_product.rid R A) (tensor_product.tmul R a r) = r • a := sorry

/--
The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm (R : Type u) [comm_semiring R] (A : Type v₁) [semiring A] [algebra R A] (B : Type v₂) [semiring B] [algebra R B] : alg_equiv R (tensor_product R A B) (tensor_product R B A) :=
  alg_equiv_of_linear_equiv_tensor_product (tensor_product.comm R A B) sorry sorry

@[simp] theorem comm_tmul (R : Type u) [comm_semiring R] (A : Type v₁) [semiring A] [algebra R A] (B : Type v₂) [semiring B] [algebra R B] (a : A) (b : B) : coe_fn (tensor_product.comm R A B) (tensor_product.tmul R a b) = tensor_product.tmul R b a := sorry

theorem assoc_aux_1 {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] (a₁ : A) (a₂ : A) (b₁ : B) (b₂ : B) (c₁ : C) (c₂ : C) : coe_fn (tensor_product.assoc R A B C) (tensor_product.tmul R (tensor_product.tmul R (a₁ * a₂) (b₁ * b₂)) (c₁ * c₂)) =
  coe_fn (tensor_product.assoc R A B C) (tensor_product.tmul R (tensor_product.tmul R a₁ b₁) c₁) *
    coe_fn (tensor_product.assoc R A B C) (tensor_product.tmul R (tensor_product.tmul R a₂ b₂) c₂) :=
  rfl

theorem assoc_aux_2 {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] (r : R) : coe_fn (tensor_product.assoc R A B C) (tensor_product.tmul R (tensor_product.tmul R (coe_fn (algebra_map R A) r) 1) 1) =
  coe_fn (algebra_map R (tensor_product R A (tensor_product R B C))) r :=
  rfl

-- variables (R A B C)

-- -- local attribute [elab_simple] alg_equiv_of_linear_equiv_triple_tensor_product

-- /-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/

-- -- FIXME This is _really_ slow to compile. :-(

-- protected def assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C)) :=

-- alg_equiv_of_linear_equiv_triple_tensor_product

--   (tensor_product.assoc R A B C)

--   assoc_aux_1 assoc_aux_2

-- variables {R A B C}

-- @[simp] theorem assoc_tmul (a : A) (b : B) (c : C) :

--   ((tensor_product.assoc R A B C) : (A ⊗[R] B) ⊗[R] C → A ⊗[R] (B ⊗[R] C)) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=

-- rfl

/-- The tensor product of a pair of algebra morphisms. -/
def map {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : alg_hom R A B) (g : alg_hom R C D) : alg_hom R (tensor_product R A C) (tensor_product R B D) :=
  alg_hom_of_linear_map_tensor_product (tensor_product.map (alg_hom.to_linear_map f) (alg_hom.to_linear_map g)) sorry
    sorry

@[simp] theorem map_tmul {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : alg_hom R A B) (g : alg_hom R C D) (a : A) (c : C) : coe_fn (map f g) (tensor_product.tmul R a c) = tensor_product.tmul R (coe_fn f a) (coe_fn g c) :=
  rfl

/--
Construct an isomorphism between tensor products of R-algebras
from isomorphisms between the tensor factors.
-/
def congr {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : alg_equiv R A B) (g : alg_equiv R C D) : alg_equiv R (tensor_product R A C) (tensor_product R B D) :=
  alg_equiv.of_alg_hom (map ↑f ↑g) (map ↑(alg_equiv.symm f) ↑(alg_equiv.symm g)) sorry sorry

@[simp] theorem congr_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : alg_equiv R A B) (g : alg_equiv R C D) (x : tensor_product R A C) : coe_fn (congr f g) x = coe_fn (map ↑f ↑g) x :=
  rfl

@[simp] theorem congr_symm_apply {R : Type u} [comm_semiring R] {A : Type v₁} [semiring A] [algebra R A] {B : Type v₂} [semiring B] [algebra R B] {C : Type v₃} [semiring C] [algebra R C] {D : Type v₄} [semiring D] [algebra R D] (f : alg_equiv R A B) (g : alg_equiv R C D) (x : tensor_product R B D) : coe_fn (alg_equiv.symm (congr f g)) x = coe_fn (map ↑(alg_equiv.symm f) ↑(alg_equiv.symm g)) x :=
  rfl

