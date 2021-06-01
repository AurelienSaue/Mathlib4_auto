/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.tactic.nth_rewrite.default
import Mathlib.data.matrix.basic
import Mathlib.data.equiv.ring_aut
import Mathlib.linear_algebra.tensor_product
import Mathlib.ring_theory.subring
import Mathlib.deprecated.subring
import Mathlib.algebra.opposites
import Mathlib.PostPort

universes u v l u_1 u_2 w u₁ v₁ u_3 u_4 

namespace Mathlib

/-!
# Algebra over Commutative Semiring

In this file we define `algebra`s over commutative (semi)rings, algebra homomorphisms `alg_hom`,
algebra equivalences `alg_equiv`. We also define usual operations on `alg_hom`s
(`id`, `comp`).

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

If `S` is an `R`-algebra and `A` is an `S`-algebra then `algebra.comap.algebra R S A` can be used
to provide `A` with a structure of an `R`-algebra. Other than that, `algebra.comap` is now
deprecated and replaced with `is_scalar_tower`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

-- We set this priority to 0 later in this file

/--
Given a commutative (semi)ring `R`, an `R`-algebra is a (possibly noncommutative)
(semi)ring `A` endowed with a morphism of rings `R →+* A` which lands in the
center of `A`.

For convenience, this typeclass extends `has_scalar R A` where the scalar action must
agree with left multiplication by the image of the structure morphism.

Given an `algebra R A` instance, the structure morphism `R →+* A` is denoted `algebra_map R A`.
-/
class algebra (R : Type u) (A : Type v) [comm_semiring R] [semiring A] 
extends has_scalar R A, R →+* A
where
  commutes' : ∀ (r : R) (x : A), ring_hom.to_fun _to_ring_hom r * x = x * ring_hom.to_fun _to_ring_hom r
  smul_def' : ∀ (r : R) (x : A), r • x = ring_hom.to_fun _to_ring_hom r * x

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebra_map (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : R →+* A :=
  algebra.to_ring_hom

/-- Creating an algebra from a morphism to the center of a semiring. -/
def ring_hom.to_algebra' {R : Type u_1} {S : Type u_2} [comm_semiring R] [semiring S] (i : R →+* S) (h : ∀ (c : R) (x : S), coe_fn i c * x = x * coe_fn i c) : algebra R S :=
  algebra.mk i h sorry

/-- Creating an algebra from a morphism to a commutative semiring. -/
def ring_hom.to_algebra {R : Type u_1} {S : Type u_2} [comm_semiring R] [comm_semiring S] (i : R →+* S) : algebra R S :=
  ring_hom.to_algebra' i sorry

theorem ring_hom.algebra_map_to_algebra {R : Type u_1} {S : Type u_2} [comm_semiring R] [comm_semiring S] (i : R →+* S) : algebra_map R S = i :=
  rfl

namespace algebra


/-- Let `R` be a commutative semiring, let `A` be a semiring with a `semimodule R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`. -/
def of_semimodule' {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [semimodule R A] (h₁ : ∀ (r : R) (x : A), r • 1 * x = r • x) (h₂ : ∀ (r : R) (x : A), x * r • 1 = r • x) : algebra R A :=
  mk (ring_hom.mk (fun (r : R) => r • 1) sorry sorry sorry sorry) sorry sorry

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `semimodule R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`. -/
def of_semimodule {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [semimodule R A] (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y)) (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : algebra R A :=
  of_semimodule' sorry sorry

theorem smul_def'' {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (r : R) (x : A) : r • x = coe_fn (algebra_map R A) r * x :=
  smul_def' r x

/--
To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
-- We'll later use this to show `algebra ℤ M` is a subsingleton.

theorem algebra_ext {R : Type u_1} [comm_semiring R] {A : Type u_2} [semiring A] (P : algebra R A) (Q : algebra R A) (w : ∀ (r : R), coe_fn (algebra_map R A) r = coe_fn (algebra_map R A) r) : P = Q := sorry

protected instance to_semimodule {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] : semimodule R A :=
  semimodule.mk sorry sorry

-- from now on, we don't want to use the following instance anymore

theorem smul_def {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (r : R) (x : A) : r • x = coe_fn (algebra_map R A) r * x :=
  smul_def' r x

theorem algebra_map_eq_smul_one {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (r : R) : coe_fn (algebra_map R A) r = r • 1 :=
  Eq.trans (Eq.symm (mul_one (coe_fn (algebra_map R A) r))) (Eq.symm (smul_def r 1))

theorem commutes {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (r : R) (x : A) : coe_fn (algebra_map R A) r * x = x * coe_fn (algebra_map R A) r :=
  commutes' r x

theorem left_comm {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (r : R) (x : A) (y : A) : x * (coe_fn (algebra_map R A) r * y) = coe_fn (algebra_map R A) r * (x * y) := sorry

@[simp] theorem mul_smul_comm {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (s : R) (x : A) (y : A) : x * s • y = s • (x * y) := sorry

@[simp] theorem smul_mul_assoc {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (r : R) (x : A) (y : A) : r • x * y = r • (x * y) := sorry

@[simp] theorem bit0_smul_one {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] {r : R} : bit0 r • 1 = r • bit0 1 := sorry

@[simp] theorem bit0_smul_bit0 {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] {r : R} {a : A} : bit0 r • bit0 a = r • bit0 (bit0 a) := sorry

@[simp] theorem bit0_smul_bit1 {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] {r : R} {a : A} : bit0 r • bit1 a = r • bit0 (bit1 a) := sorry

@[simp] theorem bit1_smul_one {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] {r : R} : bit1 r • 1 = r • bit0 1 + 1 := sorry

@[simp] theorem bit1_smul_bit0 {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] {r : R} {a : A} : bit1 r • bit0 a = r • bit0 (bit0 a) + bit0 a := sorry

@[simp] theorem bit1_smul_bit1 {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] {r : R} {a : A} : bit1 r • bit1 a = r • bit0 (bit1 a) + bit1 a := sorry

/--
The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linear_map (R : Type u) (A : Type w) [comm_semiring R] [semiring A] [algebra R A] : linear_map R R A :=
  linear_map.mk (ring_hom.to_fun (algebra_map R A)) sorry sorry

@[simp] theorem linear_map_apply (R : Type u) (A : Type w) [comm_semiring R] [semiring A] [algebra R A] (r : R) : coe_fn (algebra.linear_map R A) r = coe_fn (algebra_map R A) r :=
  rfl

protected instance id (R : Type u) [comm_semiring R] : algebra R R :=
  ring_hom.to_algebra (ring_hom.id R)

namespace id


@[simp] theorem map_eq_self {R : Type u} [comm_semiring R] (x : R) : coe_fn (algebra_map R R) x = x :=
  rfl

@[simp] theorem smul_eq_mul {R : Type u} [comm_semiring R] (x : R) (y : R) : x • y = x * y :=
  rfl

end id


protected instance prod.algebra (R : Type u) (A : Type w) (B : Type u_1) [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B] : algebra R (A × B) :=
  mk (ring_hom.mk (ring_hom.to_fun (ring_hom.prod (algebra_map R A) (algebra_map R B))) sorry sorry sorry sorry) sorry
    sorry

@[simp] theorem algebra_map_prod_apply {R : Type u} {A : Type w} {B : Type u_1} [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B] (r : R) : coe_fn (algebra_map R (A × B)) r = (coe_fn (algebra_map R A) r, coe_fn (algebra_map R B) r) :=
  rfl

/-- Algebra over a subsemiring. -/
protected instance of_subsemiring {R : Type u} {A : Type w} [comm_semiring R] [semiring A] [algebra R A] (S : subsemiring R) : algebra (↥S) A :=
  mk (ring_hom.mk (ring_hom.to_fun (ring_hom.comp (algebra_map R A) (subsemiring.subtype S))) sorry sorry sorry sorry)
    sorry sorry

/-- Algebra over a subring. -/
protected instance of_subring {R : Type u_1} {A : Type u_2} [comm_ring R] [ring A] [algebra R A] (S : subring R) : algebra (↥S) A :=
  mk (ring_hom.mk (ring_hom.to_fun (ring_hom.comp (algebra_map R A) (subring.subtype S))) sorry sorry sorry sorry) sorry
    sorry

theorem algebra_map_of_subring {R : Type u_1} [comm_ring R] (S : subring R) : algebra_map (↥S) R = subring.subtype S :=
  rfl

theorem coe_algebra_map_of_subring {R : Type u_1} [comm_ring R] (S : subring R) : ⇑(algebra_map (↥S) R) = subtype.val :=
  rfl

theorem algebra_map_of_subring_apply {R : Type u_1} [comm_ring R] (S : subring R) (x : ↥S) : coe_fn (algebra_map (↥S) R) x = ↑x :=
  rfl

/-- Algebra over a set that is closed under the ring operations. -/
def of_is_subring {R : Type u_1} {A : Type u_2} [comm_ring R] [ring A] [algebra R A] (S : set R) [is_subring S] : algebra (↥S) A :=
  algebra.of_subring (set.to_subring S)

theorem is_subring_coe_algebra_map_hom {R : Type u_1} [comm_ring R] (S : set R) [is_subring S] : algebra_map (↥S) R = is_subring.subtype S :=
  rfl

theorem is_subring_coe_algebra_map {R : Type u_1} [comm_ring R] (S : set R) [is_subring S] : ⇑(algebra_map (↥S) R) = subtype.val :=
  rfl

theorem is_subring_algebra_map_apply {R : Type u_1} [comm_ring R] (S : set R) [is_subring S] (x : ↥S) : coe_fn (algebra_map (↥S) R) x = ↑x :=
  rfl

theorem set_range_subset {R : Type u_1} [comm_ring R] {T₁ : set R} {T₂ : set R} [is_subring T₁] (hyp : T₁ ⊆ T₂) : set.range ⇑(algebra_map (↥T₁) R) ⊆ T₂ := sorry

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebra_map_submonoid {R : Type u} [comm_semiring R] (S : Type u_1) [semiring S] [algebra R S] (M : submonoid R) : submonoid S :=
  submonoid.map (↑(algebra_map R S)) M

theorem mem_algebra_map_submonoid_of_mem {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] [algebra R S] {M : submonoid R} (x : ↥M) : coe_fn (algebra_map R S) ↑x ∈ algebra_map_submonoid S M :=
  set.mem_image_of_mem (⇑(algebra_map R S)) (subtype.property x)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure. -/
def semiring_to_ring (R : Type u) {A : Type w} [comm_ring R] [semiring A] [algebra R A] : ring A :=
  ring.mk add_comm_group.add sorry add_comm_group.zero sorry sorry add_comm_group.neg add_comm_group.sub sorry sorry
    semiring.mul sorry semiring.one sorry sorry sorry sorry

theorem mul_sub_algebra_map_commutes {R : Type u} {A : Type w} [comm_ring R] [ring A] [algebra R A] (x : A) (r : R) : x * (x - coe_fn (algebra_map R A) r) = (x - coe_fn (algebra_map R A) r) * x := sorry

theorem mul_sub_algebra_map_pow_commutes {R : Type u} {A : Type w} [comm_ring R] [ring A] [algebra R A] (x : A) (r : R) (n : ℕ) : x * (x - coe_fn (algebra_map R A) r) ^ n = (x - coe_fn (algebra_map R A) r) ^ n * x := sorry

end algebra


namespace opposite


protected instance algebra {R : Type u_1} {A : Type u_2} [comm_semiring R] [semiring A] [algebra R A] : algebra R (Aᵒᵖ) :=
  algebra.mk (ring_hom.to_opposite (algebra_map R A) sorry) sorry sorry

@[simp] theorem algebra_map_apply {R : Type u_1} {A : Type u_2} [comm_semiring R] [semiring A] [algebra R A] (c : R) : coe_fn (algebra_map R (Aᵒᵖ)) c = op (coe_fn (algebra_map R A) c) :=
  rfl

end opposite


namespace module


protected instance endomorphism_algebra (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] : algebra R (linear_map R M M) :=
  algebra.mk (ring_hom.mk (fun (r : R) => r • linear_map.id) sorry sorry sorry sorry) sorry sorry

theorem algebra_map_End_eq_smul_id (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] (a : R) : coe_fn (algebra_map R (End R M)) a = a • linear_map.id :=
  rfl

@[simp] theorem algebra_map_End_apply (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [semimodule R M] (a : R) (m : M) : coe_fn (coe_fn (algebra_map R (End R M)) a) m = a • m :=
  rfl

@[simp] theorem ker_algebra_map_End (K : Type u) (V : Type v) [field K] [add_comm_group V] [vector_space K V] (a : K) (ha : a ≠ 0) : linear_map.ker (coe_fn (algebra_map K (End K V)) a) = ⊥ :=
  linear_map.ker_smul linear_map.id a ha

end module


protected instance matrix_algebra (n : Type u) (R : Type v) [DecidableEq n] [fintype n] [comm_semiring R] : algebra R (matrix n n R) :=
  algebra.mk (ring_hom.mk (ring_hom.to_fun (matrix.scalar n)) sorry sorry sorry sorry) sorry sorry

/-- Defining the homomorphism in the category R-Alg. -/
structure alg_hom (R : Type u) (A : Type v) (B : Type w) [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] 
extends A →+* B
where
  commutes' : ∀ (r : R), to_fun (coe_fn (algebra_map R A) r) = coe_fn (algebra_map R B) r

namespace alg_hom


protected instance has_coe_to_fun {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : has_coe_to_fun (alg_hom R A B) :=
  has_coe_to_fun.mk (fun (f : alg_hom R A B) => A → B) fun (f : alg_hom R A B) => to_fun f

protected instance coe_ring_hom {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : has_coe (alg_hom R A B) (A →+* B) :=
  has_coe.mk to_ring_hom

protected instance coe_monoid_hom {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : has_coe (alg_hom R A B) (A →* B) :=
  has_coe.mk fun (f : alg_hom R A B) => ↑↑f

protected instance coe_add_monoid_hom {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : has_coe (alg_hom R A B) (A →+ B) :=
  has_coe.mk fun (f : alg_hom R A B) => ↑↑f

@[simp] theorem coe_mk {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {f : A → B} (h₁ : f 1 = 1) (h₂ : ∀ (x y : A), f (x * y) = f x * f y) (h₃ : f 0 = 0) (h₄ : ∀ (x y : A), f (x + y) = f x + f y) (h₅ : ∀ (r : R), f (coe_fn (algebra_map R A) r) = coe_fn (algebra_map R B) r) : ⇑(mk f h₁ h₂ h₃ h₄ h₅) = f :=
  rfl

@[simp] theorem coe_to_ring_hom {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) : ⇑↑f = ⇑f :=
  rfl

-- as `simp` can already prove this lemma, it is not tagged with the `simp` attribute.

theorem coe_to_monoid_hom {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) : ⇑↑f = ⇑f :=
  rfl

-- as `simp` can already prove this lemma, it is not tagged with the `simp` attribute.

theorem coe_to_add_monoid_hom {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) : ⇑↑f = ⇑f :=
  rfl

theorem coe_fn_inj {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {φ₁ : alg_hom R A B} {φ₂ : alg_hom R A B} (H : ⇑φ₁ = ⇑φ₂) : φ₁ = φ₂ := sorry

theorem coe_ring_hom_injective {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : function.injective coe :=
  fun (φ₁ φ₂ : alg_hom R A B) (H : ↑φ₁ = ↑φ₂) => coe_fn_inj ((fun (this : ⇑↑φ₁ = ⇑↑φ₂) => this) (congr_arg coe_fn H))

theorem coe_monoid_hom_injective {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : function.injective coe :=
  function.injective.comp ring_hom.coe_monoid_hom_injective coe_ring_hom_injective

theorem coe_add_monoid_hom_injective {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] : function.injective coe :=
  function.injective.comp ring_hom.coe_add_monoid_hom_injective coe_ring_hom_injective

protected theorem congr_fun {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {φ₁ : alg_hom R A B} {φ₂ : alg_hom R A B} (H : φ₁ = φ₂) (x : A) : coe_fn φ₁ x = coe_fn φ₂ x :=
  H ▸ rfl

protected theorem congr_arg {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) {x : A} {y : A} (h : x = y) : coe_fn φ x = coe_fn φ y :=
  h ▸ rfl

theorem ext {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {φ₁ : alg_hom R A B} {φ₂ : alg_hom R A B} (H : ∀ (x : A), coe_fn φ₁ x = coe_fn φ₂ x) : φ₁ = φ₂ :=
  coe_fn_inj (funext H)

theorem ext_iff {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {φ₁ : alg_hom R A B} {φ₂ : alg_hom R A B} : φ₁ = φ₂ ↔ ∀ (x : A), coe_fn φ₁ x = coe_fn φ₂ x :=
  { mp := alg_hom.congr_fun, mpr := ext }

@[simp] theorem mk_coe {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {f : alg_hom R A B} (h₁ : coe_fn f 1 = 1) (h₂ : ∀ (x y : A), coe_fn f (x * y) = coe_fn f x * coe_fn f y) (h₃ : coe_fn f 0 = 0) (h₄ : ∀ (x y : A), coe_fn f (x + y) = coe_fn f x + coe_fn f y) (h₅ : ∀ (r : R), coe_fn f (coe_fn (algebra_map R A) r) = coe_fn (algebra_map R B) r) : mk (⇑f) h₁ h₂ h₃ h₄ h₅ = f :=
  ext fun (_x : A) => rfl

@[simp] theorem commutes {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (r : R) : coe_fn φ (coe_fn (algebra_map R A) r) = coe_fn (algebra_map R B) r :=
  commutes' φ r

theorem comp_algebra_map {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : ring_hom.comp (↑φ) (algebra_map R A) = algebra_map R B :=
  ring_hom.ext (commutes φ)

@[simp] theorem map_add {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (r : A) (s : A) : coe_fn φ (r + s) = coe_fn φ r + coe_fn φ s :=
  ring_hom.map_add (to_ring_hom φ) r s

@[simp] theorem map_zero {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : coe_fn φ 0 = 0 :=
  ring_hom.map_zero (to_ring_hom φ)

@[simp] theorem map_mul {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) (y : A) : coe_fn φ (x * y) = coe_fn φ x * coe_fn φ y :=
  ring_hom.map_mul (to_ring_hom φ) x y

@[simp] theorem map_one {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : coe_fn φ 1 = 1 :=
  ring_hom.map_one (to_ring_hom φ)

@[simp] theorem map_smul {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (r : R) (x : A) : coe_fn φ (r • x) = r • coe_fn φ x := sorry

@[simp] theorem map_pow {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) (n : ℕ) : coe_fn φ (x ^ n) = coe_fn φ x ^ n :=
  ring_hom.map_pow (to_ring_hom φ) x n

theorem map_sum {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) {ι : Type u_1} (f : ι → A) (s : finset ι) : coe_fn φ (finset.sum s fun (x : ι) => f x) = finset.sum s fun (x : ι) => coe_fn φ (f x) :=
  ring_hom.map_sum (to_ring_hom φ) f s

theorem map_finsupp_sum {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) {α : Type u_1} [HasZero α] {ι : Type u_2} (f : ι →₀ α) (g : ι → α → A) : coe_fn φ (finsupp.sum f g) = finsupp.sum f fun (i : ι) (a : α) => coe_fn φ (g i a) :=
  map_sum φ (fun (a : ι) => g a (coe_fn f a)) (finsupp.support f)

@[simp] theorem map_nat_cast {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (n : ℕ) : coe_fn φ ↑n = ↑n :=
  ring_hom.map_nat_cast (to_ring_hom φ) n

@[simp] theorem map_bit0 {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) : coe_fn φ (bit0 x) = bit0 (coe_fn φ x) :=
  ring_hom.map_bit0 (to_ring_hom φ) x

@[simp] theorem map_bit1 {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) : coe_fn φ (bit1 x) = bit1 (coe_fn φ x) :=
  ring_hom.map_bit1 (to_ring_hom φ) x

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (f : A →+* B) (h : ∀ (c : R) (x : A), coe_fn f (c • x) = c • coe_fn f x) : alg_hom R A B :=
  mk (⇑f) (ring_hom.map_one' f) (ring_hom.map_mul' f) (ring_hom.map_zero' f) (ring_hom.map_add' f) sorry

@[simp] theorem coe_mk' {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (f : A →+* B) (h : ∀ (c : R) (x : A), coe_fn f (c • x) = c • coe_fn f x) : ⇑(mk' f h) = ⇑f :=
  rfl

/-- Identity map as an `alg_hom`. -/
protected def id (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : alg_hom R A A :=
  mk (ring_hom.to_fun (ring_hom.id A)) sorry sorry sorry sorry sorry

@[simp] theorem id_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (p : A) : coe_fn (alg_hom.id R A) p = p :=
  rfl

/-- Composition of algebra homeomorphisms. -/
def comp {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} [comm_semiring R] [semiring A] [semiring B] [semiring C] [algebra R A] [algebra R B] [algebra R C] (φ₁ : alg_hom R B C) (φ₂ : alg_hom R A B) : alg_hom R A C :=
  mk (ring_hom.to_fun (ring_hom.comp (to_ring_hom φ₁) ↑φ₂)) sorry sorry sorry sorry sorry

@[simp] theorem comp_apply {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} [comm_semiring R] [semiring A] [semiring B] [semiring C] [algebra R A] [algebra R B] [algebra R C] (φ₁ : alg_hom R B C) (φ₂ : alg_hom R A B) (p : A) : coe_fn (comp φ₁ φ₂) p = coe_fn φ₁ (coe_fn φ₂ p) :=
  rfl

@[simp] theorem comp_id {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : comp φ (alg_hom.id R A) = φ :=
  ext fun (x : A) => rfl

@[simp] theorem id_comp {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : comp (alg_hom.id R B) φ = φ :=
  ext fun (x : A) => rfl

theorem comp_assoc {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁} [comm_semiring R] [semiring A] [semiring B] [semiring C] [semiring D] [algebra R A] [algebra R B] [algebra R C] [algebra R D] (φ₁ : alg_hom R C D) (φ₂ : alg_hom R B C) (φ₃ : alg_hom R A B) : comp (comp φ₁ φ₂) φ₃ = comp φ₁ (comp φ₂ φ₃) :=
  ext fun (x : A) => rfl

/-- R-Alg ⥤ R-Mod -/
def to_linear_map {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) : linear_map R A B :=
  linear_map.mk (⇑φ) (map_add φ) (map_smul φ)

@[simp] theorem to_linear_map_apply {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (p : A) : coe_fn (to_linear_map φ) p = coe_fn φ p :=
  rfl

theorem to_linear_map_inj {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] {φ₁ : alg_hom R A B} {φ₂ : alg_hom R A B} (H : to_linear_map φ₁ = to_linear_map φ₂) : φ₁ = φ₂ := sorry

@[simp] theorem comp_to_linear_map {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} [comm_semiring R] [semiring A] [semiring B] [semiring C] [algebra R A] [algebra R B] [algebra R C] (f : alg_hom R A B) (g : alg_hom R B C) : to_linear_map (comp g f) = linear_map.comp (to_linear_map g) (to_linear_map f) :=
  rfl

theorem map_prod {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [comm_semiring A] [comm_semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) {ι : Type u_1} (f : ι → A) (s : finset ι) : coe_fn φ (finset.prod s fun (x : ι) => f x) = finset.prod s fun (x : ι) => coe_fn φ (f x) :=
  ring_hom.map_prod (to_ring_hom φ) f s

theorem map_finsupp_prod {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [comm_semiring A] [comm_semiring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) {α : Type u_1} [HasZero α] {ι : Type u_2} (f : ι →₀ α) (g : ι → α → A) : coe_fn φ (finsupp.prod f g) = finsupp.prod f fun (i : ι) (a : α) => coe_fn φ (g i a) :=
  map_prod φ (fun (a : ι) => g a (coe_fn f a)) (finsupp.support f)

@[simp] theorem map_neg {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [ring A] [ring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) : coe_fn φ (-x) = -coe_fn φ x :=
  ring_hom.map_neg (to_ring_hom φ) x

@[simp] theorem map_sub {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [ring A] [ring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) (y : A) : coe_fn φ (x - y) = coe_fn φ x - coe_fn φ y :=
  ring_hom.map_sub (to_ring_hom φ) x y

@[simp] theorem map_int_cast {R : Type u} {A : Type v} {B : Type w} [comm_semiring R] [ring A] [ring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (n : ℤ) : coe_fn φ ↑n = ↑n :=
  ring_hom.map_int_cast (to_ring_hom φ) n

@[simp] theorem map_inv {R : Type u} {A : Type v} {B : Type w} [comm_ring R] [division_ring A] [division_ring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) : coe_fn φ (x⁻¹) = (coe_fn φ x⁻¹) :=
  ring_hom.map_inv (to_ring_hom φ) x

@[simp] theorem map_div {R : Type u} {A : Type v} {B : Type w} [comm_ring R] [division_ring A] [division_ring B] [algebra R A] [algebra R B] (φ : alg_hom R A B) (x : A) (y : A) : coe_fn φ (x / y) = coe_fn φ x / coe_fn φ y :=
  ring_hom.map_div (to_ring_hom φ) x y

theorem injective_iff {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_semiring R] [ring A] [semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) : function.injective ⇑f ↔ ∀ (x : A), coe_fn f x = 0 → x = 0 :=
  ring_hom.injective_iff ↑f

end alg_hom


/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure alg_equiv (R : Type u) (A : Type v) (B : Type w) [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] 
extends A ≃+ B, A ≃+* B, A ≃ B, A ≃* B
where
  commutes' : ∀ (r : R), to_fun (coe_fn (algebra_map R A) r) = coe_fn (algebra_map R B) r

namespace alg_equiv


protected instance has_coe_to_fun {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] : has_coe_to_fun (alg_equiv R A₁ A₂) :=
  has_coe_to_fun.mk (fun (x : alg_equiv R A₁ A₂) => A₁ → A₂) to_fun

theorem ext {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {f : alg_equiv R A₁ A₂} {g : alg_equiv R A₁ A₂} (h : ∀ (a : A₁), coe_fn f a = coe_fn g a) : f = g := sorry

protected theorem congr_arg {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {f : alg_equiv R A₁ A₂} {x : A₁} {x' : A₁} : x = x' → coe_fn f x = coe_fn f x' := sorry

protected theorem congr_fun {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {f : alg_equiv R A₁ A₂} {g : alg_equiv R A₁ A₂} (h : f = g) (x : A₁) : coe_fn f x = coe_fn g x :=
  h ▸ rfl

theorem ext_iff {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {f : alg_equiv R A₁ A₂} {g : alg_equiv R A₁ A₂} : f = g ↔ ∀ (x : A₁), coe_fn f x = coe_fn g x :=
  { mp := fun (h : f = g) (x : A₁) => h ▸ rfl, mpr := ext }

theorem coe_fun_injective {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] : function.injective fun (e : alg_equiv R A₁ A₂) => ⇑e :=
  id
    fun (f g : alg_equiv R A₁ A₂) (w : (fun (e : alg_equiv R A₁ A₂) => ⇑e) f = (fun (e : alg_equiv R A₁ A₂) => ⇑e) g) =>
      ext fun (a : A₁) => congr_fun w a

protected instance has_coe_to_ring_equiv {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] : has_coe (alg_equiv R A₁ A₂) (A₁ ≃+* A₂) :=
  has_coe.mk to_ring_equiv

@[simp] theorem mk_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {to_fun : A₁ → A₂} {inv_fun : A₂ → A₁} {left_inv : function.left_inverse inv_fun to_fun} {right_inv : function.right_inverse inv_fun to_fun} {map_mul : ∀ (x y : A₁), to_fun (x * y) = to_fun x * to_fun y} {map_add : ∀ (x y : A₁), to_fun (x + y) = to_fun x + to_fun y} {commutes : ∀ (r : R), to_fun (coe_fn (algebra_map R A₁) r) = coe_fn (algebra_map R A₂) r} {a : A₁} : coe_fn (mk to_fun inv_fun left_inv right_inv map_mul map_add commutes) a = to_fun a :=
  rfl

@[simp] theorem to_fun_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {e : alg_equiv R A₁ A₂} {a : A₁} : to_fun e a = coe_fn e a :=
  rfl

@[simp] theorem coe_ring_equiv {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : ⇑↑e = ⇑e :=
  rfl

theorem coe_ring_equiv_injective {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] : function.injective fun (e : alg_equiv R A₁ A₂) => ↑e :=
  id
    fun (f g : alg_equiv R A₁ A₂) (w : (fun (e : alg_equiv R A₁ A₂) => ↑e) f = (fun (e : alg_equiv R A₁ A₂) => ↑e) g) =>
      ext fun (a : A₁) => congr_fun (congr_arg (fun (e : A₁ ≃+* A₂) => ⇑e) w) a

@[simp] theorem map_add {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) (y : A₁) : coe_fn e (x + y) = coe_fn e x + coe_fn e y :=
  add_equiv.map_add (to_add_equiv e)

@[simp] theorem map_zero {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : coe_fn e 0 = 0 :=
  add_equiv.map_zero (to_add_equiv e)

@[simp] theorem map_mul {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) (y : A₁) : coe_fn e (x * y) = coe_fn e x * coe_fn e y :=
  mul_equiv.map_mul (to_mul_equiv e)

@[simp] theorem map_one {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : coe_fn e 1 = 1 :=
  mul_equiv.map_one (to_mul_equiv e)

@[simp] theorem commutes {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (r : R) : coe_fn e (coe_fn (algebra_map R A₁) r) = coe_fn (algebra_map R A₂) r :=
  commutes' e

theorem map_sum {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) {ι : Type u_1} (f : ι → A₁) (s : finset ι) : coe_fn e (finset.sum s fun (x : ι) => f x) = finset.sum s fun (x : ι) => coe_fn e (f x) :=
  add_equiv.map_sum (to_add_equiv e) f s

theorem map_finsupp_sum {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) {α : Type u_1} [HasZero α] {ι : Type u_2} (f : ι →₀ α) (g : ι → α → A₁) : coe_fn e (finsupp.sum f g) = finsupp.sum f fun (i : ι) (b : α) => coe_fn e (g i b) :=
  map_sum e (fun (a : ι) => g a (coe_fn f a)) (finsupp.support f)

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `has_coe_to_alg_hom` instance. -/
def to_alg_hom {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : alg_hom R A₁ A₂ :=
  alg_hom.mk (to_fun e) (map_one e) (map_mul' e) (map_zero e) (map_add' e) (commutes' e)

protected instance has_coe_to_alg_hom {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] : has_coe (alg_equiv R A₁ A₂) (alg_hom R A₁ A₂) :=
  has_coe.mk to_alg_hom

@[simp] theorem to_alg_hom_eq_coe {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : to_alg_hom e = ↑e :=
  rfl

@[simp] theorem coe_alg_hom {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : ⇑↑e = ⇑e :=
  rfl

@[simp] theorem map_pow {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) (n : ℕ) : coe_fn e (x ^ n) = coe_fn e x ^ n :=
  alg_hom.map_pow (to_alg_hom e)

theorem injective {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : function.injective ⇑e :=
  equiv.injective (to_equiv e)

theorem surjective {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : function.surjective ⇑e :=
  equiv.surjective (to_equiv e)

theorem bijective {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : function.bijective ⇑e :=
  equiv.bijective (to_equiv e)

protected instance has_one {R : Type u} {A₁ : Type v} [comm_semiring R] [semiring A₁] [algebra R A₁] : HasOne (alg_equiv R A₁ A₁) :=
  { one := mk (ring_equiv.to_fun 1) (ring_equiv.inv_fun 1) sorry sorry sorry sorry sorry }

protected instance inhabited {R : Type u} {A₁ : Type v} [comm_semiring R] [semiring A₁] [algebra R A₁] : Inhabited (alg_equiv R A₁ A₁) :=
  { default := 1 }

/-- Algebra equivalences are reflexive. -/
def refl {R : Type u} {A₁ : Type v} [comm_semiring R] [semiring A₁] [algebra R A₁] : alg_equiv R A₁ A₁ :=
  1

@[simp] theorem coe_refl {R : Type u} {A₁ : Type v} [comm_semiring R] [semiring A₁] [algebra R A₁] : ↑refl = alg_hom.id R A₁ :=
  alg_hom.ext fun (x : A₁) => rfl

/-- Algebra equivalences are symmetric. -/
def symm {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : alg_equiv R A₂ A₁ :=
  mk (ring_equiv.to_fun (ring_equiv.symm (to_ring_equiv e))) (ring_equiv.inv_fun (ring_equiv.symm (to_ring_equiv e)))
    sorry sorry sorry sorry sorry

/-- See Note [custom simps projection] -/
def simps.inv_fun {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : A₂ → A₁ :=
  ⇑(symm e)

@[simp] theorem inv_fun_eq_symm {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {e : alg_equiv R A₁ A₂} : inv_fun e = ⇑(symm e) :=
  rfl

@[simp] theorem symm_symm {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {e : alg_equiv R A₁ A₂} : symm (symm e) = e :=
  ext fun (a : A₁) => Eq.refl (coe_fn (symm (symm e)) a)

/-- Algebra equivalences are transitive. -/
def trans {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁} [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃] [algebra R A₁] [algebra R A₂] [algebra R A₃] (e₁ : alg_equiv R A₁ A₂) (e₂ : alg_equiv R A₂ A₃) : alg_equiv R A₁ A₃ :=
  mk (ring_equiv.to_fun (ring_equiv.trans (to_ring_equiv e₁) (to_ring_equiv e₂)))
    (ring_equiv.inv_fun (ring_equiv.trans (to_ring_equiv e₁) (to_ring_equiv e₂))) sorry sorry sorry sorry sorry

@[simp] theorem apply_symm_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₂) : coe_fn e (coe_fn (symm e) x) = x :=
  equiv.apply_symm_apply (to_equiv e)

@[simp] theorem symm_apply_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) : coe_fn (symm e) (coe_fn e x) = x :=
  equiv.symm_apply_apply (to_equiv e)

@[simp] theorem trans_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁} [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃] [algebra R A₁] [algebra R A₂] [algebra R A₃] (e₁ : alg_equiv R A₁ A₂) (e₂ : alg_equiv R A₂ A₃) (x : A₁) : coe_fn (trans e₁ e₂) x = coe_fn e₂ (coe_fn e₁ x) :=
  rfl

@[simp] theorem comp_symm {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : alg_hom.comp ↑e ↑(symm e) = alg_hom.id R A₂ := sorry

@[simp] theorem symm_comp {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : alg_hom.comp ↑(symm e) ↑e = alg_hom.id R A₁ := sorry

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrow_congr {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {A₁' : Type u_1} {A₂' : Type u_2} [semiring A₁'] [semiring A₂'] [algebra R A₁'] [algebra R A₂'] (e₁ : alg_equiv R A₁ A₁') (e₂ : alg_equiv R A₂ A₂') : alg_hom R A₁ A₂ ≃ alg_hom R A₁' A₂' :=
  equiv.mk (fun (f : alg_hom R A₁ A₂) => alg_hom.comp (alg_hom.comp (to_alg_hom e₂) f) (to_alg_hom (symm e₁)))
    (fun (f : alg_hom R A₁' A₂') => alg_hom.comp (alg_hom.comp (to_alg_hom (symm e₂)) f) (to_alg_hom e₁)) sorry sorry

theorem arrow_congr_comp {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁} [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃] [algebra R A₁] [algebra R A₂] [algebra R A₃] {A₁' : Type u_1} {A₂' : Type u_2} {A₃' : Type u_3} [semiring A₁'] [semiring A₂'] [semiring A₃'] [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : alg_equiv R A₁ A₁') (e₂ : alg_equiv R A₂ A₂') (e₃ : alg_equiv R A₃ A₃') (f : alg_hom R A₁ A₂) (g : alg_hom R A₂ A₃) : coe_fn (arrow_congr e₁ e₃) (alg_hom.comp g f) =
  alg_hom.comp (coe_fn (arrow_congr e₂ e₃) g) (coe_fn (arrow_congr e₁ e₂) f) := sorry

@[simp] theorem arrow_congr_refl {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] : arrow_congr refl refl = equiv.refl (alg_hom R A₁ A₂) :=
  equiv.ext
    fun (x : alg_hom R A₁ A₂) => alg_hom.ext fun (x_1 : A₁) => Eq.refl (coe_fn (coe_fn (arrow_congr refl refl) x) x_1)

@[simp] theorem arrow_congr_trans {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁} [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃] [algebra R A₁] [algebra R A₂] [algebra R A₃] {A₁' : Type u_1} {A₂' : Type u_2} {A₃' : Type u_3} [semiring A₁'] [semiring A₂'] [semiring A₃'] [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : alg_equiv R A₁ A₂) (e₁' : alg_equiv R A₁' A₂') (e₂ : alg_equiv R A₂ A₃) (e₂' : alg_equiv R A₂' A₃') : arrow_congr (trans e₁ e₂) (trans e₁' e₂') = equiv.trans (arrow_congr e₁ e₁') (arrow_congr e₂ e₂') :=
  equiv.ext
    fun (x : alg_hom R A₁ A₁') =>
      alg_hom.ext fun (x_1 : A₃) => Eq.refl (coe_fn (coe_fn (arrow_congr (trans e₁ e₂) (trans e₁' e₂')) x) x_1)

@[simp] theorem arrow_congr_symm {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {A₁' : Type u_1} {A₂' : Type u_2} [semiring A₁'] [semiring A₂'] [algebra R A₁'] [algebra R A₂'] (e₁ : alg_equiv R A₁ A₁') (e₂ : alg_equiv R A₂ A₂') : equiv.symm (arrow_congr e₁ e₂) = arrow_congr (symm e₁) (symm e₂) :=
  equiv.ext
    fun (x : alg_hom R A₁' A₂') =>
      alg_hom.ext fun (x_1 : A₁) => Eq.refl (coe_fn (coe_fn (equiv.symm (arrow_congr e₁ e₂)) x) x_1)

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_alg_hom {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (f : alg_hom R A₁ A₂) (g : alg_hom R A₂ A₁) (h₁ : alg_hom.comp f g = alg_hom.id R A₂) (h₂ : alg_hom.comp g f = alg_hom.id R A₁) : alg_equiv R A₁ A₂ :=
  mk (alg_hom.to_fun f) ⇑g sorry sorry (alg_hom.map_mul' f) (alg_hom.map_add' f) (alg_hom.commutes' f)

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
def of_bijective {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (f : alg_hom R A₁ A₂) (hf : function.bijective ⇑f) : alg_equiv R A₁ A₂ :=
  mk (ring_equiv.to_fun (ring_equiv.of_bijective (↑f) hf)) (ring_equiv.inv_fun (ring_equiv.of_bijective (↑f) hf)) sorry
    sorry sorry sorry (alg_hom.commutes' f)

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
def to_linear_equiv {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : linear_equiv R A₁ A₂ :=
  linear_equiv.mk (to_fun e) sorry sorry (to_fun (symm e)) (left_inv e) (right_inv e)

@[simp] theorem to_linear_equiv_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) : coe_fn (to_linear_equiv e) x = coe_fn e x :=
  rfl

theorem to_linear_equiv_inj {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {e₁ : alg_equiv R A₁ A₂} {e₂ : alg_equiv R A₁ A₂} (H : to_linear_equiv e₁ = to_linear_equiv e₂) : e₁ = e₂ := sorry

/-- Interpret an algebra equivalence as a linear map. -/
def to_linear_map {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : linear_map R A₁ A₂ :=
  alg_hom.to_linear_map (to_alg_hom e)

@[simp] theorem to_alg_hom_to_linear_map {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : alg_hom.to_linear_map ↑e = to_linear_map e :=
  rfl

@[simp] theorem to_linear_equiv_to_linear_map {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) : linear_equiv.to_linear_map (to_linear_equiv e) = to_linear_map e :=
  rfl

@[simp] theorem to_linear_map_apply {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) : coe_fn (to_linear_map e) x = coe_fn e x :=
  rfl

theorem to_linear_map_inj {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [semiring A₁] [semiring A₂] [algebra R A₁] [algebra R A₂] {e₁ : alg_equiv R A₁ A₂} {e₂ : alg_equiv R A₁ A₂} (H : to_linear_map e₁ = to_linear_map e₂) : e₁ = e₂ := sorry

@[simp] theorem trans_to_linear_map {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁} [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃] [algebra R A₁] [algebra R A₂] [algebra R A₃] (f : alg_equiv R A₁ A₂) (g : alg_equiv R A₂ A₃) : to_linear_map (trans f g) = linear_map.comp (to_linear_map g) (to_linear_map f) :=
  rfl

protected instance aut {R : Type u} {A₁ : Type v} [comm_semiring R] [semiring A₁] [algebra R A₁] : group (alg_equiv R A₁ A₁) :=
  group.mk (fun (ϕ ψ : alg_equiv R A₁ A₁) => trans ψ ϕ) sorry 1 sorry sorry symm
    (div_inv_monoid.div._default (fun (ϕ ψ : alg_equiv R A₁ A₁) => trans ψ ϕ) sorry 1 sorry sorry symm) sorry

theorem map_prod {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [comm_semiring A₁] [comm_semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) {ι : Type u_1} (f : ι → A₁) (s : finset ι) : coe_fn e (finset.prod s fun (x : ι) => f x) = finset.prod s fun (x : ι) => coe_fn e (f x) :=
  alg_hom.map_prod (to_alg_hom e) f s

theorem map_finsupp_prod {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_semiring R] [comm_semiring A₁] [comm_semiring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) {α : Type u_1} [HasZero α] {ι : Type u_2} (f : ι →₀ α) (g : ι → α → A₁) : coe_fn e (finsupp.prod f g) = finsupp.prod f fun (i : ι) (a : α) => coe_fn e (g i a) :=
  alg_hom.map_finsupp_prod (to_alg_hom e) f g

@[simp] theorem map_neg {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) : coe_fn e (-x) = -coe_fn e x :=
  alg_hom.map_neg (to_alg_hom e) x

@[simp] theorem map_sub {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) (y : A₁) : coe_fn e (x - y) = coe_fn e x - coe_fn e y :=
  alg_hom.map_sub (to_alg_hom e) x y

@[simp] theorem map_inv {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [division_ring A₁] [division_ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) : coe_fn e (x⁻¹) = (coe_fn e x⁻¹) :=
  alg_hom.map_inv (to_alg_hom e) x

@[simp] theorem map_div {R : Type u} {A₁ : Type v} {A₂ : Type w} [comm_ring R] [division_ring A₁] [division_ring A₂] [algebra R A₁] [algebra R A₂] (e : alg_equiv R A₁ A₂) (x : A₁) (y : A₁) : coe_fn e (x / y) = coe_fn e x / coe_fn e y :=
  alg_hom.map_div (to_alg_hom e) x y

end alg_equiv


namespace matrix


/-! ### `matrix` section

Specialize `matrix.one_map` and `matrix.zero_map` to `alg_hom` and `alg_equiv`.
TODO: there should be a way to avoid restating these for each `foo_hom`.
-/

/-- A version of `matrix.one_map` where `f` is an `alg_hom`. -/
@[simp] theorem alg_hom_map_one {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} {n : Type u_4} [fintype n] [comm_semiring R] [semiring A₁] [algebra R A₁] [semiring A₂] [algebra R A₂] [DecidableEq n] (f : alg_hom R A₁ A₂) : map 1 ⇑f = 1 :=
  one_map (alg_hom.map_zero f) (alg_hom.map_one f)

/-- A version of `matrix.one_map` where `f` is an `alg_equiv`. -/
@[simp] theorem alg_equiv_map_one {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} {n : Type u_4} [fintype n] [comm_semiring R] [semiring A₁] [algebra R A₁] [semiring A₂] [algebra R A₂] [DecidableEq n] (f : alg_equiv R A₁ A₂) : map 1 ⇑f = 1 :=
  one_map (alg_equiv.map_zero f) (alg_equiv.map_one f)

/-- A version of `matrix.zero_map` where `f` is an `alg_hom`. -/
@[simp] theorem alg_hom_map_zero {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} {n : Type u_4} [fintype n] [comm_semiring R] [semiring A₁] [algebra R A₁] [semiring A₂] [algebra R A₂] (f : alg_hom R A₁ A₂) : map 0 ⇑f = 0 :=
  map_zero (alg_hom.map_zero f)

/-- A version of `matrix.zero_map` where `f` is an `alg_equiv`. -/
@[simp] theorem alg_equiv_map_zero {R : Type u_1} {A₁ : Type u_2} {A₂ : Type u_3} {n : Type u_4} [fintype n] [comm_semiring R] [semiring A₁] [algebra R A₁] [semiring A₂] [algebra R A₂] (f : alg_equiv R A₁ A₂) : map 0 ⇑f = 0 :=
  map_zero (alg_equiv.map_zero f)

end matrix


namespace algebra


/-- `comap R S A` is a type alias for `A`, and has an R-algebra structure defined on it
  when `algebra R S` and `algebra S A`. If `S` is an `R`-algebra and `A` is an `S`-algebra then
  `algebra.comap.algebra R S A` can be used to provide `A` with a structure of an `R`-algebra.
  Other than that, `algebra.comap` is now deprecated and replaced with `is_scalar_tower`. -/
/- This is done to avoid a type class search with meta-variables `algebra R ?m_1` and
    `algebra ?m_1 A -/

/- The `nolint` attribute is added because it has unused arguments `R` and `S`, but these are
  necessary for synthesizing the appropriate type classes -/

def comap (R : Type u) (S : Type v) (A : Type w) :=
  A

protected instance comap.inhabited (R : Type u) (S : Type v) (A : Type w) [h : Inhabited A] : Inhabited (comap R S A) :=
  h

protected instance comap.semiring (R : Type u) (S : Type v) (A : Type w) [h : semiring A] : semiring (comap R S A) :=
  h

protected instance comap.ring (R : Type u) (S : Type v) (A : Type w) [h : ring A] : ring (comap R S A) :=
  h

protected instance comap.comm_semiring (R : Type u) (S : Type v) (A : Type w) [h : comm_semiring A] : comm_semiring (comap R S A) :=
  h

protected instance comap.comm_ring (R : Type u) (S : Type v) (A : Type w) [h : comm_ring A] : comm_ring (comap R S A) :=
  h

protected instance comap.algebra' (R : Type u) (S : Type v) (A : Type w) [comm_semiring S] [semiring A] [h : algebra S A] : algebra S (comap R S A) :=
  h

/-- Identity homomorphism `A →ₐ[S] comap R S A`. -/
def comap.to_comap (R : Type u) (S : Type v) (A : Type w) [comm_semiring S] [semiring A] [algebra S A] : alg_hom S A (comap R S A) :=
  alg_hom.id S A

/-- Identity homomorphism `comap R S A →ₐ[S] A`. -/
def comap.of_comap (R : Type u) (S : Type v) (A : Type w) [comm_semiring S] [semiring A] [algebra S A] : alg_hom S (comap R S A) A :=
  alg_hom.id S A

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
protected instance comap.algebra (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] : algebra R (comap R S A) :=
  mk (ring_hom.mk (ring_hom.to_fun (ring_hom.comp (algebra_map S A) (algebra_map R S))) sorry sorry sorry sorry) sorry
    sorry

/-- Embedding of `S` into `comap R S A`. -/
def to_comap (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] : alg_hom R S (comap R S A) :=
  alg_hom.mk (ring_hom.to_fun (algebra_map S A)) sorry sorry sorry sorry sorry

theorem to_comap_apply (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] (x : S) : coe_fn (to_comap R S A) x = coe_fn (algebra_map S A) x :=
  rfl

end algebra


namespace alg_hom


/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def comap {R : Type u} {S : Type v} {A : Type w} {B : Type u₁} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] (φ : alg_hom S A B) : alg_hom R (algebra.comap R S A) (algebra.comap R S B) :=
  mk (to_fun φ) (map_one' φ) (map_mul' φ) (map_zero' φ) (map_add' φ) sorry

end alg_hom


namespace ring_hom


/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def to_nat_alg_hom {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] [algebra ℕ R] [algebra ℕ S] (f : R →+* S) : alg_hom ℕ R S :=
  alg_hom.mk (⇑f) (map_one' f) (map_mul' f) (map_zero' f) (map_add' f) sorry

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def to_int_alg_hom {R : Type u_1} {S : Type u_2} [ring R] [ring S] [algebra ℤ R] [algebra ℤ S] (f : R →+* S) : alg_hom ℤ R S :=
  alg_hom.mk (to_fun f) sorry sorry sorry sorry sorry

@[simp] theorem map_rat_algebra_map {R : Type u_1} {S : Type u_2} [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] (f : R →+* S) (r : ℚ) : coe_fn f (coe_fn (algebra_map ℚ R) r) = coe_fn (algebra_map ℚ S) r :=
  iff.mp ext_iff (subsingleton.elim (comp f (algebra_map ℚ R)) (algebra_map ℚ S)) r

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. -/
def to_rat_alg_hom {R : Type u_1} {S : Type u_2} [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] (f : R →+* S) : alg_hom ℚ R S :=
  alg_hom.mk (to_fun f) sorry sorry sorry sorry (map_rat_algebra_map f)

end ring_hom


namespace rat


protected instance algebra_rat {α : Type u_1} [division_ring α] [char_zero α] : algebra ℚ α :=
  ring_hom.to_algebra' (cast_hom α) sorry

end rat


namespace algebra


/-- `algebra_map` as an `alg_hom`. -/
def of_id (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : alg_hom R R A :=
  alg_hom.mk (ring_hom.to_fun (algebra_map R A)) sorry sorry sorry sorry sorry

theorem of_id_apply {R : Type u} (A : Type v) [comm_semiring R] [semiring A] [algebra R A] (r : R) : coe_fn (of_id R A) r = coe_fn (algebra_map R A) r :=
  rfl

/-- The multiplication in an algebra is a bilinear map. -/
def lmul (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : alg_hom R A (module.End R A) :=
  alg_hom.mk
    (linear_map.to_fun
      ((fun (this : linear_map R A (linear_map R A A)) => this) (linear_map.mk₂ R Mul.mul sorry sorry sorry sorry)))
    sorry sorry sorry sorry sorry

/-- The multiplication on the left in an algebra is a linear map. -/
def lmul_left (R : Type u) {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (r : A) : linear_map R A A :=
  coe_fn (lmul R A) r

/-- The multiplication on the right in an algebra is a linear map. -/
def lmul_right (R : Type u) {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (r : A) : linear_map R A A :=
  coe_fn (linear_map.flip (alg_hom.to_linear_map (lmul R A))) r

/-- Simultaneous multiplication on the left and right is a linear map. -/
def lmul_left_right (R : Type u) {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (vw : A × A) : linear_map R A A :=
  linear_map.comp (lmul_right R (prod.snd vw)) (lmul_left R (prod.fst vw))

/-- The multiplication map on an algebra, as an `R`-linear map from `A ⊗[R] A` to `A`. -/
def lmul' (R : Type u) {A : Type v} [comm_semiring R] [semiring A] [algebra R A] : linear_map R (tensor_product R A A) A :=
  tensor_product.lift (alg_hom.to_linear_map (lmul R A))

@[simp] theorem lmul_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (p : A) (q : A) : coe_fn (coe_fn (lmul R A) p) q = p * q :=
  rfl

@[simp] theorem lmul_left_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (p : A) (q : A) : coe_fn (lmul_left R p) q = p * q :=
  rfl

@[simp] theorem lmul_right_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (p : A) (q : A) : coe_fn (lmul_right R p) q = q * p :=
  rfl

@[simp] theorem lmul_left_right_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (vw : A × A) (p : A) : coe_fn (lmul_left_right R vw) p = prod.fst vw * p * prod.snd vw :=
  rfl

@[simp] theorem lmul_left_one {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] : lmul_left R 1 = linear_map.id := sorry

@[simp] theorem lmul_left_mul {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (a : A) (b : A) : lmul_left R (a * b) = linear_map.comp (lmul_left R a) (lmul_left R b) := sorry

@[simp] theorem lmul_right_one {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] : lmul_right R 1 = linear_map.id := sorry

@[simp] theorem lmul_right_mul {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] (a : A) (b : A) : lmul_right R (a * b) = linear_map.comp (lmul_right R b) (lmul_right R a) := sorry

@[simp] theorem lmul'_apply {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A] {x : A} {y : A} : coe_fn (lmul' R) (tensor_product.tmul R x y) = x * y := sorry

protected instance linear_map.semimodule' (R : Type u) [comm_semiring R] (M : Type v) [add_comm_monoid M] [semimodule R M] (S : Type w) [comm_semiring S] [algebra R S] : semimodule S (linear_map R M S) :=
  semimodule.mk sorry sorry

end algebra


/-- Semiring ⥤ ℕ-Alg -/
protected instance algebra_nat (R : Type u_1) [semiring R] : algebra ℕ R :=
  algebra.mk (nat.cast_ring_hom R) nat.cast_commute sorry

theorem span_nat_eq_add_group_closure (R : Type u_1) [semiring R] (s : set R) : submodule.to_add_submonoid (submodule.span ℕ s) = add_submonoid.closure s := sorry

@[simp] theorem span_nat_eq (R : Type u_1) [semiring R] (s : add_submonoid R) : submodule.to_add_submonoid (submodule.span ℕ ↑s) = s := sorry

/-- Ring ⥤ ℤ-Alg -/
protected instance algebra_int (R : Type u_1) [ring R] : algebra ℤ R :=
  algebra.mk (int.cast_ring_hom R) int.cast_commute sorry

protected instance int_algebra_subsingleton {S : Type u_2} [ring S] : subsingleton (algebra ℤ S) :=
  subsingleton.intro
    fun (P Q : algebra ℤ S) =>
      algebra.algebra_ext P Q
        fun (r : ℤ) =>
          eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : S) (e_1 : a = a_1) (ᾰ ᾰ_1 : S) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                  (coe_fn (algebra_map ℤ S) r) (↑r) (ring_hom.eq_int_cast (algebra_map ℤ S) r)
                  (coe_fn (algebra_map ℤ S) r) (↑r) (ring_hom.eq_int_cast (algebra_map ℤ S) r))
                (propext (eq_self_iff_true ↑r))))
            trivial

protected instance nat_algebra_subsingleton {S : Type u_2} [semiring S] : subsingleton (algebra ℕ S) :=
  subsingleton.intro
    fun (P Q : algebra ℕ S) =>
      algebra.algebra_ext P Q
        fun (r : ℕ) =>
          eq.mpr
            (id
              (Eq.trans
                ((fun (a a_1 : S) (e_1 : a = a_1) (ᾰ ᾰ_1 : S) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2)
                  (coe_fn (algebra_map ℕ S) r) (↑r) (ring_hom.eq_nat_cast (algebra_map ℕ S) r)
                  (coe_fn (algebra_map ℕ S) r) (↑r) (ring_hom.eq_nat_cast (algebra_map ℕ S) r))
                (propext (eq_self_iff_true ↑r))))
            trivial

theorem span_int_eq_add_group_closure {R : Type u_1} [ring R] (s : set R) : submodule.to_add_subgroup (submodule.span ℤ s) = add_subgroup.closure s := sorry

@[simp] theorem span_int_eq {R : Type u_1} [ring R] (s : add_subgroup R) : submodule.to_add_subgroup (submodule.span ℤ ↑s) = s :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (submodule.to_add_subgroup (submodule.span ℤ ↑s) = s)) (span_int_eq_add_group_closure ↑s)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (add_subgroup.closure ↑s = s)) (add_subgroup.closure_eq s))) (Eq.refl s))

/-!
The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

We couldn't set this up back in `algebra.pi_instances` because this file imports it.
-/

namespace pi


protected instance algebra (I : Type u) (f : I → Type v) (α : Type u_1) {r : comm_semiring α} [s : (i : I) → semiring (f i)] [(i : I) → algebra α (f i)] : algebra α ((i : I) → f i) :=
  algebra.mk (ring_hom.mk (ring_hom.to_fun (pi.ring_hom fun (i : I) => algebra_map α (f i))) sorry sorry sorry sorry)
    sorry sorry

@[simp] theorem algebra_map_apply (I : Type u) (f : I → Type v) (α : Type u_1) {r : comm_semiring α} [s : (i : I) → semiring (f i)] [(i : I) → algebra α (f i)] (a : α) (i : I) : coe_fn (algebra_map α ((i : I) → f i)) a i = coe_fn (algebra_map α (f i)) a :=
  rfl

-- One could also build a `Π i, R i`-algebra structure on `Π i, A i`,

-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.

end pi


theorem algebra_compatible_smul {R : Type u_1} [comm_semiring R] (A : Type u_2) [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (r : R) (m : M) : r • m = coe_fn (algebra_map R A) r • m := sorry

@[simp] theorem algebra_map_smul {R : Type u_1} [comm_semiring R] (A : Type u_2) [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (r : R) (m : M) : coe_fn (algebra_map R A) r • m = r • m :=
  Eq.symm (algebra_compatible_smul A r m)

protected instance is_scalar_tower.to_smul_comm_class {R : Type u_1} [comm_semiring R] {A : Type u_2} [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : smul_comm_class R A M :=
  smul_comm_class.mk
    fun (r : R) (a : A) (m : M) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (r • a • m = a • r • m)) (algebra_compatible_smul A r (a • m))))
        (eq.mpr
          (id
            (Eq._oldrec (Eq.refl (coe_fn (algebra_map R A) r • a • m = a • r • m))
              (smul_smul (coe_fn (algebra_map R A) r) a m)))
          (eq.mpr (id (Eq._oldrec (Eq.refl ((coe_fn (algebra_map R A) r * a) • m = a • r • m)) (algebra.commutes r a)))
            (eq.mpr
              (id
                (Eq._oldrec (Eq.refl ((a * coe_fn (algebra_map R A) r) • m = a • r • m))
                  (mul_smul a (coe_fn (algebra_map R A) r) m)))
              (eq.mpr
                (id
                  (Eq._oldrec (Eq.refl (a • coe_fn (algebra_map R A) r • m = a • r • m))
                    (Eq.symm (algebra_compatible_smul A r m))))
                (Eq.refl (a • r • m))))))

protected instance is_scalar_tower.to_smul_comm_class' {R : Type u_1} [comm_semiring R] {A : Type u_2} [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] : smul_comm_class A R M :=
  smul_comm_class.symm R A M

theorem smul_algebra_smul_comm {R : Type u_1} [comm_semiring R] {A : Type u_2} [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm a r m

namespace linear_map


protected instance coe_is_scalar_tower {R : Type u_1} [comm_semiring R] {A : Type u_2} [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] {N : Type u_4} [add_comm_monoid N] [semimodule A N] [semimodule R N] [is_scalar_tower R A N] : has_coe (linear_map A M N) (linear_map R M N) :=
  has_coe.mk (restrict_scalars R)

@[simp] theorem coe_restrict_scalars_eq_coe (R : Type u_1) [comm_semiring R] {A : Type u_2} [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] {N : Type u_4} [add_comm_monoid N] [semimodule A N] [semimodule R N] [is_scalar_tower R A N] (f : linear_map A M N) : ⇑(restrict_scalars R f) = ⇑f :=
  rfl

@[simp] theorem coe_coe_is_scalar_tower (R : Type u_1) [comm_semiring R] {A : Type u_2} [semiring A] [algebra R A] {M : Type u_3} [add_comm_monoid M] [semimodule A M] [semimodule R M] [is_scalar_tower R A M] {N : Type u_4} [add_comm_monoid N] [semimodule A N] [semimodule R N] [is_scalar_tower R A N] (f : linear_map A M N) : ⇑↑f = ⇑f :=
  rfl

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a semimodule over `R`. -/
def lto_fun (R : Type u) (M : Type v) (A : Type w) [comm_semiring R] [add_comm_monoid M] [semimodule R M] [comm_ring A] [algebra R A] : linear_map A (linear_map R M A) (M → A) :=
  mk to_fun sorry sorry

end linear_map


/- In this section, we describe restriction of scalars: if `S` is an algebra over `R`, then
`S`-modules are also `R`-modules. -/

/--
Warning: use this type synonym judiciously!
The preferred way of working with an `A`-module `M` as `R`-module (where `A` is an `R`-algebra),
is by `[module R M] [module A M] [is_scalar_tower R A M]`.

When `M` is a module over a ring `A`, and `A` is an algebra over `R`, then `M` inherits a
module structure over `R`, provided as a type synonym `module.restrict_scalars R A M := M`.
-/
def restrict_scalars (R : Type u_1) (A : Type u_2) (M : Type u_3) :=
  M

protected instance restrict_scalars.inhabited (R : Type u_1) (A : Type u_2) (M : Type u_3) [I : Inhabited M] : Inhabited (restrict_scalars R A M) :=
  I

protected instance restrict_scalars.add_comm_monoid (R : Type u_1) (A : Type u_2) (M : Type u_3) [I : add_comm_monoid M] : add_comm_monoid (restrict_scalars R A M) :=
  I

protected instance restrict_scalars.add_comm_group (R : Type u_1) (A : Type u_2) (M : Type u_3) [I : add_comm_group M] : add_comm_group (restrict_scalars R A M) :=
  I

protected instance restrict_scalars.module_orig (R : Type u_1) (A : Type u_2) (M : Type u_3) [semiring A] [add_comm_monoid M] [I : semimodule A M] : semimodule A (restrict_scalars R A M) :=
  I

/--
When `M` is a module over a ring `A`, and `A` is an algebra over `R`, then `M` inherits a
module structure over `R`.

The preferred way of setting this up is `[module R M] [module A M] [is_scalar_tower R A M]`.
-/
protected instance restrict_scalars.semimodule (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] : semimodule R (restrict_scalars R A M) :=
  semimodule.mk sorry sorry

theorem restrict_scalars_smul_def (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] (c : R) (x : restrict_scalars R A M) : c • x = coe_fn (algebra_map R A) c • x :=
  rfl

protected instance restrict_scalars.is_scalar_tower (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] : is_scalar_tower R A (restrict_scalars R A M) :=
  is_scalar_tower.mk
    fun (r : R) (A_1 : A) (M_1 : restrict_scalars R A M) =>
      eq.mpr (id (Eq._oldrec (Eq.refl ((r • A_1) • M_1 = r • A_1 • M_1)) (algebra.smul_def r A_1)))
        (eq.mpr
          (id
            (Eq._oldrec (Eq.refl ((coe_fn (algebra_map R A) r * A_1) • M_1 = r • A_1 • M_1))
              (mul_smul (coe_fn (algebra_map R A) r) A_1 M_1)))
          (Eq.refl (coe_fn (algebra_map R A) r • A_1 • M_1)))

protected instance submodule.restricted_module (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] (V : submodule A M) : semimodule R ↥V :=
  restrict_scalars.semimodule R A ↥V

protected instance submodule.restricted_module_is_scalar_tower (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule A M] (V : submodule A M) : is_scalar_tower R A ↥V :=
  restrict_scalars.is_scalar_tower R A ↥V

namespace submodule


/--
`V.restrict_scalars R` is the `R`-submodule of the `R`-module given by restriction of scalars,
corresponding to `V`, an `S`-submodule of the original `S`-module.
-/
def restrict_scalars (R : Type u_1) {A : Type u_2} {M : Type u_3} [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] (V : submodule A M) : submodule R M :=
  mk (carrier V) (zero_mem V) sorry sorry

@[simp] theorem restrict_scalars_mem (R : Type u_1) {A : Type u_2} {M : Type u_3} [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] (V : submodule A M) (m : M) : m ∈ restrict_scalars R V ↔ m ∈ V :=
  iff.refl (m ∈ restrict_scalars R V)

theorem restrict_scalars_injective (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] : function.injective (restrict_scalars R) :=
  fun (V₁ V₂ : submodule A M) (h : restrict_scalars R V₁ = restrict_scalars R V₂) =>
    ext (eq.mpr (Eq.refl (∀ (x : M), x ∈ V₁ ↔ x ∈ V₂)) (iff.mp set.ext_iff (iff.mp ext'_iff h)))

@[simp] theorem restrict_scalars_inj (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] {V₁ : submodule A M} {V₂ : submodule A M} : restrict_scalars R V₁ = restrict_scalars R V₂ ↔ V₁ = V₂ :=
  { mp := fun (h : restrict_scalars R V₁ = restrict_scalars R V₂) => restrict_scalars_injective R A M h,
    mpr := congr_arg fun {V₁ : submodule A M} => restrict_scalars R V₁ }

@[simp] theorem restrict_scalars_bot (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] : restrict_scalars R ⊥ = ⊥ :=
  rfl

@[simp] theorem restrict_scalars_top (R : Type u_1) (A : Type u_2) (M : Type u_3) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] : restrict_scalars R ⊤ = ⊤ :=
  rfl

end submodule


@[simp] theorem linear_map.ker_restrict_scalars (R : Type u_1) {A : Type u_2} {M : Type u_3} {N : Type u_4} [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] [add_comm_monoid N] [semimodule R N] [semimodule A N] [is_scalar_tower R A N] (f : linear_map A M N) : linear_map.ker (linear_map.restrict_scalars R f) = submodule.restrict_scalars R (linear_map.ker f) :=
  rfl

namespace linear_map


/-! When `V` is an `R`-module and `W` is an `S`-module, where `S` is an algebra over `R`, then
the collection of `R`-linear maps from `V` to `W` admits an `S`-module structure, given by
multiplication in the target. -/

protected instance is_scalar_tower_extend_scalars (R : Type u_1) [comm_semiring R] (S : Type u_2) [semiring S] [algebra R S] (V : Type u_3) [add_comm_monoid V] [semimodule R V] (W : Type u_4) [add_comm_monoid W] [semimodule R W] [semimodule S W] [is_scalar_tower R S W] : is_scalar_tower R S (linear_map R V W) := sorry

/-- When `f` is a linear map taking values in `S`, then `λb, f b • x` is a linear map. -/
def smul_algebra_right {R : Type u_1} [comm_semiring R] {S : Type u_2} [semiring S] [algebra R S] {V : Type u_3} [add_comm_monoid V] [semimodule R V] {W : Type u_4} [add_comm_monoid W] [semimodule R W] [semimodule S W] [is_scalar_tower R S W] (f : linear_map R V S) (x : W) : linear_map R V W :=
  mk (fun (b : V) => coe_fn f b • x) sorry sorry

@[simp] theorem smul_algebra_right_apply {R : Type u_1} [comm_semiring R] {S : Type u_2} [semiring S] [algebra R S] {V : Type u_3} [add_comm_monoid V] [semimodule R V] {W : Type u_4} [add_comm_monoid W] [semimodule R W] [semimodule S W] [is_scalar_tower R S W] (f : linear_map R V S) (x : W) (c : V) : coe_fn (smul_algebra_right f x) c = coe_fn f c • x :=
  rfl

