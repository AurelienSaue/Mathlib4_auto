/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.algebra.subalgebra
import PostPort

universes u v₁ w v u₁ u_1 u_2 u_3 

namespace Mathlib

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `to_alg_hom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/

namespace algebra


/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `R`-module `M`. -/
def lsmul (R : Type u) {A : Type w} (M : Type v₁) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] : alg_hom R A (module.End R M) :=
  alg_hom.mk
    (linear_map.to_fun
      ((fun (this : linear_map R A (linear_map R M M)) => this)
        (linear_map.mk₂ R has_scalar.smul sorry sorry sorry sorry)))
    sorry sorry sorry sorry sorry

@[simp] theorem lsmul_coe (R : Type u) {A : Type w} (M : Type v₁) [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] (a : A) : ⇑(coe_fn (lsmul R M) a) = has_scalar.smul a :=
  rfl

end algebra


namespace is_scalar_tower


theorem algebra_map_smul {R : Type u} (A : Type w) {M : Type v₁} [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M] [semimodule R M] [semimodule A M] [is_scalar_tower R A M] (r : R) (x : M) : coe_fn (algebra_map R A) r • x = r • x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn (algebra_map R A) r • x = r • x)) (algebra.algebra_map_eq_smul_one r)))
    (eq.mpr (id (Eq._oldrec (Eq.refl ((r • 1) • x = r • x)) (smul_assoc r 1 x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (r • 1 • x = r • x)) (one_smul A x))) (Eq.refl (r • x))))

theorem of_algebra_map_eq {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] (h : ∀ (x : R), coe_fn (algebra_map R A) x = coe_fn (algebra_map S A) (coe_fn (algebra_map R S) x)) : is_scalar_tower R S A := sorry

/-- See note [partially-applied ext lemmas]. -/
theorem of_algebra_map_eq' {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] (h : algebra_map R A = ring_hom.comp (algebra_map S A) (algebra_map R S)) : is_scalar_tower R S A :=
  of_algebra_map_eq (iff.mp ring_hom.ext_iff h)

protected instance subalgebra (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] (S₀ : subalgebra R S) : is_scalar_tower (↥S₀) S A :=
  of_algebra_map_eq fun (x : ↥S₀) => rfl

theorem algebra_map_eq (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : algebra_map R A = ring_hom.comp (algebra_map S A) (algebra_map R S) := sorry

theorem algebra_map_apply (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (x : R) : coe_fn (algebra_map R A) x = coe_fn (algebra_map S A) (coe_fn (algebra_map R S) x) := sorry

protected instance subalgebra' (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (S₀ : subalgebra R S) : is_scalar_tower R (↥S₀) A :=
  of_algebra_map_eq fun (_x : R) => algebra_map_apply R S A _x

theorem algebra.ext {S : Type u} {A : Type v} [comm_semiring S] [semiring A] (h1 : algebra S A) (h2 : algebra S A) (h : ∀ {r : S} {x : A}, r • x = r • x) : h1 = h2 := sorry

theorem algebra_comap_eq (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : algebra.comap.algebra R S A = _inst_8 := sorry

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def to_alg_hom (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : alg_hom R S A :=
  alg_hom.mk (ring_hom.to_fun (algebra_map S A)) sorry sorry sorry sorry sorry

theorem to_alg_hom_apply (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (y : S) : coe_fn (to_alg_hom R S A) y = coe_fn (algebra_map S A) y :=
  rfl

@[simp] theorem coe_to_alg_hom (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : ↑(to_alg_hom R S A) = algebra_map S A :=
  ring_hom.ext fun (_x : S) => rfl

@[simp] theorem coe_to_alg_hom' (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : ⇑(to_alg_hom R S A) = ⇑(algebra_map S A) :=
  rfl

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrict_base (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B] [is_scalar_tower R S A] [is_scalar_tower R S B] (f : alg_hom S A B) : alg_hom R A B :=
  alg_hom.mk (ring_hom.to_fun ↑f) sorry sorry sorry sorry sorry

theorem restrict_base_apply (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B] [is_scalar_tower R S A] [is_scalar_tower R S B] (f : alg_hom S A B) (x : A) : coe_fn (restrict_base R f) x = coe_fn f x :=
  rfl

@[simp] theorem coe_restrict_base (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B] [is_scalar_tower R S A] [is_scalar_tower R S B] (f : alg_hom S A B) : ↑(restrict_base R f) = ↑f :=
  rfl

@[simp] theorem coe_restrict_base' (R : Type u) {S : Type v} {A : Type w} {B : Type u₁} [comm_semiring R] [comm_semiring S] [semiring A] [semiring B] [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B] [is_scalar_tower R S A] [is_scalar_tower R S B] (f : alg_hom S A B) : ⇑(restrict_base R f) = ⇑f :=
  rfl

protected instance right {S : Type v} {A : Type w} [comm_semiring S] [semiring A] [algebra S A] : is_scalar_tower S A A :=
  mk
    fun (x : S) (y z : A) =>
      eq.mpr (id (Eq._oldrec (Eq.refl ((x • y) • z = x • y • z)) smul_eq_mul))
        (eq.mpr (id (Eq._oldrec (Eq.refl (x • y * z = x • y • z)) smul_eq_mul))
          (eq.mpr (id (Eq._oldrec (Eq.refl (x • y * z = x • (y * z))) (algebra.smul_mul_assoc x y z)))
            (Eq.refl (x • (y * z)))))

protected instance comap {R : Type u_1} {S : Type u_2} {A : Type u_3} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] : is_scalar_tower R S (algebra.comap R S A) :=
  of_algebra_map_eq fun (x : R) => rfl

-- conflicts with is_scalar_tower.subalgebra

protected instance subsemiring {S : Type v} {A : Type w} [comm_semiring S] [semiring A] [algebra S A] (U : subsemiring S) : is_scalar_tower (↥U) S A :=
  of_algebra_map_eq fun (x : ↥U) => rfl

-- conflicts with is_scalar_tower.subalgebra

protected instance subring {S : Type u_1} {A : Type u_2} [comm_ring S] [ring A] [algebra S A] (U : set S) [is_subring U] : is_scalar_tower (↥U) S A :=
  of_algebra_map_eq fun (x : ↥U) => rfl

protected instance of_ring_hom {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_semiring R] [comm_semiring A] [comm_semiring B] [algebra R A] [algebra R B] (f : alg_hom R A B) : is_scalar_tower R A B :=
  let _inst : algebra A B := ring_hom.to_algebra ↑f;
  of_algebra_map_eq fun (x : R) => Eq.symm (alg_hom.commutes f x)

protected instance rat (R : Type u) (S : Type v) [field R] [division_ring S] [algebra R S] [char_zero R] [char_zero S] : is_scalar_tower ℚ R S :=
  of_algebra_map_eq fun (x : ℚ) => Eq.symm (ring_hom.map_rat_cast (algebra_map R S) x)

end is_scalar_tower


namespace subalgebra


/-- If A/S/R is a tower of algebras then the `res`triction of a S-subalgebra of A is
an R-subalgebra of A. -/
def res (R : Type u) {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (U : subalgebra S A) : subalgebra R A :=
  mk (carrier U) (one_mem' U) (mul_mem' U) (zero_mem' U) (add_mem' U) sorry

@[simp] theorem res_top (R : Type u) {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] : res R ⊤ = ⊤ :=
  iff.mpr algebra.eq_top_iff fun (_x : A) => (fun (this : _x ∈ ⊤) => this) algebra.mem_top

@[simp] theorem mem_res (R : Type u) {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] {U : subalgebra S A} {x : A} : x ∈ res R U ↔ x ∈ U :=
  iff.rfl

theorem res_inj (R : Type u) {S : Type v} {A : Type w} [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] {U : subalgebra S A} {V : subalgebra S A} (H : res R U = res R V) : U = V := sorry

/-- Produces a map from `subalgebra.under`. -/
def of_under {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_semiring R] [comm_semiring A] [semiring B] [algebra R A] [algebra R B] (S : subalgebra R A) (U : subalgebra (↥S) A) [algebra (↥S) B] [is_scalar_tower R (↥S) B] (f : alg_hom (↥S) (↥U) B) : alg_hom R (↥(under S U)) B :=
  alg_hom.mk (alg_hom.to_fun f) sorry sorry sorry sorry sorry

end subalgebra


namespace is_scalar_tower


theorem range_under_adjoin (R : Type u) (S : Type v) (A : Type w) [comm_semiring R] [comm_semiring S] [comm_semiring A] [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A] (t : set A) : subalgebra.under (alg_hom.range (to_alg_hom R S A)) (algebra.adjoin (↥(alg_hom.range (to_alg_hom R S A))) t) =
  subalgebra.res R (algebra.adjoin S t) := sorry

end is_scalar_tower


namespace submodule


theorem smul_mem_span_smul_of_mem {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [semiring S] [add_comm_monoid A] [algebra R S] [semimodule S A] [semimodule R A] [is_scalar_tower R S A] {s : set S} {t : set A} {k : S} (hks : k ∈ span R s) {x : A} (hx : x ∈ t) : k • x ∈ span R (s • t) := sorry

theorem smul_mem_span_smul {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [semiring S] [add_comm_monoid A] [algebra R S] [semimodule S A] [semimodule R A] [is_scalar_tower R S A] {s : set S} (hs : span R s = ⊤) {t : set A} {k : S} {x : A} (hx : x ∈ span R t) : k • x ∈ span R (s • t) := sorry

theorem smul_mem_span_smul' {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [semiring S] [add_comm_monoid A] [algebra R S] [semimodule S A] [semimodule R A] [is_scalar_tower R S A] {s : set S} (hs : span R s = ⊤) {t : set A} {k : S} {x : A} (hx : x ∈ span R (s • t)) : k • x ∈ span R (s • t) := sorry

theorem span_smul {R : Type u} {S : Type v} {A : Type w} [comm_semiring R] [semiring S] [add_comm_monoid A] [algebra R S] [semimodule S A] [semimodule R A] [is_scalar_tower R S A] {s : set S} (hs : span R s = ⊤) (t : set A) : span R (s • t) = restrict_scalars R (span S t) := sorry

