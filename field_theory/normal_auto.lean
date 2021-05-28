/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.field_theory.minpoly
import Mathlib.field_theory.splitting_field
import Mathlib.field_theory.tower
import Mathlib.ring_theory.power_basis
import PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (`normal.of_is_splitting_field` and
`normal.exists_is_splitting_field`).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/

--TODO(Commelin): refactor normal to extend `is_algebraic`??

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
def normal (F : Type u_1) (K : Type u_2) [field F] [field K] [algebra F K]  :=
  ∀ (x : K), is_integral F x ∧ polynomial.splits (algebra_map F K) (minpoly F x)

protected instance normal_self (F : Type u_1) [field F] : normal F F :=
  fun (x : F) =>
    { left := is_integral_algebra_map,
      right :=
        eq.mpr (id (Eq._oldrec (Eq.refl (polynomial.splits (algebra_map F F) (minpoly F x))) (minpoly.eq_X_sub_C' x)))
          (polynomial.splits_X_sub_C (algebra_map F F)) }

theorem normal.is_integral (F : Type u_1) {K : Type u_2} [field F] [field K] [algebra F K] [h : normal F K] (x : K) : is_integral F x :=
  and.left (h x)

theorem normal.splits (F : Type u_1) {K : Type u_2} [field F] [field K] [algebra F K] [h : normal F K] (x : K) : polynomial.splits (algebra_map F K) (minpoly F x) :=
  and.right (h x)

theorem normal.exists_is_splitting_field (F : Type u_1) (K : Type u_2) [field F] [field K] [algebra F K] [normal F K] [finite_dimensional F K] : ∃ (p : polynomial F), polynomial.is_splitting_field F K p := sorry

theorem normal.tower_top_of_normal (F : Type u_1) (K : Type u_2) [field F] [field K] [algebra F K] (E : Type u_3) [field E] [algebra F E] [algebra K E] [is_scalar_tower F K E] [h : normal F E] : normal K E := sorry

theorem normal.of_alg_equiv {F : Type u_1} [field F] {E : Type u_3} [field E] [algebra F E] {E' : Type u_4} [field E'] [algebra F E'] [h : normal F E] (f : alg_equiv F E E') : normal F E' := sorry

theorem alg_equiv.transfer_normal {F : Type u_1} [field F] {E : Type u_3} [field E] [algebra F E] {E' : Type u_4} [field E'] [algebra F E'] (f : alg_equiv F E E') : normal F E ↔ normal F E' :=
  { mp := fun (h : normal F E) => normal.of_alg_equiv f,
    mpr := fun (h : normal F E') => normal.of_alg_equiv (alg_equiv.symm f) }

theorem normal.of_is_splitting_field {F : Type u_1} [field F] {E : Type u_3} [field E] [algebra F E] {p : polynomial F} [hFEp : polynomial.is_splitting_field F E p] : normal F E := sorry

/-- Restrict algebra homomorphism to image of normal subfield -/
def alg_hom.restrict_normal_aux {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (ϕ : alg_hom F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [h : normal F E] : alg_hom F ↥(alg_hom.range (is_scalar_tower.to_alg_hom F E K)) ↥(alg_hom.range (is_scalar_tower.to_alg_hom F E K)) :=
  alg_hom.mk (fun (x : ↥(alg_hom.range (is_scalar_tower.to_alg_hom F E K))) => { val := coe_fn ϕ ↑x, property := sorry })
    sorry sorry sorry sorry sorry

/-- Restrict algebra homomorphism to normal subfield -/
def alg_hom.restrict_normal {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (ϕ : alg_hom F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [normal F E] : alg_hom F E E :=
  alg_hom.comp
    (alg_hom.comp
      (alg_equiv.to_alg_hom (alg_equiv.symm (alg_hom.alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K))))
      (alg_hom.restrict_normal_aux ϕ E))
    (alg_equiv.to_alg_hom (alg_hom.alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K)))

theorem alg_hom.restrict_normal_commutes {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (ϕ : alg_hom F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [normal F E] (x : E) : coe_fn (algebra_map E K) (coe_fn (alg_hom.restrict_normal ϕ E) x) = coe_fn ϕ (coe_fn (algebra_map E K) x) := sorry

theorem alg_hom.restrict_normal_comp {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (ϕ : alg_hom F K K) (ψ : alg_hom F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [normal F E] : alg_hom.comp (alg_hom.restrict_normal ϕ E) (alg_hom.restrict_normal ψ E) = alg_hom.restrict_normal (alg_hom.comp ϕ ψ) E := sorry

/-- Restrict algebra isomorphism to a normal subfield -/
def alg_equiv.restrict_normal {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (χ : alg_equiv F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [h : normal F E] : alg_equiv F E E :=
  alg_equiv.of_alg_hom (alg_hom.restrict_normal (alg_equiv.to_alg_hom χ) E)
    (alg_hom.restrict_normal (alg_equiv.to_alg_hom (alg_equiv.symm χ)) E) sorry sorry

theorem alg_equiv.restrict_normal_commutes {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (χ : alg_equiv F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [normal F E] (x : E) : coe_fn (algebra_map E K) (coe_fn (alg_equiv.restrict_normal χ E) x) = coe_fn χ (coe_fn (algebra_map E K) x) :=
  alg_hom.restrict_normal_commutes (alg_equiv.to_alg_hom χ) E x

theorem alg_equiv.restrict_normal_trans {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (χ : alg_equiv F K K) (ω : alg_equiv F K K) (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [normal F E] : alg_equiv.restrict_normal (alg_equiv.trans χ ω) E =
  alg_equiv.trans (alg_equiv.restrict_normal χ E) (alg_equiv.restrict_normal ω E) := sorry

/-- Restriction to an normal subfield as a group homomorphism -/
def alg_equiv.restrict_normal_hom {F : Type u_1} {K : Type u_2} [field F] [field K] [algebra F K] (E : Type u_3) [field E] [algebra F E] [algebra E K] [is_scalar_tower F E K] [normal F E] : alg_equiv F K K →* alg_equiv F E E :=
  monoid_hom.mk' (fun (χ : alg_equiv F K K) => alg_equiv.restrict_normal χ E) sorry

