/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.field_theory.normal
import Mathlib.field_theory.primitive_element
import Mathlib.field_theory.fixed
import Mathlib.ring_theory.power_basis
import PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `is_galois F E` where `E` is an extension of `F`
- `fixed_field H` where `H : subgroup (E ≃ₐ[F] E)`
- `fixing_subgroup K` where `K : intermediate_field F E`
- `galois_correspondence` where `E/F` is finite dimensional and Galois

## Main results

- `fixing_subgroup_of_fixed_field` : If `E/F` is finite dimensional (but not necessarily Galois)
  then `fixing_subgroup (fixed_field H) = H`
- `fixed_field_of_fixing_subgroup`: If `E/F` is finite dimensional and Galois
  then `fixed_field (fixing_subgroup K) = K`
Together, these two result prove the Galois correspondence

- `is_galois.tfae` : Equivalent characterizations of a Galois extension of finite degree
-/

/-- A field extension E/F is galois if it is both separable and normal -/
def is_galois (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E]  :=
  is_separable F E ∧ normal F E

namespace is_galois


protected instance self (F : Type u_1) [field F] : is_galois F F :=
  { left := Mathlib.is_separable_self F, right := Mathlib.normal_self F }

protected instance to_is_separable (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [h : is_galois F E] : is_separable F E :=
  and.left h

protected instance to_normal (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [h : is_galois F E] : normal F E :=
  and.right h

theorem integral (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] [is_galois F E] (x : E) : is_integral F x :=
  normal.is_integral F x

theorem separable (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] [h : is_galois F E] (x : E) : polynomial.separable (minpoly F x) :=
  and.right (and.left h x)

-- TODO(Commelin, Browning): rename this to `splits`

theorem normal (F : Type u_1) [field F] {E : Type u_2} [field E] [algebra F E] [is_galois F E] (x : E) : polynomial.splits (algebra_map F E) (minpoly F x) :=
  normal.splits F x

protected instance of_fixed_field (E : Type u_2) [field E] (G : Type u_1) [group G] [fintype G] [mul_semiring_action G E] : is_galois (↥(mul_action.fixed_points G E)) E :=
  { left := fixed_points.separable G E, right := fixed_points.normal G E }

theorem intermediate_field.adjoin_simple.card_aut_eq_findim (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [finite_dimensional F E] {α : E} (hα : is_integral F α) (h_sep : polynomial.separable (minpoly F α)) (h_splits : polynomial.splits (algebra_map F ↥(intermediate_field.adjoin F (intermediate_field.insert.insert ∅ α))) (minpoly F α)) : fintype.card
    (alg_equiv F ↥(intermediate_field.adjoin F (intermediate_field.insert.insert ∅ α))
      ↥(intermediate_field.adjoin F (intermediate_field.insert.insert ∅ α))) =
  finite_dimensional.findim F ↥(intermediate_field.adjoin F (intermediate_field.insert.insert ∅ α)) := sorry

theorem card_aut_eq_findim (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [finite_dimensional F E] [h : is_galois F E] : fintype.card (alg_equiv F E E) = finite_dimensional.findim F E := sorry

end is_galois


theorem is_galois.tower_top_of_is_galois (F : Type u_1) (K : Type u_2) (E : Type u_3) [field F] [field K] [field E] [algebra F K] [algebra F E] [algebra K E] [is_scalar_tower F K E] [is_galois F E] : is_galois K E :=
  { left := is_separable_tower_top_of_is_separable F K E, right := normal.tower_top_of_normal F K E }

protected instance is_galois.tower_top_intermediate_field {F : Type u_1} {E : Type u_3} [field F] [field E] [algebra F E] (K : intermediate_field F E) [h : is_galois F E] : is_galois (↥K) E :=
  is_galois.tower_top_of_is_galois F (↥K) E

theorem is_galois_iff_is_galois_bot {F : Type u_1} {E : Type u_3} [field F] [field E] [algebra F E] : is_galois (↥⊥) E ↔ is_galois F E :=
  { mp := fun (h : is_galois (↥⊥) E) => is_galois.tower_top_of_is_galois (↥⊥) F E,
    mpr := fun (h : is_galois F E) => is_galois.tower_top_intermediate_field ⊥ }

theorem is_galois.of_alg_equiv {F : Type u_1} {E : Type u_3} [field F] [field E] {E' : Type u_4} [field E'] [algebra F E'] [algebra F E] [h : is_galois F E] (f : alg_equiv F E E') : is_galois F E' :=
  { left := is_separable.of_alg_hom F E ↑(alg_equiv.symm f), right := normal.of_alg_equiv f }

theorem alg_equiv.transfer_galois {F : Type u_1} {E : Type u_3} [field F] [field E] {E' : Type u_4} [field E'] [algebra F E'] [algebra F E] (f : alg_equiv F E E') : is_galois F E ↔ is_galois F E' :=
  { mp := fun (h : is_galois F E) => is_galois.of_alg_equiv f,
    mpr := fun (h : is_galois F E') => is_galois.of_alg_equiv (alg_equiv.symm f) }

theorem is_galois_iff_is_galois_top {F : Type u_1} {E : Type u_3} [field F] [field E] [algebra F E] : is_galois F ↥⊤ ↔ is_galois F E :=
  alg_equiv.transfer_galois intermediate_field.top_equiv

protected instance is_galois_bot {F : Type u_1} {E : Type u_3} [field F] [field E] [algebra F E] : is_galois F ↥⊥ :=
  iff.mpr (alg_equiv.transfer_galois intermediate_field.bot_equiv) (is_galois.self F)

namespace intermediate_field


protected instance subgroup_action {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (H : subgroup (alg_equiv F E E)) : faithful_mul_semiring_action (↥H) E :=
  faithful_mul_semiring_action.mk sorry

/-- The intermediate_field fixed by a subgroup -/
def fixed_field {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (H : subgroup (alg_equiv F E E)) : intermediate_field F E :=
  mk (mul_action.fixed_points (↥H) E) sorry sorry sorry sorry sorry sorry sorry

theorem findim_fixed_field_eq_card {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (H : subgroup (alg_equiv F E E)) [finite_dimensional F E] : finite_dimensional.findim (↥(fixed_field H)) E = fintype.card ↥H :=
  fixed_points.findim_eq_card (↥H) E

/-- The subgroup fixing an intermediate_field -/
def fixing_subgroup {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (K : intermediate_field F E) : subgroup (alg_equiv F E E) :=
  subgroup.mk (fun (ϕ : alg_equiv F E E) => ∀ (x : ↥K), coe_fn ϕ ↑x = ↑x) sorry sorry sorry

theorem le_iff_le {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (H : subgroup (alg_equiv F E E)) (K : intermediate_field F E) : K ≤ fixed_field H ↔ H ≤ fixing_subgroup K := sorry

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixing_subgroup_equiv {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (K : intermediate_field F E) : ↥(fixing_subgroup K) ≃* alg_equiv (↥K) E E :=
  mul_equiv.mk
    (fun (ϕ : ↥(fixing_subgroup K)) => alg_equiv.of_bijective (alg_hom.mk ⇑ϕ sorry sorry sorry sorry sorry) sorry)
    (fun (ϕ : alg_equiv (↥K) E E) =>
      { val := alg_equiv.of_bijective (alg_hom.mk ⇑ϕ sorry sorry sorry sorry sorry) sorry, property := sorry })
    sorry sorry sorry

theorem fixing_subgroup_fixed_field {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (H : subgroup (alg_equiv F E E)) [finite_dimensional F E] : fixing_subgroup (fixed_field H) = H := sorry

protected instance fixed_field.algebra {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (K : intermediate_field F E) : algebra ↥K ↥(fixed_field (fixing_subgroup K)) :=
  algebra.mk (ring_hom.mk (fun (x : ↥K) => { val := ↑x, property := sorry }) sorry sorry sorry sorry) sorry sorry

protected instance fixed_field.is_scalar_tower {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (K : intermediate_field F E) : is_scalar_tower (↥K) (↥(fixed_field (fixing_subgroup K))) E :=
  is_scalar_tower.mk fun (_x : ↥K) (_x_1 : ↥(fixed_field (fixing_subgroup K))) (_x_2 : E) => mul_assoc (↑_x) (↑_x_1) _x_2

end intermediate_field


namespace is_galois


theorem fixed_field_fixing_subgroup {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (K : intermediate_field F E) [finite_dimensional F E] [h : is_galois F E] : intermediate_field.fixed_field (intermediate_field.fixing_subgroup K) = K := sorry

theorem card_fixing_subgroup_eq_findim {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] (K : intermediate_field F E) [finite_dimensional F E] [is_galois F E] : fintype.card ↥(intermediate_field.fixing_subgroup K) = finite_dimensional.findim (↥K) E := sorry

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediate_field_equiv_subgroup {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] [finite_dimensional F E] [is_galois F E] : intermediate_field F E ≃o order_dual (subgroup (alg_equiv F E E)) :=
  rel_iso.mk (equiv.mk intermediate_field.fixing_subgroup intermediate_field.fixed_field sorry sorry) sorry

/-- The Galois correspondence as a galois_insertion -/
def galois_insertion_intermediate_field_subgroup {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] [finite_dimensional F E] : galois_insertion (⇑order_dual.to_dual ∘ intermediate_field.fixing_subgroup)
  (intermediate_field.fixed_field ∘ ⇑order_dual.to_dual) :=
  galois_insertion.mk
    (fun (K : intermediate_field F E)
      (_x :
      function.comp intermediate_field.fixed_field (⇑order_dual.to_dual)
          (function.comp (⇑order_dual.to_dual) intermediate_field.fixing_subgroup K) ≤
        K) =>
      intermediate_field.fixing_subgroup K)
    sorry sorry sorry

/-- The Galois correspondence as a galois_coinsertion -/
def galois_coinsertion_intermediate_field_subgroup {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] [finite_dimensional F E] [is_galois F E] : galois_coinsertion (⇑order_dual.to_dual ∘ intermediate_field.fixing_subgroup)
  (intermediate_field.fixed_field ∘ ⇑order_dual.to_dual) :=
  galois_coinsertion.mk
    (fun (H : order_dual (subgroup (alg_equiv F E E)))
      (_x :
      H ≤
        function.comp (⇑order_dual.to_dual) intermediate_field.fixing_subgroup
          (function.comp intermediate_field.fixed_field (⇑order_dual.to_dual) H)) =>
      intermediate_field.fixed_field H)
    sorry sorry sorry

end is_galois


namespace is_galois


theorem is_separable_splitting_field (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [finite_dimensional F E] [h : is_galois F E] : ∃ (p : polynomial F), polynomial.separable p ∧ polynomial.is_splitting_field F E p := sorry

theorem of_fixed_field_eq_bot (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [finite_dimensional F E] (h : intermediate_field.fixed_field ⊤ = ⊥) : is_galois F E :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_galois F E)) (Eq.symm (propext is_galois_iff_is_galois_bot))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (is_galois (↥⊥) E)) (Eq.symm h))) (is_galois.of_fixed_field E ↥⊤))

theorem of_card_aut_eq_findim (F : Type u_1) [field F] (E : Type u_2) [field E] [algebra F E] [finite_dimensional F E] (h : fintype.card (alg_equiv F E E) = finite_dimensional.findim F E) : is_galois F E := sorry

theorem of_separable_splitting_field_aux {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] {p : polynomial F} [hFE : finite_dimensional F E] [sp : polynomial.is_splitting_field F E p] (hp : polynomial.separable p) (K : intermediate_field F E) {x : E} (hx : x ∈ polynomial.roots (polynomial.map (algebra_map F E) p)) : fintype.card (alg_hom F (↥↑(intermediate_field.adjoin (↥K) (intermediate_field.insert.insert ∅ x))) E) =
  fintype.card (alg_hom F (↥K) E) *
    finite_dimensional.findim ↥K ↥(intermediate_field.adjoin (↥K) (intermediate_field.insert.insert ∅ x)) := sorry

theorem of_separable_splitting_field {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] {p : polynomial F} [sp : polynomial.is_splitting_field F E p] (hp : polynomial.separable p) : is_galois F E := sorry

/--Equivalent characterizations of a Galois extension of finite degree-/
theorem tfae {F : Type u_1} [field F] {E : Type u_2} [field E] [algebra F E] [finite_dimensional F E] : tfae
  [is_galois F E, intermediate_field.fixed_field ⊤ = ⊥, fintype.card (alg_equiv F E E) = finite_dimensional.findim F E,
    ∃ (p : polynomial F), polynomial.separable p ∧ polynomial.is_splitting_field F E p] := sorry

