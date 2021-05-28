/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.algebra.polynomial.group_ring_action
import Mathlib.deprecated.subfield
import Mathlib.field_theory.normal
import Mathlib.field_theory.separable
import Mathlib.field_theory.tower
import Mathlib.linear_algebra.matrix
import Mathlib.ring_theory.polynomial.default
import PostPort

universes u v w 

namespace Mathlib

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `fixed_points G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition (TODO) if `G` acts faithfully on `F`
then `findim (fixed_points G F) F = fintype.card G`.

## Main Definitions

- `fixed_points G F`, the subfield consisting of elements of `F` fixed_points by every element of `G`, where
`G` is a group that acts on `F`.

-/

protected instance fixed_by.is_subfield (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G) : is_subfield (mul_action.fixed_by G F g) :=
  is_subfield.mk fun (x : F) (hx : x ∈ mul_action.fixed_by G F g) => Eq.trans (smul_inv F g x) (congr_arg has_inv.inv hx)

namespace fixed_points


protected instance mul_action.fixed_points.is_subfield (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] : is_subfield (mul_action.fixed_points G F) :=
  eq.mpr
    ((fun (S S_1 : set F) (e_2 : S = S_1) => congr_arg is_subfield e_2) (mul_action.fixed_points G F)
      (set.Inter (mul_action.fixed_by G F))
      (eq.mpr
        (id
          (Eq._oldrec (Eq.refl (mul_action.fixed_points G F = set.Inter (mul_action.fixed_by G F)))
            (mul_action.fixed_eq_Inter_fixed_by G F)))
        (Eq.refl (set.Inter fun (g : G) => mul_action.fixed_by G F g))))
    (is_subfield.Inter (mul_action.fixed_by G F))

protected instance mul_action.fixed_points.is_invariant_subring (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] : is_invariant_subring G (mul_action.fixed_points G F) :=
  is_invariant_subring.mk
    fun (g : G) (x : F) (hx : x ∈ mul_action.fixed_points G F) (g' : G) =>
      eq.mpr (id (Eq._oldrec (Eq.refl (g' • g • x = g • x)) (hx g)))
        (eq.mpr (id (Eq._oldrec (Eq.refl (g' • x = x)) (hx g'))) (Eq.refl x))

@[simp] theorem smul (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G) (x : ↥(mul_action.fixed_points G F)) : g • x = x :=
  subtype.eq (subtype.property x g)

-- Why is this so slow?

@[simp] theorem smul_polynomial (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G) (p : polynomial ↥(mul_action.fixed_points G F)) : g • p = p := sorry

protected instance algebra (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] : algebra (↥(mul_action.fixed_points G F)) F :=
  algebra.of_is_subring (mul_action.fixed_points G F)

theorem coe_algebra_map (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] : algebra_map (↥(mul_action.fixed_points G F)) F = is_subring.subtype (mul_action.fixed_points G F) :=
  rfl

theorem linear_independent_smul_of_linear_independent (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] {s : finset F} : (linear_independent ↥(mul_action.fixed_points G F) fun (i : ↥↑s) => ↑i) →
  linear_independent F fun (i : ↥↑s) => coe_fn (mul_action.to_fun G F) ↑i := sorry

/-- `minpoly G F x` is the minimal polynomial of `(x : F)` over `fixed_points G F`. -/
def minpoly (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : polynomial ↥(mul_action.fixed_points G F) :=
  polynomial.to_subring (prod_X_sub_smul G F x) (mul_action.fixed_points G F) sorry

namespace minpoly


theorem monic (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : polynomial.monic (minpoly G F x) :=
  subtype.eq (prod_X_sub_smul.monic G F x)

theorem eval₂ (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : polynomial.eval₂ (is_subring.subtype (mul_action.fixed_points G F)) x (minpoly G F x) = 0 := sorry

theorem ne_one (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : minpoly G F x ≠ 1 := sorry

theorem of_eval₂ (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) (f : polynomial ↥(mul_action.fixed_points G F)) (hf : polynomial.eval₂ (is_subring.subtype (mul_action.fixed_points G F)) x f = 0) : minpoly G F x ∣ f := sorry

/- Why is this so slow? -/

theorem irreducible_aux (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) (f : polynomial ↥(mul_action.fixed_points G F)) (g : polynomial ↥(mul_action.fixed_points G F)) (hf : polynomial.monic f) (hg : polynomial.monic g) (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1 := sorry

theorem irreducible (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : irreducible (minpoly G F x) :=
  iff.mpr (polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)) (irreducible_aux G F x)

end minpoly


theorem is_integral (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : is_integral (↥(mul_action.fixed_points G F)) x :=
  Exists.intro (minpoly G F x) { left := minpoly.monic G F x, right := minpoly.eval₂ G F x }

theorem minpoly_eq_minpoly (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] (x : F) : minpoly G F x = minpoly (↥(mul_action.fixed_points G F)) x :=
  minpoly.unique' (is_integral G F x) (minpoly.irreducible G F x) (minpoly.eval₂ G F x) (minpoly.monic G F x)

protected instance normal (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] : normal (↥(mul_action.fixed_points G F)) F := sorry

protected instance separable (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] : is_separable (↥(mul_action.fixed_points G F)) F := sorry

theorem dim_le_card (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] : vector_space.dim (↥(mul_action.fixed_points G F)) F ≤ ↑(fintype.card G) := sorry

protected instance finite_dimensional (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] : finite_dimensional (↥(mul_action.fixed_points G F)) F :=
  iff.mpr finite_dimensional.finite_dimensional_iff_dim_lt_omega
    (lt_of_le_of_lt (dim_le_card G F) (cardinal.nat_lt_omega (fintype.card G)))

theorem findim_le_card (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] [fintype G] : finite_dimensional.findim (↥(mul_action.fixed_points G F)) F ≤ fintype.card G :=
  eq.mp (propext cardinal.nat_cast_le)
    (trans_rel_right LessEq (finite_dimensional.findim_eq_dim (↥(mul_action.fixed_points G F)) F) (dim_le_card G F))

end fixed_points


theorem linear_independent_to_linear_map (R : Type u) (A : Type v) (B : Type w) [comm_semiring R] [integral_domain A] [algebra R A] [integral_domain B] [algebra R B] : linear_independent B alg_hom.to_linear_map := sorry

theorem cardinal_mk_alg_hom (K : Type u) (V : Type v) (W : Type w) [field K] [field V] [algebra K V] [finite_dimensional K V] [field W] [algebra K W] [finite_dimensional K W] : cardinal.mk (alg_hom K V W) ≤ ↑(finite_dimensional.findim W (linear_map K V W)) :=
  finite_dimensional.cardinal_mk_le_findim_of_linear_independent (linear_independent_to_linear_map K V W)

protected instance alg_hom.fintype (K : Type u) (V : Type v) (W : Type w) [field K] [field V] [algebra K V] [finite_dimensional K V] [field W] [algebra K W] [finite_dimensional K W] : fintype (alg_hom K V W) :=
  Classical.choice sorry

protected instance alg_equiv.fintype (K : Type u) (V : Type v) [field K] [field V] [algebra K V] [finite_dimensional K V] : fintype (alg_equiv K V V) :=
  fintype.of_equiv (alg_hom K V V) (equiv.symm (alg_equiv_equiv_alg_hom K V))

theorem findim_alg_hom (K : Type u) (V : Type v) [field K] [field V] [algebra K V] [finite_dimensional K V] : fintype.card (alg_hom K V V) ≤ finite_dimensional.findim V (linear_map K V V) :=
  finite_dimensional.fintype_card_le_findim_of_linear_independent (linear_independent_to_linear_map K V V)

namespace fixed_points


/-- Embedding produced from a faithful action. -/
@[simp] theorem to_alg_hom_apply (G : Type u) (F : Type v) [group G] [field F] [faithful_mul_semiring_action G F] : ⇑(to_alg_hom G F) =
  fun (g : G) =>
    alg_hom.mk (ring_hom.to_fun (mul_semiring_action.to_semiring_hom G F g)) (to_alg_hom._proof_3 G F g)
      (to_alg_hom._proof_4 G F g) (to_alg_hom._proof_5 G F g) (to_alg_hom._proof_6 G F g) (to_alg_hom._proof_7 G F g) :=
  Eq.refl ⇑(to_alg_hom G F)

theorem to_alg_hom_apply_apply {G : Type u} {F : Type v} [group G] [field F] [faithful_mul_semiring_action G F] (g : G) (x : F) : coe_fn (coe_fn (to_alg_hom G F) g) x = g • x :=
  rfl

theorem findim_eq_card (G : Type u) (F : Type v) [group G] [field F] [fintype G] [faithful_mul_semiring_action G F] : finite_dimensional.findim (↥(mul_action.fixed_points G F)) F = fintype.card G := sorry

theorem to_alg_hom_bijective (G : Type u) (F : Type v) [group G] [field F] [fintype G] [faithful_mul_semiring_action G F] : function.bijective ⇑(to_alg_hom G F) := sorry

/-- Bijection between G and algebra homomorphisms that fix the fixed points -/
def to_alg_hom_equiv (G : Type u) (F : Type v) [group G] [field F] [fintype G] [faithful_mul_semiring_action G F] : G ≃ alg_hom (↥(mul_action.fixed_points G F)) F F :=
  function.embedding.equiv_of_surjective (to_alg_hom G F) sorry

