/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.monic
import Mathlib.algebra.group_ring_action
import Mathlib.algebra.group_action_hom
import Mathlib.PostPort

universes u_1 u_2 u_3 u_4 

namespace Mathlib

/-!
# Group action on rings applied to polynomials

This file contains instances and definitions relating `mul_semiring_action` to `polynomial`.
-/

namespace polynomial


protected instance mul_semiring_action (M : Type u_1) [monoid M] (R : Type u_2) [semiring R]
    [mul_semiring_action M R] : mul_semiring_action M (polynomial R) :=
  mul_semiring_action.mk sorry sorry

protected instance faithful_mul_semiring_action (M : Type u_1) [monoid M] (R : Type u_2)
    [semiring R] [faithful_mul_semiring_action M R] :
    faithful_mul_semiring_action M (polynomial R) :=
  faithful_mul_semiring_action.mk sorry

@[simp] theorem coeff_smul' {M : Type u_1} [monoid M] {R : Type u_2} [semiring R]
    [mul_semiring_action M R] (m : M) (p : polynomial R) (n : ℕ) :
    coeff (m • p) n = m • coeff p n :=
  coeff_map (mul_semiring_action.to_semiring_hom M R m) n

@[simp] theorem smul_C {M : Type u_1} [monoid M] {R : Type u_2} [semiring R]
    [mul_semiring_action M R] (m : M) (r : R) : m • coe_fn C r = coe_fn C (m • r) :=
  map_C (mul_semiring_action.to_semiring_hom M R m)

@[simp] theorem smul_X {M : Type u_1} [monoid M] {R : Type u_2} [semiring R]
    [mul_semiring_action M R] (m : M) : m • X = X :=
  map_X (mul_semiring_action.to_semiring_hom M R m)

theorem smul_eval_smul {M : Type u_1} [monoid M] (S : Type u_3) [comm_semiring S]
    [mul_semiring_action M S] (m : M) (f : polynomial S) (x : S) :
    eval (m • x) (m • f) = m • eval x f :=
  sorry

theorem eval_smul' (S : Type u_3) [comm_semiring S] (G : Type u_4) [group G]
    [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
    eval (g • x) f = g • eval x (g⁻¹ • f) :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (eval (g • x) f = g • eval x (g⁻¹ • f)))
        (Eq.symm (smul_eval_smul S g (g⁻¹ • f) x))))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (eval (g • x) f = eval (g • x) (g • g⁻¹ • f))) (smul_inv_smul g f)))
      (Eq.refl (eval (g • x) f)))

theorem smul_eval (S : Type u_3) [comm_semiring S] (G : Type u_4) [group G]
    [mul_semiring_action G S] (g : G) (f : polynomial S) (x : S) :
    eval x (g • f) = g • eval (g⁻¹ • x) f :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (eval x (g • f) = g • eval (g⁻¹ • x) f))
        (Eq.symm (smul_eval_smul S g f (g⁻¹ • x)))))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (eval x (g • f) = eval (g • g⁻¹ • x) (g • f))) (smul_inv_smul g x)))
      (Eq.refl (eval x (g • f))))

end polynomial


/-- the product of `(X - g • x)` over distinct `g • x`. -/
def prod_X_sub_smul (G : Type u_2) [group G] [fintype G] (R : Type u_3) [comm_ring R]
    [mul_semiring_action G R] (x : R) : polynomial R :=
  finset.prod finset.univ
    fun (g : quotient_group.quotient (mul_action.stabilizer G x)) =>
      polynomial.X - coe_fn polynomial.C (mul_action.of_quotient_stabilizer G x g)

theorem prod_X_sub_smul.monic (G : Type u_2) [group G] [fintype G] (R : Type u_3) [comm_ring R]
    [mul_semiring_action G R] (x : R) : polynomial.monic (prod_X_sub_smul G R x) :=
  sorry

theorem prod_X_sub_smul.eval (G : Type u_2) [group G] [fintype G] (R : Type u_3) [comm_ring R]
    [mul_semiring_action G R] (x : R) : polynomial.eval x (prod_X_sub_smul G R x) = 0 :=
  sorry

theorem prod_X_sub_smul.smul (G : Type u_2) [group G] [fintype G] (R : Type u_3) [comm_ring R]
    [mul_semiring_action G R] (x : R) (g : G) : g • prod_X_sub_smul G R x = prod_X_sub_smul G R x :=
  sorry

theorem prod_X_sub_smul.coeff (G : Type u_2) [group G] [fintype G] (R : Type u_3) [comm_ring R]
    [mul_semiring_action G R] (x : R) (g : G) (n : ℕ) :
    g • polynomial.coeff (prod_X_sub_smul G R x) n = polynomial.coeff (prod_X_sub_smul G R x) n :=
  sorry

namespace mul_semiring_action_hom


/-- An equivariant map induces an equivariant map on polynomials. -/
protected def polynomial {M : Type u_1} [monoid M] {P : Type u_2} [comm_semiring P]
    [mul_semiring_action M P] {Q : Type u_3} [comm_semiring Q] [mul_semiring_action M Q]
    (g : mul_semiring_action_hom M P Q) : mul_semiring_action_hom M (polynomial P) (polynomial Q) :=
  mk (polynomial.map ↑g) sorry sorry sorry sorry sorry

@[simp] theorem coe_polynomial {M : Type u_1} [monoid M] {P : Type u_2} [comm_semiring P]
    [mul_semiring_action M P] {Q : Type u_3} [comm_semiring Q] [mul_semiring_action M Q]
    (g : mul_semiring_action_hom M P Q) :
    ⇑(mul_semiring_action_hom.polynomial g) = polynomial.map ↑g :=
  rfl

end Mathlib