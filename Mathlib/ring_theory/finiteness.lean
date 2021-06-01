/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.noetherian
import Mathlib.ring_theory.ideal.operations
import Mathlib.ring_theory.algebra_tower
import Mathlib.PostPort

universes u_1 u_4 u_2 u_5 u_3 

namespace Mathlib

/-!
# Finiteness conditions in commutative algebra

In this file we define several notions of finiteness that are common in commutative algebra.

## Main declarations

- `module.finite`, `algebra.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.
- `algebra.finite_type`, `ring_hom.finite_type`, `alg_hom.finite_type`
  all of these express that some object is finitely generated *as algebra* over some base ring.

-/

/-- A module over a commutative ring is `finite` if it is finitely generated as a module. -/
def module.finite (R : Type u_1) (M : Type u_4) [comm_ring R] [add_comm_group M] [module R M] :=
  submodule.fg ⊤

/-- An algebra over a commutative ring is of `finite_type` if it is finitely generated
over the base ring as algebra. -/
def algebra.finite_type (R : Type u_1) (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] :=
  subalgebra.fg ⊤

/-- An algebra over a commutative ring is `finitely_presented` if it is the quotient of a
polynomial ring in `n` variables by a finitely generated ideal. -/
def algebra.finitely_presented (R : Type u_1) (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] :=
  ∃ (n : ℕ),
    ∃ (f : alg_hom R (mv_polynomial (fin n) R) A),
      function.surjective ⇑f ∧ submodule.fg (ring_hom.ker (alg_hom.to_ring_hom f))

namespace module


theorem finite_def {R : Type u_1} {M : Type u_4} [comm_ring R] [add_comm_group M] [module R M] : finite R M ↔ submodule.fg ⊤ :=
  iff.rfl

protected instance is_noetherian.finite (R : Type u_1) (M : Type u_4) [comm_ring R] [add_comm_group M] [module R M] [is_noetherian R M] : finite R M :=
  is_noetherian.noetherian ⊤

namespace finite


theorem of_surjective {R : Type u_1} {M : Type u_4} {N : Type u_5} [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] [hM : finite R M] (f : linear_map R M N) (hf : function.surjective ⇑f) : finite R N := sorry

theorem of_injective {R : Type u_1} {M : Type u_4} {N : Type u_5} [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] [is_noetherian R N] (f : linear_map R M N) (hf : function.injective ⇑f) : finite R M :=
  fg_of_injective f (iff.mpr linear_map.ker_eq_bot hf)

protected instance self (R : Type u_1) [comm_ring R] : finite R R :=
  Exists.intro (singleton 1)
    (eq.mpr
      (id
        ((fun (a a_1 : submodule R R) (e_1 : a = a_1) (ᾰ ᾰ_1 : submodule R R) (e_2 : ᾰ = ᾰ_1) =>
            congr (congr_arg Eq e_1) e_2)
          (submodule.span R ↑(singleton 1)) (submodule.span R (singleton 1))
          ((fun (s s_1 : set R) (e_2 : s = s_1) => congr_arg (submodule.span R) e_2) (↑(singleton 1)) (singleton 1)
            (finset.coe_singleton 1))
          ⊤ ⊤ (Eq.refl ⊤)))
      (eq.mp (Eq.refl (ideal.span 1 = ⊤)) ideal.span_singleton_one))

protected instance prod {R : Type u_1} {M : Type u_4} {N : Type u_5} [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite R (M × N))) (equations._eqn_1 R (M × N))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (submodule.fg ⊤)) (Eq.symm submodule.prod_top))) (submodule.fg_prod hM hN))

theorem equiv {R : Type u_1} {M : Type u_4} {N : Type u_5} [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N] [hM : finite R M] (e : linear_equiv R M N) : finite R N :=
  of_surjective (↑e) (linear_equiv.surjective e)

theorem trans {R : Type u_1} (A : Type u_2) (B : Type u_3) [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B] [algebra A B] [is_scalar_tower R A B] [hRA : finite R A] [hAB : finite A B] : finite R B := sorry

protected instance finite_type {R : Type u_1} (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] [hRA : finite R A] : algebra.finite_type R A :=
  subalgebra.fg_of_submodule_fg hRA

end finite


end module


namespace algebra


namespace finite_type


theorem self (R : Type u_1) [comm_ring R] : finite_type R R :=
  Exists.intro (singleton 1) (subsingleton.elim (adjoin R ↑(singleton 1)) ⊤)

protected theorem mv_polynomial (R : Type u_1) [comm_ring R] (ι : Type u_2) [fintype ι] : finite_type R (mv_polynomial ι R) := sorry

theorem of_surjective {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B] (hRA : finite_type R A) (f : alg_hom R A B) (hf : function.surjective ⇑f) : finite_type R B := sorry

theorem equiv {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B] (hRA : finite_type R A) (e : alg_equiv R A B) : finite_type R B :=
  of_surjective hRA (↑e) (alg_equiv.surjective e)

theorem trans {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B] [algebra A B] [is_scalar_tower R A B] (hRA : finite_type R A) (hAB : finite_type A B) : finite_type R B :=
  fg_trans' hRA hAB

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a finset. -/
theorem iff_quotient_mv_polynomial {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : finite_type R A ↔
  ∃ (s : finset A), ∃ (f : alg_hom R (mv_polynomial (Subtype fun (x : A) => x ∈ s) R) A), function.surjective ⇑f := sorry

/-- An algebra is finitely generated if and only if it is a quotient
of a polynomial ring whose variables are indexed by a fintype. -/
theorem iff_quotient_mv_polynomial' {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : finite_type R A ↔ ∃ (ι : Type u_2), Exists (∃ (f : alg_hom R (mv_polynomial ι R) A), function.surjective ⇑f) := sorry

/-- An algebra is finitely generated if and only if it is a quotient of a polynomial ring in `n`
variables. -/
theorem iff_quotient_mv_polynomial'' {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : finite_type R A ↔ ∃ (n : ℕ), ∃ (f : alg_hom R (mv_polynomial (fin n) R) A), function.surjective ⇑f := sorry

/-- A finitely presented algebra is of finite type. -/
theorem of_finitely_presented {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : finitely_presented R A → finite_type R A := sorry

end finite_type


namespace finitely_presented


/-- If `e : A ≃ₐ[R] B` and `A` is finitely presented, then so is `B`. -/
theorem equiv (R : Type u_1) (A : Type u_2) (B : Type u_3) [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B] (hfp : finitely_presented R A) (e : alg_equiv R A B) : finitely_presented R B := sorry

/-- The ring of polynomials in finitely many variables is finitely presented. -/
theorem mv_polynomial (R : Type u_1) [comm_ring R] (ι : Type u_2) [fintype ι] : finitely_presented R (mv_polynomial ι R) := sorry

/-- `R` is finitely presented as `R`-algebra. -/
theorem self (R : Type u_1) [comm_ring R] : finitely_presented R R :=
  let hempty : finitely_presented R (mv_polynomial pempty R) := mv_polynomial R pempty;
  equiv R (mv_polynomial pempty R) R hempty (mv_polynomial.pempty_alg_equiv R)

end finitely_presented


end algebra


namespace ring_hom


/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite {A : Type u_1} {B : Type u_2} [comm_ring A] [comm_ring B] (f : A →+* B) :=
  let _inst : algebra A B := to_algebra f;
  module.finite A B

/-- A ring morphism `A →+* B` is of `finite_type` if `B` is finitely generated as `A`-algebra. -/
def finite_type {A : Type u_1} {B : Type u_2} [comm_ring A] [comm_ring B] (f : A →+* B) :=
  algebra.finite_type A B

namespace finite


theorem id (A : Type u_1) [comm_ring A] : finite (id A) :=
  module.finite.self A

theorem of_surjective {A : Type u_1} {B : Type u_2} [comm_ring A] [comm_ring B] (f : A →+* B) (hf : function.surjective ⇑f) : finite f :=
  let _inst : algebra A B := to_algebra f;
  module.finite.of_surjective (alg_hom.to_linear_map (algebra.of_id A B)) hf

theorem comp {A : Type u_1} {B : Type u_2} {C : Type u_3} [comm_ring A] [comm_ring B] [comm_ring C] {g : B →+* C} {f : A →+* B} (hg : finite g) (hf : finite f) : finite (comp g f) :=
  module.finite.trans B C

theorem finite_type {A : Type u_1} {B : Type u_2} [comm_ring A] [comm_ring B] {f : A →+* B} (hf : finite f) : finite_type f :=
  module.finite.finite_type B

end finite


namespace finite_type


theorem id (A : Type u_1) [comm_ring A] : finite_type (id A) :=
  algebra.finite_type.self A

theorem comp_surjective {A : Type u_1} {B : Type u_2} {C : Type u_3} [comm_ring A] [comm_ring B] [comm_ring C] {f : A →+* B} {g : B →+* C} (hf : finite_type f) (hg : function.surjective ⇑g) : finite_type (comp g f) :=
  algebra.finite_type.of_surjective hf
    (alg_hom.mk (⇑g) (map_one' g) (map_mul' g) (map_zero' g) (map_add' g) fun (a : A) => rfl) hg

theorem of_surjective {A : Type u_1} {B : Type u_2} [comm_ring A] [comm_ring B] (f : A →+* B) (hf : function.surjective ⇑f) : finite_type f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (finite_type f)) (Eq.symm (comp_id f)))) (comp_surjective (id A) hf)

theorem comp {A : Type u_1} {B : Type u_2} {C : Type u_3} [comm_ring A] [comm_ring B] [comm_ring C] {g : B →+* C} {f : A →+* B} (hg : finite_type g) (hf : finite_type f) : finite_type (comp g f) :=
  algebra.finite_type.trans hf hg

end finite_type


end ring_hom


namespace alg_hom


/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_hom R A B) :=
  ring_hom.finite (to_ring_hom f)

/-- An algebra morphism `A →ₐ[R] B` is of `finite_type` if it is of finite type as ring morphism.
In other words, if `B` is finitely generated as `A`-algebra. -/
def finite_type {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_hom R A B) :=
  ring_hom.finite_type (to_ring_hom f)

namespace finite


theorem id (R : Type u_1) (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] : finite (alg_hom.id R A) :=
  ring_hom.finite.id A

theorem comp {R : Type u_1} {A : Type u_2} {B : Type u_3} {C : Type u_4} [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring C] [algebra R A] [algebra R B] [algebra R C] {g : alg_hom R B C} {f : alg_hom R A B} (hg : finite g) (hf : finite f) : finite (comp g f) :=
  ring_hom.finite.comp hg hf

theorem of_surjective {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_hom R A B) (hf : function.surjective ⇑f) : finite f :=
  ring_hom.finite.of_surjective (↑f) hf

theorem finite_type {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] {f : alg_hom R A B} (hf : finite f) : finite_type f :=
  ring_hom.finite.finite_type hf

end finite


namespace finite_type


theorem id (R : Type u_1) (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] : finite_type (alg_hom.id R A) :=
  ring_hom.finite_type.id A

theorem comp {R : Type u_1} {A : Type u_2} {B : Type u_3} {C : Type u_4} [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring C] [algebra R A] [algebra R B] [algebra R C] {g : alg_hom R B C} {f : alg_hom R A B} (hg : finite_type g) (hf : finite_type f) : finite_type (comp g f) :=
  ring_hom.finite_type.comp hg hf

theorem comp_surjective {R : Type u_1} {A : Type u_2} {B : Type u_3} {C : Type u_4} [comm_ring R] [comm_ring A] [comm_ring B] [comm_ring C] [algebra R A] [algebra R B] [algebra R C] {f : alg_hom R A B} {g : alg_hom R B C} (hf : finite_type f) (hg : function.surjective ⇑g) : finite_type (comp g f) :=
  ring_hom.finite_type.comp_surjective hf hg

theorem of_surjective {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_hom R A B) (hf : function.surjective ⇑f) : finite_type f :=
  ring_hom.finite_type.of_surjective (↑f) hf

