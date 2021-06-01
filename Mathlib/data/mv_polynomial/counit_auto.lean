/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.mv_polynomial.basic
import Mathlib.PostPort

universes u_1 u_2 u_3 

namespace Mathlib

/-!
## Counit morphisms for multivariate polynomials

One may consider the ring of multivariate polynomials `mv_polynomial A R` with coefficients in `R`
and variables indexed by `A`. If `A` is not just a type, but an algebra over `R`,
then there is a natural surjective algebra homomorphism `mv_polynomial A R →ₐ[R] A`
obtained by `X a ↦ a`.

### Main declarations

* `mv_polynomial.acounit R A` is the natural surjective algebra homomorphism `mv_polynomial A R →ₐ[R] A`
     obtained by `X a ↦ a`
* `mv_polynomial.counit` is an “absolute” variant with `R = ℤ`
* `mv_polynomial.counit_nat` is an “absolute” variant with `R = ℕ`

-/

namespace mv_polynomial


/-- `mv_polynomial.acounit A B` is the natural surjective algebra homomorphism
`mv_polynomial B A →ₐ[A] B` obtained by `X a ↦ a`.

See `mv_polynomial.counit` for the “absolute” variant with `A = ℤ`,
and `mv_polynomial.counit_nat` for the “absolute” variant with `A = ℕ`. -/
def acounit (A : Type u_1) (B : Type u_2) [comm_semiring A] [comm_semiring B] [algebra A B] :
    alg_hom A (mv_polynomial B A) B :=
  aeval id

@[simp] theorem acounit_X (A : Type u_1) {B : Type u_2} [comm_semiring A] [comm_semiring B]
    [algebra A B] (b : B) : coe_fn (acounit A B) (X b) = b :=
  aeval_X id b

@[simp] theorem acounit_C {A : Type u_1} (B : Type u_2) [comm_semiring A] [comm_semiring B]
    [algebra A B] (a : A) : coe_fn (acounit A B) (coe_fn C a) = coe_fn (algebra_map A B) a :=
  aeval_C id a

theorem acounit_surjective (A : Type u_1) (B : Type u_2) [comm_semiring A] [comm_semiring B]
    [algebra A B] : function.surjective ⇑(acounit A B) :=
  fun (b : B) => Exists.intro (X b) (acounit_X A b)

/-- `mv_polynomial.counit R` is the natural surjective ring homomorphism
`mv_polynomial R ℤ →+* R` obtained by `X r ↦ r`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring,
and `mv_polynomial.counit_nat` for the “absolute” variant with `R = ℕ`. -/
def counit (R : Type u_3) [comm_ring R] : mv_polynomial R ℤ →+* R := ↑(acounit ℤ R)

/-- `mv_polynomial.counit_nat A` is the natural surjective ring homomorphism
`mv_polynomial A ℕ →+* A` obtained by `X a ↦ a`.

See `mv_polynomial.acounit` for a “relative” variant for algebras over a base ring
and `mv_polynomial.counit` for the “absolute” variant with `A = ℤ`. -/
def counit_nat (A : Type u_1) [comm_semiring A] : mv_polynomial A ℕ →+* A := ↑(acounit ℕ A)

theorem counit_surjective (R : Type u_3) [comm_ring R] : function.surjective ⇑(counit R) :=
  acounit_surjective ℤ R

theorem counit_nat_surjective (A : Type u_1) [comm_semiring A] :
    function.surjective ⇑(counit_nat A) :=
  acounit_surjective ℕ A

theorem counit_C (R : Type u_3) [comm_ring R] (n : ℤ) : coe_fn (counit R) (coe_fn C n) = ↑n :=
  acounit_C R n

theorem counit_nat_C (A : Type u_1) [comm_semiring A] (n : ℕ) :
    coe_fn (counit_nat A) (coe_fn C n) = ↑n :=
  acounit_C A n

@[simp] theorem counit_X {R : Type u_3} [comm_ring R] (r : R) : coe_fn (counit R) (X r) = r :=
  acounit_X ℤ r

@[simp] theorem counit_nat_X {A : Type u_1} [comm_semiring A] (a : A) :
    coe_fn (counit_nat A) (X a) = a :=
  acounit_X ℕ a

end Mathlib