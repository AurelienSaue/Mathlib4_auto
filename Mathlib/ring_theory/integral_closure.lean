/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.algebra_tower
import Mathlib.ring_theory.polynomial.scale_roots
import Mathlib.PostPort

universes u_1 u_3 u_2 u_4 u_5 

namespace Mathlib

/-!
# Integral closure of a subring.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R. Enough theory is developed to prove that integral elements
form a sub-R-algebra of A.

## Main definitions

Let `R` be a `comm_ring` and let `A` be an R-algebra.

* `ring_hom.is_integral_elem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `is_integral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                           coefficients in `R`.
* `integral_closure R A` : the integral closure of `R` in `A`, regarded as a sub-`R`-algebra of `A`.
-/

/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : polynomial R` evaluated under `f` -/
def ring_hom.is_integral_elem {R : Type u_1} {A : Type u_3} [comm_ring R] [ring A] (f : R →+* A) (x : A)  :=
  ∃ (p : polynomial R), polynomial.monic p ∧ polynomial.eval₂ f x p = 0

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
def ring_hom.is_integral {R : Type u_1} {A : Type u_3} [comm_ring R] [ring A] (f : R →+* A)  :=
  ∀ (x : A), ring_hom.is_integral_elem f x

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : polynomial R`.
Equivalently, the element is integral over `R` with respect to the induced `algebra_map` -/
def is_integral (R : Type u_1) {A : Type u_3} [comm_ring R] [ring A] [algebra R A] (x : A)  :=
  ring_hom.is_integral_elem (algebra_map R A) x

/-- An algebra is integral if every element of the extension is integral over the base ring -/
def algebra.is_integral (R : Type u_1) (A : Type u_3) [comm_ring R] [ring A] [algebra R A]  :=
  ring_hom.is_integral (algebra_map R A)

theorem ring_hom.is_integral_map {R : Type u_1} {S : Type u_2} [comm_ring R] [ring S] (f : R →+* S) {x : R} : ring_hom.is_integral_elem f (coe_fn f x) := sorry

theorem is_integral_algebra_map {R : Type u_1} {A : Type u_3} [comm_ring R] [ring A] [algebra R A] {x : R} : is_integral R (coe_fn (algebra_map R A) x) :=
  ring_hom.is_integral_map (algebra_map R A)

theorem is_integral_of_noetherian {R : Type u_1} {A : Type u_3} [comm_ring R] [ring A] [algebra R A] (H : is_noetherian R A) (x : A) : is_integral R x := sorry

theorem is_integral_of_submodule_noetherian {R : Type u_1} {A : Type u_3} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) (H : is_noetherian R ↥↑S) (x : A) (hx : x ∈ S) : is_integral R x := sorry

theorem is_integral_alg_hom {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_hom R A B) {x : A} (hx : is_integral R x) : is_integral R (coe_fn f x) := sorry

theorem is_integral_of_is_scalar_tower {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B] (x : B) (hx : is_integral R x) : is_integral A x := sorry

theorem is_integral_of_subring {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} (T : set R) [is_subring T] (hx : is_integral (↥T) x) : is_integral R x :=
  is_integral_of_is_scalar_tower x hx

theorem is_integral_algebra_map_iff {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B] {x : A} (hAB : function.injective ⇑(algebra_map A B)) : is_integral R (coe_fn (algebra_map A B) x) ↔ is_integral R x := sorry

theorem is_integral_iff_is_integral_closure_finite {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {r : A} : is_integral R r ↔ ∃ (s : set R), set.finite s ∧ is_integral (↥(ring.closure s)) r := sorry

theorem fg_adjoin_singleton_of_integral {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] (x : A) (hx : is_integral R x) : submodule.fg ↑(algebra.adjoin R (singleton x)) := sorry

theorem fg_adjoin_of_finite {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {s : set A} (hfs : set.finite s) (his : ∀ (x : A), x ∈ s → is_integral R x) : submodule.fg ↑(algebra.adjoin R s) := sorry

theorem is_integral_of_mem_of_fg {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] (S : subalgebra R A) (HS : submodule.fg ↑S) (x : A) (hx : x ∈ S) : is_integral R x := sorry

theorem ring_hom.is_integral_of_mem_closure {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {x : S} {y : S} {z : S} (hx : ring_hom.is_integral_elem f x) (hy : ring_hom.is_integral_elem f y) (hz : z ∈ ring.closure (insert x (singleton y))) : ring_hom.is_integral_elem f z := sorry

theorem is_integral_of_mem_closure {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} {y : A} {z : A} (hx : is_integral R x) (hy : is_integral R y) (hz : z ∈ ring.closure (insert x (singleton y))) : is_integral R z :=
  ring_hom.is_integral_of_mem_closure (algebra_map R A) hx hy hz

theorem ring_hom.is_integral_zero {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) : ring_hom.is_integral_elem f 0 :=
  ring_hom.map_zero f ▸ ring_hom.is_integral_map f

theorem is_integral_zero {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : is_integral R 0 :=
  ring_hom.is_integral_zero (algebra_map R A)

theorem ring_hom.is_integral_one {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) : ring_hom.is_integral_elem f 1 :=
  ring_hom.map_one f ▸ ring_hom.is_integral_map f

theorem is_integral_one {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : is_integral R 1 :=
  ring_hom.is_integral_one (algebra_map R A)

theorem ring_hom.is_integral_add {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {x : S} {y : S} (hx : ring_hom.is_integral_elem f x) (hy : ring_hom.is_integral_elem f y) : ring_hom.is_integral_elem f (x + y) :=
  ring_hom.is_integral_of_mem_closure f hx hy
    (is_add_submonoid.add_mem (ring.subset_closure (Or.inl rfl)) (ring.subset_closure (Or.inr rfl)))

theorem is_integral_add {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} {y : A} (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x + y) :=
  ring_hom.is_integral_add (algebra_map R A) hx hy

theorem ring_hom.is_integral_neg {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {x : S} (hx : ring_hom.is_integral_elem f x) : ring_hom.is_integral_elem f (-x) :=
  ring_hom.is_integral_of_mem_closure f hx hx (is_add_subgroup.neg_mem (ring.subset_closure (Or.inl rfl)))

theorem is_integral_neg {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} (hx : is_integral R x) : is_integral R (-x) :=
  ring_hom.is_integral_neg (algebra_map R A) hx

theorem ring_hom.is_integral_sub {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {x : S} {y : S} (hx : ring_hom.is_integral_elem f x) (hy : ring_hom.is_integral_elem f y) : ring_hom.is_integral_elem f (x - y) := sorry

theorem is_integral_sub {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} {y : A} (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x - y) :=
  ring_hom.is_integral_sub (algebra_map R A) hx hy

theorem ring_hom.is_integral_mul {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {x : S} {y : S} (hx : ring_hom.is_integral_elem f x) (hy : ring_hom.is_integral_elem f y) : ring_hom.is_integral_elem f (x * y) :=
  ring_hom.is_integral_of_mem_closure f hx hy
    (is_submonoid.mul_mem (ring.subset_closure (Or.inl rfl)) (ring.subset_closure (Or.inr rfl)))

theorem is_integral_mul {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} {y : A} (hx : is_integral R x) (hy : is_integral R y) : is_integral R (x * y) :=
  ring_hom.is_integral_mul (algebra_map R A) hx hy

/-- The integral closure of R in an R-algebra A. -/
def integral_closure (R : Type u_1) (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] : subalgebra R A :=
  subalgebra.mk (set_of fun (r : A) => is_integral R r) is_integral_one sorry is_integral_zero sorry sorry

theorem mem_integral_closure_iff_mem_fg (R : Type u_1) (A : Type u_2) [comm_ring R] [comm_ring A] [algebra R A] {r : A} : r ∈ integral_closure R A ↔ ∃ (M : subalgebra R A), submodule.fg ↑M ∧ r ∈ M := sorry

/-- Mapping an integral closure along an `alg_equiv` gives the integral closure. -/
theorem integral_closure_map_alg_equiv {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B] (f : alg_equiv R A B) : subalgebra.map (integral_closure R A) ↑f = integral_closure R B := sorry

theorem integral_closure.is_integral {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] (x : ↥(integral_closure R A)) : is_integral R x := sorry

theorem ring_hom.is_integral_of_is_integral_mul_unit {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) (x : S) (y : S) (r : R) (hr : coe_fn f r * y = 1) (hx : ring_hom.is_integral_elem f (x * y)) : ring_hom.is_integral_elem f x := sorry

theorem is_integral_of_is_integral_mul_unit {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {x : A} {y : A} {r : R} (hr : coe_fn (algebra_map R A) r * y = 1) (hx : is_integral R (x * y)) : is_integral R x :=
  ring_hom.is_integral_of_is_integral_mul_unit (algebra_map R A) x y r hr hx

/-- Generalization of `is_integral_of_mem_closure` bootstrapped up from that lemma -/
theorem is_integral_of_mem_closure' {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] (G : set A) (hG : ∀ (x : A), x ∈ G → is_integral R x) (x : A) (H : x ∈ subring.closure G) : is_integral R x :=
  subring.closure_induction hx hG is_integral_zero is_integral_one (fun (_x _x_1 : A) => is_integral_add)
    (fun (_x : A) => is_integral_neg) fun (_x _x_1 : A) => is_integral_mul

theorem is_integral_of_mem_closure'' {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] {f : R →+* S} (G : set S) (hG : ∀ (x : S), x ∈ G → ring_hom.is_integral_elem f x) (x : S) (H : x ∈ subring.closure G) : ring_hom.is_integral_elem f x :=
  is_integral_of_mem_closure' G hG x hx

theorem is_integral_trans_aux {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra A B] [algebra R B] (x : B) {p : polynomial A} (pmonic : polynomial.monic p) (hp : coe_fn (polynomial.aeval x) p = 0) : is_integral (↥(algebra.adjoin R ↑(finsupp.frange (polynomial.map (algebra_map A B) p)))) x := sorry

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
theorem is_integral_trans {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra A B] [algebra R B] [algebra R A] [is_scalar_tower R A B] (A_int : algebra.is_integral R A) (x : B) (hx : is_integral A x) : is_integral R x := sorry

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
theorem algebra.is_integral_trans {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra A B] [algebra R B] [algebra R A] [is_scalar_tower R A B] (hA : algebra.is_integral R A) (hB : algebra.is_integral A B) : algebra.is_integral R B :=
  fun (x : B) => is_integral_trans hA x (hB x)

theorem ring_hom.is_integral_trans {R : Type u_1} {S : Type u_4} {T : Type u_5} [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T) (hf : ring_hom.is_integral f) (hg : ring_hom.is_integral g) : ring_hom.is_integral (ring_hom.comp g f) :=
  algebra.is_integral_trans hf hg

theorem ring_hom.is_integral_of_surjective {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) (hf : function.surjective ⇑f) : ring_hom.is_integral f :=
  fun (x : S) => Exists.rec_on (hf x) fun (y : R) (hy : coe_fn f y = x) => hy ▸ ring_hom.is_integral_map f

theorem is_integral_of_surjective {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] (h : function.surjective ⇑(algebra_map R A)) : algebra.is_integral R A :=
  ring_hom.is_integral_of_surjective (algebra_map R A) h

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
theorem is_integral_tower_bot_of_is_integral {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra A B] [algebra R B] [algebra R A] [is_scalar_tower R A B] (H : function.injective ⇑(algebra_map A B)) {x : A} (h : is_integral R (coe_fn (algebra_map A B) x)) : is_integral R x := sorry

theorem ring_hom.is_integral_tower_bot_of_is_integral {R : Type u_1} {S : Type u_4} {T : Type u_5} [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T) (hg : function.injective ⇑g) (hfg : ring_hom.is_integral (ring_hom.comp g f)) : ring_hom.is_integral f :=
  fun (x : S) => is_integral_tower_bot_of_is_integral hg (hfg (coe_fn g x))

theorem is_integral_tower_bot_of_is_integral_field {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [field A] [comm_ring B] [nontrivial B] [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B] {x : A} (h : is_integral R (coe_fn (algebra_map A B) x)) : is_integral R x :=
  is_integral_tower_bot_of_is_integral (ring_hom.injective (algebra_map A B)) h

theorem ring_hom.is_integral_elem_of_is_integral_elem_comp {R : Type u_1} {S : Type u_4} {T : Type u_5} [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T) {x : T} (h : ring_hom.is_integral_elem (ring_hom.comp g f) x) : ring_hom.is_integral_elem g x := sorry

theorem ring_hom.is_integral_tower_top_of_is_integral {R : Type u_1} {S : Type u_4} {T : Type u_5} [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T) (h : ring_hom.is_integral (ring_hom.comp g f)) : ring_hom.is_integral g :=
  fun (x : T) => ring_hom.is_integral_elem_of_is_integral_elem_comp f g (h x)

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
theorem is_integral_tower_top_of_is_integral {R : Type u_1} {A : Type u_2} {B : Type u_3} [comm_ring R] [comm_ring A] [comm_ring B] [algebra A B] [algebra R B] [algebra R A] [is_scalar_tower R A B] {x : B} (h : is_integral R x) : is_integral A x := sorry

theorem ring_hom.is_integral_quotient_of_is_integral {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {I : ideal S} (hf : ring_hom.is_integral f) : ring_hom.is_integral (ideal.quotient_map I f le_rfl) := sorry

theorem is_integral_quotient_of_is_integral {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] {I : ideal A} (hRA : algebra.is_integral R A) : algebra.is_integral (ideal.quotient (ideal.comap (algebra_map R A) I)) (ideal.quotient I) :=
  ring_hom.is_integral_quotient_of_is_integral (algebra_map R A) hRA

theorem is_integral_quotient_map_iff {R : Type u_1} {S : Type u_4} [comm_ring R] [comm_ring S] (f : R →+* S) {I : ideal S} : ring_hom.is_integral (ideal.quotient_map I f le_rfl) ↔ ring_hom.is_integral (ring_hom.comp (ideal.quotient.mk I) f) := sorry

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
theorem is_field_of_is_integral_of_is_field {R : Type u_1} {S : Type u_2} [integral_domain R] [integral_domain S] [algebra R S] (H : algebra.is_integral R S) (hRS : function.injective ⇑(algebra_map R S)) (hS : is_field S) : is_field R := sorry

theorem integral_closure_idem {R : Type u_1} {A : Type u_2} [comm_ring R] [comm_ring A] [algebra R A] : integral_closure (↥↑(integral_closure R A)) A = ⊥ := sorry

protected instance integral_closure.integral_domain {R : Type u_1} {S : Type u_2} [comm_ring R] [integral_domain S] [algebra R S] : integral_domain ↥(integral_closure R S) :=
  integral_domain.mk comm_ring.add sorry comm_ring.zero sorry sorry comm_ring.neg comm_ring.sub sorry sorry comm_ring.mul
    sorry comm_ring.one sorry sorry sorry sorry sorry sorry sorry

