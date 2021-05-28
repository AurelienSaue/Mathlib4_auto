/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.polynomial.induction
import Mathlib.data.polynomial.degree.definitions
import Mathlib.deprecated.ring
import Mathlib.PostPort

universes u v u_1 u_2 w y 

namespace Mathlib

/-!
# Theory of univariate polynomials

The main defs here are `eval₂`, `eval`, and `map`.
We give several lemmas about their interaction with each other and with module operations.
-/

namespace polynomial


/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) (p : polynomial R) : S :=
  finsupp.sum p fun (e : ℕ) (a : R) => coe_fn f a * x ^ e

theorem eval₂_eq_sum {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] {f : R →+* S} {x : S} : eval₂ f x p = finsupp.sum p fun (e : ℕ) (a : R) => coe_fn f a * x ^ e :=
  rfl

theorem eval₂_eq_lift_nc {R : Type u} {S : Type v} [semiring R] [semiring S] {f : R →+* S} {x : S} : eval₂ f x = ⇑(add_monoid_algebra.lift_nc (↑f) (coe_fn (powers_hom S) x)) :=
  rfl

theorem eval₂_congr {R : Type u_1} {S : Type u_2} [semiring R] [semiring S] {f : R →+* S} {g : R →+* S} {s : S} {t : S} {φ : polynomial R} {ψ : polynomial R} : f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ :=
  fun (ᾰ : f = g) (ᾰ_1 : s = t) (ᾰ_2 : φ = ψ) => Eq._oldrec (Eq._oldrec (Eq._oldrec (Eq.refl (eval₂ f s φ)) ᾰ_2) ᾰ_1) ᾰ

@[simp] theorem eval₂_zero {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) : eval₂ f x 0 = 0 :=
  finsupp.sum_zero_index

@[simp] theorem eval₂_C {R : Type u} {S : Type v} {a : R} [semiring R] [semiring S] (f : R →+* S) (x : S) : eval₂ f x (coe_fn C a) = coe_fn f a := sorry

@[simp] theorem eval₂_X {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) : eval₂ f x X = x := sorry

@[simp] theorem eval₂_monomial {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) {n : ℕ} {r : R} : eval₂ f x (coe_fn (monomial n) r) = coe_fn f r * x ^ n := sorry

@[simp] theorem eval₂_X_pow {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) {n : ℕ} : eval₂ f x (X ^ n) = x ^ n := sorry

@[simp] theorem eval₂_add {R : Type u} {S : Type v} [semiring R] {p : polynomial R} {q : polynomial R} [semiring S] (f : R →+* S) (x : S) : eval₂ f x (p + q) = eval₂ f x p + eval₂ f x q := sorry

@[simp] theorem eval₂_one {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) : eval₂ f x 1 = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (eval₂ f x 1 = 1)) (Eq.symm C_1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (eval₂ f x (coe_fn C 1) = 1)) (eval₂_C f x)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn f 1 = 1)) (ring_hom.map_one f))) (Eq.refl 1)))

@[simp] theorem eval₂_bit0 {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (x : S) : eval₂ f x (bit0 p) = bit0 (eval₂ f x p) := sorry

@[simp] theorem eval₂_bit1 {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (x : S) : eval₂ f x (bit1 p) = bit1 (eval₂ f x p) := sorry

@[simp] theorem eval₂_smul {R : Type u} {S : Type v} [semiring R] [semiring S] (g : R →+* S) (p : polynomial R) (x : S) {s : R} : eval₂ g x (s • p) = coe_fn g s • eval₂ g x p := sorry

@[simp] theorem eval₂_C_X {R : Type u} [semiring R] {p : polynomial R} : eval₂ C X p = p := sorry

protected instance eval₂.is_add_monoid_hom {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) : is_add_monoid_hom (eval₂ f x) :=
  is_add_monoid_hom.mk (eval₂_zero f x)

@[simp] theorem eval₂_nat_cast {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) (n : ℕ) : eval₂ f x ↑n = ↑n := sorry

theorem eval₂_sum {R : Type u} {S : Type v} {T : Type w} [semiring R] [semiring S] (f : R →+* S) [semiring T] (p : polynomial T) (g : ℕ → T → polynomial R) (x : S) : eval₂ f x (finsupp.sum p g) = finsupp.sum p fun (n : ℕ) (a : T) => eval₂ f x (g n a) := sorry

theorem eval₂_finset_sum {R : Type u} {S : Type v} {ι : Type y} [semiring R] [semiring S] (f : R →+* S) (s : finset ι) (g : ι → polynomial R) (x : S) : eval₂ f x (finset.sum s fun (i : ι) => g i) = finset.sum s fun (i : ι) => eval₂ f x (g i) := sorry

theorem eval₂_mul_noncomm {R : Type u} {S : Type v} [semiring R] {p : polynomial R} {q : polynomial R} [semiring S] (f : R →+* S) (x : S) (hf : ∀ (k : ℕ), commute (coe_fn f (coeff q k)) x) : eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q := sorry

@[simp] theorem eval₂_mul_X {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (x : S) : eval₂ f x (p * X) = eval₂ f x p * x := sorry

@[simp] theorem eval₂_X_mul {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (x : S) : eval₂ f x (X * p) = eval₂ f x p * x :=
  eq.mpr (id (Eq._oldrec (Eq.refl (eval₂ f x (X * p) = eval₂ f x p * x)) X_mul))
    (eq.mpr (id (Eq._oldrec (Eq.refl (eval₂ f x (p * X) = eval₂ f x p * x)) (eval₂_mul_X f x)))
      (Eq.refl (eval₂ f x p * x)))

theorem eval₂_mul_C' {R : Type u} {S : Type v} {a : R} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (x : S) (h : commute (coe_fn f a) x) : eval₂ f x (p * coe_fn C a) = eval₂ f x p * coe_fn f a := sorry

theorem eval₂_list_prod_noncomm {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) (ps : List (polynomial R)) (hf : ∀ (p : polynomial R), p ∈ ps → ∀ (k : ℕ), commute (coe_fn f (coeff p k)) x) : eval₂ f x (list.prod ps) = list.prod (list.map (eval₂ f x) ps) := sorry

/-- `eval₂` as a `ring_hom` for noncommutative rings -/
def eval₂_ring_hom' {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (x : S) (hf : ∀ (a : R), commute (coe_fn f a) x) : polynomial R →+* S :=
  ring_hom.mk (eval₂ f x) (eval₂_one f x) sorry (eval₂_zero f x) sorry

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/

@[simp] theorem eval₂_mul {R : Type u} {S : Type v} [semiring R] {p : polynomial R} {q : polynomial R} [comm_semiring S] (f : R →+* S) (x : S) : eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q :=
  eval₂_mul_noncomm f x fun (k : ℕ) => commute.all (coe_fn f (coeff q k)) x

theorem eval₂_mul_eq_zero_of_left {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [comm_semiring S] (f : R →+* S) (x : S) (q : polynomial R) (hp : eval₂ f x p = 0) : eval₂ f x (p * q) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (eval₂ f x (p * q) = 0)) (eval₂_mul f x))) (mul_eq_zero_of_left hp (eval₂ f x q))

theorem eval₂_mul_eq_zero_of_right {R : Type u} {S : Type v} [semiring R] {q : polynomial R} [comm_semiring S] (f : R →+* S) (x : S) (p : polynomial R) (hq : eval₂ f x q = 0) : eval₂ f x (p * q) = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (eval₂ f x (p * q) = 0)) (eval₂_mul f x))) (mul_eq_zero_of_right (eval₂ f x p) hq)

protected instance eval₂.is_semiring_hom {R : Type u} {S : Type v} [semiring R] [comm_semiring S] (f : R →+* S) (x : S) : is_semiring_hom (eval₂ f x) :=
  is_semiring_hom.mk (eval₂_zero f x) (eval₂_one f x) (fun (_x _x_1 : polynomial R) => eval₂_add f x)
    fun (_x _x_1 : polynomial R) => eval₂_mul f x

/-- `eval₂` as a `ring_hom` -/
def eval₂_ring_hom {R : Type u} {S : Type v} [semiring R] [comm_semiring S] (f : R →+* S) (x : S) : polynomial R →+* S :=
  ring_hom.of (eval₂ f x)

@[simp] theorem coe_eval₂_ring_hom {R : Type u} {S : Type v} [semiring R] [comm_semiring S] (f : R →+* S) (x : S) : ⇑(eval₂_ring_hom f x) = eval₂ f x :=
  rfl

theorem eval₂_pow {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [comm_semiring S] (f : R →+* S) (x : S) (n : ℕ) : eval₂ f x (p ^ n) = eval₂ f x p ^ n :=
  ring_hom.map_pow (eval₂_ring_hom f x) p n

theorem eval₂_eq_sum_range {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [comm_semiring S] (f : R →+* S) (x : S) : eval₂ f x p = finset.sum (finset.range (nat_degree p + 1)) fun (i : ℕ) => coe_fn f (coeff p i) * x ^ i := sorry

theorem eval₂_eq_sum_range' {R : Type u} {S : Type v} [semiring R] [comm_semiring S] (f : R →+* S) {p : polynomial R} {n : ℕ} (hn : nat_degree p < n) (x : S) : eval₂ f x p = finset.sum (finset.range n) fun (i : ℕ) => coe_fn f (coeff p i) * x ^ i := sorry

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval {R : Type u} [semiring R] : R → polynomial R → R :=
  eval₂ (ring_hom.id R)

theorem eval_eq_sum {R : Type u} [semiring R] {p : polynomial R} {x : R} : eval x p = finsupp.sum p fun (e : ℕ) (a : R) => a * x ^ e :=
  rfl

@[simp] theorem eval_C {R : Type u} {a : R} [semiring R] {x : R} : eval x (coe_fn C a) = a :=
  eval₂_C (ring_hom.id R) x

@[simp] theorem eval_nat_cast {R : Type u} [semiring R] {x : R} {n : ℕ} : eval x ↑n = ↑n := sorry

@[simp] theorem eval_X {R : Type u} [semiring R] {x : R} : eval x X = x :=
  eval₂_X (ring_hom.id R) x

@[simp] theorem eval_monomial {R : Type u} [semiring R] {x : R} {n : ℕ} {a : R} : eval x (coe_fn (monomial n) a) = a * x ^ n :=
  eval₂_monomial (ring_hom.id R) x

@[simp] theorem eval_zero {R : Type u} [semiring R] {x : R} : eval x 0 = 0 :=
  eval₂_zero (ring_hom.id R) x

@[simp] theorem eval_add {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} {x : R} : eval x (p + q) = eval x p + eval x q :=
  eval₂_add (ring_hom.id R) x

@[simp] theorem eval_one {R : Type u} [semiring R] {x : R} : eval x 1 = 1 :=
  eval₂_one (ring_hom.id R) x

@[simp] theorem eval_bit0 {R : Type u} [semiring R] {p : polynomial R} {x : R} : eval x (bit0 p) = bit0 (eval x p) :=
  eval₂_bit0 (ring_hom.id R) x

@[simp] theorem eval_bit1 {R : Type u} [semiring R] {p : polynomial R} {x : R} : eval x (bit1 p) = bit1 (eval x p) :=
  eval₂_bit1 (ring_hom.id R) x

@[simp] theorem eval_smul {R : Type u} [semiring R] (p : polynomial R) (x : R) {s : R} : eval x (s • p) = s • eval x p :=
  eval₂_smul (ring_hom.id R) p x

theorem eval_sum {R : Type u} [semiring R] (p : polynomial R) (f : ℕ → R → polynomial R) (x : R) : eval x (finsupp.sum p f) = finsupp.sum p fun (n : ℕ) (a : R) => eval x (f n a) :=
  eval₂_sum (ring_hom.id R) p f x

theorem eval_finset_sum {R : Type u} {ι : Type y} [semiring R] (s : finset ι) (g : ι → polynomial R) (x : R) : eval x (finset.sum s fun (i : ι) => g i) = finset.sum s fun (i : ι) => eval x (g i) :=
  eval₂_finset_sum (ring_hom.id R) s (fun (i : ι) => g i) x

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root {R : Type u} [semiring R] (p : polynomial R) (a : R)  :=
  eval a p = 0

protected instance is_root.decidable {R : Type u} {a : R} [semiring R] {p : polynomial R} [DecidableEq R] : Decidable (is_root p a) :=
  eq.mpr sorry (_inst_2 (eval a p) 0)

@[simp] theorem is_root.def {R : Type u} {a : R} [semiring R] {p : polynomial R} : is_root p a ↔ eval a p = 0 :=
  iff.rfl

theorem coeff_zero_eq_eval_zero {R : Type u} [semiring R] (p : polynomial R) : coeff p 0 = eval 0 p := sorry

theorem zero_is_root_of_coeff_zero_eq_zero {R : Type u} [semiring R] {p : polynomial R} (hp : coeff p 0 = 0) : is_root p 0 :=
  eq.mp (Eq._oldrec (Eq.refl (coeff p 0 = 0)) (coeff_zero_eq_eval_zero p)) hp

/-- The composition of polynomials as a polynomial. -/
def comp {R : Type u} [semiring R] (p : polynomial R) (q : polynomial R) : polynomial R :=
  eval₂ C q p

theorem comp_eq_sum_left {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} : comp p q = finsupp.sum p fun (e : ℕ) (a : R) => coe_fn C a * q ^ e :=
  rfl

@[simp] theorem comp_X {R : Type u} [semiring R] {p : polynomial R} : comp p X = p := sorry

@[simp] theorem X_comp {R : Type u} [semiring R] {p : polynomial R} : comp X p = p :=
  eval₂_X C p

@[simp] theorem comp_C {R : Type u} {a : R} [semiring R] {p : polynomial R} : comp p (coe_fn C a) = coe_fn C (eval a p) := sorry

@[simp] theorem C_comp {R : Type u} {a : R} [semiring R] {p : polynomial R} : comp (coe_fn C a) p = coe_fn C a :=
  eval₂_C C p

@[simp] theorem comp_zero {R : Type u} [semiring R] {p : polynomial R} : comp p 0 = coe_fn C (eval 0 p) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comp p 0 = coe_fn C (eval 0 p))) (Eq.symm C_0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (comp p (coe_fn C 0) = coe_fn C (eval 0 p))) comp_C))
      (Eq.refl (coe_fn C (eval 0 p))))

@[simp] theorem zero_comp {R : Type u} [semiring R] {p : polynomial R} : comp 0 p = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comp 0 p = 0)) (Eq.symm C_0)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (comp (coe_fn C 0) p = coe_fn C 0)) C_comp)) (Eq.refl (coe_fn C 0)))

@[simp] theorem comp_one {R : Type u} [semiring R] {p : polynomial R} : comp p 1 = coe_fn C (eval 1 p) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comp p 1 = coe_fn C (eval 1 p))) (Eq.symm C_1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (comp p (coe_fn C 1) = coe_fn C (eval 1 p))) comp_C))
      (Eq.refl (coe_fn C (eval 1 p))))

@[simp] theorem one_comp {R : Type u} [semiring R] {p : polynomial R} : comp 1 p = 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (comp 1 p = 1)) (Eq.symm C_1)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (comp (coe_fn C 1) p = coe_fn C 1)) C_comp)) (Eq.refl (coe_fn C 1)))

@[simp] theorem add_comp {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} {r : polynomial R} : comp (p + q) r = comp p r + comp q r :=
  eval₂_add C r

@[simp] theorem mul_comp {R : Type u_1} [comm_semiring R] (p : polynomial R) (q : polynomial R) (r : polynomial R) : comp (p * q) r = comp p r * comp q r :=
  eval₂_mul C r

@[simp] theorem bit0_comp {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} : comp (bit0 p) q = bit0 (comp p q) := sorry

@[simp] theorem bit1_comp {R : Type u} [semiring R] {p : polynomial R} {q : polynomial R} : comp (bit1 p) q = bit1 (comp p q) := sorry

theorem comp_assoc {R : Type u_1} [comm_semiring R] (φ : polynomial R) (ψ : polynomial R) (χ : polynomial R) : comp (comp φ ψ) χ = comp φ (comp ψ χ) := sorry

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : polynomial R → polynomial S :=
  eval₂ (ring_hom.comp C f) X

protected instance is_semiring_hom_C_f {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : is_semiring_hom (⇑C ∘ ⇑f) :=
  is_semiring_hom.comp ⇑f ⇑C

@[simp] theorem map_C {R : Type u} {S : Type v} {a : R} [semiring R] [semiring S] (f : R →+* S) : map f (coe_fn C a) = coe_fn C (coe_fn f a) :=
  eval₂_C (ring_hom.comp C f) X

@[simp] theorem map_X {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : map f X = X :=
  eval₂_X (ring_hom.comp C f) X

@[simp] theorem map_monomial {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) {n : ℕ} {a : R} : map f (coe_fn (monomial n) a) = coe_fn (monomial n) (coe_fn f a) := sorry

@[simp] theorem map_zero {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : map f 0 = 0 :=
  eval₂_zero (ring_hom.comp C f) X

@[simp] theorem map_add {R : Type u} {S : Type v} [semiring R] {p : polynomial R} {q : polynomial R} [semiring S] (f : R →+* S) : map f (p + q) = map f p + map f q :=
  eval₂_add (ring_hom.comp C f) X

@[simp] theorem map_one {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : map f 1 = 1 :=
  eval₂_one (ring_hom.comp C f) X

@[simp] theorem map_nat_cast {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (n : ℕ) : map f ↑n = ↑n := sorry

@[simp] theorem coeff_map {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (n : ℕ) : coeff (map f p) n = coe_fn f (coeff p n) := sorry

theorem map_map {R : Type u} {S : Type v} {T : Type w} [semiring R] [semiring S] (f : R →+* S) [semiring T] (g : S →+* T) (p : polynomial R) : map g (map f p) = map (ring_hom.comp g f) p := sorry

@[simp] theorem map_id {R : Type u} [semiring R] {p : polynomial R} : map (ring_hom.id R) p = p := sorry

theorem eval₂_eq_eval_map {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) {x : S} : eval₂ f x p = eval x (map f p) := sorry

theorem map_injective {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (hf : function.injective ⇑f) : function.injective (map f) := sorry

theorem map_surjective {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (hf : function.surjective ⇑f) : function.surjective (map f) := sorry

theorem map_monic_eq_zero_iff {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] {f : R →+* S} (hp : monic p) : map f p = 0 ↔ ∀ (x : R), coe_fn f x = 0 := sorry

theorem map_monic_ne_zero {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] {f : R →+* S} (hp : monic p) [nontrivial S] : map f p ≠ 0 :=
  fun (h : map f p = 0) => ring_hom.map_one_ne_zero f (iff.mp (map_monic_eq_zero_iff hp) h 1)

-- If the rings were commutative, we could prove this just using `eval₂_mul`.

-- TODO this proof is just a hack job on the proof of `eval₂_mul`,

-- using that `X` is central. It should probably be golfed!

@[simp] theorem map_mul {R : Type u} {S : Type v} [semiring R] {p : polynomial R} {q : polynomial R} [semiring S] (f : R →+* S) : map f (p * q) = map f p * map f q := sorry

protected instance map.is_semiring_hom {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : is_semiring_hom (map f) :=
  is_semiring_hom.mk (eval₂_zero (ring_hom.comp C f) X) (eval₂_one (ring_hom.comp C f) X)
    (fun (_x _x_1 : polynomial R) => eval₂_add (ring_hom.comp C f) X) fun (_x _x_1 : polynomial R) => map_mul f

/-- `polynomial.map` as a `ring_hom` -/
def map_ring_hom {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : polynomial R →+* polynomial S :=
  ring_hom.mk (map f) sorry sorry sorry sorry

@[simp] theorem coe_map_ring_hom {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) : ⇑(map_ring_hom f) = map f :=
  rfl

theorem map_list_prod {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) (L : List (polynomial R)) : map f (list.prod L) = list.prod (list.map (map f) L) :=
  Eq.symm (list.prod_hom L (monoid_hom.of (map f)))

@[simp] theorem map_pow {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (n : ℕ) : map f (p ^ n) = map f p ^ n :=
  is_monoid_hom.map_pow (map f) p n

theorem mem_map_range {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) {p : polynomial S} : p ∈ set.range (map f) ↔ ∀ (n : ℕ), coeff p n ∈ set.range ⇑f := sorry

theorem eval₂_map {R : Type u} {S : Type v} {T : Type w} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) [semiring T] (g : S →+* T) (x : T) : eval₂ g x (map f p) = eval₂ (ring_hom.comp g f) x p := sorry

theorem eval_map {R : Type u} {S : Type v} [semiring R] {p : polynomial R} [semiring S] (f : R →+* S) (x : S) : eval x (map f p) = eval₂ f x p :=
  eval₂_map f (ring_hom.id S) x

theorem map_sum {R : Type u} {S : Type v} [semiring R] [semiring S] (f : R →+* S) {ι : Type u_1} (g : ι → polynomial R) (s : finset ι) : map f (finset.sum s fun (i : ι) => g i) = finset.sum s fun (i : ι) => map f (g i) :=
  Eq.symm (finset.sum_hom s (map f))

/-!
After having set up the basic theory of `eval₂`, `eval`, `comp`, and `map`,
we make `eval₂` irreducible.

Perhaps we can make the others irreducible too?
-/

-- TODO: Here we need commutativity in both `S` and `T`?

theorem hom_eval₂ {R : Type u} {S : Type v} {T : Type w} [semiring R] (p : polynomial R) [comm_semiring S] [comm_semiring T] (f : R →+* S) (g : S →+* T) (x : S) : coe_fn g (eval₂ f x p) = eval₂ (ring_hom.comp g f) (coe_fn g x) p := sorry

@[simp] theorem eval_mul {R : Type u} [comm_semiring R] {p : polynomial R} {q : polynomial R} {x : R} : eval x (p * q) = eval x p * eval x q :=
  eval₂_mul (ring_hom.id R) x

protected instance eval.is_semiring_hom {R : Type u} [comm_semiring R] {x : R} : is_semiring_hom (eval x) :=
  eval₂.is_semiring_hom (ring_hom.id R) x

@[simp] theorem eval_pow {R : Type u} [comm_semiring R] {p : polynomial R} {x : R} (n : ℕ) : eval x (p ^ n) = eval x p ^ n :=
  eval₂_pow (ring_hom.id R) x n

theorem eval₂_hom {R : Type u} {S : Type v} [comm_semiring R] {p : polynomial R} [comm_semiring S] (f : R →+* S) (x : R) : eval₂ f (coe_fn f x) p = coe_fn f (eval x p) :=
  ring_hom.comp_id f ▸ Eq.symm (hom_eval₂ p (ring_hom.id R) f x)

theorem root_mul_left_of_is_root {R : Type u} {a : R} [comm_semiring R] (p : polynomial R) {q : polynomial R} : is_root q a → is_root (p * q) a := sorry

theorem root_mul_right_of_is_root {R : Type u} {a : R} [comm_semiring R] {p : polynomial R} (q : polynomial R) : is_root p a → is_root (p * q) a := sorry

/--
Polynomial evaluation commutes with finset.prod
-/
theorem eval_prod {R : Type u} [comm_semiring R] {ι : Type u_1} (s : finset ι) (p : ι → polynomial R) (x : R) : eval x (finset.prod s fun (j : ι) => p j) = finset.prod s fun (j : ι) => eval x (p j) := sorry

theorem map_multiset_prod {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] (f : R →+* S) (m : multiset (polynomial R)) : map f (multiset.prod m) = multiset.prod (multiset.map (map f) m) :=
  Eq.symm (multiset.prod_hom m (monoid_hom.of (map f)))

theorem map_prod {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] (f : R →+* S) {ι : Type u_1} (g : ι → polynomial R) (s : finset ι) : map f (finset.prod s fun (i : ι) => g i) = finset.prod s fun (i : ι) => map f (g i) :=
  Eq.symm (finset.prod_hom s (map f))

theorem support_map_subset {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] (f : R →+* S) (p : polynomial R) : finsupp.support (map f p) ⊆ finsupp.support p := sorry

theorem map_comp {R : Type u} {S : Type v} [comm_semiring R] [comm_semiring S] (f : R →+* S) (p : polynomial R) (q : polynomial R) : map f (comp p q) = comp (map f p) (map f q) := sorry

-- @[simp]

-- lemma C_eq_int_cast (n : ℤ) : C ↑n = (n : polynomial R) :=

-- (C : R →+* _).map_int_cast n

theorem C_neg {R : Type u} {a : R} [ring R] : coe_fn C (-a) = -coe_fn C a :=
  ring_hom.map_neg C a

theorem C_sub {R : Type u} {a : R} {b : R} [ring R] : coe_fn C (a - b) = coe_fn C a - coe_fn C b :=
  ring_hom.map_sub C a b

protected instance map.is_ring_hom {R : Type u} [ring R] {S : Type u_1} [ring S] (f : R →+* S) : is_ring_hom (map f) :=
  is_ring_hom.of_semiring (map f)

@[simp] theorem map_sub {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} {S : Type u_1} [ring S] (f : R →+* S) : map f (p - q) = map f p - map f q :=
  is_ring_hom.map_sub (map f)

@[simp] theorem map_neg {R : Type u} [ring R] {p : polynomial R} {S : Type u_1} [ring S] (f : R →+* S) : map f (-p) = -map f p :=
  is_ring_hom.map_neg (map f)

@[simp] theorem map_int_cast {R : Type u} [ring R] {S : Type u_1} [ring S] (f : R →+* S) (n : ℤ) : map f ↑n = ↑n :=
  ring_hom.map_int_cast (ring_hom.of (map f)) n

@[simp] theorem eval_int_cast {R : Type u} [ring R] {n : ℤ} {x : R} : eval x ↑n = ↑n := sorry

@[simp] theorem eval₂_neg {R : Type u} [ring R] {p : polynomial R} {S : Type u_1} [ring S] (f : R →+* S) {x : S} : eval₂ f x (-p) = -eval₂ f x p := sorry

@[simp] theorem eval₂_sub {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} {S : Type u_1} [ring S] (f : R →+* S) {x : S} : eval₂ f x (p - q) = eval₂ f x p - eval₂ f x q := sorry

@[simp] theorem eval_neg {R : Type u} [ring R] (p : polynomial R) (x : R) : eval x (-p) = -eval x p :=
  eval₂_neg (ring_hom.id R)

@[simp] theorem eval_sub {R : Type u} [ring R] (p : polynomial R) (q : polynomial R) (x : R) : eval x (p - q) = eval x p - eval x q :=
  eval₂_sub (ring_hom.id R)

theorem root_X_sub_C {R : Type u} {a : R} {b : R} [ring R] : is_root (X - coe_fn C a) b ↔ a = b := sorry

@[simp] theorem neg_comp {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} : comp (-p) q = -comp p q :=
  eval₂_neg C

@[simp] theorem sub_comp {R : Type u} [ring R] {p : polynomial R} {q : polynomial R} {r : polynomial R} : comp (p - q) r = comp p r - comp q r :=
  eval₂_sub C

protected instance eval₂.is_ring_hom {R : Type u} [comm_ring R] {S : Type u_1} [comm_ring S] (f : R →+* S) {x : S} : is_ring_hom (eval₂ f x) :=
  is_ring_hom.of_semiring (eval₂ f x)

protected instance eval.is_ring_hom {R : Type u} [comm_ring R] {x : R} : is_ring_hom (eval x) :=
  eval₂.is_ring_hom (ring_hom.id R)

