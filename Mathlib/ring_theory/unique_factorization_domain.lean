/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson

-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebra.gcd_monoid
import Mathlib.ring_theory.integral_domain
import Mathlib.ring_theory.noetherian
import Mathlib.PostPort

universes u_2 l u_1 u 

namespace Mathlib

/--

# Unique factorization

## Main Definitions
* `wf_dvd_monoid` holds for `monoid`s for which a strict divisibility relation is
  well-founded.
* `unique_factorization_monoid` holds for `wf_dvd_monoid`s where
  `irreducible` is equivalent to `prime`

## To do
* set up the complete lattice structure on `factor_set`.

-/
/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class wf_dvd_monoid (α : Type u_2) [comm_monoid_with_zero α] 
where
  well_founded_dvd_not_unit : well_founded dvd_not_unit

protected instance is_noetherian_ring.wf_dvd_monoid {α : Type u_1} [integral_domain α] [is_noetherian_ring α] : wf_dvd_monoid α :=
  wf_dvd_monoid.mk
    (eq.mpr
      ((fun (r r_1 : α → α → Prop) (e_1 : r = r_1) => congr_arg well_founded e_1) dvd_not_unit
        (inv_image gt fun (a : α) => ideal.span (singleton a))
        (funext fun (x : α) => funext fun (x_1 : α) => propext (iff.symm ideal.span_singleton_lt_span_singleton)))
      (inv_image.wf (fun (a : α) => ideal.span (singleton a)) (well_founded_submodule_gt α α)))

namespace wf_dvd_monoid


theorem of_wf_dvd_monoid_associates {α : Type u_1} [comm_monoid_with_zero α] (h : wf_dvd_monoid (associates α)) : wf_dvd_monoid α := sorry

protected instance wf_dvd_monoid_associates {α : Type u_1} [comm_monoid_with_zero α] [wf_dvd_monoid α] : wf_dvd_monoid (associates α) :=
  mk
    (iff.mp
      (surjective.well_founded_iff associates.mk_surjective
        fun (a b : α) =>
          eq.mpr
            (id
              (Eq._oldrec (Eq.refl (dvd_not_unit a b ↔ dvd_not_unit (associates.mk a) (associates.mk b)))
                (propext associates.mk_dvd_not_unit_mk_iff)))
            (iff.refl (dvd_not_unit a b)))
      well_founded_dvd_not_unit)

theorem well_founded_associates {α : Type u_1} [comm_monoid_with_zero α] [wf_dvd_monoid α] : well_founded Less :=
  subrelation.wf (fun (x y : associates α) => associates.dvd_not_unit_of_lt) well_founded_dvd_not_unit

theorem exists_irreducible_factor {α : Type u_1} [comm_monoid_with_zero α] [wf_dvd_monoid α] {a : α} (ha : ¬is_unit a) (ha0 : a ≠ 0) : ∃ (i : α), irreducible i ∧ i ∣ a := sorry

theorem induction_on_irreducible {α : Type u_1} [comm_monoid_with_zero α] [wf_dvd_monoid α] {P : α → Prop} (a : α) (h0 : P 0) (hu : ∀ (u : α), is_unit u → P u) (hi : ∀ (a i : α), a ≠ 0 → irreducible i → P a → P (i * a)) : P a := sorry

theorem exists_factors {α : Type u_1} [comm_monoid_with_zero α] [wf_dvd_monoid α] (a : α) : a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → irreducible b) ∧ associated (multiset.prod f) a := sorry

end wf_dvd_monoid


theorem wf_dvd_monoid.of_well_founded_associates {α : Type u_1} [comm_cancel_monoid_with_zero α] (h : well_founded Less) : wf_dvd_monoid α := sorry

theorem wf_dvd_monoid.iff_well_founded_associates {α : Type u_1} [comm_cancel_monoid_with_zero α] : wf_dvd_monoid α ↔ well_founded Less :=
  { mp := wf_dvd_monoid.well_founded_associates, mpr := wf_dvd_monoid.of_well_founded_associates }

/-- unique factorization monoids.

These are defined as `comm_cancel_monoid_with_zero`s with well-founded strict divisibility
relations, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_exists_unique_irreducible_factors`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factors`

-/
class unique_factorization_monoid (α : Type u_2) [comm_cancel_monoid_with_zero α] 
extends wf_dvd_monoid α
where
  irreducible_iff_prime : ∀ {a : α}, irreducible a ↔ prime a

protected instance ufm_of_gcd_of_wf_dvd_monoid {α : Type u_1} [nontrivial α] [comm_cancel_monoid_with_zero α] [wf_dvd_monoid α] [gcd_monoid α] : unique_factorization_monoid α :=
  unique_factorization_monoid.mk fun (_x : α) => gcd_monoid.irreducible_iff_prime

protected instance associates.ufm {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] : unique_factorization_monoid (associates α) :=
  unique_factorization_monoid.mk
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (∀ {a : associates α}, irreducible a ↔ prime a))
          (Eq.symm (propext associates.irreducible_iff_prime_iff))))
      unique_factorization_monoid.irreducible_iff_prime)

namespace unique_factorization_monoid


theorem exists_prime_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] (a : α) : a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → prime b) ∧ associated (multiset.prod f) a := sorry

theorem induction_on_prime {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] {P : α → Prop} (a : α) (h₁ : P 0) (h₂ : ∀ (x : α), is_unit x → P x) (h₃ : ∀ (a p : α), a ≠ 0 → prime p → P a → P (p * a)) : P a := sorry

theorem factors_unique {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] {f : multiset α} {g : multiset α} : (∀ (x : α), x ∈ f → irreducible x) →
  (∀ (x : α), x ∈ g → irreducible x) → associated (multiset.prod f) (multiset.prod g) → multiset.rel associated f g := sorry

end unique_factorization_monoid


theorem prime_factors_unique {α : Type u_1} [comm_cancel_monoid_with_zero α] {f : multiset α} {g : multiset α} : (∀ (x : α), x ∈ f → prime x) →
  (∀ (x : α), x ∈ g → prime x) → associated (multiset.prod f) (multiset.prod g) → multiset.rel associated f g := sorry

/-- If an irreducible has a prime factorization,
  then it is an associate of one of its prime factors. -/
theorem prime_factors_irreducible {α : Type u_1} [comm_cancel_monoid_with_zero α] {a : α} {f : multiset α} (ha : irreducible a) (pfa : (∀ (b : α), b ∈ f → prime b) ∧ associated (multiset.prod f) a) : ∃ (p : α), associated a p ∧ f = p ::ₘ 0 := sorry

theorem wf_dvd_monoid.of_exists_prime_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] (pf : ∀ (a : α), a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → prime b) ∧ associated (multiset.prod f) a) : wf_dvd_monoid α := sorry

theorem irreducible_iff_prime_of_exists_prime_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] (pf : ∀ (a : α), a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → prime b) ∧ associated (multiset.prod f) a) {p : α} : irreducible p ↔ prime p := sorry

theorem unique_factorization_monoid.of_exists_prime_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] (pf : ∀ (a : α), a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → prime b) ∧ associated (multiset.prod f) a) : unique_factorization_monoid α :=
  unique_factorization_monoid.mk fun (_x : α) => irreducible_iff_prime_of_exists_prime_factors pf

theorem unique_factorization_monoid.iff_exists_prime_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] : unique_factorization_monoid α ↔
  ∀ (a : α), a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → prime b) ∧ associated (multiset.prod f) a :=
  { mp := fun (h : unique_factorization_monoid α) => unique_factorization_monoid.exists_prime_factors,
    mpr := unique_factorization_monoid.of_exists_prime_factors }

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] (eif : ∀ (a : α), a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → irreducible b) ∧ associated (multiset.prod f) a) (uif : ∀ (f g : multiset α),
  (∀ (x : α), x ∈ f → irreducible x) →
    (∀ (x : α), x ∈ g → irreducible x) → associated (multiset.prod f) (multiset.prod g) → multiset.rel associated f g) (p : α) : irreducible p ↔ prime p := sorry

theorem unique_factorization_monoid.of_exists_unique_irreducible_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] (eif : ∀ (a : α), a ≠ 0 → ∃ (f : multiset α), (∀ (b : α), b ∈ f → irreducible b) ∧ associated (multiset.prod f) a) (uif : ∀ (f g : multiset α),
  (∀ (x : α), x ∈ f → irreducible x) →
    (∀ (x : α), x ∈ g → irreducible x) → associated (multiset.prod f) (multiset.prod g) → multiset.rel associated f g) : unique_factorization_monoid α := sorry

namespace unique_factorization_monoid


/-- Noncomputably determines the multiset of prime factors. -/
def factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] (a : α) : multiset α :=
  dite (a = 0) (fun (h : a = 0) => 0)
    fun (h : ¬a = 0) => multiset.map (⇑normalize) (classical.some (exists_prime_factors a h))

theorem factors_prod {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {a : α} (ane0 : a ≠ 0) : associated (multiset.prod (factors a)) a := sorry

theorem prime_of_factor {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {a : α} (x : α) : x ∈ factors a → prime x := sorry

theorem irreducible_of_factor {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {a : α} (x : α) : x ∈ factors a → irreducible x :=
  fun (h : x ∈ factors a) => irreducible_of_prime (prime_of_factor x h)

theorem normalize_factor {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {a : α} (x : α) : x ∈ factors a → coe_fn normalize x = x := sorry

theorem factors_irreducible {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {a : α} (ha : irreducible a) : factors a = coe_fn normalize a ::ₘ 0 := sorry

theorem exists_mem_factors_of_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {a : α} {p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a → ∃ (q : α), ∃ (H : q ∈ factors a), associated p q := sorry

@[simp] theorem factors_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] : factors 0 = 0 :=
  dif_pos rfl

@[simp] theorem factors_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] : factors 1 = 0 := sorry

@[simp] theorem factors_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {x : α} {y : α} (hx : x ≠ 0) (hy : y ≠ 0) : factors (x * y) = factors x + factors y := sorry

@[simp] theorem factors_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {x : α} (n : ℕ) : factors (x ^ n) = n •ℕ factors x := sorry

theorem dvd_iff_factors_le_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq α] [nontrivial α] [normalization_monoid α] [unique_factorization_monoid α] {x : α} {y : α} (hx : x ≠ 0) (hy : y ≠ 0) : x ∣ y ↔ factors x ≤ factors y := sorry

end unique_factorization_monoid


namespace unique_factorization_monoid


/-- Noncomputably defines a `normalization_monoid` structure on a `unique_factorization_monoid`. -/
protected def normalization_monoid {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [unique_factorization_monoid α] : normalization_monoid α :=
  normalization_monoid_of_monoid_hom_right_inverse
    (monoid_hom.mk
      (fun (a : associates α) => ite (a = 0) 0 (multiset.prod (multiset.map (classical.some sorry) (factors a)))) sorry
      sorry)
    sorry

protected instance normalization_monoid.inhabited {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] [unique_factorization_monoid α] : Inhabited (normalization_monoid α) :=
  { default := unique_factorization_monoid.normalization_monoid }

end unique_factorization_monoid


namespace unique_factorization_monoid


theorem no_factors_of_no_prime_factors {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] {a : R} {b : R} (ha : a ≠ 0) (h : ∀ {d : R}, d ∣ a → d ∣ b → ¬prime d) {d : R} : d ∣ a → d ∣ b → is_unit d := sorry

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
theorem dvd_of_dvd_mul_left_of_no_prime_factors {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] {a : R} {b : R} {c : R} (ha : a ≠ 0) : (∀ {d : R}, d ∣ a → d ∣ c → ¬prime d) → a ∣ b * c → a ∣ b := sorry

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] {a : R} {b : R} {c : R} (ha : a ≠ 0) (no_factors : ∀ {d : R}, d ∣ a → d ∣ b → ¬prime d) : a ∣ b * c → a ∣ c := sorry

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
theorem exists_reduced_factors {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] (a : R) (H : a ≠ 0) (b : R) : ∃ (a' : R), ∃ (b' : R), ∃ (c' : R), (∀ {d : R}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b := sorry

theorem exists_reduced_factors' {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] (a : R) (b : R) (hb : b ≠ 0) : ∃ (a' : R), ∃ (b' : R), ∃ (c' : R), (∀ {d : R}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b := sorry

theorem le_multiplicity_iff_repeat_le_factors {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] [nontrivial R] [normalization_monoid R] [DecidableEq R] [DecidableRel has_dvd.dvd] {a : R} {b : R} {n : ℕ} (ha : irreducible a) (hb : b ≠ 0) : ↑n ≤ multiplicity a b ↔ multiset.repeat (coe_fn normalize a) n ≤ factors b := sorry

theorem multiplicity_eq_count_factors {R : Type u_2} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R] [nontrivial R] [normalization_monoid R] [DecidableEq R] [DecidableRel has_dvd.dvd] {a : R} {b : R} (ha : irreducible a) (hb : b ≠ 0) : multiplicity a b = ↑(multiset.count (coe_fn normalize a) (factors b)) := sorry

end unique_factorization_monoid


namespace associates


/-- `factor_set α` representation elements of unique factorization domain as multisets.
`multiset α` produced by `factors` are only unique up to associated elements, while the multisets in
`factor_set α` are unqiue by equality and restricted to irreducible elements. This gives us a
representation of each element as a unique multisets (or the added ⊤ for 0), which has a complete
lattice struture. Infimum is the greatest common divisor and supremum is the least common multiple.
-/
def factor_set (α : Type u) [comm_cancel_monoid_with_zero α]  :=
  with_top (multiset (Subtype fun (a : associates α) => irreducible a))

theorem factor_set.coe_add {α : Type u_1} [comm_cancel_monoid_with_zero α] {a : multiset (Subtype fun (a : associates α) => irreducible a)} {b : multiset (Subtype fun (a : associates α) => irreducible a)} : ↑(a + b) = ↑a + ↑b := sorry

theorem factor_set.sup_add_inf_eq_add {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq (associates α)] (a : factor_set α) (b : factor_set α) : a ⊔ b + a ⊓ b = a + b := sorry

/-- Evaluates the product of a `factor_set` to be the product of the corresponding multiset,
  or `0` if there is none. -/
def factor_set.prod {α : Type u_1} [comm_cancel_monoid_with_zero α] : factor_set α → associates α :=
  sorry

@[simp] theorem prod_top {α : Type u_1} [comm_cancel_monoid_with_zero α] : factor_set.prod ⊤ = 0 :=
  rfl

@[simp] theorem prod_coe {α : Type u_1} [comm_cancel_monoid_with_zero α] {s : multiset (Subtype fun (a : associates α) => irreducible a)} : factor_set.prod ↑s = multiset.prod (multiset.map coe s) :=
  rfl

@[simp] theorem prod_add {α : Type u_1} [comm_cancel_monoid_with_zero α] (a : factor_set α) (b : factor_set α) : factor_set.prod (a + b) = factor_set.prod a * factor_set.prod b := sorry

theorem prod_mono {α : Type u_1} [comm_cancel_monoid_with_zero α] {a : factor_set α} {b : factor_set α} : a ≤ b → factor_set.prod a ≤ factor_set.prod b := sorry

/-- `bcount p s` is the multiplicity of `p` in the factor_set `s` (with bundled `p`)-/
def bcount {α : Type u_1} [comm_cancel_monoid_with_zero α] [DecidableEq (associates α)] (p : Subtype fun (a : associates α) => irreducible a) : factor_set α → ℕ :=
  sorry

/-- `count p s` is the multiplicity of the irreducible `p` in the factor_set `s`.

If `p` is not irreducible, `count p s` is defined to be `0`. -/
def count {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [DecidableEq (associates α)] (p : associates α) : factor_set α → ℕ :=
  dite (irreducible p) (fun (hp : irreducible p) => bcount { val := p, property := hp }) fun (hp : ¬irreducible p) => 0

@[simp] theorem count_some {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [DecidableEq (associates α)] {p : associates α} (hp : irreducible p) (s : multiset (Subtype fun (a : associates α) => irreducible a)) : count p (some s) = multiset.count { val := p, property := hp } s := sorry

@[simp] theorem count_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [DecidableEq (associates α)] {p : associates α} (hp : irreducible p) : count p 0 = 0 := sorry

theorem count_reducible {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [DecidableEq (associates α)] {p : associates α} (hp : ¬irreducible p) : count p = 0 :=
  dif_neg hp

/-- membership in a factor_set (bundled version) -/
def bfactor_set_mem {α : Type u_1} [comm_cancel_monoid_with_zero α] : (Subtype fun (a : associates α) => irreducible a) → factor_set α → Prop :=
  sorry

/-- `factor_set_mem p s` is the predicate that the irreducible `p` is a member of `s : factor_set α`.

If `p` is not irreducible, `p` is not a member of any `factor_set`. -/
def factor_set_mem {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] (p : associates α) (s : factor_set α)  :=
  dite (irreducible p) (fun (hp : irreducible p) => bfactor_set_mem { val := p, property := hp } s)
    fun (hp : ¬irreducible p) => False

protected instance factor_set.has_mem {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] : has_mem (associates α) (factor_set α) :=
  has_mem.mk factor_set_mem

@[simp] theorem factor_set_mem_eq_mem {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] (p : associates α) (s : factor_set α) : factor_set_mem p s = (p ∈ s) :=
  rfl

theorem mem_factor_set_top {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] {p : associates α} {hp : irreducible p} : p ∈ ⊤ :=
  id (id (eq.mpr (id (dif_pos hp)) trivial))

theorem mem_factor_set_some {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] {p : associates α} {hp : irreducible p} {l : multiset (Subtype fun (a : associates α) => irreducible a)} : p ∈ ↑l ↔ { val := p, property := hp } ∈ l := sorry

theorem reducible_not_mem_factor_set {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] {p : associates α} (hp : ¬irreducible p) (s : factor_set α) : ¬p ∈ s := sorry

theorem unique' {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] {p : multiset (associates α)} {q : multiset (associates α)} : (∀ (a : associates α), a ∈ p → irreducible a) →
  (∀ (a : associates α), a ∈ q → irreducible a) → multiset.prod p = multiset.prod q → p = q := sorry

theorem prod_le_prod_iff_le {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] {p : multiset (associates α)} {q : multiset (associates α)} (hp : ∀ (a : associates α), a ∈ p → irreducible a) (hq : ∀ (a : associates α), a ∈ q → irreducible a) : multiset.prod p ≤ multiset.prod q ↔ p ≤ q := sorry

/-- This returns the multiset of irreducible factors as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
def factors' {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] (a : α) : multiset (Subtype fun (a : associates α) => irreducible a) :=
  multiset.pmap (fun (a : α) (ha : irreducible a) => { val := associates.mk a, property := sorry })
    (unique_factorization_monoid.factors a) sorry

@[simp] theorem map_subtype_coe_factors' {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] {a : α} : multiset.map coe (factors' a) = multiset.map associates.mk (unique_factorization_monoid.factors a) := sorry

theorem factors'_cong {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] {a : α} {b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : associated a b) : factors' a = factors' b := sorry

/-- This returns the multiset of irreducible factors of an associate as a `factor_set`,
  a multiset of irreducible associates `with_top`. -/
def factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] (a : associates α) : factor_set α :=
  dite (a = 0) (fun (h : a = 0) => ⊤)
    fun (h : ¬a = 0) => quotient.hrec_on a (fun (x : α) (h : ¬quotient.mk x = 0) => some (factors' x)) sorry h

@[simp] theorem factors_0 {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] : factors 0 = ⊤ :=
  dif_pos rfl

@[simp] theorem factors_mk {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] (a : α) (h : a ≠ 0) : factors (associates.mk a) = ↑(factors' a) :=
  dif_neg (mt (iff.mp mk_eq_zero) h)

theorem prod_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] (s : factor_set α) : factors (factor_set.prod s) = s := sorry

@[simp] theorem factors_prod {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] (a : associates α) : factor_set.prod (factors a) = a := sorry

theorem eq_of_factors_eq_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} {b : associates α} (h : factors a = factors b) : a = b := sorry

theorem eq_of_prod_eq_prod {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] {a : factor_set α} {b : factor_set α} (h : factor_set.prod a = factor_set.prod b) : a = b := sorry

@[simp] theorem factors_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] (a : associates α) (b : associates α) : factors (a * b) = factors a + factors b := sorry

theorem factors_mono {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} {b : associates α} : a ≤ b → factors a ≤ factors b := sorry

theorem factors_le {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} {b : associates α} : factors a ≤ factors b ↔ a ≤ b := sorry

theorem prod_le {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] {a : factor_set α} {b : factor_set α} : factor_set.prod a ≤ factor_set.prod b ↔ a ≤ b := sorry

protected instance has_sup {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] : has_sup (associates α) :=
  has_sup.mk fun (a b : associates α) => factor_set.prod (factors a ⊔ factors b)

protected instance has_inf {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] : has_inf (associates α) :=
  has_inf.mk fun (a b : associates α) => factor_set.prod (factors a ⊓ factors b)

protected instance bounded_lattice {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] : bounded_lattice (associates α) :=
  bounded_lattice.mk has_sup.sup partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry has_inf.inf sorry
    sorry sorry order_top.top sorry order_bot.bot sorry

theorem sup_mul_inf {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] (a : associates α) (b : associates α) : (a ⊔ b) * (a ⊓ b) = a * b := sorry

theorem dvd_of_mem_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} {p : associates α} {hp : irreducible p} (hm : p ∈ factors a) : p ∣ a := sorry

theorem dvd_of_mem_factors' {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] {a : α} {p : associates α} {hp : irreducible p} {hz : a ≠ 0} (h_mem : { val := p, property := hp } ∈ factors' a) : p ∣ associates.mk a :=
  dvd_of_mem_factors
    (eq.mpr (id (Eq._oldrec (Eq.refl (p ∈ factors (associates.mk a))) (factors_mk a hz)))
      (iff.mpr mem_factor_set_some h_mem))

theorem mem_factors'_of_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] {a : α} {p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) : { val := associates.mk p, property := iff.mpr (irreducible_mk p) hp } ∈ factors' a := sorry

theorem mem_factors'_iff_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] {a : α} {p : α} (ha0 : a ≠ 0) (hp : irreducible p) : { val := associates.mk p, property := iff.mpr (irreducible_mk p) hp } ∈ factors' a ↔ p ∣ a := sorry

theorem mem_factors_of_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : α} {p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) : associates.mk p ∈ factors (associates.mk a) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (associates.mk p ∈ factors (associates.mk a))) (factors_mk a ha0)))
    (iff.mpr mem_factor_set_some (mem_factors'_of_dvd ha0 hp hd))

theorem mem_factors_iff_dvd {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : α} {p : α} (ha0 : a ≠ 0) (hp : irreducible p) : associates.mk p ∈ factors (associates.mk a) ↔ p ∣ a := sorry

theorem exists_prime_dvd_of_not_inf_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : α} {b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : associates.mk a ⊓ associates.mk b ≠ 1) : ∃ (p : α), prime p ∧ p ∣ a ∧ p ∣ b := sorry

theorem coprime_iff_inf_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : α} {b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) : associates.mk a ⊓ associates.mk b = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬prime d := sorry

theorem factors_prime_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {p : associates α} (hp : irreducible p) (k : ℕ) : factors (p ^ k) = some (multiset.repeat { val := p, property := hp } k) := sorry

theorem prime_pow_dvd_iff_le {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {m : associates α} {p : associates α} (h₁ : m ≠ 0) (h₂ : irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ count p (factors m) := sorry

theorem le_of_count_ne_zero {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {m : associates α} {p : associates α} (h0 : m ≠ 0) (hp : irreducible p) : count p (factors m) ≠ 0 → p ≤ m := sorry

theorem count_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0) {p : associates α} (hp : irreducible p) : count p (factors (a * b)) = count p (factors a) + count p (factors b) := sorry

theorem count_of_coprime {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0) (hab : ∀ (d : associates α), d ∣ a → d ∣ b → ¬prime d) {p : associates α} (hp : irreducible p) : count p (factors a) = 0 ∨ count p (factors b) = 0 := sorry

theorem count_mul_of_coprime {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0) {p : associates α} (hp : irreducible p) (hab : ∀ (d : associates α), d ∣ a → d ∣ b → ¬prime d) : count p (factors a) = 0 ∨ count p (factors a) = count p (factors (a * b)) := sorry

theorem count_mul_of_coprime' {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0) {p : associates α} (hp : irreducible p) (hab : ∀ (d : associates α), d ∣ a → d ∣ b → ¬prime d) : count p (factors (a * b)) = count p (factors a) ∨ count p (factors (a * b)) = count p (factors b) := sorry

theorem dvd_count_of_dvd_count_mul {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} {b : associates α} (ha : a ≠ 0) (hb : b ≠ 0) {p : associates α} (hp : irreducible p) (hab : ∀ (d : associates α), d ∣ a → d ∣ b → ¬prime d) {k : ℕ} (habk : k ∣ count p (factors (a * b))) : k ∣ count p (factors a) := sorry

@[simp] theorem factors_one {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] : factors 1 = 0 :=
  eq_of_prod_eq_prod
    (eq.mpr (id (Eq._oldrec (Eq.refl (factor_set.prod (factors 1) = factor_set.prod 0)) (factors_prod 1)))
      multiset.prod_zero)

@[simp] theorem pow_factors {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} {k : ℕ} : factors (a ^ k) = k •ℕ factors a := sorry

theorem count_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {p : associates α} (hp : irreducible p) (k : ℕ) : count p (factors (a ^ k)) = k * count p (factors a) := sorry

theorem dvd_count_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {p : associates α} (hp : irreducible p) (k : ℕ) : k ∣ count p (factors (a ^ k)) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (k ∣ count p (factors (a ^ k)))) (count_pow ha hp k)))
    (dvd_mul_right k (count p (factors a)))

theorem is_pow_of_dvd_count {α : Type u_1} [comm_cancel_monoid_with_zero α] [dec_irr : (p : associates α) → Decidable (irreducible p)] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] [dec : DecidableEq α] [dec' : DecidableEq (associates α)] {a : associates α} (ha : a ≠ 0) {k : ℕ} (hk : ∀ (p : associates α), irreducible p → k ∣ count p (factors a)) : ∃ (b : associates α), a = b ^ k := sorry

theorem eq_pow_of_mul_eq_pow {α : Type u_1} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α] [nontrivial α] [normalization_monoid α] {a : associates α} {b : associates α} {c : associates α} (ha : a ≠ 0) (hb : b ≠ 0) (hab : ∀ (d : associates α), d ∣ a → d ∣ b → ¬prime d) {k : ℕ} (h : a * b = c ^ k) : ∃ (d : associates α), a = d ^ k := sorry

end associates


/-- `to_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
def unique_factorization_monoid.to_gcd_monoid (α : Type u_1) [comm_cancel_monoid_with_zero α] [nontrivial α] [unique_factorization_monoid α] [normalization_monoid α] [DecidableEq (associates α)] [DecidableEq α] : gcd_monoid α :=
  gcd_monoid.mk norm_unit norm_unit_zero norm_unit_mul norm_unit_coe_units
    (fun (a b : α) => associates.out (associates.mk a ⊓ associates.mk b))
    (fun (a b : α) => associates.out (associates.mk a ⊔ associates.mk b)) sorry sorry sorry sorry sorry sorry sorry

