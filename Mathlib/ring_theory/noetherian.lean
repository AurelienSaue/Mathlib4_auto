/-
Copyright (c) 2018 Mario Carneiro and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.algebraic_geometry.prime_spectrum
import Mathlib.data.multiset.finset_ops
import Mathlib.linear_algebra.linear_independent
import Mathlib.order.order_iso_nat
import Mathlib.order.compactly_generated
import Mathlib.ring_theory.ideal.operations
import Mathlib.PostPort

universes u_1 u_2 u_3 l 

namespace Mathlib

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodule M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `fg N : Prop` is the assertion that `N` is finitely generated as an `R`-module.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

namespace submodule


/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def fg {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] (N : submodule R M) :=
  ∃ (S : finset M), span R ↑S = N

theorem fg_def {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] {N : submodule R M} : fg N ↔ ∃ (S : set M), set.finite S ∧ span R S = N := sorry

/-- Nakayama's Lemma. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2, Stacks 00DV -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type u_1} [comm_ring R] {M : Type u_2} [add_comm_group M] [module R M] (I : ideal R) (N : submodule R M) (hn : fg N) (hin : N ≤ I • N) : ∃ (r : R), r - 1 ∈ I ∧ ∀ (n : M), n ∈ N → r • n = 0 := sorry

theorem fg_bot {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] : fg ⊥ :=
  Exists.intro ∅
    (eq.mpr (id (Eq._oldrec (Eq.refl (span R ↑∅ = ⊥)) finset.coe_empty))
      (eq.mpr (id (Eq._oldrec (Eq.refl (span R ∅ = ⊥)) span_empty)) (Eq.refl ⊥)))

theorem fg_sup {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] {N₁ : submodule R M} {N₂ : submodule R M} (hN₁ : fg N₁) (hN₂ : fg N₂) : fg (N₁ ⊔ N₂) := sorry

theorem fg_map {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] {P : Type u_3} [add_comm_monoid P] [semimodule R P] {f : linear_map R M P} {N : submodule R M} (hs : fg N) : fg (map f N) := sorry

theorem fg_of_fg_map {R : Type u_1} {M : Type u_2} {P : Type u_3} [ring R] [add_comm_group M] [module R M] [add_comm_group P] [module R P] (f : linear_map R M P) (hf : linear_map.ker f = ⊥) {N : submodule R M} (hfn : fg (map f N)) : fg N := sorry

theorem fg_top {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] (N : submodule R M) : fg ⊤ ↔ fg N := sorry

theorem fg_of_linear_equiv {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] {P : Type u_3} [add_comm_monoid P] [semimodule R P] (e : linear_equiv R M P) (h : fg ⊤) : fg ⊤ :=
  linear_equiv.range (linear_equiv.symm e) ▸ map_top ↑(linear_equiv.symm e) ▸ fg_map h

theorem fg_prod {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] {P : Type u_3} [add_comm_monoid P] [semimodule R P] {sb : submodule R M} {sc : submodule R P} (hsb : fg sb) (hsc : fg sc) : fg (prod sb sc) := sorry

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker {R : Type u_1} {M : Type u_2} {P : Type u_3} [ring R] [add_comm_group M] [module R M] [add_comm_group P] [module R P] (f : linear_map R M P) {s : submodule R M} (hs1 : fg (map f s)) (hs2 : fg (s ⊓ linear_map.ker f)) : fg s := sorry

theorem singleton_span_is_compact_element {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] (x : M) : complete_lattice.is_compact_element (span R (singleton x)) := sorry

/-- Finitely generated submodules are precisely compact elements in the submodule lattice -/
theorem fg_iff_compact {R : Type u_1} {M : Type u_2} [semiring R] [add_comm_monoid M] [semimodule R M] (s : submodule R M) : fg s ↔ complete_lattice.is_compact_element s := sorry

end submodule


/--
`is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class is_noetherian (R : Type u_1) (M : Type u_2) [semiring R] [add_comm_monoid M] [semimodule R M] 
where
  noetherian : ∀ (s : submodule R M), submodule.fg s

theorem is_noetherian_submodule {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {N : submodule R M} : is_noetherian R ↥N ↔ ∀ (s : submodule R M), s ≤ N → submodule.fg s := sorry

theorem is_noetherian_submodule_left {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {N : submodule R M} : is_noetherian R ↥N ↔ ∀ (s : submodule R M), submodule.fg (N ⊓ s) := sorry

theorem is_noetherian_submodule_right {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] {N : submodule R M} : is_noetherian R ↥N ↔ ∀ (s : submodule R M), submodule.fg (s ⊓ N) := sorry

protected instance is_noetherian_submodule' {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] [is_noetherian R M] (N : submodule R M) : is_noetherian R ↥N :=
  iff.mpr is_noetherian_submodule fun (_x : submodule R M) (_x_1 : _x ≤ N) => is_noetherian.noetherian _x

theorem is_noetherian_of_surjective {R : Type u_1} (M : Type u_2) {P : Type u_3} [ring R] [add_comm_group M] [add_comm_group P] [module R M] [module R P] (f : linear_map R M P) (hf : linear_map.range f = ⊤) [is_noetherian R M] : is_noetherian R P := sorry

theorem is_noetherian_of_linear_equiv {R : Type u_1} {M : Type u_2} {P : Type u_3} [ring R] [add_comm_group M] [add_comm_group P] [module R M] [module R P] (f : linear_equiv R M P) [is_noetherian R M] : is_noetherian R P :=
  is_noetherian_of_surjective M (linear_equiv.to_linear_map f) (linear_equiv.range f)

theorem is_noetherian_of_injective {R : Type u_1} {M : Type u_2} {P : Type u_3} [ring R] [add_comm_group M] [add_comm_group P] [module R M] [module R P] [is_noetherian R P] (f : linear_map R M P) (hf : linear_map.ker f = ⊥) : is_noetherian R M :=
  is_noetherian_of_linear_equiv (linear_equiv.symm (linear_equiv.of_injective f hf))

theorem fg_of_injective {R : Type u_1} {M : Type u_2} {P : Type u_3} [ring R] [add_comm_group M] [add_comm_group P] [module R M] [module R P] [is_noetherian R P] {N : submodule R M} (f : linear_map R M P) (hf : linear_map.ker f = ⊥) : submodule.fg N :=
  is_noetherian.noetherian N

protected instance is_noetherian_prod {R : Type u_1} {M : Type u_2} {P : Type u_3} [ring R] [add_comm_group M] [add_comm_group P] [module R M] [module R P] [is_noetherian R M] [is_noetherian R P] : is_noetherian R (M × P) :=
  is_noetherian.mk
    fun (s : submodule R (M × P)) =>
      submodule.fg_of_fg_map_of_fg_inf_ker (linear_map.snd R M P)
        (is_noetherian.noetherian (submodule.map (linear_map.snd R M P) s))
        ((fun (this : s ⊓ linear_map.ker (linear_map.snd R M P) ≤ linear_map.range (linear_map.inl R M P)) =>
            linear_map.map_comap_eq_self this ▸
              submodule.fg_map
                (is_noetherian.noetherian
                  (submodule.comap (linear_map.inl R M P) (s ⊓ linear_map.ker (linear_map.snd R M P)))))
          fun (x : M × P) (_x : x ∈ s ⊓ linear_map.ker (linear_map.snd R M P)) => sorry)

protected instance is_noetherian_pi {R : Type u_1} {ι : Type u_2} {M : ι → Type u_3} [ring R] [(i : ι) → add_comm_group (M i)] [(i : ι) → module R (M i)] [fintype ι] [∀ (i : ι), is_noetherian R (M i)] : is_noetherian R ((i : ι) → M i) := sorry

theorem is_noetherian_iff_well_founded {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] : is_noetherian R M ↔ well_founded gt := sorry

theorem well_founded_submodule_gt (R : Type u_1) (M : Type u_2) [ring R] [add_comm_group M] [module R M] [is_noetherian R M] : well_founded gt :=
  iff.mp is_noetherian_iff_well_founded

theorem finite_of_linear_independent {R : Type u_1} {M : Type u_2} [comm_ring R] [nontrivial R] [add_comm_group M] [module R M] [is_noetherian R M] {s : set M} (hs : linear_independent R coe) : set.finite s := sorry

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them. -/
theorem set_has_maximal_iff_noetherian {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] : (∀ (a : set (submodule R M)),
    set.nonempty a → ∃ (M' : submodule R M), ∃ (H : M' ∈ a), ∀ (I : submodule R M), I ∈ a → M' ≤ I → I = M') ↔
  is_noetherian R M := sorry

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem is_noetherian.induction {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] [is_noetherian R M] {P : submodule R M → Prop} (hgt : ∀ (I : submodule R M), (∀ (J : submodule R M), J > I → P J) → P I) (I : submodule R M) : P I :=
  well_founded.recursion (well_founded_submodule_gt R M) I hgt

/--
A ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
def is_noetherian_ring (R : Type u_1) [ring R] :=
  is_noetherian R R

protected instance is_noetherian_ring.to_is_noetherian {R : Type u_1} [ring R] [is_noetherian_ring R] : is_noetherian R R :=
  id

protected instance ring.is_noetherian_of_fintype (R : Type u_1) (M : Type u_2) [fintype M] [ring R] [add_comm_group M] [module R M] : is_noetherian R M :=
  let _inst : (p : Prop) → Decidable p := classical.dec;
  is_noetherian.mk
    fun (s : submodule R M) =>
      Exists.intro (set.to_finset ↑s)
        (eq.mpr (id (Eq._oldrec (Eq.refl (submodule.span R ↑(set.to_finset ↑s) = s)) (set.coe_to_finset ↑s)))
          (eq.mpr (id (Eq._oldrec (Eq.refl (submodule.span R ↑s = s)) (submodule.span_eq s))) (Eq.refl s)))

theorem ring.is_noetherian_of_zero_eq_one {R : Type u_1} [ring R] (h01 : 0 = 1) : is_noetherian_ring R :=
  ring.is_noetherian_of_fintype R R

theorem is_noetherian_of_submodule_of_noetherian (R : Type u_1) (M : Type u_2) [ring R] [add_comm_group M] [module R M] (N : submodule R M) (h : is_noetherian R M) : is_noetherian R ↥N :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_noetherian R ↥N)) (propext is_noetherian_iff_well_founded)))
    (order_embedding.well_founded (order_embedding.dual (submodule.map_subtype.order_embedding N))
      (eq.mp (Eq._oldrec (Eq.refl (is_noetherian R M)) (propext is_noetherian_iff_well_founded)) h))

theorem is_noetherian_of_quotient_of_noetherian (R : Type u_1) [ring R] (M : Type u_2) [add_comm_group M] [module R M] (N : submodule R M) (h : is_noetherian R M) : is_noetherian R (submodule.quotient N) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (is_noetherian R (submodule.quotient N))) (propext is_noetherian_iff_well_founded)))
    (order_embedding.well_founded (order_embedding.dual (submodule.comap_mkq.order_embedding N))
      (eq.mp (Eq._oldrec (Eq.refl (is_noetherian R M)) (propext is_noetherian_iff_well_founded)) h))

theorem is_noetherian_of_fg_of_noetherian {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] (N : submodule R M) [is_noetherian_ring R] (hN : submodule.fg N) : is_noetherian R ↥N := sorry

theorem is_noetherian_of_fg_of_noetherian' {R : Type u_1} {M : Type u_2} [ring R] [add_comm_group M] [module R M] [is_noetherian_ring R] (h : submodule.fg ⊤) : is_noetherian R M :=
  (fun (this : is_noetherian R ↥⊤) => is_noetherian_of_linear_equiv (linear_equiv.of_top ⊤ rfl))
    (is_noetherian_of_fg_of_noetherian ⊤ h)

/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem is_noetherian_span_of_finite (R : Type u_1) {M : Type u_2} [ring R] [add_comm_group M] [module R M] [is_noetherian_ring R] {A : set M} (hA : set.finite A) : is_noetherian R ↥(submodule.span R A) :=
  is_noetherian_of_fg_of_noetherian (submodule.span R A)
    (iff.mpr submodule.fg_def (Exists.intro A { left := hA, right := rfl }))

theorem is_noetherian_ring_of_surjective (R : Type u_1) [comm_ring R] (S : Type u_2) [comm_ring S] (f : R →+* S) (hf : function.surjective ⇑f) [H : is_noetherian_ring R] : is_noetherian_ring S := sorry

protected instance is_noetherian_ring_set_range {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] (f : R →+* S) [is_noetherian_ring R] : is_noetherian_ring ↥(set.range ⇑f) :=
  is_noetherian_ring_of_surjective R (↥(set.range ⇑f)) (ring_hom.cod_restrict f (set.range ⇑f) set.mem_range_self)
    set.surjective_onto_range

protected instance is_noetherian_ring_range {R : Type u_1} [comm_ring R] {S : Type u_2} [comm_ring S] (f : R →+* S) [is_noetherian_ring R] : is_noetherian_ring ↥(ring_hom.range f) :=
  is_noetherian_ring_of_surjective R (↥(ring_hom.range f))
    (ring_hom.cod_restrict' f (ring_hom.range f) (ring_hom.mem_range_self f)) (ring_hom.surjective_onto_range f)

theorem is_noetherian_ring_of_ring_equiv (R : Type u_1) [comm_ring R] {S : Type u_2} [comm_ring S] (f : R ≃+* S) [is_noetherian_ring R] : is_noetherian_ring S :=
  is_noetherian_ring_of_surjective R S (ring_equiv.to_ring_hom f) (equiv.surjective (ring_equiv.to_equiv f))

namespace submodule


theorem fg_mul {R : Type u_1} {A : Type u_2} [comm_ring R] [ring A] [algebra R A] (M : submodule R A) (N : submodule R A) (hm : fg M) (hn : fg N) : fg (M * N) := sorry

theorem fg_pow {R : Type u_1} {A : Type u_2} [comm_ring R] [ring A] [algebra R A] (M : submodule R A) (h : fg M) (n : ℕ) : fg (M ^ n) := sorry

end submodule


/--In a noetherian ring, every ideal contains a product of prime ideals
([samuel, § 3.3, Lemma 3])-/
theorem exists_prime_spectrum_prod_le {R : Type u_1} [comm_ring R] [is_noetherian_ring R] (I : ideal R) : ∃ (Z : multiset (prime_spectrum R)), multiset.prod (multiset.map coe Z) ≤ I := sorry

/--In a noetherian integral domain which is not a field, every non-zero ideal contains a non-zero
  product of prime ideals; in a field, the whole ring is a non-zero ideal containing only 0 as product
  or prime ideals ([samuel, § 3.3, Lemma 3])
-/
theorem exists_prime_spectrum_prod_le_and_ne_bot_of_domain {A : Type u_2} [integral_domain A] [is_noetherian_ring A] (h_fA : ¬is_field A) {I : ideal A} (h_nzI : I ≠ ⊥) : ∃ (Z : multiset (prime_spectrum A)), multiset.prod (multiset.map coe Z) ≤ I ∧ multiset.prod (multiset.map coe Z) ≠ ⊥ := sorry

