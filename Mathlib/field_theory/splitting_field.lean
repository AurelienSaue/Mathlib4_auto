/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Definition of splitting fields, and definition of homomorphism into any field that splits
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.ring_theory.adjoin_root
import Mathlib.ring_theory.algebra_tower
import Mathlib.ring_theory.algebraic
import Mathlib.ring_theory.polynomial.default
import Mathlib.field_theory.minpoly
import Mathlib.linear_algebra.finite_dimensional
import Mathlib.tactic.field_simp
import Mathlib.PostPort

universes u v w u_1 u_2 u_3 l 

namespace Mathlib

namespace polynomial


/-- a polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1 -/
def splits {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) (f : polynomial α) :=
  f = 0 ∨ ∀ {g : polynomial β}, irreducible g → g ∣ map i f → degree g = 1

@[simp] theorem splits_zero {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) : splits i 0 :=
  Or.inl rfl

@[simp] theorem splits_C {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) (a : α) : splits i (coe_fn C a) := sorry

theorem splits_of_degree_eq_one {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} (hf : degree f = 1) : splits i f := sorry

theorem splits_of_degree_le_one {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} (hf : degree f ≤ 1) : splits i f := sorry

theorem splits_mul {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {g : polynomial α} (hf : splits i f) (hg : splits i g) : splits i (f * g) := sorry

theorem splits_of_splits_mul {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {g : polynomial α} (hfg : f * g ≠ 0) (h : splits i (f * g)) : splits i f ∧ splits i g := sorry

theorem splits_of_splits_of_dvd {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {g : polynomial α} (hf0 : f ≠ 0) (hf : splits i f) (hgf : g ∣ f) : splits i g := sorry

theorem splits_of_splits_gcd_left {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {g : polynomial α} (hf0 : f ≠ 0) (hf : splits i f) : splits i (euclidean_domain.gcd f g) :=
  splits_of_splits_of_dvd i hf0 hf (euclidean_domain.gcd_dvd_left f g)

theorem splits_of_splits_gcd_right {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {g : polynomial α} (hg0 : g ≠ 0) (hg : splits i g) : splits i (euclidean_domain.gcd f g) :=
  splits_of_splits_of_dvd i hg0 hg (euclidean_domain.gcd_dvd_right f g)

theorem splits_map_iff {α : Type u} {β : Type v} {γ : Type w} [field α] [field β] [field γ] (i : α →+* β) (j : β →+* γ) {f : polynomial α} : splits j (map i f) ↔ splits (ring_hom.comp j i) f := sorry

theorem splits_one {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) : splits i 1 :=
  splits_C i 1

theorem splits_of_is_unit {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {u : polynomial α} (hu : is_unit u) : splits i u :=
  splits_of_splits_of_dvd i one_ne_zero (splits_one i) (iff.mp is_unit_iff_dvd_one hu)

theorem splits_X_sub_C {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {x : α} : splits i (X - coe_fn C x) :=
  splits_of_degree_eq_one i (degree_X_sub_C x)

theorem splits_X {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) : splits i X :=
  splits_of_degree_eq_one i degree_X

theorem splits_id_iff_splits {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} : splits (ring_hom.id β) (map i f) ↔ splits i f := sorry

theorem splits_mul_iff {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {g : polynomial α} (hf : f ≠ 0) (hg : g ≠ 0) : splits i (f * g) ↔ splits i f ∧ splits i g := sorry

theorem splits_prod {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {ι : Type w} {s : ι → polynomial α} {t : finset ι} : (∀ (j : ι), j ∈ t → splits i (s j)) → splits i (finset.prod t fun (x : ι) => s x) := sorry

theorem splits_prod_iff {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {ι : Type w} {s : ι → polynomial α} {t : finset ι} : (∀ (j : ι), j ∈ t → s j ≠ 0) → (splits i (finset.prod t fun (x : ι) => s x) ↔ ∀ (j : ι), j ∈ t → splits i (s j)) := sorry

theorem degree_eq_one_of_irreducible_of_splits {β : Type v} [field β] {p : polynomial β} (h_nz : p ≠ 0) (hp : irreducible p) (hp_splits : splits (ring_hom.id β) p) : degree p = 1 := sorry

theorem exists_root_of_splits {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} (hs : splits i f) (hf0 : degree f ≠ 0) : ∃ (x : β), eval₂ i x f = 0 := sorry

theorem exists_multiset_of_splits {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} : splits i f →
  ∃ (s : multiset β),
    map i f = coe_fn C (coe_fn i (leading_coeff f)) * multiset.prod (multiset.map (fun (a : β) => X - coe_fn C a) s) := sorry

/-- Pick a root of a polynomial that splits. -/
def root_of_splits {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} (hf : splits i f) (hfd : degree f ≠ 0) : β :=
  classical.some (exists_root_of_splits i hf hfd)

theorem map_root_of_splits {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} (hf : splits i f) (hfd : degree f ≠ 0) : eval₂ i (root_of_splits i hf hfd) f = 0 :=
  classical.some_spec (exists_root_of_splits i hf hfd)

theorem roots_map {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} (hf : splits (ring_hom.id α) f) : roots (map i f) = multiset.map (⇑i) (roots f) := sorry

theorem eq_prod_roots_of_splits {α : Type u} {β : Type v} [field α] [field β] {p : polynomial α} {i : α →+* β} (hsplit : splits i p) : map i p =
  coe_fn C (coe_fn i (leading_coeff p)) * multiset.prod (multiset.map (fun (a : β) => X - coe_fn C a) (roots (map i p))) := sorry

theorem eq_X_sub_C_of_splits_of_single_root {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {x : α} {h : polynomial α} (h_splits : splits i h) (h_roots : roots (map i h) = singleton (coe_fn i x)) : h = coe_fn C (leading_coeff h) * (X - coe_fn C x) := sorry

theorem nat_degree_multiset_prod {R : Type u_1} [integral_domain R] {s : multiset (polynomial R)} (h : ∀ (p : polynomial R), p ∈ s → p ≠ 0) : nat_degree (multiset.prod s) = multiset.sum (multiset.map nat_degree s) := sorry

theorem nat_degree_eq_card_roots {α : Type u} {β : Type v} [field α] [field β] {p : polynomial α} {i : α →+* β} (hsplit : splits i p) : nat_degree p = coe_fn multiset.card (roots (map i p)) := sorry

theorem degree_eq_card_roots {α : Type u} {β : Type v} [field α] [field β] {p : polynomial α} {i : α →+* β} (p_ne_zero : p ≠ 0) (hsplit : splits i p) : degree p = ↑(coe_fn multiset.card (roots (map i p))) := sorry

theorem splits_of_exists_multiset {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} {s : multiset β} (hs : map i f = coe_fn C (coe_fn i (leading_coeff f)) * multiset.prod (multiset.map (fun (a : β) => X - coe_fn C a) s)) : splits i f := sorry

theorem splits_of_splits_id {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} : splits (ring_hom.id α) f → splits i f := sorry

theorem splits_iff_exists_multiset {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β) {f : polynomial α} : splits i f ↔
  ∃ (s : multiset β),
    map i f = coe_fn C (coe_fn i (leading_coeff f)) * multiset.prod (multiset.map (fun (a : β) => X - coe_fn C a) s) := sorry

theorem splits_comp_of_splits {α : Type u} {β : Type v} {γ : Type w} [field α] [field β] [field γ] (i : α →+* β) (j : β →+* γ) {f : polynomial α} (h : splits i f) : splits (ring_hom.comp j i) f := sorry

/-- A monic polynomial `p` that has as much roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq {α : Type u} [field α] {p : polynomial α} (hmonic : monic p) (hroots : coe_fn multiset.card (roots p) = nat_degree p) : multiset.prod (multiset.map (fun (a : α) => X - coe_fn C a) (roots p)) = p := sorry

/-- A polynomial `p` that has as much roots as its degree
can be written `p = p.leading_coeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leading_coeff_mul_prod_multiset_X_sub_C {α : Type u} [field α] {p : polynomial α} (hroots : coe_fn multiset.card (roots p) = nat_degree p) : coe_fn C (leading_coeff p) * multiset.prod (multiset.map (fun (a : α) => X - coe_fn C a) (roots p)) = p := sorry

/-- A polynomial splits if and only if it has as much roots as its degree. -/
theorem splits_iff_card_roots {α : Type u} [field α] {p : polynomial α} : splits (ring_hom.id α) p ↔ coe_fn multiset.card (roots p) = nat_degree p := sorry

end polynomial


/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly (F : Type u_1) [field F] {R : Type u_2} [comm_ring R] [algebra F R] (x : R) : alg_equiv F (↥(algebra.adjoin F (singleton x))) (adjoin_root (minpoly F x)) :=
  alg_equiv.symm
    (alg_equiv.of_bijective
      (alg_hom.cod_restrict (adjoin_root.lift_hom (minpoly F x) x sorry) (algebra.adjoin F (singleton x)) sorry) sorry)

-- Speed up the following proof.

-- TODO: Why is this so slow?

/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F : Type u_1} {K : Type u_2} {L : Type u_3} [field F] [field K] [field L] [algebra F K] [algebra F L] (s : finset K) : (∀ (x : K), x ∈ s → is_integral F x ∧ polynomial.splits (algebra_map F L) (minpoly F x)) →
  Nonempty (alg_hom F (↥(algebra.adjoin F ↑s)) L) := sorry

namespace polynomial


/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor {α : Type u} [field α] (f : polynomial α) : polynomial α :=
  dite (∃ (g : polynomial α), irreducible g ∧ g ∣ f)
    (fun (H : ∃ (g : polynomial α), irreducible g ∧ g ∣ f) => classical.some H)
    fun (H : ¬∃ (g : polynomial α), irreducible g ∧ g ∣ f) => X

protected instance irreducible_factor {α : Type u} [field α] (f : polynomial α) : irreducible (factor f) := sorry

theorem factor_dvd_of_not_is_unit {α : Type u} [field α] {f : polynomial α} (hf1 : ¬is_unit f) : factor f ∣ f := sorry

theorem factor_dvd_of_degree_ne_zero {α : Type u} [field α] {f : polynomial α} (hf : degree f ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {α : Type u} [field α] {f : polynomial α} (hf : nat_degree f ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor {α : Type u} [field α] (f : polynomial α) : polynomial (adjoin_root (factor f)) :=
  map (adjoin_root.of (factor f)) f /ₘ (X - coe_fn C (adjoin_root.root (factor f)))

theorem X_sub_C_mul_remove_factor {α : Type u} [field α] (f : polynomial α) (hf : nat_degree f ≠ 0) : (X - coe_fn C (adjoin_root.root (factor f))) * remove_factor f = map (adjoin_root.of (factor f)) f := sorry

theorem nat_degree_remove_factor {α : Type u} [field α] (f : polynomial α) : nat_degree (remove_factor f) = nat_degree f - 1 := sorry

theorem nat_degree_remove_factor' {α : Type u} [field α] {f : polynomial α} {n : ℕ} (hfn : nat_degree f = n + 1) : nat_degree (remove_factor f) = n :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree (remove_factor f) = n)) (nat_degree_remove_factor f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (nat_degree f - 1 = n)) hfn))
      (eq.mpr (id (Eq._oldrec (Eq.refl (n + 1 - 1 = n)) (nat.add_sub_cancel n 1))) (Eq.refl n)))

/-- Auxiliary construction to a splitting field of a polynomial. Uses induction on the degree. -/
def splitting_field_aux (n : ℕ) {α : Type u} [field α] (f : polynomial α) : nat_degree f = n → Type u :=
  nat.rec_on n (fun (α : Type u) (_x : field α) (_x_1 : polynomial α) (_x : nat_degree _x_1 = 0) => α)
    fun (n : ℕ) (ih : {α : Type u} → [_inst_4 : field α] → (f : polynomial α) → nat_degree f = n → Type u) (α : Type u)
      (_x : field α) (f : polynomial α) (hf : nat_degree f = Nat.succ n) =>
      ih (remove_factor f) (nat_degree_remove_factor' hf)

namespace splitting_field_aux


theorem succ {α : Type u} [field α] (n : ℕ) (f : polynomial α) (hfn : nat_degree f = n + 1) : splitting_field_aux (n + 1) f hfn = splitting_field_aux n (remove_factor f) (nat_degree_remove_factor' hfn) :=
  rfl

protected instance field (n : ℕ) {α : Type u} [field α] {f : polynomial α} (hfn : nat_degree f = n) : field (splitting_field_aux n f hfn) :=
  nat.rec_on n (fun (α : Type u) (_x : field α) (_x_1 : polynomial α) (_x_2 : nat_degree _x_1 = 0) => _x)
    fun (n : ℕ)
      (ih :
      {α : Type u} →
        [_inst_4 : field α] → {f : polynomial α} → (hfn : nat_degree f = n) → field (splitting_field_aux n f hfn))
      (α : Type u) (_x : field α) (f : polynomial α) (hf : nat_degree f = Nat.succ n) => ih (nat_degree_remove_factor' hf)

protected instance inhabited {α : Type u} [field α] {n : ℕ} {f : polynomial α} (hfn : nat_degree f = n) : Inhabited (splitting_field_aux n f hfn) :=
  { default := bit1 (bit0 (bit1 (bit0 (bit0 1)))) }

protected instance algebra (n : ℕ) {α : Type u} [field α] {f : polynomial α} (hfn : nat_degree f = n) : algebra α (splitting_field_aux n f hfn) :=
  nat.rec_on n (fun (α : Type u) (_x : field α) (_x_1 : polynomial α) (_x_2 : nat_degree _x_1 = 0) => algebra.id α)
    fun (n : ℕ)
      (ih :
      {α : Type u} →
        [_inst_4 : field α] → {f : polynomial α} → (hfn : nat_degree f = n) → algebra α (splitting_field_aux n f hfn))
      (α : Type u) (_x : field α) (f : polynomial α) (hfn : nat_degree f = Nat.succ n) =>
      algebra.comap.algebra α (adjoin_root (factor f))
        (splitting_field_aux n (remove_factor f) (nat_degree_remove_factor' hfn))

protected instance algebra' {α : Type u} [field α] {n : ℕ} {f : polynomial α} (hfn : nat_degree f = n + 1) : algebra (adjoin_root (factor f)) (splitting_field_aux (n + 1) f hfn) :=
  splitting_field_aux.algebra n sorry

protected instance algebra'' {α : Type u} [field α] {n : ℕ} {f : polynomial α} (hfn : nat_degree f = n + 1) : algebra α (splitting_field_aux n (remove_factor f) (nat_degree_remove_factor' hfn)) :=
  splitting_field_aux.algebra (n + 1) hfn

protected instance algebra''' {α : Type u} [field α] {n : ℕ} {f : polynomial α} (hfn : nat_degree f = n + 1) : algebra (adjoin_root (factor f)) (splitting_field_aux n (remove_factor f) (nat_degree_remove_factor' hfn)) :=
  splitting_field_aux.algebra n (nat_degree_remove_factor' hfn)

protected instance scalar_tower {α : Type u} [field α] {n : ℕ} {f : polynomial α} (hfn : nat_degree f = n + 1) : is_scalar_tower α (adjoin_root (factor f)) (splitting_field_aux (n + 1) f hfn) :=
  is_scalar_tower.of_algebra_map_eq fun (x : α) => rfl

protected instance scalar_tower' {α : Type u} [field α] {n : ℕ} {f : polynomial α} (hfn : nat_degree f = n + 1) : is_scalar_tower α (adjoin_root (factor f)) (splitting_field_aux n (remove_factor f) (nat_degree_remove_factor' hfn)) :=
  is_scalar_tower.of_algebra_map_eq fun (x : α) => rfl

theorem algebra_map_succ {α : Type u} [field α] (n : ℕ) (f : polynomial α) (hfn : nat_degree f = n + 1) : algebra_map α (splitting_field_aux (n + 1) f hfn) =
  ring_hom.comp
    (algebra_map (adjoin_root (factor f)) (splitting_field_aux n (remove_factor f) (nat_degree_remove_factor' hfn)))
    (adjoin_root.of (factor f)) :=
  rfl

protected theorem splits (n : ℕ) {α : Type u} [field α] (f : polynomial α) (hfn : nat_degree f = n) : splits (algebra_map α (splitting_field_aux n f hfn)) f := sorry

theorem exists_lift (n : ℕ) {α : Type u} [field α] (f : polynomial α) (hfn : nat_degree f = n) {β : Type u_1} [field β] (j : α →+* β) (hf : splits j f) : ∃ (k : splitting_field_aux n f hfn →+* β), ring_hom.comp k (algebra_map α (splitting_field_aux n f hfn)) = j := sorry

theorem adjoin_roots (n : ℕ) {α : Type u} [field α] (f : polynomial α) (hfn : nat_degree f = n) : algebra.adjoin α ↑(multiset.to_finset (roots (map (algebra_map α (splitting_field_aux n f hfn)) f))) = ⊤ := sorry

end splitting_field_aux


/-- A splitting field of a polynomial. -/
def splitting_field {α : Type u} [field α] (f : polynomial α) :=
  splitting_field_aux (nat_degree f) f sorry

namespace splitting_field


protected instance field {α : Type u} [field α] (f : polynomial α) : field (splitting_field f) :=
  splitting_field_aux.field (nat_degree f) (_proof_1 f)

protected instance inhabited {α : Type u} [field α] (f : polynomial α) : Inhabited (splitting_field f) :=
  { default := bit1 (bit0 (bit1 (bit0 (bit0 1)))) }

protected instance algebra {α : Type u} [field α] (f : polynomial α) : algebra α (splitting_field f) :=
  splitting_field_aux.algebra (nat_degree f) (_proof_1 f)

protected theorem splits {α : Type u} [field α] (f : polynomial α) : splits (algebra_map α (splitting_field f)) f :=
  splitting_field_aux.splits (nat_degree f) f (_proof_1 f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift {α : Type u} {β : Type v} [field α] [field β] (f : polynomial α) [algebra α β] (hb : splits (algebra_map α β) f) : alg_hom α (splitting_field f) β :=
  alg_hom.mk (ring_hom.to_fun (classical.some sorry)) sorry sorry sorry sorry sorry

theorem adjoin_roots {α : Type u} [field α] (f : polynomial α) : algebra.adjoin α ↑(multiset.to_finset (roots (map (algebra_map α (splitting_field f)) f))) = ⊤ :=
  splitting_field_aux.adjoin_roots (nat_degree f) f (_proof_1 f)

end splitting_field


/-- Typeclass characterising splitting fields. -/
class is_splitting_field (α : Type u) (β : Type v) [field α] [field β] [algebra α β] (f : polynomial α) 
where
  splits : splits (algebra_map α β) f
  adjoin_roots : algebra.adjoin α ↑(multiset.to_finset (roots (map (algebra_map α β) f))) = ⊤

namespace is_splitting_field


protected instance splitting_field {α : Type u} [field α] (f : polynomial α) : is_splitting_field α (splitting_field f) f :=
  mk (splitting_field.splits f) (splitting_field.adjoin_roots f)

protected instance map {α : Type u} {β : Type v} {γ : Type w} [field α] [field β] [field γ] [algebra α β] [algebra β γ] [algebra α γ] [is_scalar_tower α β γ] (f : polynomial α) [is_splitting_field α γ f] : is_splitting_field β γ (map (algebra_map α β) f) := sorry

theorem splits_iff {α : Type u} (β : Type v) [field α] [field β] [algebra α β] (f : polynomial α) [is_splitting_field α β f] : splits (ring_hom.id α) f ↔ ⊤ = ⊥ := sorry

theorem mul {α : Type u} (β : Type v) {γ : Type w} [field α] [field β] [field γ] [algebra α β] [algebra β γ] [algebra α γ] [is_scalar_tower α β γ] (f : polynomial α) (g : polynomial α) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field α β f] [is_splitting_field β γ (map (algebra_map α β) g)] : is_splitting_field α γ (f * g) := sorry

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift {α : Type u} (β : Type v) {γ : Type w} [field α] [field β] [field γ] [algebra α β] [algebra α γ] (f : polynomial α) [is_splitting_field α β f] (hf : splits (algebra_map α γ) f) : alg_hom α β γ :=
  dite (f = 0)
    (fun (hf0 : f = 0) =>
      alg_hom.comp (algebra.of_id α γ) (alg_hom.comp (↑(algebra.bot_equiv α β)) (eq.mpr sorry algebra.to_top)))
    fun (hf0 : ¬f = 0) => alg_hom.comp (eq.mpr sorry (Classical.choice sorry)) algebra.to_top

theorem finite_dimensional {α : Type u} (β : Type v) [field α] [field β] [algebra α β] (f : polynomial α) [is_splitting_field α β f] : finite_dimensional α β := sorry

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def alg_equiv {α : Type u} (β : Type v) [field α] [field β] [algebra α β] (f : polynomial α) [is_splitting_field α β f] : alg_equiv α β (splitting_field f) :=
  alg_equiv.of_bijective (lift β f sorry) sorry

