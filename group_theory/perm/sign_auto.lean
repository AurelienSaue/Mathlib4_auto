/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.data.finset.sort
import Mathlib.group_theory.perm.basic
import Mathlib.group_theory.order_of_element
import PostPort

universes u u_1 v 

namespace Mathlib

/-!
# Sign of a permutation

The main definition of this file is `equiv.perm.sign`, associating a `units ℤ` sign with a
permutation.

This file also contains miscellaneous lemmas about `equiv.perm` and `equiv.swap`, building on top
of those in `data/equiv/basic` and `data/equiv/perm`.

-/

namespace equiv.perm


/--
`mod_swap i j` contains permutations up to swapping `i` and `j`.

We use this to partition permutations in `matrix.det_zero_of_row_eq`, such that each partition
sums up to `0`.
-/
def mod_swap {α : Type u} [DecidableEq α] (i : α) (j : α) : setoid (perm α) :=
  setoid.mk (fun (σ τ : perm α) => σ = τ ∨ σ = swap i j * τ) sorry

protected instance r.decidable_rel {α : Type u_1} [fintype α] [DecidableEq α] (i : α) (j : α) : DecidableRel setoid.r :=
  fun (σ τ : perm α) => or.decidable

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtype_perm {α : Type u} (f : perm α) {p : α → Prop} (h : ∀ (x : α), p x ↔ p (coe_fn f x)) : perm (Subtype fun (x : α) => p x) :=
  mk (fun (x : Subtype fun (x : α) => p x) => { val := coe_fn f ↑x, property := sorry })
    (fun (x : Subtype fun (x : α) => p x) => { val := coe_fn (f⁻¹) ↑x, property := sorry }) sorry sorry

@[simp] theorem subtype_perm_one {α : Type u} (p : α → Prop) (h : ∀ (x : α), p x ↔ p (coe_fn 1 x)) : subtype_perm 1 h = 1 := sorry

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def of_subtype {α : Type u} {p : α → Prop} [decidable_pred p] : perm (Subtype p) →* perm α :=
  monoid_hom.mk
    (fun (f : perm (Subtype p)) =>
      mk (fun (x : α) => dite (p x) (fun (h : p x) => ↑(coe_fn f { val := x, property := h })) fun (h : ¬p x) => x)
        (fun (x : α) => dite (p x) (fun (h : p x) => ↑(coe_fn (f⁻¹) { val := x, property := h })) fun (h : ¬p x) => x)
        sorry sorry)
    sorry sorry

/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def disjoint {α : Type u} (f : perm α) (g : perm α)  :=
  ∀ (x : α), coe_fn f x = x ∨ coe_fn g x = x

theorem disjoint.symm {α : Type u} {f : perm α} {g : perm α} : disjoint f g → disjoint g f := sorry

theorem disjoint_comm {α : Type u} {f : perm α} {g : perm α} : disjoint f g ↔ disjoint g f :=
  { mp := disjoint.symm, mpr := disjoint.symm }

theorem disjoint.mul_comm {α : Type u} {f : perm α} {g : perm α} (h : disjoint f g) : f * g = g * f := sorry

@[simp] theorem disjoint_one_left {α : Type u} (f : perm α) : disjoint 1 f :=
  fun (_x : α) => Or.inl rfl

@[simp] theorem disjoint_one_right {α : Type u} (f : perm α) : disjoint f 1 :=
  fun (_x : α) => Or.inr rfl

theorem disjoint.mul_left {α : Type u} {f : perm α} {g : perm α} {h : perm α} (H1 : disjoint f h) (H2 : disjoint g h) : disjoint (f * g) h := sorry

theorem disjoint.mul_right {α : Type u} {f : perm α} {g : perm α} {h : perm α} (H1 : disjoint f g) (H2 : disjoint f h) : disjoint f (g * h) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (disjoint f (g * h))) (propext disjoint_comm)))
    (disjoint.mul_left (disjoint.symm H1) (disjoint.symm H2))

theorem disjoint_prod_right {α : Type u} {f : perm α} (l : List (perm α)) (h : ∀ (g : perm α), g ∈ l → disjoint f g) : disjoint f (list.prod l) := sorry

theorem disjoint_prod_perm {α : Type u} {l₁ : List (perm α)} {l₂ : List (perm α)} (hl : list.pairwise disjoint l₁) (hp : l₁ ~ l₂) : list.prod l₁ = list.prod l₂ :=
  list.perm.prod_eq' hp (list.pairwise.imp (fun (f g : perm α) => disjoint.mul_comm) hl)

theorem of_subtype_subtype_perm {α : Type u} {f : perm α} {p : α → Prop} [decidable_pred p] (h₁ : ∀ (x : α), p x ↔ p (coe_fn f x)) (h₂ : ∀ (x : α), coe_fn f x ≠ x → p x) : coe_fn of_subtype (subtype_perm f h₁) = f := sorry

theorem of_subtype_apply_of_not_mem {α : Type u} {p : α → Prop} [decidable_pred p] (f : perm (Subtype p)) {x : α} (hx : ¬p x) : coe_fn (coe_fn of_subtype f) x = x :=
  dif_neg hx

theorem mem_iff_of_subtype_apply_mem {α : Type u} {p : α → Prop} [decidable_pred p] (f : perm (Subtype p)) (x : α) : p x ↔ p (coe_fn (coe_fn of_subtype f) x) := sorry

@[simp] theorem subtype_perm_of_subtype {α : Type u} {p : α → Prop} [decidable_pred p] (f : perm (Subtype p)) : subtype_perm (coe_fn of_subtype f) (mem_iff_of_subtype_apply_mem f) = f := sorry

theorem pow_apply_eq_self_of_apply_eq_self {α : Type u} {f : perm α} {x : α} (hfx : coe_fn f x = x) (n : ℕ) : coe_fn (f ^ n) x = x := sorry

theorem gpow_apply_eq_self_of_apply_eq_self {α : Type u} {f : perm α} {x : α} (hfx : coe_fn f x = x) (n : ℤ) : coe_fn (f ^ n) x = x := sorry

theorem pow_apply_eq_of_apply_apply_eq_self {α : Type u} {f : perm α} {x : α} (hffx : coe_fn f (coe_fn f x) = x) (n : ℕ) : coe_fn (f ^ n) x = x ∨ coe_fn (f ^ n) x = coe_fn f x := sorry

theorem gpow_apply_eq_of_apply_apply_eq_self {α : Type u} {f : perm α} {x : α} (hffx : coe_fn f (coe_fn f x) = x) (i : ℤ) : coe_fn (f ^ i) x = x ∨ coe_fn (f ^ i) x = coe_fn f x := sorry

/-- The `finset` of nonfixed points of a permutation. -/
def support {α : Type u} [DecidableEq α] [fintype α] (f : perm α) : finset α :=
  finset.filter (fun (x : α) => coe_fn f x ≠ x) finset.univ

@[simp] theorem mem_support {α : Type u} [DecidableEq α] [fintype α] {f : perm α} {x : α} : x ∈ support f ↔ coe_fn f x ≠ x := sorry

/-- `f.is_swap` indicates that the permutation `f` is a transposition of two elements. -/
def is_swap {α : Type u} [DecidableEq α] (f : perm α)  :=
  ∃ (x : α), ∃ (y : α), x ≠ y ∧ f = swap x y

theorem is_swap.of_subtype_is_swap {α : Type u} [DecidableEq α] {p : α → Prop} [decidable_pred p] {f : perm (Subtype p)} (h : is_swap f) : is_swap (coe_fn of_subtype f) := sorry

theorem ne_and_ne_of_swap_mul_apply_ne_self {α : Type u} [DecidableEq α] {f : perm α} {x : α} {y : α} (hy : coe_fn (swap x (coe_fn f x) * f) y ≠ y) : coe_fn f y ≠ y ∧ y ≠ x := sorry

theorem support_swap_mul_eq {α : Type u} [DecidableEq α] [fintype α] {f : perm α} {x : α} (hffx : coe_fn f (coe_fn f x) ≠ x) : support (swap x (coe_fn f x) * f) = finset.erase (support f) x := sorry

theorem card_support_swap_mul {α : Type u} [DecidableEq α] [fintype α] {f : perm α} {x : α} (hx : coe_fn f x ≠ x) : finset.card (support (swap x (coe_fn f x) * f)) < finset.card (support f) := sorry

/-- Given a list `l : list α` and a permutation `f : perm α` such that the nonfixed points of `f`
  are in `l`, recursively factors `f` as a product of transpositions. -/
def swap_factors_aux {α : Type u} [DecidableEq α] (l : List α) (f : perm α) : (∀ {x : α}, coe_fn f x ≠ x → x ∈ l) →
  Subtype fun (l : List (perm α)) => list.prod l = f ∧ ∀ (g : perm α), g ∈ l → is_swap g :=
  sorry

/-- `swap_factors` represents a permutation as a product of a list of transpositions.
The representation is non unique and depends on the linear order structure.
For types without linear order `trunc_swap_factors` can be used. -/
def swap_factors {α : Type u} [DecidableEq α] [fintype α] [linear_order α] (f : perm α) : Subtype fun (l : List (perm α)) => list.prod l = f ∧ ∀ (g : perm α), g ∈ l → is_swap g :=
  swap_factors_aux (finset.sort LessEq finset.univ) f sorry

/-- This computably represents the fact that any permutation can be represented as the product of
  a list of transpositions. -/
def trunc_swap_factors {α : Type u} [DecidableEq α] [fintype α] (f : perm α) : trunc (Subtype fun (l : List (perm α)) => list.prod l = f ∧ ∀ (g : perm α), g ∈ l → is_swap g) :=
  quotient.rec_on_subsingleton (finset.val finset.univ)
    (fun (l : List α) (h : ∀ (x : α), coe_fn f x ≠ x → x ∈ quotient.mk l) => trunc.mk (swap_factors_aux l f h)) sorry

/-- An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
theorem swap_induction_on {α : Type u} [DecidableEq α] [fintype α] {P : perm α → Prop} (f : perm α) : P 1 → (∀ (f : perm α) (x y : α), x ≠ y → P f → P (swap x y * f)) → P f := sorry

/-- Like `swap_induction_on`, but with the composition on the right of `f`.

An induction principle for permutations. If `P` holds for the identity permutation, and
is preserved under composition with a non-trivial swap, then `P` holds for all permutations. -/
theorem swap_induction_on' {α : Type u} [DecidableEq α] [fintype α] {P : perm α → Prop} (f : perm α) : P 1 → (∀ (f : perm α) (x y : α), x ≠ y → P f → P (f * swap x y)) → P f :=
  fun (h1 : P 1) (IH : ∀ (f : perm α) (x y : α), x ≠ y → P f → P (f * swap x y)) =>
    inv_inv f ▸ swap_induction_on (f⁻¹) h1 fun (f : perm α) => IH (f⁻¹)

theorem is_conj_swap {α : Type u} [DecidableEq α] {w : α} {x : α} {y : α} {z : α} (hwx : w ≠ x) (hyz : y ≠ z) : is_conj (swap w x) (swap y z) := sorry

/-- set of all pairs (⟨a, b⟩ : Σ a : fin n, fin n) such that b < a -/
def fin_pairs_lt (n : ℕ) : finset (sigma fun (a : fin n) => fin n) :=
  finset.sigma finset.univ fun (a : fin n) => finset.attach_fin (finset.range ↑a) sorry

theorem mem_fin_pairs_lt {n : ℕ} {a : sigma fun (a : fin n) => fin n} : a ∈ fin_pairs_lt n ↔ sigma.snd a < sigma.fst a := sorry

/-- `sign_aux σ` is the sign of a permutation on `fin n`, defined as the parity of the number of
  pairs `(x₁, x₂)` such that `x₂ < x₁` but `σ x₁ ≤ σ x₂` -/
def sign_aux {n : ℕ} (a : perm (fin n)) : units ℤ :=
  finset.prod (fin_pairs_lt n)
    fun (x : sigma fun (a : fin n) => fin n) => ite (coe_fn a (sigma.fst x) ≤ coe_fn a (sigma.snd x)) (-1) 1

@[simp] theorem sign_aux_one (n : ℕ) : sign_aux 1 = 1 := sorry

/-- `sign_bij_aux f ⟨a, b⟩` returns the pair consisting of `f a` and `f b` in decreasing order. -/
def sign_bij_aux {n : ℕ} (f : perm (fin n)) (a : sigma fun (a : fin n) => fin n) : sigma fun (a : fin n) => fin n :=
  dite (coe_fn f (sigma.snd a) < coe_fn f (sigma.fst a))
    (fun (hxa : coe_fn f (sigma.snd a) < coe_fn f (sigma.fst a)) =>
      sigma.mk (coe_fn f (sigma.fst a)) (coe_fn f (sigma.snd a)))
    fun (hxa : ¬coe_fn f (sigma.snd a) < coe_fn f (sigma.fst a)) =>
      sigma.mk (coe_fn f (sigma.snd a)) (coe_fn f (sigma.fst a))

theorem sign_bij_aux_inj {n : ℕ} {f : perm (fin n)} (a : sigma fun (a : fin n) => fin n) (b : sigma fun (a : fin n) => fin n) : a ∈ fin_pairs_lt n → b ∈ fin_pairs_lt n → sign_bij_aux f a = sign_bij_aux f b → a = b := sorry

theorem sign_bij_aux_surj {n : ℕ} {f : perm (fin n)} (a : sigma fun (a : fin n) => fin n) (H : a ∈ fin_pairs_lt n) : ∃ (b : sigma fun (a : fin n) => fin n), ∃ (H : b ∈ fin_pairs_lt n), a = sign_bij_aux f b := sorry

theorem sign_bij_aux_mem {n : ℕ} {f : perm (fin n)} (a : sigma fun (a : fin n) => fin n) : a ∈ fin_pairs_lt n → sign_bij_aux f a ∈ fin_pairs_lt n := sorry

@[simp] theorem sign_aux_inv {n : ℕ} (f : perm (fin n)) : sign_aux (f⁻¹) = sign_aux f := sorry

theorem sign_aux_mul {n : ℕ} (f : perm (fin n)) (g : perm (fin n)) : sign_aux (f * g) = sign_aux f * sign_aux g := sorry

-- TODO: slow

theorem sign_aux_swap {n : ℕ} {x : fin n} {y : fin n} (hxy : x ≠ y) : sign_aux (swap x y) = -1 := sorry

/-- When the list `l : list α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 l f` recursively calculates the sign of `f`. -/
def sign_aux2 {α : Type u} [DecidableEq α] : List α → perm α → units ℤ :=
  sorry

theorem sign_aux_eq_sign_aux2 {α : Type u} [DecidableEq α] {n : ℕ} (l : List α) (f : perm α) (e : α ≃ fin n) (h : ∀ (x : α), coe_fn f x ≠ x → x ∈ l) : sign_aux (equiv.trans (equiv.trans (equiv.symm e) f) e) = sign_aux2 l f := sorry

/-- When the multiset `s : multiset α` contains all nonfixed points of the permutation `f : perm α`,
  `sign_aux2 f _` recursively calculates the sign of `f`. -/
def sign_aux3 {α : Type u} [DecidableEq α] [fintype α] (f : perm α) {s : multiset α} : (∀ (x : α), x ∈ s) → units ℤ :=
  quotient.hrec_on s (fun (l : List α) (h : ∀ (x : α), x ∈ quotient.mk l) => sign_aux2 l f) sorry

theorem sign_aux3_mul_and_swap {α : Type u} [DecidableEq α] [fintype α] (f : perm α) (g : perm α) (s : multiset α) (hs : ∀ (x : α), x ∈ s) : sign_aux3 (f * g) hs = sign_aux3 f hs * sign_aux3 g hs ∧ ∀ (x y : α), x ≠ y → sign_aux3 (swap x y) hs = -1 := sorry

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`perm α` to the group with two elements.-/
def sign {α : Type u} [DecidableEq α] [fintype α] : perm α →* units ℤ :=
  monoid_hom.mk' (fun (f : perm α) => sign_aux3 f finset.mem_univ) sorry

@[simp] theorem sign_mul {α : Type u} [DecidableEq α] [fintype α] (f : perm α) (g : perm α) : coe_fn sign (f * g) = coe_fn sign f * coe_fn sign g :=
  monoid_hom.map_mul sign f g

@[simp] theorem sign_trans {α : Type u} [DecidableEq α] [fintype α] (f : perm α) (g : perm α) : coe_fn sign (equiv.trans f g) = coe_fn sign g * coe_fn sign f := sorry

@[simp] theorem sign_one {α : Type u} [DecidableEq α] [fintype α] : coe_fn sign 1 = 1 :=
  monoid_hom.map_one sign

@[simp] theorem sign_refl {α : Type u} [DecidableEq α] [fintype α] : coe_fn sign (equiv.refl α) = 1 :=
  monoid_hom.map_one sign

@[simp] theorem sign_inv {α : Type u} [DecidableEq α] [fintype α] (f : perm α) : coe_fn sign (f⁻¹) = coe_fn sign f :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn sign (f⁻¹) = coe_fn sign f)) (monoid_hom.map_inv sign f)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn sign f⁻¹ = coe_fn sign f)) (int.units_inv_eq_self (coe_fn sign f))))
      (Eq.refl (coe_fn sign f)))

@[simp] theorem sign_symm {α : Type u} [DecidableEq α] [fintype α] (e : perm α) : coe_fn sign (equiv.symm e) = coe_fn sign e :=
  sign_inv e

theorem sign_swap {α : Type u} [DecidableEq α] [fintype α] {x : α} {y : α} (h : x ≠ y) : coe_fn sign (swap x y) = -1 :=
  and.right (sign_aux3_mul_and_swap 1 1 (finset.val finset.univ) finset.mem_univ) x y h

@[simp] theorem sign_swap' {α : Type u} [DecidableEq α] [fintype α] {x : α} {y : α} : coe_fn sign (swap x y) = ite (x = y) 1 (-1) := sorry

theorem is_swap.sign_eq {α : Type u} [DecidableEq α] [fintype α] {f : perm α} (h : is_swap f) : coe_fn sign f = -1 := sorry

theorem sign_aux3_symm_trans_trans {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (f : perm α) (e : α ≃ β) {s : multiset α} {t : multiset β} (hs : ∀ (x : α), x ∈ s) (ht : ∀ (x : β), x ∈ t) : sign_aux3 (equiv.trans (equiv.trans (equiv.symm e) f) e) ht = sign_aux3 f hs := sorry

@[simp] theorem sign_symm_trans_trans {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (f : perm α) (e : α ≃ β) : coe_fn sign (equiv.trans (equiv.trans (equiv.symm e) f) e) = coe_fn sign f :=
  sign_aux3_symm_trans_trans f e finset.mem_univ finset.mem_univ

@[simp] theorem sign_trans_trans_symm {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (f : perm β) (e : α ≃ β) : coe_fn sign (equiv.trans (equiv.trans e f) (equiv.symm e)) = coe_fn sign f :=
  sign_symm_trans_trans f (equiv.symm e)

theorem sign_prod_list_swap {α : Type u} [DecidableEq α] [fintype α] {l : List (perm α)} (hl : ∀ (g : perm α), g ∈ l → is_swap g) : coe_fn sign (list.prod l) = (-1) ^ list.length l := sorry

theorem sign_surjective {α : Type u} [DecidableEq α] [fintype α] (hα : 1 < fintype.card α) : function.surjective ⇑sign := sorry

theorem eq_sign_of_surjective_hom {α : Type u} [DecidableEq α] [fintype α] {s : perm α →* units ℤ} (hs : function.surjective ⇑s) : s = sign := sorry

theorem sign_subtype_perm {α : Type u} [DecidableEq α] [fintype α] (f : perm α) {p : α → Prop} [decidable_pred p] (h₁ : ∀ (x : α), p x ↔ p (coe_fn f x)) (h₂ : ∀ (x : α), coe_fn f x ≠ x → p x) : coe_fn sign (subtype_perm f h₁) = coe_fn sign f := sorry

@[simp] theorem sign_of_subtype {α : Type u} [DecidableEq α] [fintype α] {p : α → Prop} [decidable_pred p] (f : perm (Subtype p)) : coe_fn sign (coe_fn of_subtype f) = coe_fn sign f := sorry

theorem sign_eq_sign_of_equiv {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (f : perm α) (g : perm β) (e : α ≃ β) (h : ∀ (x : α), coe_fn e (coe_fn f x) = coe_fn g (coe_fn e x)) : coe_fn sign f = coe_fn sign g := sorry

theorem sign_bij {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] {f : perm α} {g : perm β} (i : (x : α) → coe_fn f x ≠ x → β) (h : ∀ (x : α) (hx : coe_fn f x ≠ x) (hx' : coe_fn f (coe_fn f x) ≠ coe_fn f x), i (coe_fn f x) hx' = coe_fn g (i x hx)) (hi : ∀ (x₁ x₂ : α) (hx₁ : coe_fn f x₁ ≠ x₁) (hx₂ : coe_fn f x₂ ≠ x₂), i x₁ hx₁ = i x₂ hx₂ → x₁ = x₂) (hg : ∀ (y : β), coe_fn g y ≠ y → ∃ (x : α), ∃ (hx : coe_fn f x ≠ x), i x hx = y) : coe_fn sign f = coe_fn sign g := sorry

@[simp] theorem support_swap {α : Type u} [DecidableEq α] [fintype α] {x : α} {y : α} (hxy : x ≠ y) : support (swap x y) = insert x (singleton y) := sorry

theorem card_support_swap {α : Type u} [DecidableEq α] [fintype α] {x : α} {y : α} (hxy : x ≠ y) : finset.card (support (swap x y)) = bit0 1 := sorry

/-- If we apply `prod_extend_right a (σ a)` for all `a : α` in turn,
we get `prod_congr_right σ`. -/
theorem prod_prod_extend_right {β : Type v} {α : Type u_1} [DecidableEq α] (σ : α → perm β) {l : List α} (hl : list.nodup l) (mem_l : ∀ (a : α), a ∈ l) : list.prod (list.map (fun (a : α) => prod_extend_right a (σ a)) l) = prod_congr_right σ := sorry

@[simp] theorem sign_prod_extend_right {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (a : α) (σ : perm β) : coe_fn sign (prod_extend_right a σ) = coe_fn sign σ := sorry

theorem sign_prod_congr_right {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (σ : α → perm β) : coe_fn sign (prod_congr_right σ) = finset.prod finset.univ fun (k : α) => coe_fn sign (σ k) := sorry

theorem sign_prod_congr_left {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (σ : α → perm β) : coe_fn sign (prod_congr_left σ) = finset.prod finset.univ fun (k : α) => coe_fn sign (σ k) := sorry

@[simp] theorem sign_perm_congr {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (e : α ≃ β) (p : perm α) : coe_fn sign (coe_fn (perm_congr e) p) = coe_fn sign p := sorry

@[simp] theorem sign_sum_congr {α : Type u} {β : Type v} [DecidableEq α] [fintype α] [DecidableEq β] [fintype β] (σa : perm α) (σb : perm β) : coe_fn sign (sum_congr σa σb) = coe_fn sign σa * coe_fn sign σb := sorry

