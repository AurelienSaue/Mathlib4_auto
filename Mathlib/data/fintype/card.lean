/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.fintype.basic
import Mathlib.algebra.big_operators.ring
import Mathlib.PostPort

universes u_1 u_4 u_2 u_3 u_5 u_6 

namespace Mathlib

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `data.fintype`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.
-/

namespace fintype


theorem prod_bool {α : Type u_1} [comm_monoid α] (f : Bool → α) : (finset.prod finset.univ fun (b : Bool) => f b) = f tt * f false := sorry

theorem card_eq_sum_ones {α : Type u_1} [fintype α] : card α = finset.sum finset.univ fun (a : α) => 1 :=
  finset.card_eq_sum_ones finset.univ

theorem prod_extend_by_one {α : Type u_1} {ι : Type u_4} [DecidableEq ι] [fintype ι] [comm_monoid α] (s : finset ι) (f : ι → α) : (finset.prod finset.univ fun (i : ι) => ite (i ∈ s) (f i) 1) = finset.prod s fun (i : ι) => f i := sorry

theorem sum_eq_zero {α : Type u_1} {M : Type u_4} [fintype α] [add_comm_monoid M] (f : α → M) (h : ∀ (a : α), f a = 0) : (finset.sum finset.univ fun (a : α) => f a) = 0 :=
  finset.sum_eq_zero fun (a : α) (ha : a ∈ finset.univ) => h a

theorem sum_congr {α : Type u_1} {M : Type u_4} [fintype α] [add_comm_monoid M] (f : α → M) (g : α → M) (h : ∀ (a : α), f a = g a) : (finset.sum finset.univ fun (a : α) => f a) = finset.sum finset.univ fun (a : α) => g a :=
  finset.sum_congr rfl fun (a : α) (ha : a ∈ finset.univ) => h a

theorem sum_eq_single {α : Type u_1} {M : Type u_4} [fintype α] [add_comm_monoid M] {f : α → M} (a : α) (h : ∀ (x : α), x ≠ a → f x = 0) : (finset.sum finset.univ fun (x : α) => f x) = f a :=
  finset.sum_eq_single a (fun (x : α) (_x : x ∈ finset.univ) (hx : x ≠ a) => h x hx)
    fun (ha : ¬a ∈ finset.univ) => false.elim (ha (finset.mem_univ a))

theorem sum_unique {β : Type u_2} {M : Type u_4} [add_comm_monoid M] [unique β] (f : β → M) : (finset.sum finset.univ fun (x : β) => f x) = f Inhabited.default := sorry

/-- If a product of a `finset` of a subsingleton type has a given
value, so do the terms in that product. -/
theorem eq_of_subsingleton_of_sum_eq {M : Type u_4} [add_comm_monoid M] {ι : Type u_1} [subsingleton ι] {s : finset ι} {f : ι → M} {b : M} (h : (finset.sum s fun (i : ι) => f i) = b) (i : ι) (H : i ∈ s) : f i = b :=
  finset.eq_of_card_le_one_of_sum_eq (finset.card_le_one_of_subsingleton s) h

end fintype


theorem is_compl.prod_mul_prod {α : Type u_1} {M : Type u_4} [fintype α] [DecidableEq α] [comm_monoid M] {s : finset α} {t : finset α} (h : is_compl s t) (f : α → M) : ((finset.prod s fun (i : α) => f i) * finset.prod t fun (i : α) => f i) = finset.prod finset.univ fun (i : α) => f i := sorry

theorem finset.prod_mul_prod_compl {α : Type u_1} {M : Type u_4} [fintype α] [DecidableEq α] [comm_monoid M] (s : finset α) (f : α → M) : ((finset.prod s fun (i : α) => f i) * finset.prod (sᶜ) fun (i : α) => f i) = finset.prod finset.univ fun (i : α) => f i :=
  is_compl.prod_mul_prod is_compl_compl f

theorem finset.sum_compl_add_sum {α : Type u_1} {M : Type u_4} [fintype α] [DecidableEq α] [add_comm_monoid M] (s : finset α) (f : α → M) : ((finset.sum (sᶜ) fun (i : α) => f i) + finset.sum s fun (i : α) => f i) = finset.sum finset.univ fun (i : α) => f i :=
  is_compl.sum_add_sum (is_compl.symm is_compl_compl) f

theorem fin.prod_univ_def {β : Type u_2} [comm_monoid β] {n : ℕ} (f : fin n → β) : (finset.prod finset.univ fun (i : fin n) => f i) = list.prod (list.map f (list.fin_range n)) := sorry

theorem fin.sum_of_fn {β : Type u_2} [add_comm_monoid β] {n : ℕ} (f : fin n → β) : list.sum (list.of_fn f) = finset.sum finset.univ fun (i : fin n) => f i := sorry

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[simp] theorem fin.prod_univ_zero {β : Type u_2} [comm_monoid β] (f : fin 0 → β) : (finset.prod finset.univ fun (i : fin 0) => f i) = 1 :=
  rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
theorem fin.prod_univ_succ_above {β : Type u_2} [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) (x : fin (n + 1)) : (finset.prod finset.univ fun (i : fin (n + 1)) => f i) =
  f x * finset.prod finset.univ fun (i : fin n) => f (coe_fn (fin.succ_above x) i) := sorry

/-- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f x`, for some `x : fin (n + 1)` plus the remaining product -/
theorem fin.sum_univ_succ_above {β : Type u_2} [add_comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) (x : fin (n + 1)) : (finset.sum finset.univ fun (i : fin (n + 1)) => f i) =
  f x + finset.sum finset.univ fun (i : fin n) => f (coe_fn (fin.succ_above x) i) :=
  fin.prod_univ_succ_above (fun (i : fin (n + 1)) => f i) x

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
theorem fin.prod_univ_succ {β : Type u_2} [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) : (finset.prod finset.univ fun (i : fin (n + 1)) => f i) = f 0 * finset.prod finset.univ fun (i : fin n) => f (fin.succ i) :=
  fin.prod_univ_succ_above f 0

/-- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f 0` plus the remaining product -/
theorem fin.sum_univ_succ {β : Type u_2} [add_comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) : (finset.sum finset.univ fun (i : fin (n + 1)) => f i) = f 0 + finset.sum finset.univ fun (i : fin n) => f (fin.succ i) :=
  fin.sum_univ_succ_above f 0

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
theorem fin.prod_univ_cast_succ {β : Type u_2} [comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) : (finset.prod finset.univ fun (i : fin (n + 1)) => f i) =
  (finset.prod finset.univ fun (i : fin n) => f (coe_fn fin.cast_succ i)) * f (fin.last n) := sorry

/-- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f (fin.last n)` plus the remaining sum -/
theorem fin.sum_univ_cast_succ {β : Type u_2} [add_comm_monoid β] {n : ℕ} (f : fin (n + 1) → β) : (finset.sum finset.univ fun (i : fin (n + 1)) => f i) =
  (finset.sum finset.univ fun (i : fin n) => f (coe_fn fin.cast_succ i)) + f (fin.last n) :=
  fin.prod_univ_cast_succ fun (i : fin (n + 1)) => f i

@[simp] theorem fintype.card_sigma {α : Type u_1} (β : α → Type u_2) [fintype α] [(a : α) → fintype (β a)] : fintype.card (sigma β) = finset.sum finset.univ fun (a : α) => fintype.card (β a) :=
  finset.card_sigma finset.univ fun (a : α) => (fun (_x : α) => finset.univ) a

-- FIXME ouch, this should be in the main file.

@[simp] theorem fintype.card_sum (α : Type u_1) (β : Type u_2) [fintype α] [fintype β] : fintype.card (α ⊕ β) = fintype.card α + fintype.card β := sorry

@[simp] theorem finset.card_pi {α : Type u_1} [DecidableEq α] {δ : α → Type u_2} (s : finset α) (t : (a : α) → finset (δ a)) : finset.card (finset.pi s t) = finset.prod s fun (a : α) => finset.card (t a) :=
  multiset.card_pi (finset.val s) fun (a : α) => (fun (a : α) => finset.val (t a)) a

@[simp] theorem fintype.card_pi_finset {α : Type u_1} [DecidableEq α] [fintype α] {δ : α → Type u_2} (t : (a : α) → finset (δ a)) : finset.card (fintype.pi_finset t) = finset.prod finset.univ fun (a : α) => finset.card (t a) := sorry

@[simp] theorem fintype.card_pi {α : Type u_1} {β : α → Type u_2} [DecidableEq α] [fintype α] [f : (a : α) → fintype (β a)] : fintype.card ((a : α) → β a) = finset.prod finset.univ fun (a : α) => fintype.card (β a) :=
  fintype.card_pi_finset fun (_x : α) => finset.univ

-- FIXME ouch, this should be in the main file.

@[simp] theorem fintype.card_fun {α : Type u_1} {β : Type u_2} [DecidableEq α] [fintype α] [fintype β] : fintype.card (α → β) = fintype.card β ^ fintype.card α := sorry

@[simp] theorem card_vector {α : Type u_1} [fintype α] (n : ℕ) : fintype.card (vector α n) = fintype.card α ^ n := sorry

@[simp] theorem finset.prod_attach_univ {α : Type u_1} {β : Type u_2} [fintype α] [comm_monoid β] (f : (Subtype fun (a : α) => a ∈ finset.univ) → β) : (finset.prod (finset.attach finset.univ) fun (x : Subtype fun (a : α) => a ∈ finset.univ) => f x) =
  finset.prod finset.univ fun (x : α) => f { val := x, property := finset.mem_univ x } := sorry

/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
theorem finset.prod_univ_pi {α : Type u_1} {β : Type u_2} [DecidableEq α] [fintype α] [comm_monoid β] {δ : α → Type u_3} {t : (a : α) → finset (δ a)} (f : ((a : α) → a ∈ finset.univ → δ a) → β) : (finset.prod (finset.pi finset.univ t) fun (x : (a : α) → a ∈ finset.univ → δ a) => f x) =
  finset.prod (fintype.pi_finset t) fun (x : (a : α) → δ a) => f fun (a : α) (_x : a ∈ finset.univ) => x a := sorry

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
theorem finset.prod_univ_sum {α : Type u_1} {β : Type u_2} [DecidableEq α] [fintype α] [comm_semiring β] {δ : α → Type u_1} [(a : α) → DecidableEq (δ a)] {t : (a : α) → finset (δ a)} {f : (a : α) → δ a → β} : (finset.prod finset.univ fun (a : α) => finset.sum (t a) fun (b : δ a) => f a b) =
  finset.sum (fintype.pi_finset t) fun (p : (a : α) → δ a) => finset.prod finset.univ fun (x : α) => f x (p x) := sorry

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
theorem fintype.sum_pow_mul_eq_add_pow (α : Type u_1) [fintype α] {R : Type u_2} [comm_semiring R] (a : R) (b : R) : (finset.sum finset.univ fun (s : finset α) => a ^ finset.card s * b ^ (fintype.card α - finset.card s)) =
  (a + b) ^ fintype.card α :=
  finset.sum_pow_mul_eq_add_pow a b finset.univ

theorem fin.sum_pow_mul_eq_add_pow {n : ℕ} {R : Type u_1} [comm_semiring R] (a : R) (b : R) : (finset.sum finset.univ fun (s : finset (fin n)) => a ^ finset.card s * b ^ (n - finset.card s)) = (a + b) ^ n := sorry

theorem function.bijective.sum_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [fintype α] [fintype β] [add_comm_monoid γ] {f : α → β} (hf : function.bijective f) (g : β → γ) : (finset.sum finset.univ fun (i : α) => g (f i)) = finset.sum finset.univ fun (i : β) => g i := sorry

theorem equiv.sum_comp {α : Type u_1} {β : Type u_2} {γ : Type u_3} [fintype α] [fintype β] [add_comm_monoid γ] (e : α ≃ β) (f : β → γ) : (finset.sum finset.univ fun (i : α) => f (coe_fn e i)) = finset.sum finset.univ fun (i : β) => f i :=
  function.bijective.sum_comp (equiv.bijective e) f

/-- It is equivalent to sum a function over `fin n` or `finset.range n`. -/
theorem fin.sum_univ_eq_sum_range {α : Type u_1} [add_comm_monoid α] (f : ℕ → α) (n : ℕ) : (finset.sum finset.univ fun (i : fin n) => f ↑i) = finset.sum (finset.range n) fun (i : ℕ) => f i := sorry

theorem finset.prod_fin_eq_prod_range {β : Type u_2} [comm_monoid β] {n : ℕ} (c : fin n → β) : (finset.prod finset.univ fun (i : fin n) => c i) =
  finset.prod (finset.range n)
    fun (i : ℕ) => dite (i < n) (fun (h : i < n) => c { val := i, property := h }) fun (h : ¬i < n) => 1 := sorry

theorem finset.prod_subtype {α : Type u_1} {M : Type u_2} [comm_monoid M] {p : α → Prop} {F : fintype (Subtype p)} (s : finset α) (h : ∀ (x : α), x ∈ s ↔ p x) (f : α → M) : (finset.prod s fun (a : α) => f a) = finset.prod finset.univ fun (a : Subtype p) => f ↑a := sorry

theorem finset.sum_to_finset_eq_subtype {α : Type u_1} {M : Type u_2} [add_comm_monoid M] [fintype α] (p : α → Prop) [decidable_pred p] (f : α → M) : (finset.sum (set.to_finset (set_of fun (x : α) => p x)) fun (a : α) => f a) =
  finset.sum finset.univ fun (a : Subtype p) => f ↑a := sorry

theorem finset.prod_fiberwise {α : Type u_1} {β : Type u_2} {γ : Type u_3} [DecidableEq β] [fintype β] [comm_monoid γ] (s : finset α) (f : α → β) (g : α → γ) : (finset.prod finset.univ fun (b : β) => finset.prod (finset.filter (fun (a : α) => f a = b) s) fun (a : α) => g a) =
  finset.prod s fun (a : α) => g a :=
  finset.prod_fiberwise_of_maps_to (fun (x : α) (_x : x ∈ s) => finset.mem_univ (f x)) fun (a : α) => g a

theorem fintype.prod_fiberwise {α : Type u_1} {β : Type u_2} {γ : Type u_3} [fintype α] [DecidableEq β] [fintype β] [comm_monoid γ] (f : α → β) (g : α → γ) : (finset.prod finset.univ fun (b : β) => finset.prod finset.univ fun (a : Subtype fun (a : α) => f a = b) => g ↑a) =
  finset.prod finset.univ fun (a : α) => g a := sorry

theorem fintype.prod_dite {α : Type u_1} {β : Type u_2} [fintype α] {p : α → Prop} [decidable_pred p] [comm_monoid β] (f : (a : α) → p a → β) (g : (a : α) → ¬p a → β) : (finset.prod finset.univ fun (a : α) => dite (p a) (f a) (g a)) =
  (finset.prod finset.univ fun (a : Subtype fun (a : α) => p a) => f (↑a) (subtype.property a)) *
    finset.prod finset.univ fun (a : Subtype fun (a : α) => ¬p a) => g (↑a) (subtype.property a) := sorry

theorem fintype.sum_sum_elim {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [fintype α₁] [fintype α₂] [add_comm_monoid M] (f : α₁ → M) (g : α₂ → M) : (finset.sum finset.univ fun (x : α₁ ⊕ α₂) => sum.elim f g x) =
  (finset.sum finset.univ fun (a₁ : α₁) => f a₁) + finset.sum finset.univ fun (a₂ : α₂) => g a₂ := sorry

theorem fintype.prod_sum_type {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [fintype α₁] [fintype α₂] [comm_monoid M] (f : α₁ ⊕ α₂ → M) : (finset.prod finset.univ fun (x : α₁ ⊕ α₂) => f x) =
  (finset.prod finset.univ fun (a₁ : α₁) => f (sum.inl a₁)) * finset.prod finset.univ fun (a₂ : α₂) => f (sum.inr a₂) := sorry

namespace list


theorem prod_take_of_fn {α : Type u_1} [comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) : prod (take i (of_fn f)) =
  finset.prod (finset.filter (fun (j : fin n) => subtype.val j < i) finset.univ) fun (j : fin n) => f j := sorry

-- `to_additive` does not work on `prod_take_of_fn` because of `0 : ℕ` in the proof.

-- Use `multiplicative` instead.

theorem sum_take_of_fn {α : Type u_1} [add_comm_monoid α] {n : ℕ} (f : fin n → α) (i : ℕ) : sum (take i (of_fn f)) =
  finset.sum (finset.filter (fun (j : fin n) => subtype.val j < i) finset.univ) fun (j : fin n) => f j :=
  prod_take_of_fn f i

theorem prod_of_fn {α : Type u_1} [comm_monoid α] {n : ℕ} {f : fin n → α} : prod (of_fn f) = finset.prod finset.univ fun (i : fin n) => f i := sorry

theorem alternating_sum_eq_finset_sum {G : Type u_1} [add_comm_group G] (L : List G) : alternating_sum L = finset.sum finset.univ fun (i : fin (length L)) => (-1) ^ ↑i •ℤ nth_le L (↑i) (fin.is_lt i) := sorry

theorem alternating_prod_eq_finset_prod {G : Type u_1} [comm_group G] (L : List G) : alternating_prod L = finset.prod finset.univ fun (i : fin (length L)) => nth_le L (↑i) (subtype.property i) ^ (-1) ^ ↑i := sorry

