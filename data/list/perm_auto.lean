/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.bag_inter
import Mathlib.data.list.erase_dup
import Mathlib.data.list.zip
import Mathlib.logic.relation
import Mathlib.data.nat.factorial
import PostPort

universes uu u_1 vv 

namespace Mathlib

/-!
# List permutations
-/

namespace list


/-- `perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive perm {α : Type uu} : List α → List α → Prop
where
| nil : perm [] []
| cons : ∀ (x : α) {l₁ l₂ : List α}, perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
| swap : ∀ (x y : α) (l : List α), perm (y :: x :: l) (x :: y :: l)
| trans : ∀ {l₁ l₂ l₃ : List α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

infixl:50 " ~ " => Mathlib.list.perm

protected theorem perm.refl {α : Type uu} (l : List α) : l ~ l := sorry

protected theorem perm.symm {α : Type uu} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
  perm.rec_on p perm.nil (fun (x : α) (l₁ l₂ : List α) (p₁ : l₁ ~ l₂) (r₁ : l₂ ~ l₁) => perm.cons x r₁)
    (fun (x y : α) (l : List α) => perm.swap y x l)
    fun (l₁ l₂ l₃ : List α) (p₁ : l₁ ~ l₂) (p₂ : l₂ ~ l₃) (r₁ : l₂ ~ l₁) (r₂ : l₃ ~ l₂) => perm.trans r₂ r₁

theorem perm_comm {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ ~ l₂ ↔ l₂ ~ l₁ :=
  { mp := perm.symm, mpr := perm.symm }

theorem perm.swap' {α : Type uu} (x : α) (y : α) {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : y :: x :: l₁ ~ x :: y :: l₂ :=
  perm.trans (perm.swap x y l₁) (perm.cons x (perm.cons y p))

theorem perm.eqv (α : Type u_1) : equivalence perm :=
  mk_equivalence perm perm.refl perm.symm perm.trans

protected instance is_setoid (α : Type u_1) : setoid (List α) :=
  setoid.mk perm (perm.eqv α)

theorem perm.subset {α : Type uu} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : l₁ ⊆ l₂ := sorry

theorem perm.mem_iff {α : Type uu} {a : α} {l₁ : List α} {l₂ : List α} (h : l₁ ~ l₂) : a ∈ l₁ ↔ a ∈ l₂ :=
  { mp := fun (m : a ∈ l₁) => perm.subset h m, mpr := fun (m : a ∈ l₂) => perm.subset (perm.symm h) m }

theorem perm.append_right {α : Type uu} {l₁ : List α} {l₂ : List α} (t₁ : List α) (p : l₁ ~ l₂) : l₁ ++ t₁ ~ l₂ ++ t₁ := sorry

theorem perm.append_left {α : Type uu} {t₁ : List α} {t₂ : List α} (l : List α) : t₁ ~ t₂ → l ++ t₁ ~ l ++ t₂ := sorry

theorem perm.append {α : Type uu} {l₁ : List α} {l₂ : List α} {t₁ : List α} {t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ++ t₁ ~ l₂ ++ t₂ :=
  perm.trans (perm.append_right t₁ p₁) (perm.append_left l₂ p₂)

theorem perm.append_cons {α : Type uu} (a : α) {h₁ : List α} {h₂ : List α} {t₁ : List α} {t₂ : List α} (p₁ : h₁ ~ h₂) (p₂ : t₁ ~ t₂) : h₁ ++ a :: t₁ ~ h₂ ++ a :: t₂ :=
  perm.append p₁ (perm.cons a p₂)

@[simp] theorem perm_middle {α : Type uu} {a : α} {l₁ : List α} {l₂ : List α} : l₁ ++ a :: l₂ ~ a :: (l₁ ++ l₂) := sorry

@[simp] theorem perm_append_singleton {α : Type uu} (a : α) (l : List α) : l ++ [a] ~ a :: l :=
  perm.trans perm_middle
    (eq.mpr (id (Eq._oldrec (Eq.refl (a :: (l ++ []) ~ a :: l)) (append_nil l))) (perm.refl (a :: l)))

theorem perm_append_comm {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ ++ l₂ ~ l₂ ++ l₁ := sorry

theorem concat_perm {α : Type uu} (l : List α) (a : α) : concat l a ~ a :: l := sorry

theorem perm.length_eq {α : Type uu} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : length l₁ = length l₂ := sorry

theorem perm.eq_nil {α : Type uu} {l : List α} (p : l ~ []) : l = [] :=
  eq_nil_of_length_eq_zero (perm.length_eq p)

theorem perm.nil_eq {α : Type uu} {l : List α} (p : [] ~ l) : [] = l :=
  Eq.symm (perm.eq_nil (perm.symm p))

theorem perm_nil {α : Type uu} {l₁ : List α} : l₁ ~ [] ↔ l₁ = [] :=
  { mp := fun (p : l₁ ~ []) => perm.eq_nil p, mpr := fun (e : l₁ = []) => e ▸ perm.refl l₁ }

theorem not_perm_nil_cons {α : Type uu} (x : α) (l : List α) : ¬[] ~ x :: l :=
  fun (ᾰ : [] ~ x :: l) =>
    idRhs (list.no_confusion_type False (x :: l) []) (list.no_confusion (perm.eq_nil (perm.symm ᾰ)))

@[simp] theorem reverse_perm {α : Type uu} (l : List α) : reverse l ~ l := sorry

theorem perm_cons_append_cons {α : Type uu} {l : List α} {l₁ : List α} {l₂ : List α} (a : α) (p : l ~ l₁ ++ l₂) : a :: l ~ l₁ ++ a :: l₂ :=
  perm.trans (perm.cons a p) (perm.symm perm_middle)

@[simp] theorem perm_repeat {α : Type uu} {a : α} {n : ℕ} {l : List α} : l ~ repeat a n ↔ l = repeat a n := sorry

@[simp] theorem repeat_perm {α : Type uu} {a : α} {n : ℕ} {l : List α} : repeat a n ~ l ↔ repeat a n = l :=
  iff.trans (iff.trans perm_comm perm_repeat) eq_comm

@[simp] theorem perm_singleton {α : Type uu} {a : α} {l : List α} : l ~ [a] ↔ l = [a] :=
  perm_repeat

@[simp] theorem singleton_perm {α : Type uu} {a : α} {l : List α} : [a] ~ l ↔ [a] = l :=
  repeat_perm

theorem perm.eq_singleton {α : Type uu} {a : α} {l : List α} (p : l ~ [a]) : l = [a] :=
  iff.mp perm_singleton p

theorem perm.singleton_eq {α : Type uu} {a : α} {l : List α} (p : [a] ~ l) : [a] = l :=
  Eq.symm (perm.eq_singleton (perm.symm p))

theorem singleton_perm_singleton {α : Type uu} {a : α} {b : α} : [a] ~ [b] ↔ a = b := sorry

theorem perm_cons_erase {α : Type uu} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : l ~ a :: list.erase l a := sorry

theorem perm_induction_on {α : Type uu} {P : List α → List α → Prop} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) (h₁ : P [] []) (h₂ : ∀ (x : α) (l₁ l₂ : List α), l₁ ~ l₂ → P l₁ l₂ → P (x :: l₁) (x :: l₂)) (h₃ : ∀ (x y : α) (l₁ l₂ : List α), l₁ ~ l₂ → P l₁ l₂ → P (y :: x :: l₁) (x :: y :: l₂)) (h₄ : ∀ (l₁ l₂ l₃ : List α), l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) : P l₁ l₂ :=
  (fun (P_refl : ∀ (l : List α), P l l) =>
      perm.rec_on p h₁ h₂ (fun (x y : α) (l : List α) => h₃ x y l l (perm.refl l) (P_refl l)) h₄)
    fun (l : List α) => list.rec_on l h₁ fun (x : α) (xs : List α) (ih : P xs xs) => h₂ x xs xs (perm.refl xs) ih

theorem perm.filter_map {α : Type uu} {β : Type vv} (f : α → Option β) {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : filter_map f l₁ ~ filter_map f l₂ := sorry

theorem perm.map {α : Type uu} {β : Type vv} (f : α → β) {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : map f l₁ ~ map f l₂ :=
  filter_map_eq_map f ▸ perm.filter_map (some ∘ f) p

theorem perm.pmap {α : Type uu} {β : Type vv} {p : α → Prop} (f : (a : α) → p a → β) {l₁ : List α} {l₂ : List α} : l₁ ~ l₂ → ∀ {H₁ : ∀ (a : α), a ∈ l₁ → p a} {H₂ : ∀ (a : α), a ∈ l₂ → p a}, pmap f l₁ H₁ ~ pmap f l₂ H₂ := sorry

theorem perm.filter {α : Type uu} (p : α → Prop) [decidable_pred p] {l₁ : List α} {l₂ : List α} (s : l₁ ~ l₂) : filter p l₁ ~ filter p l₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (filter p l₁ ~ filter p l₂)) (Eq.symm (filter_map_eq_filter p))))
    (perm.filter_map (option.guard p) s)

theorem exists_perm_sublist {α : Type uu} {l₁ : List α} {l₂ : List α} {l₂' : List α} (s : l₁ <+ l₂) (p : l₂ ~ l₂') : ∃ (l₁' : List α), ∃ (H : l₁' ~ l₁), l₁' <+ l₂' := sorry

theorem perm.sizeof_eq_sizeof {α : Type uu} [SizeOf α] {l₁ : List α} {l₂ : List α} (h : l₁ ~ l₂) : list.sizeof l₁ = list.sizeof l₂ := sorry

theorem perm_comp_perm {α : Type uu} : relation.comp perm perm = perm := sorry

theorem perm_comp_forall₂ {α : Type uu} {β : Type vv} {r : α → β → Prop} {l : List α} {u : List α} {v : List β} (hlu : l ~ u) (huv : forall₂ r u v) : relation.comp (forall₂ r) perm l v := sorry

theorem forall₂_comp_perm_eq_perm_comp_forall₂ {α : Type uu} {β : Type vv} {r : α → β → Prop} : relation.comp (forall₂ r) perm = relation.comp perm (forall₂ r) := sorry

theorem rel_perm_imp {α : Type uu} {β : Type vv} {r : α → β → Prop} (hr : relator.right_unique r) : relator.lift_fun (forall₂ r) (forall₂ r ⇒ implies) perm perm := sorry

theorem rel_perm {α : Type uu} {β : Type vv} {r : α → β → Prop} (hr : relator.bi_unique r) : relator.lift_fun (forall₂ r) (forall₂ r ⇒ Iff) perm perm := sorry

/-- `subperm l₁ l₂`, denoted `l₁ <+~ l₂`, means that `l₁` is a sublist of
  a permutation of `l₂`. This is an analogue of `l₁ ⊆ l₂` which respects
  multiplicities of elements, and is used for the `≤` relation on multisets. -/
def subperm {α : Type uu} (l₁ : List α) (l₂ : List α)  :=
  ∃ (l : List α), ∃ (H : l ~ l₁), l <+ l₂

infixl:50 " <+~ " => Mathlib.list.subperm

theorem nil_subperm {α : Type uu} {l : List α} : [] <+~ l :=
  Exists.intro []
    (Exists.intro perm.nil
      (eq.mpr (id (propext ((fun {α : Type uu} (l : List α) => iff_true_intro (nil_sublist l)) l))) trivial))

theorem perm.subperm_left {α : Type uu} {l : List α} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : l <+~ l₁ ↔ l <+~ l₂ := sorry

theorem perm.subperm_right {α : Type uu} {l₁ : List α} {l₂ : List α} {l : List α} (p : l₁ ~ l₂) : l₁ <+~ l ↔ l₂ <+~ l := sorry

theorem sublist.subperm {α : Type uu} {l₁ : List α} {l₂ : List α} (s : l₁ <+ l₂) : l₁ <+~ l₂ :=
  Exists.intro l₁ (Exists.intro (perm.refl l₁) s)

theorem perm.subperm {α : Type uu} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : l₁ <+~ l₂ :=
  Exists.intro l₂ (Exists.intro (perm.symm p) (sublist.refl l₂))

theorem subperm.refl {α : Type uu} (l : List α) : l <+~ l :=
  perm.subperm (perm.refl l)

theorem subperm.trans {α : Type uu} {l₁ : List α} {l₂ : List α} {l₃ : List α} : l₁ <+~ l₂ → l₂ <+~ l₃ → l₁ <+~ l₃ := sorry

theorem subperm.length_le {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ <+~ l₂ → length l₁ ≤ length l₂ := sorry

theorem subperm.perm_of_length_le {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ <+~ l₂ → length l₂ ≤ length l₁ → l₁ ~ l₂ := sorry

theorem subperm.antisymm {α : Type uu} {l₁ : List α} {l₂ : List α} (h₁ : l₁ <+~ l₂) (h₂ : l₂ <+~ l₁) : l₁ ~ l₂ :=
  subperm.perm_of_length_le h₁ (subperm.length_le h₂)

theorem subperm.subset {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ <+~ l₂ → l₁ ⊆ l₂ := sorry

theorem sublist.exists_perm_append {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ <+ l₂ → ∃ (l : List α), l₂ ~ l₁ ++ l := sorry

theorem perm.countp_eq {α : Type uu} (p : α → Prop) [decidable_pred p] {l₁ : List α} {l₂ : List α} (s : l₁ ~ l₂) : countp p l₁ = countp p l₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (countp p l₁ = countp p l₂)) (countp_eq_length_filter p l₁)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (length (filter p l₁) = countp p l₂)) (countp_eq_length_filter p l₂)))
      (perm.length_eq (perm.filter p s)))

theorem subperm.countp_le {α : Type uu} (p : α → Prop) [decidable_pred p] {l₁ : List α} {l₂ : List α} : l₁ <+~ l₂ → countp p l₁ ≤ countp p l₂ := sorry

theorem perm.count_eq {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) (a : α) : count a l₁ = count a l₂ :=
  perm.countp_eq (Eq a) p

theorem subperm.count_le {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (s : l₁ <+~ l₂) (a : α) : count a l₁ ≤ count a l₂ :=
  subperm.countp_le (Eq a) s

theorem perm.foldl_eq' {α : Type uu} {β : Type vv} {f : β → α → β} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : (∀ (x : α), x ∈ l₁ → ∀ (y : α), y ∈ l₁ → ∀ (z : β), f (f z x) y = f (f z y) x) → ∀ (b : β), foldl f b l₁ = foldl f b l₂ := sorry

theorem perm.foldl_eq {α : Type uu} {β : Type vv} {f : β → α → β} {l₁ : List α} {l₂ : List α} (rcomm : right_commutative f) (p : l₁ ~ l₂) (b : β) : foldl f b l₁ = foldl f b l₂ :=
  perm.foldl_eq' p fun (x : α) (hx : x ∈ l₁) (y : α) (hy : y ∈ l₁) (z : β) => rcomm z x y

theorem perm.foldr_eq {α : Type uu} {β : Type vv} {f : α → β → β} {l₁ : List α} {l₂ : List α} (lcomm : left_commutative f) (p : l₁ ~ l₂) (b : β) : foldr f b l₁ = foldr f b l₂ := sorry

theorem perm.rec_heq {α : Type uu} {β : List α → Sort u_1} {f : (a : α) → (l : List α) → β l → β (a :: l)} {b : β []} {l : List α} {l' : List α} (hl : l ~ l') (f_congr : ∀ {a : α} {l l' : List α} {b : β l} {b' : β l'}, l ~ l' → b == b' → f a l b == f a l' b') (f_swap : ∀ {a a' : α} {l : List α} {b : β l}, f a (a' :: l) (f a' l b) == f a' (a :: l) (f a l b)) : List.rec b f l == List.rec b f l' := sorry

theorem perm.fold_op_eq {α : Type uu} {op : α → α → α} [is_associative α op] [is_commutative α op] {l₁ : List α} {l₂ : List α} {a : α} (h : l₁ ~ l₂) : foldl op a l₁ = foldl op a l₂ :=
  perm.foldl_eq (right_comm op is_commutative.comm is_associative.assoc) h a

/-- If elements of a list commute with each other, then their product does not
depend on the order of elements-/
theorem perm.sum_eq' {α : Type uu} [add_monoid α] {l₁ : List α} {l₂ : List α} (h : l₁ ~ l₂) (hc : pairwise (fun (x y : α) => x + y = y + x) l₁) : sum l₁ = sum l₂ := sorry

theorem perm.sum_eq {α : Type uu} [add_comm_monoid α] {l₁ : List α} {l₂ : List α} (h : l₁ ~ l₂) : sum l₁ = sum l₂ :=
  perm.fold_op_eq h

theorem sum_reverse {α : Type uu} [add_comm_monoid α] (l : List α) : sum (reverse l) = sum l :=
  perm.sum_eq (reverse_perm l)

theorem perm_inv_core {α : Type uu} {a : α} {l₁ : List α} {l₂ : List α} {r₁ : List α} {r₂ : List α} : l₁ ++ a :: r₁ ~ l₂ ++ a :: r₂ → l₁ ++ r₁ ~ l₂ ++ r₂ := sorry

theorem perm.cons_inv {α : Type uu} {a : α} {l₁ : List α} {l₂ : List α} : a :: l₁ ~ a :: l₂ → l₁ ~ l₂ :=
  perm_inv_core

@[simp] theorem perm_cons {α : Type uu} (a : α) {l₁ : List α} {l₂ : List α} : a :: l₁ ~ a :: l₂ ↔ l₁ ~ l₂ :=
  { mp := perm.cons_inv, mpr := perm.cons a }

theorem perm_append_left_iff {α : Type uu} {l₁ : List α} {l₂ : List α} (l : List α) : l ++ l₁ ~ l ++ l₂ ↔ l₁ ~ l₂ := sorry

theorem perm_append_right_iff {α : Type uu} {l₁ : List α} {l₂ : List α} (l : List α) : l₁ ++ l ~ l₂ ++ l ↔ l₁ ~ l₂ := sorry

theorem perm_option_to_list {α : Type uu} {o₁ : Option α} {o₂ : Option α} : option.to_list o₁ ~ option.to_list o₂ ↔ o₁ = o₂ := sorry

theorem subperm_cons {α : Type uu} (a : α) {l₁ : List α} {l₂ : List α} : a :: l₁ <+~ a :: l₂ ↔ l₁ <+~ l₂ := sorry

theorem cons_subperm_of_mem {α : Type uu} {a : α} {l₁ : List α} {l₂ : List α} (d₁ : nodup l₁) (h₁ : ¬a ∈ l₁) (h₂ : a ∈ l₂) (s : l₁ <+~ l₂) : a :: l₁ <+~ l₂ := sorry

theorem subperm_append_left {α : Type uu} {l₁ : List α} {l₂ : List α} (l : List α) : l ++ l₁ <+~ l ++ l₂ ↔ l₁ <+~ l₂ := sorry

theorem subperm_append_right {α : Type uu} {l₁ : List α} {l₂ : List α} (l : List α) : l₁ ++ l <+~ l₂ ++ l ↔ l₁ <+~ l₂ :=
  iff.trans (iff.trans (perm.subperm_left perm_append_comm) (perm.subperm_right perm_append_comm)) (subperm_append_left l)

theorem subperm.exists_of_length_lt {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ <+~ l₂ → length l₁ < length l₂ → ∃ (a : α), a :: l₁ <+~ l₂ := sorry

theorem subperm_of_subset_nodup {α : Type uu} {l₁ : List α} {l₂ : List α} (d : nodup l₁) (H : l₁ ⊆ l₂) : l₁ <+~ l₂ := sorry

theorem perm_ext {α : Type uu} {l₁ : List α} {l₂ : List α} (d₁ : nodup l₁) (d₂ : nodup l₂) : l₁ ~ l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂ := sorry

theorem nodup.sublist_ext {α : Type uu} {l₁ : List α} {l₂ : List α} {l : List α} (d : nodup l) (s₁ : l₁ <+ l) (s₂ : l₂ <+ l) : l₁ ~ l₂ ↔ l₁ = l₂ := sorry

-- attribute [congr]

theorem perm.erase {α : Type uu} [DecidableEq α] (a : α) {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : list.erase l₁ a ~ list.erase l₂ a := sorry

theorem subperm_cons_erase {α : Type uu} [DecidableEq α] (a : α) (l : List α) : l <+~ a :: list.erase l a := sorry

theorem erase_subperm {α : Type uu} [DecidableEq α] (a : α) (l : List α) : list.erase l a <+~ l :=
  sublist.subperm (erase_sublist a l)

theorem subperm.erase {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (a : α) (h : l₁ <+~ l₂) : list.erase l₁ a <+~ list.erase l₂ a := sorry

theorem perm.diff_right {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (t : List α) (h : l₁ ~ l₂) : list.diff l₁ t ~ list.diff l₂ t := sorry

theorem perm.diff_left {α : Type uu} [DecidableEq α] (l : List α) {t₁ : List α} {t₂ : List α} (h : t₁ ~ t₂) : list.diff l t₁ = list.diff l t₂ := sorry

theorem perm.diff {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} {t₁ : List α} {t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : list.diff l₁ t₁ ~ list.diff l₂ t₂ :=
  perm.diff_left l₂ ht ▸ perm.diff_right t₁ hl

theorem subperm.diff_right {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (h : l₁ <+~ l₂) (t : List α) : list.diff l₁ t <+~ list.diff l₂ t := sorry

theorem erase_cons_subperm_cons_erase {α : Type uu} [DecidableEq α] (a : α) (b : α) (l : List α) : list.erase (a :: l) b <+~ a :: list.erase l b := sorry

theorem subperm_cons_diff {α : Type uu} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} : list.diff (a :: l₁) l₂ <+~ a :: list.diff l₁ l₂ := sorry

theorem subset_cons_diff {α : Type uu} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} : list.diff (a :: l₁) l₂ ⊆ a :: list.diff l₁ l₂ :=
  subperm.subset subperm_cons_diff

theorem perm.bag_inter_right {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (t : List α) (h : l₁ ~ l₂) : list.bag_inter l₁ t ~ list.bag_inter l₂ t := sorry

theorem perm.bag_inter_left {α : Type uu} [DecidableEq α] (l : List α) {t₁ : List α} {t₂ : List α} (p : t₁ ~ t₂) : list.bag_inter l t₁ = list.bag_inter l t₂ := sorry

theorem perm.bag_inter {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} {t₁ : List α} {t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) : list.bag_inter l₁ t₁ ~ list.bag_inter l₂ t₂ :=
  perm.bag_inter_left l₂ ht ▸ perm.bag_inter_right t₁ hl

theorem cons_perm_iff_perm_erase {α : Type uu} [DecidableEq α] {a : α} {l₁ : List α} {l₂ : List α} : a :: l₁ ~ l₂ ↔ a ∈ l₂ ∧ l₁ ~ list.erase l₂ a := sorry

theorem perm_iff_count {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} : l₁ ~ l₂ ↔ ∀ (a : α), count a l₁ = count a l₂ := sorry

protected instance decidable_perm {α : Type uu} [DecidableEq α] (l₁ : List α) (l₂ : List α) : Decidable (l₁ ~ l₂) :=
  sorry

-- @[congr]

theorem perm.erase_dup {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : erase_dup l₁ ~ erase_dup l₂ := sorry

-- attribute [congr]

theorem perm.insert {α : Type uu} [DecidableEq α] (a : α) {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : insert a l₁ ~ insert a l₂ := sorry

theorem perm_insert_swap {α : Type uu} [DecidableEq α] (x : α) (y : α) (l : List α) : insert x (insert y l) ~ insert y (insert x l) := sorry

theorem perm_insert_nth {α : Type u_1} (x : α) (l : List α) {n : ℕ} (h : n ≤ length l) : insert_nth n x l ~ x :: l := sorry

theorem perm.union_right {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (t₁ : List α) (h : l₁ ~ l₂) : l₁ ∪ t₁ ~ l₂ ∪ t₁ := sorry

theorem perm.union_left {α : Type uu} [DecidableEq α] (l : List α) {t₁ : List α} {t₂ : List α} (h : t₁ ~ t₂) : l ∪ t₁ ~ l ∪ t₂ := sorry

-- @[congr]

theorem perm.union {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} {t₁ : List α} {t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∪ t₁ ~ l₂ ∪ t₂ :=
  perm.trans (perm.union_right t₁ p₁) (perm.union_left l₂ p₂)

theorem perm.inter_right {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} (t₁ : List α) : l₁ ~ l₂ → l₁ ∩ t₁ ~ l₂ ∩ t₁ :=
  perm.filter fun (_x : α) => _x ∈ t₁

theorem perm.inter_left {α : Type uu} [DecidableEq α] (l : List α) {t₁ : List α} {t₂ : List α} (p : t₁ ~ t₂) : l ∩ t₁ = l ∩ t₂ := sorry

-- @[congr]

theorem perm.inter {α : Type uu} [DecidableEq α] {l₁ : List α} {l₂ : List α} {t₁ : List α} {t₂ : List α} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : l₁ ∩ t₁ ~ l₂ ∩ t₂ :=
  perm.inter_left l₂ p₂ ▸ perm.inter_right t₁ p₁

theorem perm.inter_append {α : Type uu} [DecidableEq α] {l : List α} {t₁ : List α} {t₂ : List α} (h : disjoint t₁ t₂) : l ∩ (t₁ ++ t₂) ~ l ∩ t₁ ++ l ∩ t₂ := sorry

theorem perm.pairwise_iff {α : Type uu} {R : α → α → Prop} (S : symmetric R) {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) : pairwise R l₁ ↔ pairwise R l₂ := sorry

theorem perm.nodup_iff {α : Type uu} {l₁ : List α} {l₂ : List α} : l₁ ~ l₂ → (nodup l₁ ↔ nodup l₂) :=
  perm.pairwise_iff ne.symm

theorem perm.bind_right {α : Type uu} {β : Type vv} {l₁ : List α} {l₂ : List α} (f : α → List β) (p : l₁ ~ l₂) : list.bind l₁ f ~ list.bind l₂ f := sorry

theorem perm.bind_left {α : Type uu} {β : Type vv} (l : List α) {f : α → List β} {g : α → List β} (h : ∀ (a : α), f a ~ g a) : list.bind l f ~ list.bind l g := sorry

theorem perm.product_right {α : Type uu} {β : Type vv} {l₁ : List α} {l₂ : List α} (t₁ : List β) (p : l₁ ~ l₂) : product l₁ t₁ ~ product l₂ t₁ :=
  perm.bind_right (fun (a : α) => map (Prod.mk a) t₁) p

theorem perm.product_left {α : Type uu} {β : Type vv} (l : List α) {t₁ : List β} {t₂ : List β} (p : t₁ ~ t₂) : product l t₁ ~ product l t₂ :=
  perm.bind_left l fun (a : α) => perm.map (Prod.mk a) p

theorem perm.product {α : Type uu} {β : Type vv} {l₁ : List α} {l₂ : List α} {t₁ : List β} {t₂ : List β} (p₁ : l₁ ~ l₂) (p₂ : t₁ ~ t₂) : product l₁ t₁ ~ product l₂ t₂ :=
  perm.trans (perm.product_right t₁ p₁) (perm.product_left l₂ p₂)

theorem sublists_cons_perm_append {α : Type uu} (a : α) (l : List α) : sublists (a :: l) ~ sublists l ++ map (List.cons a) (sublists l) := sorry

theorem sublists_perm_sublists' {α : Type uu} (l : List α) : sublists l ~ sublists' l := sorry

theorem revzip_sublists {α : Type uu} (l : List α) (l₁ : List α) (l₂ : List α) : (l₁, l₂) ∈ revzip (sublists l) → l₁ ++ l₂ ~ l := sorry

theorem revzip_sublists' {α : Type uu} (l : List α) (l₁ : List α) (l₂ : List α) : (l₁, l₂) ∈ revzip (sublists' l) → l₁ ++ l₂ ~ l := sorry

theorem perm_lookmap {α : Type uu} (f : α → Option α) {l₁ : List α} {l₂ : List α} (H : pairwise (fun (a b : α) => ∀ (c : α), c ∈ f a → ∀ (d : α), d ∈ f b → a = b ∧ c = d) l₁) (p : l₁ ~ l₂) : lookmap f l₁ ~ lookmap f l₂ := sorry

theorem perm.erasep {α : Type uu} (f : α → Prop) [decidable_pred f] {l₁ : List α} {l₂ : List α} (H : pairwise (fun (a b : α) => f a → f b → False) l₁) (p : l₁ ~ l₂) : erasep f l₁ ~ erasep f l₂ := sorry

theorem perm.take_inter {α : Type u_1} [DecidableEq α] {xs : List α} {ys : List α} (n : ℕ) (h : xs ~ ys) (h' : nodup ys) : take n xs ~ list.inter ys (take n xs) := sorry

theorem perm.drop_inter {α : Type u_1} [DecidableEq α] {xs : List α} {ys : List α} (n : ℕ) (h : xs ~ ys) (h' : nodup ys) : drop n xs ~ list.inter ys (drop n xs) := sorry

theorem perm.slice_inter {α : Type u_1} [DecidableEq α] {xs : List α} {ys : List α} (n : ℕ) (m : ℕ) (h : xs ~ ys) (h' : nodup ys) : slice n m xs ~ ys ∩ slice n m xs := sorry

/- enumerating permutations -/

theorem permutations_aux2_fst {α : Type uu} {β : Type vv} (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) : prod.fst (permutations_aux2 t ts r ys f) = ys ++ ts := sorry

@[simp] theorem permutations_aux2_snd_nil {α : Type uu} {β : Type vv} (t : α) (ts : List α) (r : List β) (f : List α → β) : prod.snd (permutations_aux2 t ts r [] f) = r :=
  rfl

@[simp] theorem permutations_aux2_snd_cons {α : Type uu} {β : Type vv} (t : α) (ts : List α) (r : List β) (y : α) (ys : List α) (f : List α → β) : prod.snd (permutations_aux2 t ts r (y :: ys) f) =
  f (t :: y :: ys ++ ts) :: prod.snd (permutations_aux2 t ts r ys fun (x : List α) => f (y :: x)) := sorry

theorem permutations_aux2_append {α : Type uu} {β : Type vv} (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) : prod.snd (permutations_aux2 t ts [] ys f) ++ r = prod.snd (permutations_aux2 t ts r ys f) := sorry

theorem mem_permutations_aux2 {α : Type uu} {t : α} {ts : List α} {ys : List α} {l : List α} {l' : List α} : l' ∈ prod.snd (permutations_aux2 t ts [] ys (append l)) ↔
  ∃ (l₁ : List α), ∃ (l₂ : List α), l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts := sorry

theorem mem_permutations_aux2' {α : Type uu} {t : α} {ts : List α} {ys : List α} {l : List α} : l ∈ prod.snd (permutations_aux2 t ts [] ys id) ↔
  ∃ (l₁ : List α), ∃ (l₂ : List α), l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts := sorry

theorem length_permutations_aux2 {α : Type uu} {β : Type vv} (t : α) (ts : List α) (ys : List α) (f : List α → β) : length (prod.snd (permutations_aux2 t ts [] ys f)) = length ys := sorry

theorem foldr_permutations_aux2 {α : Type uu} (t : α) (ts : List α) (r : List (List α)) (L : List (List α)) : foldr (fun (y : List α) (r : List (List α)) => prod.snd (permutations_aux2 t ts r y id)) r L =
  (list.bind L fun (y : List α) => prod.snd (permutations_aux2 t ts [] y id)) ++ r := sorry

theorem mem_foldr_permutations_aux2 {α : Type uu} {t : α} {ts : List α} {r : List (List α)} {L : List (List α)} {l' : List α} : l' ∈ foldr (fun (y : List α) (r : List (List α)) => prod.snd (permutations_aux2 t ts r y id)) r L ↔
  l' ∈ r ∨ ∃ (l₁ : List α), ∃ (l₂ : List α), l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts := sorry

theorem length_foldr_permutations_aux2 {α : Type uu} (t : α) (ts : List α) (r : List (List α)) (L : List (List α)) : length (foldr (fun (y : List α) (r : List (List α)) => prod.snd (permutations_aux2 t ts r y id)) r L) =
  sum (map length L) + length r := sorry

theorem length_foldr_permutations_aux2' {α : Type uu} (t : α) (ts : List α) (r : List (List α)) (L : List (List α)) (n : ℕ) (H : ∀ (l : List α), l ∈ L → length l = n) : length (foldr (fun (y : List α) (r : List (List α)) => prod.snd (permutations_aux2 t ts r y id)) r L) =
  n * length L + length r := sorry

theorem perm_of_mem_permutations_aux {α : Type uu} {ts : List α} {is : List α} {l : List α} : l ∈ permutations_aux ts is → l ~ ts ++ is := sorry

theorem perm_of_mem_permutations {α : Type uu} {l₁ : List α} {l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  or.elim (eq_or_mem_of_mem_cons h) (fun (e : l₁ = l₂) => e ▸ perm.refl l₁)
    fun (m : l₁ ∈ permutations_aux l₂ []) => append_nil l₂ ▸ perm_of_mem_permutations_aux m

theorem length_permutations_aux {α : Type uu} (ts : List α) (is : List α) : length (permutations_aux ts is) + nat.factorial (length is) = nat.factorial (length ts + length is) := sorry

theorem length_permutations {α : Type uu} (l : List α) : length (permutations l) = nat.factorial (length l) :=
  length_permutations_aux l []

theorem mem_permutations_of_perm_lemma {α : Type uu} {is : List α} {l : List α} (H : l ~ [] ++ is → (∃ (ts' : List α), ∃ (H : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutations_aux is []) : l ~ is → l ∈ permutations is := sorry

theorem mem_permutations_aux_of_perm {α : Type uu} {ts : List α} {is : List α} {l : List α} : l ~ is ++ ts → (∃ (is' : List α), ∃ (H : is' ~ is), l = is' ++ ts) ∨ l ∈ permutations_aux ts is := sorry

@[simp] theorem mem_permutations {α : Type uu} (s : List α) (t : List α) : s ∈ permutations t ↔ s ~ t :=
  { mp := perm_of_mem_permutations, mpr := mem_permutations_of_perm_lemma mem_permutations_aux_of_perm }

