/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.list.perm
import Mathlib.algebra.group_power.default
import Mathlib.PostPort

universes u u_1 u_4 u_2 u_3 

namespace Mathlib

/-!
# Multisets

These are implemented as the quotient of a list by permutations.

## Notation

We define the global infix notation `::ₘ` for `multiset.cons`.
-/

/-- `multiset α` is the quotient of `list α` by list permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def multiset (α : Type u) :=
  quotient (list.is_setoid α)

namespace multiset


protected instance has_coe {α : Type u_1} : has_coe (List α) (multiset α) :=
  has_coe.mk (Quot.mk setoid.r)

@[simp] theorem quot_mk_to_coe {α : Type u_1} (l : List α) : quotient.mk l = ↑l :=
  rfl

@[simp] theorem quot_mk_to_coe' {α : Type u_1} (l : List α) : Quot.mk has_equiv.equiv l = ↑l :=
  rfl

@[simp] theorem quot_mk_to_coe'' {α : Type u_1} (l : List α) : Quot.mk setoid.r l = ↑l :=
  rfl

@[simp] theorem coe_eq_coe {α : Type u_1} {l₁ : List α} {l₂ : List α} : ↑l₁ = ↑l₂ ↔ l₁ ~ l₂ :=
  quotient.eq

protected instance has_decidable_eq {α : Type u_1} [DecidableEq α] : DecidableEq (multiset α) :=
  sorry

/-- defines a size for a multiset by referring to the size of the underlying list -/
protected def sizeof {α : Type u_1} [SizeOf α] (s : multiset α) : ℕ :=
  quot.lift_on s sizeof sorry

protected instance has_sizeof {α : Type u_1} [SizeOf α] : SizeOf (multiset α) :=
  { sizeOf := multiset.sizeof }

/-! ### Empty multiset -/

/-- `0 : multiset α` is the empty set -/
protected def zero {α : Type u_1} : multiset α :=
  ↑[]

protected instance has_zero {α : Type u_1} : HasZero (multiset α) :=
  { zero := multiset.zero }

protected instance has_emptyc {α : Type u_1} : has_emptyc (multiset α) :=
  has_emptyc.mk 0

protected instance inhabited {α : Type u_1} : Inhabited (multiset α) :=
  { default := 0 }

@[simp] theorem coe_nil_eq_zero {α : Type u_1} : ↑[] = 0 :=
  rfl

@[simp] theorem empty_eq_zero {α : Type u_1} : ∅ = 0 :=
  rfl

theorem coe_eq_zero {α : Type u_1} (l : List α) : ↑l = 0 ↔ l = [] :=
  iff.trans coe_eq_coe list.perm_nil

/-! ### `multiset.cons` -/

/-- `cons a s` is the multiset which contains `s` plus one more
  instance of `a`. -/
def cons {α : Type u_1} (a : α) (s : multiset α) : multiset α :=
  quot.lift_on s (fun (l : List α) => ↑(a :: l)) sorry

infixr:67 " ::ₘ " => Mathlib.multiset.cons

protected instance has_insert {α : Type u_1} : has_insert α (multiset α) :=
  has_insert.mk cons

@[simp] theorem insert_eq_cons {α : Type u_1} (a : α) (s : multiset α) : insert a s = a ::ₘ s :=
  rfl

@[simp] theorem cons_coe {α : Type u_1} (a : α) (l : List α) : a ::ₘ ↑l = ↑(a :: l) :=
  rfl

theorem singleton_coe {α : Type u_1} (a : α) : a ::ₘ 0 = ↑[a] :=
  rfl

@[simp] theorem cons_inj_left {α : Type u_1} {a : α} {b : α} (s : multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b := sorry

@[simp] theorem cons_inj_right {α : Type u_1} (a : α) {s : multiset α} {t : multiset α} : a ::ₘ s = a ::ₘ t ↔ s = t := sorry

protected theorem induction {α : Type u_1} {p : multiset α → Prop} (h₁ : p 0) (h₂ : ∀ {a : α} {s : multiset α}, p s → p (a ::ₘ s)) (s : multiset α) : p s :=
  quot.induction_on s
    fun (l : List α) => List.rec h₁ (fun (l_hd : α) (l_tl : List α) (ih : p (Quot.mk setoid.r l_tl)) => h₂ ih) l

protected theorem induction_on {α : Type u_1} {p : multiset α → Prop} (s : multiset α) (h₁ : p 0) (h₂ : ∀ {a : α} {s : multiset α}, p s → p (a ::ₘ s)) : p s :=
  multiset.induction h₁ h₂ s

theorem cons_swap {α : Type u_1} (a : α) (b : α) (s : multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
  quot.induction_on s fun (l : List α) => quotient.sound (list.perm.swap b a l)

/-- Dependent recursor on multisets.

TODO: should be @[recursor 6], but then the definition of `multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected def rec {α : Type u_1} {C : multiset α → Sort u_4} (C_0 : C 0) (C_cons : (a : α) → (m : multiset α) → C m → C (a ::ₘ m)) (C_cons_heq : ∀ (a a' : α) (m : multiset α) (b : C m), C_cons a (a' ::ₘ m) (C_cons a' m b) == C_cons a' (a ::ₘ m) (C_cons a m b)) (m : multiset α) : C m :=
  quotient.hrec_on m (List.rec C_0 fun (a : α) (l : List α) (b : C (quotient.mk l)) => C_cons a (quotient.mk l) b) sorry

protected def rec_on {α : Type u_1} {C : multiset α → Sort u_4} (m : multiset α) (C_0 : C 0) (C_cons : (a : α) → (m : multiset α) → C m → C (a ::ₘ m)) (C_cons_heq : ∀ (a a' : α) (m : multiset α) (b : C m), C_cons a (a' ::ₘ m) (C_cons a' m b) == C_cons a' (a ::ₘ m) (C_cons a m b)) : C m :=
  multiset.rec C_0 C_cons C_cons_heq m

@[simp] theorem rec_on_0 {α : Type u_1} {C : multiset α → Sort u_4} {C_0 : C 0} {C_cons : (a : α) → (m : multiset α) → C m → C (a ::ₘ m)} {C_cons_heq : ∀ (a a' : α) (m : multiset α) (b : C m), C_cons a (a' ::ₘ m) (C_cons a' m b) == C_cons a' (a ::ₘ m) (C_cons a m b)} : multiset.rec_on 0 C_0 C_cons C_cons_heq = C_0 :=
  rfl

@[simp] theorem rec_on_cons {α : Type u_1} {C : multiset α → Sort u_4} {C_0 : C 0} {C_cons : (a : α) → (m : multiset α) → C m → C (a ::ₘ m)} {C_cons_heq : ∀ (a a' : α) (m : multiset α) (b : C m), C_cons a (a' ::ₘ m) (C_cons a' m b) == C_cons a' (a ::ₘ m) (C_cons a m b)} (a : α) (m : multiset α) : multiset.rec_on (a ::ₘ m) C_0 C_cons C_cons_heq = C_cons a m (multiset.rec_on m C_0 C_cons C_cons_heq) :=
  quotient.induction_on m fun (l : List α) => rfl

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def mem {α : Type u_1} (a : α) (s : multiset α) :=
  quot.lift_on s (fun (l : List α) => a ∈ l) sorry

protected instance has_mem {α : Type u_1} : has_mem α (multiset α) :=
  has_mem.mk mem

@[simp] theorem mem_coe {α : Type u_1} {a : α} {l : List α} : a ∈ ↑l ↔ a ∈ l :=
  iff.rfl

protected instance decidable_mem {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : Decidable (a ∈ s) :=
  quot.rec_on_subsingleton s (list.decidable_mem a)

@[simp] theorem mem_cons {α : Type u_1} {a : α} {b : α} {s : multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
  quot.induction_on s fun (l : List α) => iff.rfl

theorem mem_cons_of_mem {α : Type u_1} {a : α} {b : α} {s : multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
  iff.mpr mem_cons (Or.inr h)

@[simp] theorem mem_cons_self {α : Type u_1} (a : α) (s : multiset α) : a ∈ a ::ₘ s :=
  iff.mpr mem_cons (Or.inl rfl)

theorem forall_mem_cons {α : Type u_1} {p : α → Prop} {a : α} {s : multiset α} : (∀ (x : α), x ∈ a ::ₘ s → p x) ↔ p a ∧ ∀ (x : α), x ∈ s → p x :=
  quotient.induction_on' s fun (L : List α) => list.forall_mem_cons

theorem exists_cons_of_mem {α : Type u_1} {s : multiset α} {a : α} : a ∈ s → ∃ (t : multiset α), s = a ::ₘ t := sorry

@[simp] theorem not_mem_zero {α : Type u_1} (a : α) : ¬a ∈ 0 :=
  id

theorem eq_zero_of_forall_not_mem {α : Type u_1} {s : multiset α} : (∀ (x : α), ¬x ∈ s) → s = 0 := sorry

theorem eq_zero_iff_forall_not_mem {α : Type u_1} {s : multiset α} : s = 0 ↔ ∀ (a : α), ¬a ∈ s :=
  { mp := fun (h : s = 0) => Eq.symm h ▸ fun (_x : α) => not_false, mpr := eq_zero_of_forall_not_mem }

theorem exists_mem_of_ne_zero {α : Type u_1} {s : multiset α} : s ≠ 0 → ∃ (a : α), a ∈ s := sorry

@[simp] theorem zero_ne_cons {α : Type u_1} {a : α} {m : multiset α} : 0 ≠ a ::ₘ m :=
  fun (h : 0 = a ::ₘ m) => (fun (this : a ∈ 0) => not_mem_zero a this) (Eq.symm h ▸ mem_cons_self a m)

@[simp] theorem cons_ne_zero {α : Type u_1} {a : α} {m : multiset α} : a ::ₘ m ≠ 0 :=
  ne.symm zero_ne_cons

theorem cons_eq_cons {α : Type u_1} {a : α} {b : α} {as : multiset α} {bs : multiset α} : a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a ≠ b ∧ ∃ (cs : multiset α), as = b ::ₘ cs ∧ bs = a ::ₘ cs := sorry

/-! ### `multiset.subset` -/

/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
protected def subset {α : Type u_1} (s : multiset α) (t : multiset α) :=
  ∀ {a : α}, a ∈ s → a ∈ t

protected instance has_subset {α : Type u_1} : has_subset (multiset α) :=
  has_subset.mk multiset.subset

@[simp] theorem coe_subset {α : Type u_1} {l₁ : List α} {l₂ : List α} : ↑l₁ ⊆ ↑l₂ ↔ l₁ ⊆ l₂ :=
  iff.rfl

@[simp] theorem subset.refl {α : Type u_1} (s : multiset α) : s ⊆ s :=
  fun (a : α) (h : a ∈ s) => h

theorem subset.trans {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} : s ⊆ t → t ⊆ u → s ⊆ u :=
  fun (h₁ : s ⊆ t) (h₂ : t ⊆ u) (a : α) (m : a ∈ s) => h₂ (h₁ m)

theorem subset_iff {α : Type u_1} {s : multiset α} {t : multiset α} : s ⊆ t ↔ ∀ {x : α}, x ∈ s → x ∈ t :=
  iff.rfl

theorem mem_of_subset {α : Type u_1} {s : multiset α} {t : multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t :=
  h

@[simp] theorem zero_subset {α : Type u_1} (s : multiset α) : 0 ⊆ s :=
  fun (a : α) => not.elim (list.not_mem_nil a)

@[simp] theorem cons_subset {α : Type u_1} {a : α} {s : multiset α} {t : multiset α} : a ::ₘ s ⊆ t ↔ a ∈ t ∧ s ⊆ t := sorry

theorem eq_zero_of_subset_zero {α : Type u_1} {s : multiset α} (h : s ⊆ 0) : s = 0 :=
  eq_zero_of_forall_not_mem h

theorem subset_zero {α : Type u_1} {s : multiset α} : s ⊆ 0 ↔ s = 0 :=
  { mp := eq_zero_of_subset_zero, mpr := fun (xeq : s = 0) => Eq.symm xeq ▸ subset.refl 0 }

/-- Produces a list of the elements in the multiset using choice. -/
def to_list {α : Type u_1} (s : multiset α) : List α :=
  classical.some sorry

@[simp] theorem to_list_zero {α : Type u_1} : to_list 0 = [] :=
  iff.mp (coe_eq_zero (to_list 0)) (classical.some_spec (quotient.exists_rep multiset.zero))

theorem coe_to_list {α : Type u_1} (s : multiset α) : ↑(to_list s) = s :=
  classical.some_spec (quotient.exists_rep s)

theorem mem_to_list {α : Type u_1} (a : α) (s : multiset α) : a ∈ to_list s ↔ a ∈ s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ to_list s ↔ a ∈ s)) (Eq.symm (propext mem_coe))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ∈ ↑(to_list s) ↔ a ∈ s)) (coe_to_list s))) (iff.refl (a ∈ s)))

/-! ### Partial order on `multiset`s -/

/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
protected def le {α : Type u_1} (s : multiset α) (t : multiset α) :=
  quotient.lift_on₂ s t list.subperm sorry

protected instance partial_order {α : Type u_1} : partial_order (multiset α) :=
  partial_order.mk multiset.le (preorder.lt._default multiset.le) sorry sorry sorry

theorem subset_of_le {α : Type u_1} {s : multiset α} {t : multiset α} : s ≤ t → s ⊆ t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.subperm.subset

theorem mem_of_le {α : Type u_1} {s : multiset α} {t : multiset α} {a : α} (h : s ≤ t) : a ∈ s → a ∈ t :=
  mem_of_subset (subset_of_le h)

@[simp] theorem coe_le {α : Type u_1} {l₁ : List α} {l₂ : List α} : ↑l₁ ≤ ↑l₂ ↔ l₁ <+~ l₂ :=
  iff.rfl

theorem le_induction_on {α : Type u_1} {C : multiset α → multiset α → Prop} {s : multiset α} {t : multiset α} (h : s ≤ t) (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C ↑l₁ ↑l₂) : C s t := sorry

theorem zero_le {α : Type u_1} (s : multiset α) : 0 ≤ s :=
  quot.induction_on s fun (l : List α) => list.sublist.subperm (list.nil_sublist l)

theorem le_zero {α : Type u_1} {s : multiset α} : s ≤ 0 ↔ s = 0 :=
  { mp := fun (h : s ≤ 0) => le_antisymm h (zero_le s), mpr := le_of_eq }

theorem lt_cons_self {α : Type u_1} (s : multiset α) (a : α) : s < a ::ₘ s := sorry

theorem le_cons_self {α : Type u_1} (s : multiset α) (a : α) : s ≤ a ::ₘ s :=
  le_of_lt (lt_cons_self s a)

theorem cons_le_cons_iff {α : Type u_1} (a : α) {s : multiset α} {t : multiset α} : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.subperm_cons a

theorem cons_le_cons {α : Type u_1} (a : α) {s : multiset α} {t : multiset α} : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
  iff.mpr (cons_le_cons_iff a)

theorem le_cons_of_not_mem {α : Type u_1} {a : α} {s : multiset α} {t : multiset α} (m : ¬a ∈ s) : s ≤ a ::ₘ t ↔ s ≤ t := sorry

/-! ### Additive monoid -/

/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add {α : Type u_1} (s₁ : multiset α) (s₂ : multiset α) : multiset α :=
  quotient.lift_on₂ s₁ s₂ (fun (l₁ l₂ : List α) => ↑(l₁ ++ l₂)) sorry

protected instance has_add {α : Type u_1} : Add (multiset α) :=
  { add := multiset.add }

@[simp] theorem coe_add {α : Type u_1} (s : List α) (t : List α) : ↑s + ↑t = ↑(s ++ t) :=
  rfl

protected theorem add_comm {α : Type u_1} (s : multiset α) (t : multiset α) : s + t = t + s :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => quot.sound list.perm_append_comm

protected theorem zero_add {α : Type u_1} (s : multiset α) : 0 + s = s :=
  quot.induction_on s fun (l : List α) => rfl

theorem singleton_add {α : Type u_1} (a : α) (s : multiset α) : ↑[a] + s = a ::ₘ s :=
  rfl

protected theorem add_le_add_left {α : Type u_1} (s : multiset α) {t : multiset α} {u : multiset α} : s + t ≤ s + u ↔ t ≤ u :=
  quotient.induction_on₃ s t u fun (l₁ l₂ l₃ : List α) => list.subperm_append_left l₁

protected theorem add_left_cancel {α : Type u_1} (s : multiset α) {t : multiset α} {u : multiset α} (h : s + t = s + u) : t = u :=
  le_antisymm (iff.mp (multiset.add_le_add_left s) (le_of_eq h))
    (iff.mp (multiset.add_le_add_left s) (le_of_eq (Eq.symm h)))

protected instance ordered_cancel_add_comm_monoid {α : Type u_1} : ordered_cancel_add_comm_monoid (multiset α) :=
  ordered_cancel_add_comm_monoid.mk Add.add sorry multiset.add_left_cancel 0 multiset.zero_add sorry multiset.add_comm
    sorry partial_order.le partial_order.lt sorry sorry sorry sorry sorry

theorem le_add_right {α : Type u_1} (s : multiset α) (t : multiset α) : s ≤ s + t := sorry

theorem le_add_left {α : Type u_1} (s : multiset α) (t : multiset α) : s ≤ t + s := sorry

theorem le_iff_exists_add {α : Type u_1} {s : multiset α} {t : multiset α} : s ≤ t ↔ ∃ (u : multiset α), t = s + u := sorry

protected instance canonically_ordered_add_monoid {α : Type u_1} : canonically_ordered_add_monoid (multiset α) :=
  canonically_ordered_add_monoid.mk ordered_cancel_add_comm_monoid.add sorry ordered_cancel_add_comm_monoid.zero sorry
    sorry sorry ordered_cancel_add_comm_monoid.le ordered_cancel_add_comm_monoid.lt sorry sorry sorry sorry sorry 0
    zero_le le_iff_exists_add

@[simp] theorem cons_add {α : Type u_1} (a : α) (s : multiset α) (t : multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := sorry

@[simp] theorem add_cons {α : Type u_1} (a : α) (s : multiset α) (t : multiset α) : s + a ::ₘ t = a ::ₘ (s + t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s + a ::ₘ t = a ::ₘ (s + t))) (add_comm s (a ::ₘ t))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (a ::ₘ t + s = a ::ₘ (s + t))) (cons_add a t s)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (a ::ₘ (t + s) = a ::ₘ (s + t))) (add_comm t s))) (Eq.refl (a ::ₘ (s + t)))))

@[simp] theorem mem_add {α : Type u_1} {a : α} {s : multiset α} {t : multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.mem_append

/-! ### Cardinality -/

/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card {α : Type u_1} : multiset α →+ ℕ :=
  add_monoid_hom.mk (fun (s : multiset α) => quot.lift_on s list.length sorry) sorry sorry

@[simp] theorem coe_card {α : Type u_1} (l : List α) : coe_fn card ↑l = list.length l :=
  rfl

@[simp] theorem card_zero {α : Type u_1} : coe_fn card 0 = 0 :=
  rfl

theorem card_add {α : Type u_1} (s : multiset α) (t : multiset α) : coe_fn card (s + t) = coe_fn card s + coe_fn card t :=
  add_monoid_hom.map_add card s t

theorem card_smul {α : Type u_1} (s : multiset α) (n : ℕ) : coe_fn card (n •ℕ s) = n * coe_fn card s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn card (n •ℕ s) = n * coe_fn card s)) (add_monoid_hom.map_nsmul card s n)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (n •ℕ coe_fn card s = n * coe_fn card s)) (nat.nsmul_eq_mul n (coe_fn card s))))
      (Eq.refl (n * coe_fn card s)))

@[simp] theorem card_cons {α : Type u_1} (a : α) (s : multiset α) : coe_fn card (a ::ₘ s) = coe_fn card s + 1 :=
  quot.induction_on s fun (l : List α) => rfl

@[simp] theorem card_singleton {α : Type u_1} (a : α) : coe_fn card (a ::ₘ 0) = 1 := sorry

theorem card_le_of_le {α : Type u_1} {s : multiset α} {t : multiset α} (h : s ≤ t) : coe_fn card s ≤ coe_fn card t :=
  le_induction_on h fun (l₁ l₂ : List α) => list.length_le_of_sublist

theorem eq_of_le_of_card_le {α : Type u_1} {s : multiset α} {t : multiset α} (h : s ≤ t) : coe_fn card t ≤ coe_fn card s → s = t :=
  le_induction_on h
    fun (l₁ l₂ : List α) (s : l₁ <+ l₂) (h₂ : coe_fn card ↑l₂ ≤ coe_fn card ↑l₁) =>
      congr_arg coe (list.eq_of_sublist_of_length_le s h₂)

theorem card_lt_of_lt {α : Type u_1} {s : multiset α} {t : multiset α} (h : s < t) : coe_fn card s < coe_fn card t :=
  lt_of_not_ge fun (h₂ : coe_fn card s ≥ coe_fn card t) => ne_of_lt h (eq_of_le_of_card_le (le_of_lt h) h₂)

theorem lt_iff_cons_le {α : Type u_1} {s : multiset α} {t : multiset α} : s < t ↔ ∃ (a : α), a ::ₘ s ≤ t := sorry

@[simp] theorem card_eq_zero {α : Type u_1} {s : multiset α} : coe_fn card s = 0 ↔ s = 0 := sorry

theorem card_pos {α : Type u_1} {s : multiset α} : 0 < coe_fn card s ↔ s ≠ 0 :=
  iff.trans pos_iff_ne_zero (not_congr card_eq_zero)

theorem card_pos_iff_exists_mem {α : Type u_1} {s : multiset α} : 0 < coe_fn card s ↔ ∃ (a : α), a ∈ s :=
  quot.induction_on s fun (l : List α) => list.length_pos_iff_exists_mem

def strong_induction_on {α : Type u_1} {p : multiset α → Sort u_2} (s : multiset α) : ((s : multiset α) → ((t : multiset α) → t < s → p t) → p s) → p s :=
  sorry

theorem strong_induction_eq {α : Type u_1} {p : multiset α → Sort u_2} (s : multiset α) (H : (s : multiset α) → ((t : multiset α) → t < s → p t) → p s) : strong_induction_on s H = H s fun (t : multiset α) (h : t < s) => strong_induction_on t H := sorry

theorem case_strong_induction_on {α : Type u_1} {p : multiset α → Prop} (s : multiset α) (h₀ : p 0) (h₁ : ∀ (a : α) (s : multiset α), (∀ (t : multiset α), t ≤ s → p t) → p (a ::ₘ s)) : p s := sorry

/-! ### Singleton -/

protected instance has_singleton {α : Type u_1} : has_singleton α (multiset α) :=
  has_singleton.mk fun (a : α) => a ::ₘ 0

protected instance is_lawful_singleton {α : Type u_1} : is_lawful_singleton α (multiset α) :=
  is_lawful_singleton.mk fun (a : α) => rfl

@[simp] theorem singleton_eq_singleton {α : Type u_1} (a : α) : singleton a = a ::ₘ 0 :=
  rfl

@[simp] theorem mem_singleton {α : Type u_1} {a : α} {b : α} : b ∈ a ::ₘ 0 ↔ b = a := sorry

theorem mem_singleton_self {α : Type u_1} (a : α) : a ∈ a ::ₘ 0 :=
  mem_cons_self a 0

theorem singleton_inj {α : Type u_1} {a : α} {b : α} : a ::ₘ 0 = b ::ₘ 0 ↔ a = b :=
  cons_inj_left 0

@[simp] theorem singleton_ne_zero {α : Type u_1} (a : α) : a ::ₘ 0 ≠ 0 :=
  ne_of_gt (lt_cons_self 0 a)

@[simp] theorem singleton_le {α : Type u_1} {a : α} {s : multiset α} : a ::ₘ 0 ≤ s ↔ a ∈ s := sorry

theorem card_eq_one {α : Type u_1} {s : multiset α} : coe_fn card s = 1 ↔ ∃ (a : α), s = a ::ₘ 0 := sorry

/-! ### `multiset.repeat` -/

/-- `repeat a n` is the multiset containing only `a` with multiplicity `n`. -/
def repeat {α : Type u_1} (a : α) (n : ℕ) : multiset α :=
  ↑(list.repeat a n)

@[simp] theorem repeat_zero {α : Type u_1} (a : α) : repeat a 0 = 0 :=
  rfl

@[simp] theorem repeat_succ {α : Type u_1} (a : α) (n : ℕ) : repeat a (n + 1) = a ::ₘ repeat a n := sorry

@[simp] theorem repeat_one {α : Type u_1} (a : α) : repeat a 1 = a ::ₘ 0 := sorry

@[simp] theorem card_repeat {α : Type u_1} (a : α) (n : ℕ) : coe_fn card (repeat a n) = n :=
  list.length_repeat

theorem eq_of_mem_repeat {α : Type u_1} {a : α} {b : α} {n : ℕ} : b ∈ repeat a n → b = a :=
  list.eq_of_mem_repeat

theorem eq_repeat' {α : Type u_1} {a : α} {s : multiset α} : s = repeat a (coe_fn card s) ↔ ∀ (b : α), b ∈ s → b = a := sorry

theorem eq_repeat_of_mem {α : Type u_1} {a : α} {s : multiset α} : (∀ (b : α), b ∈ s → b = a) → s = repeat a (coe_fn card s) :=
  iff.mpr eq_repeat'

theorem eq_repeat {α : Type u_1} {a : α} {n : ℕ} {s : multiset α} : s = repeat a n ↔ coe_fn card s = n ∧ ∀ (b : α), b ∈ s → b = a := sorry

theorem repeat_subset_singleton {α : Type u_1} (a : α) (n : ℕ) : repeat a n ⊆ a ::ₘ 0 :=
  list.repeat_subset_singleton

theorem repeat_le_coe {α : Type u_1} {a : α} {n : ℕ} {l : List α} : repeat a n ≤ ↑l ↔ list.repeat a n <+ l := sorry

/-! ### Erasing one copy of an element -/

/-- `erase s a` is the multiset that subtracts 1 from the
  multiplicity of `a`. -/
def erase {α : Type u_1} [DecidableEq α] (s : multiset α) (a : α) : multiset α :=
  quot.lift_on s (fun (l : List α) => ↑(list.erase l a)) sorry

@[simp] theorem coe_erase {α : Type u_1} [DecidableEq α] (l : List α) (a : α) : erase (↑l) a = ↑(list.erase l a) :=
  rfl

@[simp] theorem erase_zero {α : Type u_1} [DecidableEq α] (a : α) : erase 0 a = 0 :=
  rfl

@[simp] theorem erase_cons_head {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : erase (a ::ₘ s) a = s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.erase_cons_head a l)

@[simp] theorem erase_cons_tail {α : Type u_1} [DecidableEq α] {a : α} {b : α} (s : multiset α) (h : b ≠ a) : erase (b ::ₘ s) a = b ::ₘ erase s a :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.erase_cons_tail l h)

@[simp] theorem erase_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : ¬a ∈ s → erase s a = s :=
  quot.induction_on s fun (l : List α) (h : ¬a ∈ Quot.mk setoid.r l) => congr_arg coe (list.erase_of_not_mem h)

@[simp] theorem cons_erase {α : Type u_1} [DecidableEq α] {s : multiset α} {a : α} : a ∈ s → a ::ₘ erase s a = s :=
  quot.induction_on s
    fun (l : List α) (h : a ∈ Quot.mk setoid.r l) => quot.sound (list.perm.symm (list.perm_cons_erase h))

theorem le_cons_erase {α : Type u_1} [DecidableEq α] (s : multiset α) (a : α) : s ≤ a ::ₘ erase s a :=
  dite (a ∈ s) (fun (h : a ∈ s) => le_of_eq (Eq.symm (cons_erase h)))
    fun (h : ¬a ∈ s) => eq.mpr (id (Eq._oldrec (Eq.refl (s ≤ a ::ₘ erase s a)) (erase_of_not_mem h))) (le_cons_self s a)

theorem erase_add_left_pos {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} (t : multiset α) : a ∈ s → erase (s + t) a = erase s a + t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) (h : a ∈ quotient.mk l₁) => congr_arg coe (list.erase_append_left l₂ h)

theorem erase_add_right_pos {α : Type u_1} [DecidableEq α] {a : α} (s : multiset α) {t : multiset α} (h : a ∈ t) : erase (s + t) a = s + erase t a := sorry

theorem erase_add_right_neg {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} (t : multiset α) : ¬a ∈ s → erase (s + t) a = s + erase t a :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) (h : ¬a ∈ quotient.mk l₁) => congr_arg coe (list.erase_append_right l₂ h)

theorem erase_add_left_neg {α : Type u_1} [DecidableEq α] {a : α} (s : multiset α) {t : multiset α} (h : ¬a ∈ t) : erase (s + t) a = erase s a + t := sorry

theorem erase_le {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : erase s a ≤ s :=
  quot.induction_on s fun (l : List α) => list.sublist.subperm (list.erase_sublist a l)

@[simp] theorem erase_lt {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : erase s a < s ↔ a ∈ s := sorry

theorem erase_subset {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : erase s a ⊆ s :=
  subset_of_le (erase_le a s)

theorem mem_erase_of_ne {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : multiset α} (ab : a ≠ b) : a ∈ erase s b ↔ a ∈ s :=
  quot.induction_on s fun (l : List α) => list.mem_erase_of_ne ab

theorem mem_of_mem_erase {α : Type u_1} [DecidableEq α] {a : α} {b : α} {s : multiset α} : a ∈ erase s b → a ∈ s :=
  mem_of_subset (erase_subset b s)

theorem erase_comm {α : Type u_1} [DecidableEq α] (s : multiset α) (a : α) (b : α) : erase (erase s a) b = erase (erase s b) a :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.erase_comm a b l)

theorem erase_le_erase {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (a : α) (h : s ≤ t) : erase s a ≤ erase t a :=
  le_induction_on h fun (l₁ l₂ : List α) (h : l₁ <+ l₂) => list.sublist.subperm (list.sublist.erase a h)

theorem erase_le_iff_le_cons {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {a : α} : erase s a ≤ t ↔ s ≤ a ::ₘ t := sorry

@[simp] theorem card_erase_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : a ∈ s → coe_fn card (erase s a) = Nat.pred (coe_fn card s) :=
  quot.induction_on s fun (l : List α) => list.length_erase_of_mem

theorem card_erase_lt_of_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : a ∈ s → coe_fn card (erase s a) < coe_fn card s :=
  fun (h : a ∈ s) => card_lt_of_lt (iff.mpr erase_lt h)

theorem card_erase_le {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : coe_fn card (erase s a) ≤ coe_fn card s :=
  card_le_of_le (erase_le a s)

@[simp] theorem coe_reverse {α : Type u_1} (l : List α) : ↑(list.reverse l) = ↑l :=
  quot.sound (list.reverse_perm l)

/-! ### `multiset.map` -/

/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map {α : Type u_1} {β : Type u_2} (f : α → β) (s : multiset α) : multiset β :=
  quot.lift_on s (fun (l : List α) => ↑(list.map f l)) sorry

theorem forall_mem_map_iff {α : Type u_1} {β : Type u_2} {f : α → β} {p : β → Prop} {s : multiset α} : (∀ (y : β), y ∈ map f s → p y) ↔ ∀ (x : α), x ∈ s → p (f x) :=
  quotient.induction_on' s fun (L : List α) => list.forall_mem_map_iff

@[simp] theorem coe_map {α : Type u_1} {β : Type u_2} (f : α → β) (l : List α) : map f ↑l = ↑(list.map f l) :=
  rfl

@[simp] theorem map_zero {α : Type u_1} {β : Type u_2} (f : α → β) : map f 0 = 0 :=
  rfl

@[simp] theorem map_cons {α : Type u_1} {β : Type u_2} (f : α → β) (a : α) (s : multiset α) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  quot.induction_on s fun (l : List α) => rfl

theorem map_singleton {α : Type u_1} {β : Type u_2} (f : α → β) (a : α) : map f (singleton a) = singleton (f a) :=
  rfl

theorem map_repeat {α : Type u_1} {β : Type u_2} (f : α → β) (a : α) (k : ℕ) : map f (repeat a k) = repeat (f a) k := sorry

@[simp] theorem map_add {α : Type u_1} {β : Type u_2} (f : α → β) (s : multiset α) (t : multiset α) : map f (s + t) = map f s + map f t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => congr_arg coe (list.map_append f l₁ l₂)

protected instance map.is_add_monoid_hom {α : Type u_1} {β : Type u_2} (f : α → β) : is_add_monoid_hom (map f) :=
  is_add_monoid_hom.mk (map_zero f)

theorem map_nsmul {α : Type u_1} {β : Type u_2} (f : α → β) (n : ℕ) (s : multiset α) : map f (n •ℕ s) = n •ℕ map f s :=
  add_monoid_hom.map_nsmul (add_monoid_hom.of (map f)) s n

@[simp] theorem mem_map {α : Type u_1} {β : Type u_2} {f : α → β} {b : β} {s : multiset α} : b ∈ map f s ↔ ∃ (a : α), a ∈ s ∧ f a = b :=
  quot.induction_on s fun (l : List α) => list.mem_map

@[simp] theorem card_map {α : Type u_1} {β : Type u_2} (f : α → β) (s : multiset α) : coe_fn card (map f s) = coe_fn card s :=
  quot.induction_on s fun (l : List α) => list.length_map f l

@[simp] theorem map_eq_zero {α : Type u_1} {β : Type u_2} {s : multiset α} {f : α → β} : map f s = 0 ↔ s = 0 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (map f s = 0 ↔ s = 0)) (Eq.symm (propext card_eq_zero))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn card (map f s) = 0 ↔ s = 0)) (card_map f s)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (coe_fn card s = 0 ↔ s = 0)) (propext card_eq_zero))) (iff.refl (s = 0))))

theorem mem_map_of_mem {α : Type u_1} {β : Type u_2} (f : α → β) {a : α} {s : multiset α} (h : a ∈ s) : f a ∈ map f s :=
  iff.mpr mem_map (Exists.intro a { left := h, right := rfl })

theorem mem_map_of_injective {α : Type u_1} {β : Type u_2} {f : α → β} (H : function.injective f) {a : α} {s : multiset α} : f a ∈ map f s ↔ a ∈ s :=
  quot.induction_on s fun (l : List α) => list.mem_map_of_injective H

@[simp] theorem map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (g : β → γ) (f : α → β) (s : multiset α) : map g (map f s) = map (g ∘ f) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.map_map g f l)

theorem map_id {α : Type u_1} (s : multiset α) : map id s = s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.map_id l)

@[simp] theorem map_id' {α : Type u_1} (s : multiset α) : map (fun (x : α) => x) s = s :=
  map_id s

@[simp] theorem map_const {α : Type u_1} {β : Type u_2} (s : multiset α) (b : β) : map (function.const α b) s = repeat b (coe_fn card s) :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.map_const l b)

theorem map_congr {α : Type u_1} {β : Type u_2} {f : α → β} {g : α → β} {s : multiset α} : (∀ (x : α), x ∈ s → f x = g x) → map f s = map g s :=
  quot.induction_on s
    fun (l : List α) (H : ∀ (x : α), x ∈ Quot.mk setoid.r l → f x = g x) => congr_arg coe (list.map_congr H)

theorem map_hcongr {α : Type u_1} {β : Type u_2} {β' : Type u_2} {m : multiset α} {f : α → β} {f' : α → β'} (h : β = β') (hf : ∀ (a : α), a ∈ m → f a == f' a) : map f m == map f' m := sorry

theorem eq_of_mem_map_const {α : Type u_1} {β : Type u_2} {b₁ : β} {b₂ : β} {l : List α} (h : b₁ ∈ map (function.const α b₂) ↑l) : b₁ = b₂ :=
  eq_of_mem_repeat (eq.mp (Eq._oldrec (Eq.refl (b₁ ∈ map (function.const α b₂) ↑l)) (map_const (↑l) b₂)) h)

@[simp] theorem map_le_map {α : Type u_1} {β : Type u_2} {f : α → β} {s : multiset α} {t : multiset α} (h : s ≤ t) : map f s ≤ map f t :=
  le_induction_on h fun (l₁ l₂ : List α) (h : l₁ <+ l₂) => list.sublist.subperm (list.sublist.map f h)

@[simp] theorem map_subset_map {α : Type u_1} {β : Type u_2} {f : α → β} {s : multiset α} {t : multiset α} (H : s ⊆ t) : map f s ⊆ map f t := sorry

/-! ### `multiset.fold` -/

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl {α : Type u_1} {β : Type u_2} (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) : β :=
  quot.lift_on s (fun (l : List α) => list.foldl f b l) sorry

@[simp] theorem foldl_zero {α : Type u_1} {β : Type u_2} (f : β → α → β) (H : right_commutative f) (b : β) : foldl f H b 0 = b :=
  rfl

@[simp] theorem foldl_cons {α : Type u_1} {β : Type u_2} (f : β → α → β) (H : right_commutative f) (b : β) (a : α) (s : multiset α) : foldl f H b (a ::ₘ s) = foldl f H (f b a) s :=
  quot.induction_on s fun (l : List α) => rfl

@[simp] theorem foldl_add {α : Type u_1} {β : Type u_2} (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) (t : multiset α) : foldl f H b (s + t) = foldl f H (foldl f H b s) t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.foldl_append f b l₁ l₂

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) : β :=
  quot.lift_on s (fun (l : List α) => list.foldr f b l) sorry

@[simp] theorem foldr_zero {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) : foldr f H b 0 = b :=
  rfl

@[simp] theorem foldr_cons {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) (a : α) (s : multiset α) : foldr f H b (a ::ₘ s) = f a (foldr f H b s) :=
  quot.induction_on s fun (l : List α) => rfl

@[simp] theorem foldr_add {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) (t : multiset α) : foldr f H b (s + t) = foldr f H (foldr f H b t) s :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.foldr_append f b l₁ l₂

@[simp] theorem coe_foldr {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) (l : List α) : foldr f H b ↑l = list.foldr f b l :=
  rfl

@[simp] theorem coe_foldl {α : Type u_1} {β : Type u_2} (f : β → α → β) (H : right_commutative f) (b : β) (l : List α) : foldl f H b ↑l = list.foldl f b l :=
  rfl

theorem coe_foldr_swap {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) (l : List α) : foldr f H b ↑l = list.foldl (fun (x : β) (y : α) => f y x) b l :=
  Eq.trans (Eq.symm (congr_arg (foldr f H b) (coe_reverse l))) (list.foldr_reverse f b l)

theorem foldr_swap {α : Type u_1} {β : Type u_2} (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) : foldr f H b s = foldl (fun (x : β) (y : α) => f y x) (fun (x : β) (y z : α) => Eq.symm (H y z x)) b s :=
  quot.induction_on s fun (l : List α) => coe_foldr_swap f H b l

theorem foldl_swap {α : Type u_1} {β : Type u_2} (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) : foldl f H b s = foldr (fun (x : α) (y : β) => f y x) (fun (x y : α) (z : β) => Eq.symm (H z x y)) b s :=
  Eq.symm (foldr_swap (fun (y : α) (x : β) => f x y) (fun (x y : α) (z : β) => Eq.symm (H z x y)) b s)

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
def sum {α : Type u_1} [add_comm_monoid α] : multiset α → α :=
  foldr Add.add sorry 0

theorem prod_eq_foldr {α : Type u_1} [comm_monoid α] (s : multiset α) : prod s =
  foldr Mul.mul
    (fun (x y z : α) =>
      eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : α) (e_1 : a = a_1) (ᾰ ᾰ_1 : α) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (x * (y * z))
              (x * (y * z)) (Eq.refl (x * (y * z))) (y * (x * z)) (x * (y * z)) (mul_left_comm y x z))
            (propext (eq_self_iff_true (x * (y * z))))))
        trivial)
    1 s :=
  rfl

theorem sum_eq_foldl {α : Type u_1} [add_comm_monoid α] (s : multiset α) : sum s =
  foldl Add.add
    (fun (x y z : α) =>
      eq.mpr
        (id
          (Eq.trans
            ((fun (a a_1 : α) (e_1 : a = a_1) (ᾰ ᾰ_1 : α) (e_2 : ᾰ = ᾰ_1) => congr (congr_arg Eq e_1) e_2) (x + y + z)
              (x + y + z) (Eq.refl (x + y + z)) (x + z + y) (x + y + z) (add_right_comm x z y))
            (propext (eq_self_iff_true (x + y + z)))))
        trivial)
    0 s := sorry

@[simp] theorem coe_sum {α : Type u_1} [add_comm_monoid α] (l : List α) : sum ↑l = list.sum l :=
  sum_eq_foldl ↑l

@[simp] theorem sum_zero {α : Type u_1} [add_comm_monoid α] : sum 0 = 0 :=
  rfl

@[simp] theorem sum_cons {α : Type u_1} [add_comm_monoid α] (a : α) (s : multiset α) : sum (a ::ₘ s) = a + sum s :=
  foldr_cons Add.add sum._proof_1 0 a s

theorem sum_singleton {α : Type u_1} [add_comm_monoid α] (a : α) : sum (a ::ₘ 0) = a := sorry

@[simp] theorem sum_add {α : Type u_1} [add_comm_monoid α] (s : multiset α) (t : multiset α) : sum (s + t) = sum s + sum t := sorry

protected instance sum.is_add_monoid_hom {α : Type u_1} [add_comm_monoid α] : is_add_monoid_hom sum :=
  is_add_monoid_hom.mk sum_zero

theorem prod_smul {α : Type u_1} [comm_monoid α] (m : multiset α) (n : ℕ) : prod (n •ℕ m) = prod m ^ n := sorry

@[simp] theorem prod_repeat {α : Type u_1} [comm_monoid α] (a : α) (n : ℕ) : prod (repeat a n) = a ^ n := sorry

@[simp] theorem sum_repeat {α : Type u_1} [add_comm_monoid α] (a : α) (n : ℕ) : sum (repeat a n) = n •ℕ a :=
  prod_repeat

theorem prod_map_one {α : Type u_1} {γ : Type u_3} [comm_monoid γ] {m : multiset α} : prod (map (fun (a : α) => 1) m) = 1 := sorry

theorem sum_map_zero {α : Type u_1} {γ : Type u_3} [add_comm_monoid γ] {m : multiset α} : sum (map (fun (a : α) => 0) m) = 0 := sorry

@[simp] theorem sum_map_add {α : Type u_1} {γ : Type u_3} [add_comm_monoid γ] {m : multiset α} {f : α → γ} {g : α → γ} : sum (map (fun (a : α) => f a + g a) m) = sum (map f m) + sum (map g m) := sorry

theorem prod_map_prod_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [comm_monoid γ] (m : multiset α) (n : multiset β) {f : α → β → γ} : prod (map (fun (a : α) => prod (map (fun (b : β) => f a b) n)) m) =
  prod (map (fun (b : β) => prod (map (fun (a : α) => f a b) m)) n) := sorry

theorem sum_map_sum_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} [add_comm_monoid γ] (m : multiset α) (n : multiset β) {f : α → β → γ} : sum (map (fun (a : α) => sum (map (fun (b : β) => f a b) n)) m) =
  sum (map (fun (b : β) => sum (map (fun (a : α) => f a b) m)) n) :=
  prod_map_prod_map

theorem sum_map_mul_left {α : Type u_1} {β : Type u_2} [semiring β] {b : β} {s : multiset α} {f : α → β} : sum (map (fun (a : α) => b * f a) s) = b * sum (map f s) := sorry

theorem sum_map_mul_right {α : Type u_1} {β : Type u_2} [semiring β] {b : β} {s : multiset α} {f : α → β} : sum (map (fun (a : α) => f a * b) s) = sum (map f s) * b := sorry

theorem prod_ne_zero {R : Type u_1} [comm_semiring R] [no_zero_divisors R] [nontrivial R] {m : multiset R} : (∀ (x : R), x ∈ m → x ≠ 0) → prod m ≠ 0 := sorry

theorem prod_eq_zero {α : Type u_1} [comm_semiring α] {s : multiset α} (h : 0 ∈ s) : prod s = 0 := sorry

theorem sum_hom {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [add_comm_monoid β] (s : multiset α) (f : α →+ β) : sum (map (⇑f) s) = coe_fn f (sum s) := sorry

theorem prod_hom_rel {α : Type u_1} {β : Type u_2} {γ : Type u_3} [comm_monoid β] [comm_monoid γ] (s : multiset α) {r : β → γ → Prop} {f : α → β} {g : α → γ} (h₁ : r 1 1) (h₂ : ∀ {a : α} {b : β} {c : γ}, r b c → r (f a * b) (g a * c)) : r (prod (map f s)) (prod (map g s)) := sorry

theorem dvd_prod {α : Type u_1} [comm_monoid α] {a : α} {s : multiset α} : a ∈ s → a ∣ prod s := sorry

theorem prod_dvd_prod {α : Type u_1} [comm_monoid α] {s : multiset α} {t : multiset α} (h : s ≤ t) : prod s ∣ prod t := sorry

theorem prod_eq_zero_iff {α : Type u_1} [comm_cancel_monoid_with_zero α] [nontrivial α] {s : multiset α} : prod s = 0 ↔ 0 ∈ s := sorry

theorem sum_nonneg {α : Type u_1} [ordered_add_comm_monoid α] {m : multiset α} : (∀ (x : α), x ∈ m → 0 ≤ x) → 0 ≤ sum m := sorry

theorem single_le_prod {α : Type u_1} [ordered_comm_monoid α] {m : multiset α} : (∀ (x : α), x ∈ m → 1 ≤ x) → ∀ (x : α), x ∈ m → x ≤ prod m := sorry

theorem all_one_of_le_one_le_of_prod_eq_one {α : Type u_1} [ordered_comm_monoid α] {m : multiset α} : (∀ (x : α), x ∈ m → 1 ≤ x) → prod m = 1 → ∀ (x : α), x ∈ m → x = 1 := sorry

theorem sum_eq_zero_iff {α : Type u_1} [canonically_ordered_add_monoid α] {m : multiset α} : sum m = 0 ↔ ∀ (x : α), x ∈ m → x = 0 := sorry

theorem le_sum_of_subadditive {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [ordered_add_comm_monoid β] (f : α → β) (h_zero : f 0 = 0) (h_add : ∀ (x y : α), f (x + y) ≤ f x + f y) (s : multiset α) : f (sum s) ≤ sum (map f s) := sorry

theorem abs_sum_le_sum_abs {α : Type u_1} [linear_ordered_field α] {s : multiset α} : abs (sum s) ≤ sum (map abs s) :=
  le_sum_of_subadditive abs abs_zero abs_add s

theorem dvd_sum {α : Type u_1} [comm_semiring α] {a : α} {s : multiset α} : (∀ (x : α), x ∈ s → a ∣ x) → a ∣ sum s := sorry

@[simp] theorem sum_map_singleton {α : Type u_1} (s : multiset α) : sum (map (fun (a : α) => a ::ₘ 0) s) = s := sorry

/-! ### Join -/

/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.

     join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2} -/
def join {α : Type u_1} : multiset (multiset α) → multiset α :=
  sum

theorem coe_join {α : Type u_1} (L : List (List α)) : join ↑(list.map coe L) = ↑(list.join L) := sorry

@[simp] theorem join_zero {α : Type u_1} : join 0 = 0 :=
  rfl

@[simp] theorem join_cons {α : Type u_1} (s : multiset α) (S : multiset (multiset α)) : join (s ::ₘ S) = s + join S :=
  sum_cons s S

@[simp] theorem join_add {α : Type u_1} (S : multiset (multiset α)) (T : multiset (multiset α)) : join (S + T) = join S + join T :=
  sum_add S T

@[simp] theorem mem_join {α : Type u_1} {a : α} {S : multiset (multiset α)} : a ∈ join S ↔ ∃ (s : multiset α), ∃ (H : s ∈ S), a ∈ s := sorry

@[simp] theorem card_join {α : Type u_1} (S : multiset (multiset α)) : coe_fn card (join S) = sum (map (⇑card) S) := sorry

/-! ### `multiset.bind` -/

/-- `bind s f` is the monad bind operation, defined as `join (map f s)`.
  It is the union of `f a` as `a` ranges over `s`. -/
def bind {α : Type u_1} {β : Type u_2} (s : multiset α) (f : α → multiset β) : multiset β :=
  join (map f s)

@[simp] theorem coe_bind {α : Type u_1} {β : Type u_2} (l : List α) (f : α → List β) : (bind ↑l fun (a : α) => ↑(f a)) = ↑(list.bind l f) := sorry

@[simp] theorem zero_bind {α : Type u_1} {β : Type u_2} (f : α → multiset β) : bind 0 f = 0 :=
  rfl

@[simp] theorem cons_bind {α : Type u_1} {β : Type u_2} (a : α) (s : multiset α) (f : α → multiset β) : bind (a ::ₘ s) f = f a + bind s f := sorry

@[simp] theorem add_bind {α : Type u_1} {β : Type u_2} (s : multiset α) (t : multiset α) (f : α → multiset β) : bind (s + t) f = bind s f + bind t f := sorry

@[simp] theorem bind_zero {α : Type u_1} {β : Type u_2} (s : multiset α) : (bind s fun (a : α) => 0) = 0 := sorry

@[simp] theorem bind_add {α : Type u_1} {β : Type u_2} (s : multiset α) (f : α → multiset β) (g : α → multiset β) : (bind s fun (a : α) => f a + g a) = bind s f + bind s g := sorry

@[simp] theorem bind_cons {α : Type u_1} {β : Type u_2} (s : multiset α) (f : α → β) (g : α → multiset β) : (bind s fun (a : α) => f a ::ₘ g a) = map f s + bind s g := sorry

@[simp] theorem mem_bind {α : Type u_1} {β : Type u_2} {b : β} {s : multiset α} {f : α → multiset β} : b ∈ bind s f ↔ ∃ (a : α), ∃ (H : a ∈ s), b ∈ f a := sorry

@[simp] theorem card_bind {α : Type u_1} {β : Type u_2} (s : multiset α) (f : α → multiset β) : coe_fn card (bind s f) = sum (map (⇑card ∘ f) s) := sorry

theorem bind_congr {α : Type u_1} {β : Type u_2} {f : α → multiset β} {g : α → multiset β} {m : multiset α} : (∀ (a : α), a ∈ m → f a = g a) → bind m f = bind m g := sorry

theorem bind_hcongr {α : Type u_1} {β : Type u_2} {β' : Type u_2} {m : multiset α} {f : α → multiset β} {f' : α → multiset β'} (h : β = β') (hf : ∀ (a : α), a ∈ m → f a == f' a) : bind m f == bind m f' := sorry

theorem map_bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : multiset α) (n : α → multiset β) (f : β → γ) : map f (bind m n) = bind m fun (a : α) => map f (n a) := sorry

theorem bind_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : multiset α) (n : β → multiset γ) (f : α → β) : bind (map f m) n = bind m fun (a : α) => n (f a) := sorry

theorem bind_assoc {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : multiset α} {f : α → multiset β} {g : β → multiset γ} : bind (bind s f) g = bind s fun (a : α) => bind (f a) g := sorry

theorem bind_bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : multiset α) (n : multiset β) {f : α → β → multiset γ} : (bind m fun (a : α) => bind n fun (b : β) => f a b) = bind n fun (b : β) => bind m fun (a : α) => f a b := sorry

theorem bind_map_comm {α : Type u_1} {β : Type u_2} {γ : Type u_3} (m : multiset α) (n : multiset β) {f : α → β → γ} : (bind m fun (a : α) => map (fun (b : β) => f a b) n) = bind n fun (b : β) => map (fun (a : α) => f a b) m := sorry

@[simp] theorem sum_bind {α : Type u_1} {β : Type u_2} [add_comm_monoid β] (s : multiset α) (t : α → multiset β) : sum (bind s t) = sum (map (fun (a : α) => sum (t a)) s) := sorry

/-! ### Product of two `multiset`s -/

/-- The multiplicity of `(a, b)` in `product s t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
def product {α : Type u_1} {β : Type u_2} (s : multiset α) (t : multiset β) : multiset (α × β) :=
  bind s fun (a : α) => map (Prod.mk a) t

@[simp] theorem coe_product {α : Type u_1} {β : Type u_2} (l₁ : List α) (l₂ : List β) : product ↑l₁ ↑l₂ = ↑(list.product l₁ l₂) := sorry

@[simp] theorem zero_product {α : Type u_1} {β : Type u_2} (t : multiset β) : product 0 t = 0 :=
  rfl

@[simp] theorem cons_product {α : Type u_1} {β : Type u_2} (a : α) (s : multiset α) (t : multiset β) : product (a ::ₘ s) t = map (Prod.mk a) t + product s t := sorry

@[simp] theorem product_singleton {α : Type u_1} {β : Type u_2} (a : α) (b : β) : product (a ::ₘ 0) (b ::ₘ 0) = (a, b) ::ₘ 0 :=
  rfl

@[simp] theorem add_product {α : Type u_1} {β : Type u_2} (s : multiset α) (t : multiset α) (u : multiset β) : product (s + t) u = product s u + product t u := sorry

@[simp] theorem product_add {α : Type u_1} {β : Type u_2} (s : multiset α) (t : multiset β) (u : multiset β) : product s (t + u) = product s t + product s u := sorry

@[simp] theorem mem_product {α : Type u_1} {β : Type u_2} {s : multiset α} {t : multiset β} {p : α × β} : p ∈ product s t ↔ prod.fst p ∈ s ∧ prod.snd p ∈ t := sorry

@[simp] theorem card_product {α : Type u_1} {β : Type u_2} (s : multiset α) (t : multiset β) : coe_fn card (product s t) = coe_fn card s * coe_fn card t := sorry

/-! ### Sigma multiset -/

/-- `sigma s t` is the dependent version of `product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
protected def sigma {α : Type u_1} {σ : α → Type u_4} (s : multiset α) (t : (a : α) → multiset (σ a)) : multiset (sigma fun (a : α) => σ a) :=
  bind s fun (a : α) => map (sigma.mk a) (t a)

@[simp] theorem coe_sigma {α : Type u_1} {σ : α → Type u_4} (l₁ : List α) (l₂ : (a : α) → List (σ a)) : (multiset.sigma ↑l₁ fun (a : α) => ↑(l₂ a)) = ↑(list.sigma l₁ l₂) := sorry

@[simp] theorem zero_sigma {α : Type u_1} {σ : α → Type u_4} (t : (a : α) → multiset (σ a)) : multiset.sigma 0 t = 0 :=
  rfl

@[simp] theorem cons_sigma {α : Type u_1} {σ : α → Type u_4} (a : α) (s : multiset α) (t : (a : α) → multiset (σ a)) : multiset.sigma (a ::ₘ s) t = map (sigma.mk a) (t a) + multiset.sigma s t := sorry

@[simp] theorem sigma_singleton {α : Type u_1} {β : Type u_2} (a : α) (b : α → β) : (multiset.sigma (a ::ₘ 0) fun (a : α) => b a ::ₘ 0) = sigma.mk a (b a) ::ₘ 0 :=
  rfl

@[simp] theorem add_sigma {α : Type u_1} {σ : α → Type u_4} (s : multiset α) (t : multiset α) (u : (a : α) → multiset (σ a)) : multiset.sigma (s + t) u = multiset.sigma s u + multiset.sigma t u := sorry

@[simp] theorem sigma_add {α : Type u_1} {σ : α → Type u_4} (s : multiset α) (t : (a : α) → multiset (σ a)) (u : (a : α) → multiset (σ a)) : (multiset.sigma s fun (a : α) => t a + u a) = multiset.sigma s t + multiset.sigma s u := sorry

@[simp] theorem mem_sigma {α : Type u_1} {σ : α → Type u_4} {s : multiset α} {t : (a : α) → multiset (σ a)} {p : sigma fun (a : α) => σ a} : p ∈ multiset.sigma s t ↔ sigma.fst p ∈ s ∧ sigma.snd p ∈ t (sigma.fst p) := sorry

@[simp] theorem card_sigma {α : Type u_1} {σ : α → Type u_4} (s : multiset α) (t : (a : α) → multiset (σ a)) : coe_fn card (multiset.sigma s t) = sum (map (fun (a : α) => coe_fn card (t a)) s) := sorry

/-! ### Map for partial functions -/

/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
def pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (s : multiset α) : (∀ (a : α), a ∈ s → p a) → multiset β :=
  quot.rec_on s (fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => ↑(list.pmap f l H)) sorry

@[simp] theorem coe_pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (l : List α) (H : ∀ (a : α), a ∈ l → p a) : pmap f (↑l) H = ↑(list.pmap f l H) :=
  rfl

@[simp] theorem pmap_zero {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (h : ∀ (a : α), a ∈ 0 → p a) : pmap f 0 h = 0 :=
  rfl

@[simp] theorem pmap_cons {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (a : α) (m : multiset α) (h : ∀ (b : α), b ∈ a ::ₘ m → p b) : pmap f (a ::ₘ m) h =
  f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun (a_1 : α) (ha : a_1 ∈ m) => h a_1 (mem_cons_of_mem ha) :=
  quotient.induction_on m fun (l : List α) (h : ∀ (b : α), b ∈ a ::ₘ quotient.mk l → p b) => rfl

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach {α : Type u_1} (s : multiset α) : multiset (Subtype fun (x : α) => x ∈ s) :=
  pmap Subtype.mk s sorry

@[simp] theorem coe_attach {α : Type u_1} (l : List α) : attach ↑l = ↑(list.attach l) :=
  rfl

theorem sizeof_lt_sizeof_of_mem {α : Type u_1} [SizeOf α] {x : α} {s : multiset α} (hx : x ∈ s) : sizeof x < sizeof s := sorry

theorem pmap_eq_map {α : Type u_1} {β : Type u_2} (p : α → Prop) (f : α → β) (s : multiset α) (H : ∀ (a : α), a ∈ s → p a) : pmap (fun (a : α) (_x : p a) => f a) s H = map f s :=
  quot.induction_on s
    fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => congr_arg coe (list.pmap_eq_map p f l H)

theorem pmap_congr {α : Type u_1} {β : Type u_2} {p : α → Prop} {q : α → Prop} {f : (a : α) → p a → β} {g : (a : α) → q a → β} (s : multiset α) {H₁ : ∀ (a : α), a ∈ s → p a} {H₂ : ∀ (a : α), a ∈ s → q a} (h : ∀ (a : α) (h₁ : p a) (h₂ : q a), f a h₁ = g a h₂) : pmap f s H₁ = pmap g s H₂ := sorry

theorem map_pmap {α : Type u_1} {β : Type u_2} {γ : Type u_3} {p : α → Prop} (g : β → γ) (f : (a : α) → p a → β) (s : multiset α) (H : ∀ (a : α), a ∈ s → p a) : map g (pmap f s H) = pmap (fun (a : α) (h : p a) => g (f a h)) s H :=
  quot.induction_on s
    fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => congr_arg coe (list.map_pmap g f l H)

theorem pmap_eq_map_attach {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (s : multiset α) (H : ∀ (a : α), a ∈ s → p a) : pmap f s H =
  map (fun (x : Subtype fun (x : α) => x ∈ s) => f (subtype.val x) (H (subtype.val x) (subtype.property x))) (attach s) :=
  quot.induction_on s
    fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => congr_arg coe (list.pmap_eq_map_attach f l H)

theorem attach_map_val {α : Type u_1} (s : multiset α) : map subtype.val (attach s) = s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.attach_map_val l)

@[simp] theorem mem_attach {α : Type u_1} (s : multiset α) (x : Subtype fun (x : α) => x ∈ s) : x ∈ attach s :=
  quot.induction_on s fun (l : List α) => list.mem_attach l

@[simp] theorem mem_pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : (a : α) → p a → β} {s : multiset α} {H : ∀ (a : α), a ∈ s → p a} {b : β} : b ∈ pmap f s H ↔ ∃ (a : α), ∃ (h : a ∈ s), f a (H a h) = b :=
  quot.induction_on s (fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => list.mem_pmap) H

@[simp] theorem card_pmap {α : Type u_1} {β : Type u_2} {p : α → Prop} (f : (a : α) → p a → β) (s : multiset α) (H : ∀ (a : α), a ∈ s → p a) : coe_fn card (pmap f s H) = coe_fn card s :=
  quot.induction_on s (fun (l : List α) (H : ∀ (a : α), a ∈ Quot.mk setoid.r l → p a) => list.length_pmap) H

@[simp] theorem card_attach {α : Type u_1} {m : multiset α} : coe_fn card (attach m) = coe_fn card m :=
  card_pmap Subtype.mk m (attach._proof_1 m)

@[simp] theorem attach_zero {α : Type u_1} : attach 0 = 0 :=
  rfl

theorem attach_cons {α : Type u_1} (a : α) (m : multiset α) : attach (a ::ₘ m) =
  { val := a, property := mem_cons_self a m } ::ₘ
    map
      (fun (p : Subtype fun (x : α) => x ∈ m) =>
        { val := subtype.val p, property := mem_cons_of_mem (subtype.property p) })
      (attach m) := sorry

protected def decidable_forall_multiset {α : Type u_1} {m : multiset α} {p : α → Prop} [hp : (a : α) → Decidable (p a)] : Decidable (∀ (a : α), a ∈ m → p a) :=
  quotient.rec_on_subsingleton m fun (l : List α) => decidable_of_iff (∀ (a : α), a ∈ l → p a) sorry

protected instance decidable_dforall_multiset {α : Type u_1} {m : multiset α} {p : (a : α) → a ∈ m → Prop} [hp : (a : α) → (h : a ∈ m) → Decidable (p a h)] : Decidable (∀ (a : α) (h : a ∈ m), p a h) :=
  decidable_of_decidable_of_iff multiset.decidable_forall_multiset sorry

/-- decidable equality for functions whose domain is bounded by multisets -/
protected instance decidable_eq_pi_multiset {α : Type u_1} {m : multiset α} {β : α → Type u_2} [h : (a : α) → DecidableEq (β a)] : DecidableEq ((a : α) → a ∈ m → β a) :=
  fun (f g : (a : α) → a ∈ m → β a) => decidable_of_iff (∀ (a : α) (h : a ∈ m), f a h = g a h) sorry

def decidable_exists_multiset {α : Type u_1} {m : multiset α} {p : α → Prop} [decidable_pred p] : Decidable (∃ (x : α), ∃ (H : x ∈ m), p x) :=
  quotient.rec_on_subsingleton m list.decidable_exists_mem

protected instance decidable_dexists_multiset {α : Type u_1} {m : multiset α} {p : (a : α) → a ∈ m → Prop} [hp : (a : α) → (h : a ∈ m) → Decidable (p a h)] : Decidable (∃ (a : α), ∃ (h : a ∈ m), p a h) :=
  decidable_of_decidable_of_iff decidable_exists_multiset sorry

/-! ### Subtraction -/

/-- `s - t` is the multiset such that
  `count a (s - t) = count a s - count a t` for all `a`. -/
protected def sub {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : multiset α :=
  quotient.lift_on₂ s t (fun (l₁ l₂ : List α) => ↑(list.diff l₁ l₂)) sorry

protected instance has_sub {α : Type u_1} [DecidableEq α] : Sub (multiset α) :=
  { sub := multiset.sub }

@[simp] theorem coe_sub {α : Type u_1} [DecidableEq α] (s : List α) (t : List α) : ↑s - ↑t = ↑(list.diff s t) :=
  rfl

theorem sub_eq_fold_erase {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s - t = foldl erase erase_comm s t := sorry

@[simp] theorem sub_zero {α : Type u_1} [DecidableEq α] (s : multiset α) : s - 0 = s :=
  quot.induction_on s fun (l : List α) => rfl

@[simp] theorem sub_cons {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : s - a ::ₘ t = erase s a - t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => congr_arg coe (list.diff_cons l₁ l₂ a)

theorem add_sub_of_le {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : s ≤ t) : s + (t - s) = t := sorry

theorem sub_add' {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} : s - (t + u) = s - t - u :=
  quotient.induction_on₃ s t u fun (l₁ l₂ l₃ : List α) => congr_arg coe (list.diff_append l₁ l₂ l₃)

theorem sub_add_cancel {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : t ≤ s) : s - t + t = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s - t + t = s)) (add_comm (s - t) t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t + (s - t) = s)) (add_sub_of_le h))) (Eq.refl s))

@[simp] theorem add_sub_cancel_left {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s + t - s = t := sorry

@[simp] theorem add_sub_cancel {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s + t - t = s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s + t - t = s)) (add_comm s t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t + s - t = s)) (add_sub_cancel_left t s))) (Eq.refl s))

theorem sub_le_sub_right {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : s ≤ t) (u : multiset α) : s - u ≤ t - u := sorry

theorem sub_le_sub_left {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : s ≤ t) (u : multiset α) : u - t ≤ u - s := sorry

theorem sub_le_iff_le_add {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} : s - t ≤ u ↔ s ≤ u + t := sorry

theorem le_sub_add {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ≤ s - t + t :=
  iff.mp sub_le_iff_le_add (le_refl (s - t))

theorem sub_le_self {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s - t ≤ s :=
  iff.mpr sub_le_iff_le_add (le_add_right s t)

@[simp] theorem card_sub {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : t ≤ s) : coe_fn card (s - t) = coe_fn card s - coe_fn card t := sorry

/-! ### Union -/

/-- `s ∪ t` is the lattice join operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∪ t` is the maximum
  of the multiplicities in `s` and `t`. -/
def union {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : multiset α :=
  s - t + t

protected instance has_union {α : Type u_1} [DecidableEq α] : has_union (multiset α) :=
  has_union.mk union

theorem union_def {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∪ t = s - t + t :=
  rfl

theorem le_union_left {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ≤ s ∪ t :=
  le_sub_add s t

theorem le_union_right {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : t ≤ s ∪ t :=
  le_add_left t (s - t)

theorem eq_union_left {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} : t ≤ s → s ∪ t = s :=
  sub_add_cancel

theorem union_le_union_right {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : s ≤ t) (u : multiset α) : s ∪ u ≤ t ∪ u :=
  add_le_add_right (sub_le_sub_right h u) u

theorem union_le {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ t ≤ u)) (Eq.symm (eq_union_left h₂)))) (union_le_union_right h₁ t)

@[simp] theorem mem_union {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {a : α} : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  { mp := fun (h : a ∈ s ∪ t) => or.imp_left (mem_of_le (sub_le_self s t)) (iff.mp mem_add h),
    mpr := Or._oldrec (mem_of_le (le_union_left s t)) (mem_of_le (le_union_right s t)) }

@[simp] theorem map_union {α : Type u_1} {β : Type u_2} [DecidableEq α] [DecidableEq β] {f : α → β} (finj : function.injective f) {s : multiset α} {t : multiset α} : map f (s ∪ t) = map f s ∪ map f t := sorry

/-! ### Intersection -/

/-- `s ∩ t` is the lattice meet operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∩ t` is the minimum
  of the multiplicities in `s` and `t`. -/
def inter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : multiset α :=
  quotient.lift_on₂ s t (fun (l₁ l₂ : List α) => ↑(list.bag_inter l₁ l₂)) sorry

protected instance has_inter {α : Type u_1} [DecidableEq α] : has_inter (multiset α) :=
  has_inter.mk inter

@[simp] theorem inter_zero {α : Type u_1} [DecidableEq α] (s : multiset α) : s ∩ 0 = 0 :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.bag_inter_nil l)

@[simp] theorem zero_inter {α : Type u_1} [DecidableEq α] (s : multiset α) : 0 ∩ s = 0 :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.nil_bag_inter l)

@[simp] theorem cons_inter_of_pos {α : Type u_1} [DecidableEq α] {a : α} (s : multiset α) {t : multiset α} : a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ erase t a :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) (h : a ∈ quotient.mk l₂) => congr_arg coe (list.cons_bag_inter_of_pos l₁ h)

@[simp] theorem cons_inter_of_neg {α : Type u_1} [DecidableEq α] {a : α} (s : multiset α) {t : multiset α} : ¬a ∈ t → (a ::ₘ s) ∩ t = s ∩ t :=
  quotient.induction_on₂ s t
    fun (l₁ l₂ : List α) (h : ¬a ∈ quotient.mk l₂) => congr_arg coe (list.cons_bag_inter_of_neg l₁ h)

theorem inter_le_left {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∩ t ≤ s :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => list.sublist.subperm (list.bag_inter_sublist_left l₁ l₂)

theorem inter_le_right {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∩ t ≤ t := sorry

theorem le_inter {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u := sorry

@[simp] theorem mem_inter {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {a : α} : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := sorry

protected instance lattice {α : Type u_1} [DecidableEq α] : lattice (multiset α) :=
  lattice.mk has_union.union partial_order.le partial_order.lt sorry sorry sorry sorry sorry sorry has_inter.inter sorry
    sorry sorry

@[simp] theorem sup_eq_union {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ⊔ t = s ∪ t :=
  rfl

@[simp] theorem inf_eq_inter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ⊓ t = s ∩ t :=
  rfl

@[simp] theorem le_inter_iff {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u :=
  le_inf_iff

@[simp] theorem union_le_iff {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u :=
  sup_le_iff

protected instance semilattice_inf_bot {α : Type u_1} [DecidableEq α] : semilattice_inf_bot (multiset α) :=
  semilattice_inf_bot.mk 0 lattice.le lattice.lt sorry sorry sorry zero_le lattice.inf sorry sorry sorry

theorem union_comm {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∪ t = t ∪ s :=
  sup_comm

theorem inter_comm {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∩ t = t ∩ s :=
  inf_comm

theorem eq_union_right {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : s ≤ t) : s ∪ t = t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (s ∪ t = t)) (union_comm s t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (t ∪ s = t)) (eq_union_left h))) (Eq.refl t))

theorem union_le_union_left {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} (h : s ≤ t) (u : multiset α) : u ∪ s ≤ u ∪ t :=
  sup_le_sup_left h u

theorem union_le_add {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∪ t ≤ s + t :=
  union_le (le_add_right s t) (le_add_left t s)

theorem union_add_distrib {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) (u : multiset α) : s ∪ t + u = s + u ∪ (t + u) := sorry

theorem add_union_distrib {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) (u : multiset α) : s + (t ∪ u) = s + t ∪ (s + u) := sorry

theorem cons_union_distrib {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : a ::ₘ (s ∪ t) = a ::ₘ s ∪ a ::ₘ t := sorry

theorem inter_add_distrib {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) (u : multiset α) : s ∩ t + u = (s + u) ∩ (t + u) := sorry

theorem add_inter_distrib {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) (u : multiset α) : s + t ∩ u = (s + t) ∩ (s + u) := sorry

theorem cons_inter_distrib {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : a ::ₘ s ∩ t = (a ::ₘ s) ∩ (a ::ₘ t) := sorry

theorem union_add_inter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s ∪ t + s ∩ t = s + t := sorry

theorem sub_add_inter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s - t + s ∩ t = s := sorry

theorem sub_inter {α : Type u_1} [DecidableEq α] (s : multiset α) (t : multiset α) : s - s ∩ t = s - t :=
  add_right_cancel
    (eq.mpr (id (Eq._oldrec (Eq.refl (s - s ∩ t + s ∩ t = s - t + s ∩ t)) (sub_add_inter s t)))
      (eq.mpr (id (Eq._oldrec (Eq.refl (s - s ∩ t + s ∩ t = s)) (sub_add_cancel (inter_le_left s t)))) (Eq.refl s)))

/-! ### `multiset.filter` -/

/-- `filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) : multiset α :=
  quot.lift_on s (fun (l : List α) => ↑(list.filter p l)) sorry

@[simp] theorem coe_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : List α) : filter p ↑l = ↑(list.filter p l) :=
  rfl

@[simp] theorem filter_zero {α : Type u_1} (p : α → Prop) [decidable_pred p] : filter p 0 = 0 :=
  rfl

theorem filter_congr {α : Type u_1} {p : α → Prop} {q : α → Prop} [decidable_pred p] [decidable_pred q] {s : multiset α} : (∀ (x : α), x ∈ s → (p x ↔ q x)) → filter p s = filter q s :=
  quot.induction_on s
    fun (l : List α) (h : ∀ (x : α), x ∈ Quot.mk setoid.r l → (p x ↔ q x)) => congr_arg coe (list.filter_congr h)

@[simp] theorem filter_add {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) (t : multiset α) : filter p (s + t) = filter p s + filter p t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => congr_arg coe (list.filter_append l₁ l₂)

@[simp] theorem filter_le {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) : filter p s ≤ s :=
  quot.induction_on s fun (l : List α) => list.sublist.subperm (list.filter_sublist l)

@[simp] theorem filter_subset {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) : filter p s ⊆ s :=
  subset_of_le (filter_le p s)

theorem filter_le_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] {s : multiset α} {t : multiset α} (h : s ≤ t) : filter p s ≤ filter p t :=
  le_induction_on h fun (l₁ l₂ : List α) (h : l₁ <+ l₂) => list.sublist.subperm (list.filter_sublist_filter p h)

@[simp] theorem filter_cons_of_pos {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} (s : multiset α) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
  quot.induction_on s fun (l : List α) (h : p a) => congr_arg coe (list.filter_cons_of_pos l h)

@[simp] theorem filter_cons_of_neg {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} (s : multiset α) : ¬p a → filter p (a ::ₘ s) = filter p s :=
  quot.induction_on s fun (l : List α) (h : ¬p a) => congr_arg coe (list.filter_cons_of_neg l h)

@[simp] theorem mem_filter {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} {s : multiset α} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
  quot.induction_on s fun (l : List α) => list.mem_filter

theorem of_mem_filter {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} {s : multiset α} (h : a ∈ filter p s) : p a :=
  and.right (iff.mp mem_filter h)

theorem mem_of_mem_filter {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} {s : multiset α} (h : a ∈ filter p s) : a ∈ s :=
  and.left (iff.mp mem_filter h)

theorem mem_filter_of_mem {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} {l : multiset α} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
  iff.mpr mem_filter { left := m, right := h }

theorem filter_eq_self {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : multiset α} : filter p s = s ↔ ∀ (a : α), a ∈ s → p a := sorry

theorem filter_eq_nil {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : multiset α} : filter p s = 0 ↔ ∀ (a : α), a ∈ s → ¬p a := sorry

theorem le_filter {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : multiset α} {t : multiset α} : s ≤ filter p t ↔ s ≤ t ∧ ∀ (a : α), a ∈ s → p a := sorry

@[simp] theorem filter_sub {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] (s : multiset α) (t : multiset α) : filter p (s - t) = filter p s - filter p t := sorry

@[simp] theorem filter_union {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] (s : multiset α) (t : multiset α) : filter p (s ∪ t) = filter p s ∪ filter p t := sorry

@[simp] theorem filter_inter {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] (s : multiset α) (t : multiset α) : filter p (s ∩ t) = filter p s ∩ filter p t := sorry

@[simp] theorem filter_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (q : α → Prop) [decidable_pred q] (s : multiset α) : filter p (filter q s) = filter (fun (a : α) => p a ∧ q a) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_filter p q l)

theorem filter_add_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (q : α → Prop) [decidable_pred q] (s : multiset α) : filter p s + filter q s = filter (fun (a : α) => p a ∨ q a) s + filter (fun (a : α) => p a ∧ q a) s := sorry

theorem filter_add_not {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) : filter p s + filter (fun (a : α) => ¬p a) s = s := sorry

/-! ### Simultaneously filter and map elements of a multiset -/

/-- `filter_map f s` is a combination filter/map operation on `s`.
  The function `f : α → option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filter_map {α : Type u_1} {β : Type u_2} (f : α → Option β) (s : multiset α) : multiset β :=
  quot.lift_on s (fun (l : List α) => ↑(list.filter_map f l)) sorry

@[simp] theorem coe_filter_map {α : Type u_1} {β : Type u_2} (f : α → Option β) (l : List α) : filter_map f ↑l = ↑(list.filter_map f l) :=
  rfl

@[simp] theorem filter_map_zero {α : Type u_1} {β : Type u_2} (f : α → Option β) : filter_map f 0 = 0 :=
  rfl

@[simp] theorem filter_map_cons_none {α : Type u_1} {β : Type u_2} {f : α → Option β} (a : α) (s : multiset α) (h : f a = none) : filter_map f (a ::ₘ s) = filter_map f s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_map_cons_none a l h)

@[simp] theorem filter_map_cons_some {α : Type u_1} {β : Type u_2} (f : α → Option β) (a : α) (s : multiset α) {b : β} (h : f a = some b) : filter_map f (a ::ₘ s) = b ::ₘ filter_map f s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_map_cons_some f a l h)

theorem filter_map_eq_map {α : Type u_1} {β : Type u_2} (f : α → β) : filter_map (some ∘ f) = map f :=
  funext
    fun (s : multiset α) => quot.induction_on s fun (l : List α) => congr_arg coe (congr_fun (list.filter_map_eq_map f) l)

theorem filter_map_eq_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] : filter_map (option.guard p) = filter p :=
  funext
    fun (s : multiset α) =>
      quot.induction_on s fun (l : List α) => congr_arg coe (congr_fun (list.filter_map_eq_filter p) l)

theorem filter_map_filter_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → Option β) (g : β → Option γ) (s : multiset α) : filter_map g (filter_map f s) = filter_map (fun (x : α) => option.bind (f x) g) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_map_filter_map f g l)

theorem map_filter_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → Option β) (g : β → γ) (s : multiset α) : map g (filter_map f s) = filter_map (fun (x : α) => option.map g (f x)) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.map_filter_map f g l)

theorem filter_map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → β) (g : β → Option γ) (s : multiset α) : filter_map g (map f s) = filter_map (g ∘ f) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_map_map f g l)

theorem filter_filter_map {α : Type u_1} {β : Type u_2} (f : α → Option β) (p : β → Prop) [decidable_pred p] (s : multiset α) : filter p (filter_map f s) = filter_map (fun (x : α) => option.filter p (f x)) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_filter_map f p l)

theorem filter_map_filter {α : Type u_1} {β : Type u_2} (p : α → Prop) [decidable_pred p] (f : α → Option β) (s : multiset α) : filter_map f (filter p s) = filter_map (fun (x : α) => ite (p x) (f x) none) s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_map_filter p f l)

@[simp] theorem filter_map_some {α : Type u_1} (s : multiset α) : filter_map some s = s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.filter_map_some l)

@[simp] theorem mem_filter_map {α : Type u_1} {β : Type u_2} (f : α → Option β) (s : multiset α) {b : β} : b ∈ filter_map f s ↔ ∃ (a : α), a ∈ s ∧ f a = some b :=
  quot.induction_on s fun (l : List α) => list.mem_filter_map f l

theorem map_filter_map_of_inv {α : Type u_1} {β : Type u_2} (f : α → Option β) (g : β → α) (H : ∀ (x : α), option.map g (f x) = some x) (s : multiset α) : map g (filter_map f s) = s :=
  quot.induction_on s fun (l : List α) => congr_arg coe (list.map_filter_map_of_inv f g H l)

theorem filter_map_le_filter_map {α : Type u_1} {β : Type u_2} (f : α → Option β) {s : multiset α} {t : multiset α} (h : s ≤ t) : filter_map f s ≤ filter_map f t :=
  le_induction_on h fun (l₁ l₂ : List α) (h : l₁ <+ l₂) => list.sublist.subperm (list.sublist.filter_map f h)

/-! ### countp -/

/-- `countp p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countp {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) : ℕ :=
  quot.lift_on s (list.countp p) sorry

@[simp] theorem coe_countp {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : List α) : countp p ↑l = list.countp p l :=
  rfl

@[simp] theorem countp_zero {α : Type u_1} (p : α → Prop) [decidable_pred p] : countp p 0 = 0 :=
  rfl

@[simp] theorem countp_cons_of_pos {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} (s : multiset α) : p a → countp p (a ::ₘ s) = countp p s + 1 :=
  quot.induction_on s (list.countp_cons_of_pos p)

@[simp] theorem countp_cons_of_neg {α : Type u_1} {p : α → Prop} [decidable_pred p] {a : α} (s : multiset α) : ¬p a → countp p (a ::ₘ s) = countp p s :=
  quot.induction_on s (list.countp_cons_of_neg p)

theorem countp_eq_card_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) : countp p s = coe_fn card (filter p s) :=
  quot.induction_on s fun (l : List α) => list.countp_eq_length_filter p l

@[simp] theorem countp_add {α : Type u_1} (p : α → Prop) [decidable_pred p] (s : multiset α) (t : multiset α) : countp p (s + t) = countp p s + countp p t := sorry

protected instance countp.is_add_monoid_hom {α : Type u_1} (p : α → Prop) [decidable_pred p] : is_add_monoid_hom (countp p) :=
  is_add_monoid_hom.mk (countp_zero p)

@[simp] theorem countp_sub {α : Type u_1} (p : α → Prop) [decidable_pred p] [DecidableEq α] {s : multiset α} {t : multiset α} (h : t ≤ s) : countp p (s - t) = countp p s - countp p t := sorry

theorem countp_le_of_le {α : Type u_1} (p : α → Prop) [decidable_pred p] {s : multiset α} {t : multiset α} (h : s ≤ t) : countp p s ≤ countp p t := sorry

@[simp] theorem countp_filter {α : Type u_1} (p : α → Prop) [decidable_pred p] (q : α → Prop) [decidable_pred q] (s : multiset α) : countp p (filter q s) = countp (fun (a : α) => p a ∧ q a) s := sorry

theorem countp_pos {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : multiset α} : 0 < countp p s ↔ ∃ (a : α), ∃ (H : a ∈ s), p a := sorry

theorem countp_pos_of_mem {α : Type u_1} {p : α → Prop} [decidable_pred p] {s : multiset α} {a : α} (h : a ∈ s) (pa : p a) : 0 < countp p s :=
  iff.mpr countp_pos (Exists.intro a (Exists.intro h pa))

/-! ### Multiplicity of an element -/

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count {α : Type u_1} [DecidableEq α] (a : α) : multiset α → ℕ :=
  countp (Eq a)

@[simp] theorem coe_count {α : Type u_1} [DecidableEq α] (a : α) (l : List α) : count a ↑l = list.count a l :=
  coe_countp (Eq a) l

@[simp] theorem count_zero {α : Type u_1} [DecidableEq α] (a : α) : count a 0 = 0 :=
  rfl

@[simp] theorem count_cons_self {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : count a (a ::ₘ s) = Nat.succ (count a s) :=
  countp_cons_of_pos s rfl

@[simp] theorem count_cons_of_ne {α : Type u_1} [DecidableEq α] {a : α} {b : α} (h : a ≠ b) (s : multiset α) : count a (b ::ₘ s) = count a s :=
  countp_cons_of_neg s h

theorem count_le_of_le {α : Type u_1} [DecidableEq α] (a : α) {s : multiset α} {t : multiset α} : s ≤ t → count a s ≤ count a t :=
  countp_le_of_le (Eq a)

theorem count_le_count_cons {α : Type u_1} [DecidableEq α] (a : α) (b : α) (s : multiset α) : count a s ≤ count a (b ::ₘ s) :=
  count_le_of_le a (le_cons_self s b)

theorem count_cons {α : Type u_1} [DecidableEq α] (a : α) (b : α) (s : multiset α) : count a (b ::ₘ s) = count a s + ite (a = b) 1 0 := sorry

theorem count_singleton {α : Type u_1} [DecidableEq α] (a : α) : count a (a ::ₘ 0) = 1 := sorry

@[simp] theorem count_add {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : count a (s + t) = count a s + count a t :=
  countp_add (Eq a)

protected instance count.is_add_monoid_hom {α : Type u_1} [DecidableEq α] (a : α) : is_add_monoid_hom (count a) :=
  countp.is_add_monoid_hom (Eq a)

@[simp] theorem count_smul {α : Type u_1} [DecidableEq α] (a : α) (n : ℕ) (s : multiset α) : count a (n •ℕ s) = n * count a s := sorry

theorem count_pos {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : 0 < count a s ↔ a ∈ s := sorry

@[simp] theorem count_eq_zero_of_not_mem {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} (h : ¬a ∈ s) : count a s = 0 :=
  by_contradiction fun (h' : ¬count a s = 0) => h (iff.mp count_pos (nat.pos_of_ne_zero h'))

@[simp] theorem count_eq_zero {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : count a s = 0 ↔ ¬a ∈ s :=
  iff.mp iff_not_comm (iff.trans (iff.symm count_pos) pos_iff_ne_zero)

theorem count_ne_zero {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} : count a s ≠ 0 ↔ a ∈ s := sorry

@[simp] theorem count_repeat_self {α : Type u_1} [DecidableEq α] (a : α) (n : ℕ) : count a (repeat a n) = n := sorry

theorem count_repeat {α : Type u_1} [DecidableEq α] (a : α) (b : α) (n : ℕ) : count a (repeat b n) = ite (a = b) n 0 := sorry

@[simp] theorem count_erase_self {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) : count a (erase s a) = Nat.pred (count a s) := sorry

@[simp] theorem count_erase_of_ne {α : Type u_1} [DecidableEq α] {a : α} {b : α} (ab : a ≠ b) (s : multiset α) : count a (erase s b) = count a s := sorry

@[simp] theorem count_sub {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : count a (s - t) = count a s - count a t := sorry

@[simp] theorem count_union {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : count a (s ∪ t) = max (count a s) (count a t) := sorry

@[simp] theorem count_inter {α : Type u_1} [DecidableEq α] (a : α) (s : multiset α) (t : multiset α) : count a (s ∩ t) = min (count a s) (count a t) := sorry

theorem count_sum {α : Type u_1} {β : Type u_2} [DecidableEq α] {m : multiset β} {f : β → multiset α} {a : α} : count a (sum (map f m)) = sum (map (fun (b : β) => count a (f b)) m) := sorry

theorem count_bind {α : Type u_1} {β : Type u_2} [DecidableEq α] {m : multiset β} {f : β → multiset α} {a : α} : count a (bind m f) = sum (map (fun (b : β) => count a (f b)) m) :=
  count_sum

theorem le_count_iff_repeat_le {α : Type u_1} [DecidableEq α] {a : α} {s : multiset α} {n : ℕ} : n ≤ count a s ↔ repeat a n ≤ s :=
  quot.induction_on s fun (l : List α) => iff.trans list.le_count_iff_repeat_sublist (iff.symm repeat_le_coe)

@[simp] theorem count_filter_of_pos {α : Type u_1} [DecidableEq α] {p : α → Prop} [decidable_pred p] {a : α} {s : multiset α} (h : p a) : count a (filter p s) = count a s :=
  quot.induction_on s fun (l : List α) => list.count_filter h

@[simp] theorem count_filter_of_neg {α : Type u_1} [DecidableEq α] {p : α → Prop} [decidable_pred p] {a : α} {s : multiset α} (h : ¬p a) : count a (filter p s) = 0 :=
  count_eq_zero_of_not_mem fun (t : a ∈ filter p s) => h (of_mem_filter t)

theorem ext {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} : s = t ↔ ∀ (a : α), count a s = count a t :=
  quotient.induction_on₂ s t fun (l₁ l₂ : List α) => iff.trans quotient.eq list.perm_iff_count

theorem ext' {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} : (∀ (a : α), count a s = count a t) → s = t :=
  iff.mpr ext

@[simp] theorem coe_inter {α : Type u_1} [DecidableEq α] (s : List α) (t : List α) : ↑s ∩ ↑t = ↑(list.bag_inter s t) := sorry

theorem le_iff_count {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} : s ≤ t ↔ ∀ (a : α), count a s ≤ count a t := sorry

protected instance distrib_lattice {α : Type u_1} [DecidableEq α] : distrib_lattice (multiset α) :=
  distrib_lattice.mk lattice.sup lattice.le lattice.lt sorry sorry sorry sorry sorry sorry lattice.inf sorry sorry sorry
    sorry

protected instance semilattice_sup_bot {α : Type u_1} [DecidableEq α] : semilattice_sup_bot (multiset α) :=
  semilattice_sup_bot.mk 0 lattice.le lattice.lt sorry sorry sorry zero_le lattice.sup sorry sorry sorry

@[simp] theorem mem_nsmul {α : Type u_1} {a : α} {s : multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n •ℕ s ↔ a ∈ s := sorry

/-! ### Lift a relation to `multiset`s -/

/-- `rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping betweem elements in `s` and `t` following `r`. -/
theorem rel_iff {α : Type u_1} {β : Type u_2} (r : α → β → Prop) : ∀ (ᾰ : multiset α) (ᾰ_1 : multiset β),
  rel r ᾰ ᾰ_1 ↔
    ᾰ = 0 ∧ ᾰ_1 = 0 ∨
      Exists
        fun {a : α} =>
          Exists
            fun {b : β} =>
              Exists
                fun {as : multiset α} =>
                  Exists fun {bs : multiset β} => r a b ∧ rel r as bs ∧ ᾰ = a ::ₘ as ∧ ᾰ_1 = b ::ₘ bs := sorry

theorem rel_flip {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {s : multiset β} {t : multiset α} : rel (flip r) s t ↔ rel r t s :=
  { mp := rel_flip_aux, mpr := rel_flip_aux }

theorem rel_eq_refl {α : Type u_1} {s : multiset α} : rel Eq s s :=
  multiset.induction_on s rel.zero fun (a : α) (s : multiset α) => rel.cons rfl

theorem rel_eq {α : Type u_1} {s : multiset α} {t : multiset α} : rel Eq s t ↔ s = t := sorry

theorem rel.mono {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {p : α → β → Prop} {s : multiset α} {t : multiset β} (h : ∀ (a : α) (b : β), r a b → p a b) (hst : rel r s t) : rel p s t := sorry

theorem rel.add {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {s : multiset α} {t : multiset β} {u : multiset α} {v : multiset β} (hst : rel r s t) (huv : rel r u v) : rel r (s + u) (t + v) := sorry

theorem rel_flip_eq {α : Type u_1} {s : multiset α} {t : multiset α} : rel (fun (a b : α) => b = a) s t ↔ s = t := sorry

@[simp] theorem rel_zero_left {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {b : multiset β} : rel r 0 b ↔ b = 0 := sorry

@[simp] theorem rel_zero_right {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {a : multiset α} : rel r a 0 ↔ a = 0 := sorry

theorem rel_cons_left {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {a : α} {as : multiset α} {bs : multiset β} : rel r (a ::ₘ as) bs ↔ ∃ (b : β), ∃ (bs' : multiset β), r a b ∧ rel r as bs' ∧ bs = b ::ₘ bs' := sorry

theorem rel_cons_right {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {as : multiset α} {b : β} {bs : multiset β} : rel r as (b ::ₘ bs) ↔ ∃ (a : α), ∃ (as' : multiset α), r a b ∧ rel r as' bs ∧ as = a ::ₘ as' := sorry

theorem rel_add_left {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {as₀ : multiset α} {as₁ : multiset α} {bs : multiset β} : rel r (as₀ + as₁) bs ↔ ∃ (bs₀ : multiset β), ∃ (bs₁ : multiset β), rel r as₀ bs₀ ∧ rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ := sorry

theorem rel_add_right {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {as : multiset α} {bs₀ : multiset β} {bs₁ : multiset β} : rel r as (bs₀ + bs₁) ↔ ∃ (as₀ : multiset α), ∃ (as₁ : multiset α), rel r as₀ bs₀ ∧ rel r as₁ bs₁ ∧ as = as₀ + as₁ := sorry

theorem rel_map_left {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → β → Prop} {s : multiset γ} {f : γ → α} {t : multiset β} : rel r (map f s) t ↔ rel (fun (a : γ) (b : β) => r (f a) b) s t := sorry

theorem rel_map_right {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → β → Prop} {s : multiset α} {t : multiset γ} {f : γ → β} : rel r s (map f t) ↔ rel (fun (a : α) (b : γ) => r a (f b)) s t := sorry

theorem rel_join {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {s : multiset (multiset α)} {t : multiset (multiset β)} (h : rel (rel r) s t) : rel r (join s) (join t) := sorry

theorem rel_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {r : α → β → Prop} {p : γ → δ → Prop} {s : multiset α} {t : multiset β} {f : α → γ} {g : β → δ} (h : relator.lift_fun r p f g) (hst : rel r s t) : rel p (map f s) (map g t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (rel p (map f s) (map g t))) (propext rel_map_left)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (rel (fun (a : α) (b : δ) => p (f a) b) s (map g t))) (propext rel_map_right)))
      (rel.mono h hst))

theorem rel_bind {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {r : α → β → Prop} {p : γ → δ → Prop} {s : multiset α} {t : multiset β} {f : α → multiset γ} {g : β → multiset δ} (h : relator.lift_fun r (rel p) f g) (hst : rel r s t) : rel p (bind s f) (bind t g) :=
  rel_join (rel_map h hst)

theorem card_eq_card_of_rel {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {s : multiset α} {t : multiset β} (h : rel r s t) : coe_fn card s = coe_fn card t := sorry

theorem exists_mem_of_rel_of_mem {α : Type u_1} {β : Type u_2} {r : α → β → Prop} {s : multiset α} {t : multiset β} (h : rel r s t) {a : α} (ha : a ∈ s) : ∃ (b : β), ∃ (H : b ∈ t), r a b := sorry

theorem map_eq_map {α : Type u_1} {β : Type u_2} {f : α → β} (hf : function.injective f) {s : multiset α} {t : multiset α} : map f s = map f t ↔ s = t := sorry

theorem map_injective {α : Type u_1} {β : Type u_2} {f : α → β} (hf : function.injective f) : function.injective (map f) :=
  fun (x y : multiset α) => iff.mp (map_eq_map hf)

theorem map_mk_eq_map_mk_of_rel {α : Type u_1} {r : α → α → Prop} {s : multiset α} {t : multiset α} (hst : rel r s t) : map (Quot.mk r) s = map (Quot.mk r) t := sorry

theorem exists_multiset_eq_map_quot_mk {α : Type u_1} {r : α → α → Prop} (s : multiset (Quot r)) : ∃ (t : multiset α), s = map (Quot.mk r) t := sorry

theorem induction_on_multiset_quot {α : Type u_1} {r : α → α → Prop} {p : multiset (Quot r) → Prop} (s : multiset (Quot r)) : (∀ (s : multiset α), p (map (Quot.mk r) s)) → p s := sorry

/-! ### Disjoint multisets -/

/-- `disjoint s t` means that `s` and `t` have no elements in common. -/
def disjoint {α : Type u_1} (s : multiset α) (t : multiset α) :=
  ∀ {a : α}, a ∈ s → a ∈ t → False

@[simp] theorem coe_disjoint {α : Type u_1} (l₁ : List α) (l₂ : List α) : disjoint ↑l₁ ↑l₂ ↔ list.disjoint l₁ l₂ :=
  iff.rfl

theorem disjoint.symm {α : Type u_1} {s : multiset α} {t : multiset α} (d : disjoint s t) : disjoint t s :=
  fun {a : α} (ᾰ : a ∈ t) (ᾰ_1 : a ∈ s) => idRhs False (d ᾰ_1 ᾰ)

theorem disjoint_comm {α : Type u_1} {s : multiset α} {t : multiset α} : disjoint s t ↔ disjoint t s :=
  { mp := disjoint.symm, mpr := disjoint.symm }

theorem disjoint_left {α : Type u_1} {s : multiset α} {t : multiset α} : disjoint s t ↔ ∀ {a : α}, a ∈ s → ¬a ∈ t :=
  iff.rfl

theorem disjoint_right {α : Type u_1} {s : multiset α} {t : multiset α} : disjoint s t ↔ ∀ {a : α}, a ∈ t → ¬a ∈ s :=
  disjoint_comm

theorem disjoint_iff_ne {α : Type u_1} {s : multiset α} {t : multiset α} : disjoint s t ↔ ∀ (a : α), a ∈ s → ∀ (b : α), b ∈ t → a ≠ b := sorry

theorem disjoint_of_subset_left {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
  fun {a : α} (ᾰ : a ∈ s) => idRhs (a ∈ t → False) (d (h ᾰ))

theorem disjoint_of_subset_right {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
  fun {a : α} (ᾰ : a ∈ s) (ᾰ_1 : a ∈ t) => idRhs False (d ᾰ (h ᾰ_1))

theorem disjoint_of_le_left {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} (h : s ≤ u) : disjoint u t → disjoint s t :=
  disjoint_of_subset_left (subset_of_le h)

theorem disjoint_of_le_right {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} (h : t ≤ u) : disjoint s u → disjoint s t :=
  disjoint_of_subset_right (subset_of_le h)

@[simp] theorem zero_disjoint {α : Type u_1} (l : multiset α) : disjoint 0 l :=
  fun {a : α} => idRhs (a ∈ [] → a ∈ l → False) (not.elim (list.not_mem_nil a))

@[simp] theorem singleton_disjoint {α : Type u_1} {l : multiset α} {a : α} : disjoint (a ::ₘ 0) l ↔ ¬a ∈ l := sorry

@[simp] theorem disjoint_singleton {α : Type u_1} {l : multiset α} {a : α} : disjoint l (a ::ₘ 0) ↔ ¬a ∈ l := sorry

@[simp] theorem disjoint_add_left {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} : disjoint (s + t) u ↔ disjoint s u ∧ disjoint t u := sorry

@[simp] theorem disjoint_add_right {α : Type u_1} {s : multiset α} {t : multiset α} {u : multiset α} : disjoint s (t + u) ↔ disjoint s t ∧ disjoint s u := sorry

@[simp] theorem disjoint_cons_left {α : Type u_1} {a : α} {s : multiset α} {t : multiset α} : disjoint (a ::ₘ s) t ↔ ¬a ∈ t ∧ disjoint s t := sorry

@[simp] theorem disjoint_cons_right {α : Type u_1} {a : α} {s : multiset α} {t : multiset α} : disjoint s (a ::ₘ t) ↔ ¬a ∈ s ∧ disjoint s t := sorry

theorem inter_eq_zero_iff_disjoint {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} : s ∩ t = 0 ↔ disjoint s t := sorry

@[simp] theorem disjoint_union_left {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} : disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u := sorry

@[simp] theorem disjoint_union_right {α : Type u_1} [DecidableEq α] {s : multiset α} {t : multiset α} {u : multiset α} : disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u := sorry

theorem disjoint_map_map {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → γ} {g : β → γ} {s : multiset α} {t : multiset β} : disjoint (map f s) (map g t) ↔ ∀ (a : α), a ∈ s → ∀ (b : β), b ∈ t → f a ≠ g b := sorry

/-- `pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this list. -/
def pairwise {α : Type u_1} (r : α → α → Prop) (m : multiset α) :=
  ∃ (l : List α), m = ↑l ∧ list.pairwise r l

theorem pairwise_coe_iff_pairwise {α : Type u_1} {r : α → α → Prop} (hr : symmetric r) {l : List α} : pairwise r ↑l ↔ list.pairwise r l := sorry

end multiset


namespace multiset


/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose_x p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
def choose_x {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : multiset α) (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : Subtype fun (a : α) => a ∈ l ∧ p a :=
  quotient.rec_on l
    (fun (l' : List α) (ex_unique : exists_unique fun (a : α) => a ∈ quotient.mk l' ∧ p a) => list.choose_x p l' sorry)
    sorry

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
def choose {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : multiset α) (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : α :=
  ↑(choose_x p l hp)

theorem choose_spec {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : multiset α) (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  subtype.property (choose_x p l hp)

theorem choose_mem {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : multiset α) (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : choose p l hp ∈ l :=
  and.left (choose_spec p l hp)

theorem choose_property {α : Type u_1} (p : α → Prop) [decidable_pred p] (l : multiset α) (hp : exists_unique fun (a : α) => a ∈ l ∧ p a) : p (choose p l hp) :=
  and.right (choose_spec p l hp)

/-- The equivalence between lists and multisets of a subsingleton type. -/
def subsingleton_equiv (α : Type u_1) [subsingleton α] : List α ≃ multiset α :=
  equiv.mk coe (Quot.lift id sorry) sorry sorry

end multiset


theorem add_monoid_hom.map_multiset_sum {α : Type u_1} {β : Type u_2} [add_comm_monoid α] [add_comm_monoid β] (f : α →+ β) (s : multiset α) : coe_fn f (multiset.sum s) = multiset.sum (multiset.map (⇑f) s) :=
  Eq.symm (multiset.sum_hom s f)

