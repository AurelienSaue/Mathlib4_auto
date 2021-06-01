/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.multiset.basic
import Mathlib.PostPort

universes u_1 

namespace Mathlib

/-!
# The powerset of a multiset
-/

namespace multiset


/-! ### powerset -/

/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists_aux`), as multisets. -/
def powerset_aux {α : Type u_1} (l : List α) : List (multiset α) :=
  0 :: list.sublists_aux l fun (x : List α) (y : List (multiset α)) => ↑x :: y

theorem powerset_aux_eq_map_coe {α : Type u_1} {l : List α} :
    powerset_aux l = list.map coe (list.sublists l) :=
  sorry

@[simp] theorem mem_powerset_aux {α : Type u_1} {l : List α} {s : multiset α} :
    s ∈ powerset_aux l ↔ s ≤ ↑l :=
  sorry

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
def powerset_aux' {α : Type u_1} (l : List α) : List (multiset α) := list.map coe (list.sublists' l)

theorem powerset_aux_perm_powerset_aux' {α : Type u_1} {l : List α} :
    powerset_aux l ~ powerset_aux' l :=
  eq.mpr (id (Eq._oldrec (Eq.refl (powerset_aux l ~ powerset_aux' l)) powerset_aux_eq_map_coe))
    (list.perm.map coe (list.sublists_perm_sublists' l))

@[simp] theorem powerset_aux'_nil {α : Type u_1} : powerset_aux' [] = [0] := rfl

@[simp] theorem powerset_aux'_cons {α : Type u_1} (a : α) (l : List α) :
    powerset_aux' (a :: l) = powerset_aux' l ++ list.map (cons a) (powerset_aux' l) :=
  sorry

theorem powerset_aux'_perm {α : Type u_1} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) :
    powerset_aux' l₁ ~ powerset_aux' l₂ :=
  sorry

theorem powerset_aux_perm {α : Type u_1} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) :
    powerset_aux l₁ ~ powerset_aux l₂ :=
  list.perm.trans powerset_aux_perm_powerset_aux'
    (list.perm.trans (powerset_aux'_perm p) (list.perm.symm powerset_aux_perm_powerset_aux'))

/-- The power set of a multiset. -/
def powerset {α : Type u_1} (s : multiset α) : multiset (multiset α) :=
  quot.lift_on s (fun (l : List α) => ↑(powerset_aux l)) sorry

theorem powerset_coe {α : Type u_1} (l : List α) :
    powerset ↑l = ↑(list.map coe (list.sublists l)) :=
  congr_arg coe powerset_aux_eq_map_coe

@[simp] theorem powerset_coe' {α : Type u_1} (l : List α) :
    powerset ↑l = ↑(list.map coe (list.sublists' l)) :=
  quot.sound powerset_aux_perm_powerset_aux'

@[simp] theorem powerset_zero {α : Type u_1} : powerset 0 = 0 ::ₘ 0 := rfl

@[simp] theorem powerset_cons {α : Type u_1} (a : α) (s : multiset α) :
    powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  sorry

@[simp] theorem mem_powerset {α : Type u_1} {s : multiset α} {t : multiset α} :
    s ∈ powerset t ↔ s ≤ t :=
  sorry

theorem map_single_le_powerset {α : Type u_1} (s : multiset α) :
    map (fun (a : α) => a ::ₘ 0) s ≤ powerset s :=
  sorry

@[simp] theorem card_powerset {α : Type u_1} (s : multiset α) :
    coe_fn card (powerset s) = bit0 1 ^ coe_fn card s :=
  sorry

theorem revzip_powerset_aux {α : Type u_1} {l : List α} {x : multiset α × multiset α}
    (h : x ∈ list.revzip (powerset_aux l)) : prod.fst x + prod.snd x = ↑l :=
  sorry

theorem revzip_powerset_aux' {α : Type u_1} {l : List α} {x : multiset α × multiset α}
    (h : x ∈ list.revzip (powerset_aux' l)) : prod.fst x + prod.snd x = ↑l :=
  sorry

theorem revzip_powerset_aux_lemma {α : Type u_1} [DecidableEq α] (l : List α)
    {l' : List (multiset α)}
    (H : ∀ {x : multiset α × multiset α}, x ∈ list.revzip l' → prod.fst x + prod.snd x = ↑l) :
    list.revzip l' = list.map (fun (x : multiset α) => (x, ↑l - x)) l' :=
  sorry

theorem revzip_powerset_aux_perm_aux' {α : Type u_1} {l : List α} :
    list.revzip (powerset_aux l) ~ list.revzip (powerset_aux' l) :=
  sorry

theorem revzip_powerset_aux_perm {α : Type u_1} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) :
    list.revzip (powerset_aux l₁) ~ list.revzip (powerset_aux l₂) :=
  sorry

/-! ### powerset_len -/

/-- Helper function for `powerset_len`. Given a list `l`, `powerset_len_aux n l` is the list
of sublists of length `n`, as multisets. -/
def powerset_len_aux {α : Type u_1} (n : ℕ) (l : List α) : List (multiset α) :=
  list.sublists_len_aux n l coe []

theorem powerset_len_aux_eq_map_coe {α : Type u_1} {n : ℕ} {l : List α} :
    powerset_len_aux n l = list.map coe (list.sublists_len n l) :=
  sorry

@[simp] theorem mem_powerset_len_aux {α : Type u_1} {n : ℕ} {l : List α} {s : multiset α} :
    s ∈ powerset_len_aux n l ↔ s ≤ ↑l ∧ coe_fn card s = n :=
  sorry

@[simp] theorem powerset_len_aux_zero {α : Type u_1} (l : List α) : powerset_len_aux 0 l = [0] :=
  sorry

@[simp] theorem powerset_len_aux_nil {α : Type u_1} (n : ℕ) : powerset_len_aux (n + 1) [] = [] :=
  rfl

@[simp] theorem powerset_len_aux_cons {α : Type u_1} (n : ℕ) (a : α) (l : List α) :
    powerset_len_aux (n + 1) (a :: l) =
        powerset_len_aux (n + 1) l ++ list.map (cons a) (powerset_len_aux n l) :=
  sorry

theorem powerset_len_aux_perm {α : Type u_1} {n : ℕ} {l₁ : List α} {l₂ : List α} (p : l₁ ~ l₂) :
    powerset_len_aux n l₁ ~ powerset_len_aux n l₂ :=
  sorry

/-- `powerset_len n s` is the multiset of all submultisets of `s` of length `n`. -/
def powerset_len {α : Type u_1} (n : ℕ) (s : multiset α) : multiset (multiset α) :=
  quot.lift_on s (fun (l : List α) => ↑(powerset_len_aux n l)) sorry

theorem powerset_len_coe' {α : Type u_1} (n : ℕ) (l : List α) :
    powerset_len n ↑l = ↑(powerset_len_aux n l) :=
  rfl

theorem powerset_len_coe {α : Type u_1} (n : ℕ) (l : List α) :
    powerset_len n ↑l = ↑(list.map coe (list.sublists_len n l)) :=
  congr_arg coe powerset_len_aux_eq_map_coe

@[simp] theorem powerset_len_zero_left {α : Type u_1} (s : multiset α) :
    powerset_len 0 s = 0 ::ₘ 0 :=
  sorry

@[simp] theorem powerset_len_zero_right {α : Type u_1} (n : ℕ) : powerset_len (n + 1) 0 = 0 := rfl

@[simp] theorem powerset_len_cons {α : Type u_1} (n : ℕ) (a : α) (s : multiset α) :
    powerset_len (n + 1) (a ::ₘ s) = powerset_len (n + 1) s + map (cons a) (powerset_len n s) :=
  sorry

@[simp] theorem mem_powerset_len {α : Type u_1} {n : ℕ} {s : multiset α} {t : multiset α} :
    s ∈ powerset_len n t ↔ s ≤ t ∧ coe_fn card s = n :=
  sorry

@[simp] theorem card_powerset_len {α : Type u_1} (n : ℕ) (s : multiset α) :
    coe_fn card (powerset_len n s) = nat.choose (coe_fn card s) n :=
  sorry

theorem powerset_len_le_powerset {α : Type u_1} (n : ℕ) (s : multiset α) :
    powerset_len n s ≤ powerset s :=
  sorry

theorem powerset_len_mono {α : Type u_1} (n : ℕ) {s : multiset α} {t : multiset α} (h : s ≤ t) :
    powerset_len n s ≤ powerset_len n t :=
  sorry

end Mathlib