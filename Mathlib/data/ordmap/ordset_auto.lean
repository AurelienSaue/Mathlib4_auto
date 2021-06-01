/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.ordmap.ordnode
import Mathlib.algebra.ordered_ring
import Mathlib.data.nat.dist
import Mathlib.tactic.linarith.default
import Mathlib.PostPort

universes u_1 l 

namespace Mathlib

/-!
# Verification of the `ordnode α` datatype

This file proves the correctness of the operations in `data.ordmap.ordnode`.
The public facing version is the type `ordset α`, which is a wrapper around
`ordnode α` which includes the correctness invariant of the type, and it exposes
parallel operations like `insert` as functions on `ordset` that do the same
thing but bundle the correctness proofs. The advantage is that it is possible
to, for example, prove that the result of `find` on `insert` will actually find
the element, while `ordnode` cannot guarantee this if the input tree did not
satisfy the type invariants.

## Main definitions

* `ordset α`: A well formed set of values of type `α`

## Implementation notes

The majority of this file is actually in the `ordnode` namespace, because we first
have to prove the correctness of all the operations (and defining what correctness
means here is actually somewhat subtle). So all the actual `ordset` operations are
at the very end, once we have all the theorems.

An `ordnode α` is an inductive type which describes a tree which stores the `size` at
internal nodes. The correctness invariant of an `ordnode α` is:

* `ordnode.sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `ordnode.balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `ordnode.bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬ (b ≤ a)`. We enforce this using `ordnode.bounded` which includes also a global
  upper and lower bound.

Because the `ordnode` file was ported from Haskell, the correctness invariants of some
of the functions have not been spelled out, and some theorems like
`ordnode.valid'.balance_l_aux` show very intricate assumptions on the sizes,
which may need to be revised if it turns out some operations violate these assumptions,
because there is a decent amount of slop in the actual data structure invariants, so the
theorem will go through with multiple choices of assumption.

**Note:** This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming

-/

namespace ordnode


/-! ### delta and ratio -/

theorem not_le_delta {s : ℕ} (H : 1 ≤ s) : ¬s ≤ delta * 0 :=
  fun (h : s ≤ delta * 0) =>
    not_lt_of_le (eq.mp (Eq._oldrec (Eq.refl (s ≤ delta * 0)) (mul_zero delta)) h) H

theorem delta_lt_false {a : ℕ} {b : ℕ} (h₁ : delta * a < b) (h₂ : delta * b < a) : False := sorry

/-! ### `singleton` -/

/-! ### `size` and `empty` -/

/-- O(n). Computes the actual number of elements in the set, ignoring the cached `size` field. -/
def real_size {α : Type u_1} : ordnode α → ℕ := sorry

/-! ### `sized` -/

/-- The `sized` property asserts that all the `size` fields in nodes match the actual size of the
respective subtrees. -/
def sized {α : Type u_1} : ordnode α → Prop := sorry

theorem sized.node' {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : sized l)
    (hr : sized r) : sized (node' l x r) :=
  { left := rfl, right := { left := hl, right := hr } }

theorem sized.eq_node' {α : Type u_1} {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    (h : sized (node s l x r)) : node s l x r = node' l x r :=
  eq.mpr (id (Eq._oldrec (Eq.refl (node s l x r = node' l x r)) (and.left h)))
    (Eq.refl (node (size l + size r + 1) l x r))

theorem sized.size_eq {α : Type u_1} {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    (H : sized (node s l x r)) : size (node s l x r) = size l + size r + 1 :=
  and.left H

theorem sized.induction {α : Type u_1} {t : ordnode α} (hl : sized t) {C : ordnode α → Prop}
    (H0 : C nil) (H1 : ∀ (l : ordnode α) (x : α) (r : ordnode α), C l → C r → C (node' l x r)) :
    C t :=
  sorry

theorem size_eq_real_size {α : Type u_1} {t : ordnode α} : sized t → size t = real_size t := sorry

@[simp] theorem sized.size_eq_zero {α : Type u_1} {t : ordnode α} (ht : sized t) :
    size t = 0 ↔ t = nil :=
  sorry

theorem sized.pos {α : Type u_1} {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    (h : sized (node s l x r)) : 0 < s :=
  eq.mpr (id (Eq._oldrec (Eq.refl (0 < s)) (and.left h)))
    (nat.le_add_left (Nat.succ 0) (size l + size r))

/-! `dual` -/

theorem dual_dual {α : Type u_1} (t : ordnode α) : dual (dual t) = t := sorry

@[simp] theorem size_dual {α : Type u_1} (t : ordnode α) : size (dual t) = size t :=
  ordnode.cases_on t (Eq.refl (size (dual nil)))
    fun (t_size : ℕ) (t_l : ordnode α) (t_x : α) (t_r : ordnode α) =>
      Eq.refl (size (dual (node t_size t_l t_x t_r)))

/-! `balanced` -/

/-- The `balanced_sz l r` asserts that a hypothetical tree with children of sizes `l` and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a singleton on one side
and nothing on the other. -/
def balanced_sz (l : ℕ) (r : ℕ) := l + r ≤ 1 ∨ l ≤ delta * r ∧ r ≤ delta * l

protected instance balanced_sz.dec : DecidableRel balanced_sz := fun (l r : ℕ) => or.decidable

/-- The `balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level). -/
def balanced {α : Type u_1} : ordnode α → Prop := sorry

protected instance balanced.dec {α : Type u_1} : decidable_pred balanced := sorry

theorem balanced_sz.symm {l : ℕ} {r : ℕ} : balanced_sz l r → balanced_sz r l :=
  or.imp (eq.mpr (id (Eq._oldrec (Eq.refl (l + r ≤ 1 → r + l ≤ 1)) (add_comm l r))) id) and.symm

theorem balanced_sz_zero {l : ℕ} : balanced_sz l 0 ↔ l ≤ 1 := sorry

theorem balanced_sz_up {l : ℕ} {r₁ : ℕ} {r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ r₂ ≤ delta * l)
    (H : balanced_sz l r₁) : balanced_sz l r₂ :=
  sorry

theorem balanced_sz_down {l : ℕ} {r₁ : ℕ} {r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ l ≤ delta * r₁)
    (H : balanced_sz l r₂) : balanced_sz l r₁ :=
  sorry

theorem balanced.dual {α : Type u_1} {t : ordnode α} : balanced t → balanced (dual t) := sorry

/-! ### `rotate` and `balance` -/

/-- Build a tree from three nodes, left associated (ignores the invariants). -/
def node3_l {α : Type u_1} (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
    ordnode α :=
  node' (node' l x m) y r

/-- Build a tree from three nodes, right associated (ignores the invariants). -/
def node3_r {α : Type u_1} (l : ordnode α) (x : α) (m : ordnode α) (y : α) (r : ordnode α) :
    ordnode α :=
  node' l x (node' m y r)

/-- Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b) (c d))`. -/
def node4_l {α : Type u_1} : ordnode α → α → ordnode α → α → ordnode α → ordnode α := sorry

/-- Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b) (c d))`. -/
def node4_r {α : Type u_1} : ordnode α → α → ordnode α → α → ordnode α → ordnode α := sorry

/-- Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset. -/
def rotate_l {α : Type u_1} : ordnode α → α → ordnode α → ordnode α := sorry

/-- Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset. -/
def rotate_r {α : Type u_1} : ordnode α → α → ordnode α → ordnode α := sorry

/-- A left balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balance_l' {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
  ite (size l + size r ≤ 1) (node' l x r)
    (ite (size l > delta * size r) (rotate_r l x r) (node' l x r))

/-- A right balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balance_r' {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
  ite (size l + size r ≤ 1) (node' l x r)
    (ite (size r > delta * size l) (rotate_l l x r) (node' l x r))

/-- The full balance operation. This is the same as `balance`, but with less manual inlining.
It is somewhat easier to work with this version in proofs. -/
def balance' {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
  ite (size l + size r ≤ 1) (node' l x r)
    (ite (size r > delta * size l) (rotate_l l x r)
      (ite (size l > delta * size r) (rotate_r l x r) (node' l x r)))

theorem dual_node' {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) :
    dual (node' l x r) = node' (dual r) x (dual l) :=
  sorry

theorem dual_node3_l {α : Type u_1} (l : ordnode α) (x : α) (m : ordnode α) (y : α)
    (r : ordnode α) : dual (node3_l l x m y r) = node3_r (dual r) y (dual m) x (dual l) :=
  sorry

theorem dual_node3_r {α : Type u_1} (l : ordnode α) (x : α) (m : ordnode α) (y : α)
    (r : ordnode α) : dual (node3_r l x m y r) = node3_l (dual r) y (dual m) x (dual l) :=
  sorry

theorem dual_node4_l {α : Type u_1} (l : ordnode α) (x : α) (m : ordnode α) (y : α)
    (r : ordnode α) : dual (node4_l l x m y r) = node4_r (dual r) y (dual m) x (dual l) :=
  sorry

theorem dual_node4_r {α : Type u_1} (l : ordnode α) (x : α) (m : ordnode α) (y : α)
    (r : ordnode α) : dual (node4_r l x m y r) = node4_l (dual r) y (dual m) x (dual l) :=
  sorry

theorem dual_rotate_l {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) :
    dual (rotate_l l x r) = rotate_r (dual r) x (dual l) :=
  sorry

theorem dual_rotate_r {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) :
    dual (rotate_r l x r) = rotate_l (dual r) x (dual l) :=
  sorry

theorem dual_balance' {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) :
    dual (balance' l x r) = balance' (dual r) x (dual l) :=
  sorry

theorem dual_balance_l {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) :
    dual (balance_l l x r) = balance_r (dual r) x (dual l) :=
  sorry

theorem dual_balance_r {α : Type u_1} (l : ordnode α) (x : α) (r : ordnode α) :
    dual (balance_r l x r) = balance_l (dual r) x (dual l) :=
  sorry

theorem sized.node3_l {α : Type u_1} {l : ordnode α} {x : α} {m : ordnode α} {y : α} {r : ordnode α}
    (hl : sized l) (hm : sized m) (hr : sized r) : sized (node3_l l x m y r) :=
  sized.node' (sized.node' hl hm) hr

theorem sized.node3_r {α : Type u_1} {l : ordnode α} {x : α} {m : ordnode α} {y : α} {r : ordnode α}
    (hl : sized l) (hm : sized m) (hr : sized r) : sized (node3_r l x m y r) :=
  sized.node' hl (sized.node' hm hr)

theorem sized.node4_l {α : Type u_1} {l : ordnode α} {x : α} {m : ordnode α} {y : α} {r : ordnode α}
    (hl : sized l) (hm : sized m) (hr : sized r) : sized (node4_l l x m y r) :=
  sorry

theorem node3_l_size {α : Type u_1} {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} : size (node3_l l x m y r) = size l + size m + size r + bit0 1 :=
  sorry

theorem node3_r_size {α : Type u_1} {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} : size (node3_r l x m y r) = size l + size m + size r + bit0 1 :=
  sorry

theorem node4_l_size {α : Type u_1} {l : ordnode α} {x : α} {m : ordnode α} {y : α} {r : ordnode α}
    (hm : sized m) : size (node4_l l x m y r) = size l + size m + size r + bit0 1 :=
  sorry

theorem sized.dual {α : Type u_1} {t : ordnode α} (h : sized t) : sized (dual t) := sorry

theorem sized.dual_iff {α : Type u_1} {t : ordnode α} : sized (dual t) ↔ sized t :=
  { mp :=
      fun (h : sized (dual t)) =>
        eq.mpr (id (Eq._oldrec (Eq.refl (sized t)) (Eq.symm (dual_dual t)))) (sized.dual h),
    mpr := sized.dual }

theorem sized.rotate_l {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : sized l)
    (hr : sized r) : sized (rotate_l l x r) :=
  sorry

theorem sized.rotate_r {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : sized l)
    (hr : sized r) : sized (rotate_r l x r) :=
  iff.mp sized.dual_iff
    (eq.mpr (id (Eq._oldrec (Eq.refl (sized (dual (rotate_r l x r)))) (dual_rotate_r l x r)))
      (sized.rotate_l (sized.dual hr) (sized.dual hl)))

theorem sized.rotate_l_size {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hm : sized r) :
    size (rotate_l l x r) = size l + size r + 1 :=
  sorry

theorem sized.rotate_r_size {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : sized l) :
    size (rotate_r l x r) = size l + size r + 1 :=
  sorry

theorem sized.balance' {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : sized l)
    (hr : sized r) : sized (balance' l x r) :=
  sorry

theorem size_balance' {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : sized l)
    (hr : sized r) : size (balance' l x r) = size l + size r + 1 :=
  sorry

/-! ## `all`, `any`, `emem`, `amem` -/

theorem all.imp {α : Type u_1} {P : α → Prop} {Q : α → Prop} (H : ∀ (a : α), P a → Q a)
    {t : ordnode α} : all P t → all Q t :=
  sorry

theorem any.imp {α : Type u_1} {P : α → Prop} {Q : α → Prop} (H : ∀ (a : α), P a → Q a)
    {t : ordnode α} : any P t → any Q t :=
  sorry

theorem all_singleton {α : Type u_1} {P : α → Prop} {x : α} : all P (singleton x) ↔ P x :=
  { mp := fun (h : all P (singleton x)) => and.left (and.right h),
    mpr := fun (h : P x) => { left := True.intro, right := { left := h, right := True.intro } } }

theorem any_singleton {α : Type u_1} {P : α → Prop} {x : α} : any P (singleton x) ↔ P x := sorry

theorem all_dual {α : Type u_1} {P : α → Prop} {t : ordnode α} : all P (dual t) ↔ all P t := sorry

theorem all_iff_forall {α : Type u_1} {P : α → Prop} {t : ordnode α} :
    all P t ↔ ∀ (x : α), emem x t → P x :=
  sorry

theorem any_iff_exists {α : Type u_1} {P : α → Prop} {t : ordnode α} :
    any P t ↔ ∃ (x : α), emem x t ∧ P x :=
  sorry

theorem emem_iff_all {α : Type u_1} {x : α} {t : ordnode α} :
    emem x t ↔ ∀ (P : α → Prop), all P t → P x :=
  sorry

theorem all_node' {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {r : ordnode α} :
    all P (node' l x r) ↔ all P l ∧ P x ∧ all P r :=
  iff.rfl

theorem all_node3_l {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} : all P (node3_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  sorry

theorem all_node3_r {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} : all P (node3_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  iff.rfl

theorem all_node4_l {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} : all P (node4_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  sorry

theorem all_node4_r {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} : all P (node4_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  sorry

theorem all_rotate_l {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {r : ordnode α} :
    all P (rotate_l l x r) ↔ all P l ∧ P x ∧ all P r :=
  sorry

theorem all_rotate_r {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {r : ordnode α} :
    all P (rotate_r l x r) ↔ all P l ∧ P x ∧ all P r :=
  sorry

theorem all_balance' {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {r : ordnode α} :
    all P (balance' l x r) ↔ all P l ∧ P x ∧ all P r :=
  sorry

/-! ### `to_list` -/

theorem foldr_cons_eq_to_list {α : Type u_1} (t : ordnode α) (r : List α) :
    foldr List.cons t r = to_list t ++ r :=
  sorry

@[simp] theorem to_list_nil {α : Type u_1} : to_list nil = [] := rfl

@[simp] theorem to_list_node {α : Type u_1} (s : ℕ) (l : ordnode α) (x : α) (r : ordnode α) :
    to_list (node s l x r) = to_list l ++ x :: to_list r :=
  sorry

theorem emem_iff_mem_to_list {α : Type u_1} {x : α} {t : ordnode α} : emem x t ↔ x ∈ to_list t :=
  sorry

theorem length_to_list' {α : Type u_1} (t : ordnode α) : list.length (to_list t) = real_size t :=
  sorry

theorem length_to_list {α : Type u_1} {t : ordnode α} (h : sized t) :
    list.length (to_list t) = size t :=
  eq.mpr (id (Eq._oldrec (Eq.refl (list.length (to_list t) = size t)) (length_to_list' t)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (real_size t = size t)) (size_eq_real_size h)))
      (Eq.refl (real_size t)))

theorem equiv_iff {α : Type u_1} {t₁ : ordnode α} {t₂ : ordnode α} (h₁ : sized t₁) (h₂ : sized t₂) :
    equiv t₁ t₂ ↔ to_list t₁ = to_list t₂ :=
  sorry

/-! ### `(find/erase/split)_(min/max)` -/

theorem find_min'_dual {α : Type u_1} (t : ordnode α) (x : α) :
    find_min' (dual t) x = find_max' x t :=
  sorry

theorem find_max'_dual {α : Type u_1} (t : ordnode α) (x : α) :
    find_max' x (dual t) = find_min' t x :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (find_max' x (dual t) = find_min' t x))
        (Eq.symm (find_min'_dual (dual t) x))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (find_min' (dual (dual t)) x = find_min' t x)) (dual_dual t)))
      (Eq.refl (find_min' t x)))

theorem find_min_dual {α : Type u_1} (t : ordnode α) : find_min (dual t) = find_max t :=
  ordnode.cases_on t (idRhs (find_min (dual nil) = find_min (dual nil)) rfl)
    fun (t_size : ℕ) (t_l : ordnode α) (t_x : α) (t_r : ordnode α) =>
      idRhs (some (find_min' (dual t_r) t_x) = some (find_max' t_x t_r))
        (congr_arg some (find_min'_dual t_r t_x))

theorem find_max_dual {α : Type u_1} (t : ordnode α) : find_max (dual t) = find_min t :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (find_max (dual t) = find_min t)) (Eq.symm (find_min_dual (dual t)))))
    (eq.mpr (id (Eq._oldrec (Eq.refl (find_min (dual (dual t)) = find_min t)) (dual_dual t)))
      (Eq.refl (find_min t)))

theorem dual_erase_min {α : Type u_1} (t : ordnode α) : dual (erase_min t) = erase_max (dual t) :=
  sorry

theorem dual_erase_max {α : Type u_1} (t : ordnode α) : dual (erase_max t) = erase_min (dual t) :=
  sorry

theorem split_min_eq {α : Type u_1} (s : ℕ) (l : ordnode α) (x : α) (r : ordnode α) :
    split_min' l x r = (find_min' l x, erase_min (node s l x r)) :=
  sorry

theorem split_max_eq {α : Type u_1} (s : ℕ) (l : ordnode α) (x : α) (r : ordnode α) :
    split_max' l x r = (erase_max (node s l x r), find_max' x r) :=
  sorry

theorem find_min'_all {α : Type u_1} {P : α → Prop} (t : ordnode α) (x : α) :
    all P t → P x → P (find_min' t x) :=
  sorry

theorem find_max'_all {α : Type u_1} {P : α → Prop} (x : α) (t : ordnode α) :
    P x → all P t → P (find_max' x t) :=
  sorry

/-! ### `glue` -/

/-! ### `merge` -/

@[simp] theorem merge_nil_left {α : Type u_1} (t : ordnode α) : merge t nil = t :=
  ordnode.cases_on t (Eq.refl (merge nil nil))
    fun (t_size : ℕ) (t_l : ordnode α) (t_x : α) (t_r : ordnode α) =>
      Eq.refl (merge (node t_size t_l t_x t_r) nil)

@[simp] theorem merge_nil_right {α : Type u_1} (t : ordnode α) : merge nil t = t := rfl

@[simp] theorem merge_node {α : Type u_1} {ls : ℕ} {ll : ordnode α} {lx : α} {lr : ordnode α}
    {rs : ℕ} {rl : ordnode α} {rx : α} {rr : ordnode α} :
    merge (node ls ll lx lr) (node rs rl rx rr) =
        ite (delta * ls < rs) (balance_l (merge (node ls ll lx lr) rl) rx rr)
          (ite (delta * rs < ls) (balance_r ll lx (merge lr (node rs rl rx rr)))
            (glue (node ls ll lx lr) (node rs rl rx rr))) :=
  rfl

/-! ### `insert` -/

theorem dual_insert {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq] (x : α)
    (t : ordnode α) : dual (ordnode.insert x t) = ordnode.insert x (dual t) :=
  sorry

/-! ### `balance` properties -/

theorem balance_eq_balance' {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : balanced l)
    (hr : balanced r) (sl : sized l) (sr : sized r) : balance l x r = balance' l x r :=
  sorry

theorem balance_l_eq_balance {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (sl : sized l)
    (sr : sized r) (H1 : size l = 0 → size r ≤ 1)
    (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) : balance_l l x r = balance l x r :=
  sorry

/-- `raised n m` means `m` is either equal or one up from `n`. -/
def raised (n : ℕ) (m : ℕ) := m = n ∨ m = n + 1

theorem raised_iff {n : ℕ} {m : ℕ} : raised n m ↔ n ≤ m ∧ m ≤ n + 1 := sorry

theorem raised.dist_le {n : ℕ} {m : ℕ} (H : raised n m) : nat.dist n m ≤ 1 := sorry

theorem raised.dist_le' {n : ℕ} {m : ℕ} (H : raised n m) : nat.dist m n ≤ 1 :=
  eq.mpr (id (Eq._oldrec (Eq.refl (nat.dist m n ≤ 1)) (nat.dist_comm m n))) (raised.dist_le H)

theorem raised.add_left (k : ℕ) {n : ℕ} {m : ℕ} (H : raised n m) : raised (k + n) (k + m) :=
  or.dcases_on H (fun (H : m = n) => Eq._oldrec (Or.inl rfl) H)
    fun (H : m = n + 1) => Eq._oldrec (Or.inr rfl) (Eq.symm H)

theorem raised.add_right (k : ℕ) {n : ℕ} {m : ℕ} (H : raised n m) : raised (n + k) (m + k) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (raised (n + k) (m + k))) (add_comm n k)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (raised (k + n) (m + k))) (add_comm m k)))
      (raised.add_left k H))

theorem raised.right {α : Type u_1} {l : ordnode α} {x₁ : α} {x₂ : α} {r₁ : ordnode α}
    {r₂ : ordnode α} (H : raised (size r₁) (size r₂)) :
    raised (size (node' l x₁ r₁)) (size (node' l x₂ r₂)) :=
  sorry

theorem balance_l_eq_balance' {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α}
    (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
    (H :
      (∃ (l' : ℕ), raised l' (size l) ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised (size r) r' ∧ balanced_sz (size l) r') :
    balance_l l x r = balance' l x r :=
  sorry

theorem balance_sz_dual {α : Type u_1} {l : ordnode α} {r : ordnode α}
    (H :
      (∃ (l' : ℕ), raised (size l) l' ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised r' (size r) ∧ balanced_sz (size l) r') :
    (∃ (l' : ℕ), raised l' (size (dual r)) ∧ balanced_sz l' (size (dual l))) ∨
        ∃ (r' : ℕ), raised (size (dual l)) r' ∧ balanced_sz (size (dual r)) r' :=
  sorry

theorem size_balance_l {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : balanced l)
    (hr : balanced r) (sl : sized l) (sr : sized r)
    (H :
      (∃ (l' : ℕ), raised l' (size l) ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised (size r) r' ∧ balanced_sz (size l) r') :
    size (balance_l l x r) = size l + size r + 1 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (size (balance_l l x r) = size l + size r + 1))
        (balance_l_eq_balance' hl hr sl sr H)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (size (balance' l x r) = size l + size r + 1)) (size_balance' sl sr)))
      (Eq.refl (size l + size r + 1)))

theorem all_balance_l {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {r : ordnode α}
    (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
    (H :
      (∃ (l' : ℕ), raised l' (size l) ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised (size r) r' ∧ balanced_sz (size l) r') :
    all P (balance_l l x r) ↔ all P l ∧ P x ∧ all P r :=
  sorry

theorem balance_r_eq_balance' {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α}
    (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
    (H :
      (∃ (l' : ℕ), raised (size l) l' ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised r' (size r) ∧ balanced_sz (size l) r') :
    balance_r l x r = balance' l x r :=
  sorry

theorem size_balance_r {α : Type u_1} {l : ordnode α} {x : α} {r : ordnode α} (hl : balanced l)
    (hr : balanced r) (sl : sized l) (sr : sized r)
    (H :
      (∃ (l' : ℕ), raised (size l) l' ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised r' (size r) ∧ balanced_sz (size l) r') :
    size (balance_r l x r) = size l + size r + 1 :=
  eq.mpr
    (id
      (Eq._oldrec (Eq.refl (size (balance_r l x r) = size l + size r + 1))
        (balance_r_eq_balance' hl hr sl sr H)))
    (eq.mpr
      (id
        (Eq._oldrec (Eq.refl (size (balance' l x r) = size l + size r + 1)) (size_balance' sl sr)))
      (Eq.refl (size l + size r + 1)))

theorem all_balance_r {α : Type u_1} {P : α → Prop} {l : ordnode α} {x : α} {r : ordnode α}
    (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
    (H :
      (∃ (l' : ℕ), raised (size l) l' ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised r' (size r) ∧ balanced_sz (size l) r') :
    all P (balance_r l x r) ↔ all P l ∧ P x ∧ all P r :=
  sorry

/-! ### `bounded` -/

/-- `bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`, and also this
property holds recursively in subtrees, making the full tree a BST. The bounds can be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints. -/
def bounded {α : Type u_1} [preorder α] : ordnode α → with_bot α → with_top α → Prop := sorry

theorem bounded.dual {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α} {o₂ : with_top α}
    (h : bounded t o₁ o₂) : bounded (dual t) o₂ o₁ :=
  sorry

theorem bounded.dual_iff {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} : bounded t o₁ o₂ ↔ bounded (dual t) o₂ o₁ :=
  sorry

theorem bounded.weak_left {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} : bounded t o₁ o₂ → bounded t ⊥ o₂ :=
  sorry

theorem bounded.weak_right {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} : bounded t o₁ o₂ → bounded t o₁ ⊤ :=
  sorry

theorem bounded.weak {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α} {o₂ : with_top α}
    (h : bounded t o₁ o₂) : bounded t ⊥ ⊤ :=
  bounded.weak_right (bounded.weak_left h)

theorem bounded.mono_left {α : Type u_1} [preorder α] {x : α} {y : α} (xy : x ≤ y) {t : ordnode α}
    {o : with_top α} : bounded t (↑y) o → bounded t (↑x) o :=
  sorry

theorem bounded.mono_right {α : Type u_1} [preorder α] {x : α} {y : α} (xy : x ≤ y) {t : ordnode α}
    {o : with_bot α} : bounded t o ↑x → bounded t o ↑y :=
  sorry

theorem bounded.to_lt {α : Type u_1} [preorder α] {t : ordnode α} {x : α} {y : α} :
    bounded t ↑x ↑y → x < y :=
  sorry

theorem bounded.to_nil {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} : bounded t o₁ o₂ → bounded nil o₁ o₂ :=
  sorry

theorem bounded.trans_left {α : Type u_1} [preorder α] {t₁ : ordnode α} {t₂ : ordnode α} {x : α}
    {o₁ : with_bot α} {o₂ : with_top α} :
    bounded t₁ o₁ ↑x → bounded t₂ (↑x) o₂ → bounded t₂ o₁ o₂ :=
  sorry

theorem bounded.trans_right {α : Type u_1} [preorder α] {t₁ : ordnode α} {t₂ : ordnode α} {x : α}
    {o₁ : with_bot α} {o₂ : with_top α} :
    bounded t₁ o₁ ↑x → bounded t₂ (↑x) o₂ → bounded t₁ o₁ o₂ :=
  sorry

theorem bounded.mem_lt {α : Type u_1} [preorder α] {t : ordnode α} {o : with_bot α} {x : α} :
    bounded t o ↑x → all (fun (_x : α) => _x < x) t :=
  sorry

theorem bounded.mem_gt {α : Type u_1} [preorder α] {t : ordnode α} {o : with_top α} {x : α} :
    bounded t (↑x) o → all (fun (_x : α) => _x > x) t :=
  sorry

theorem bounded.of_lt {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} {x : α} :
    bounded t o₁ o₂ → bounded nil o₁ ↑x → all (fun (_x : α) => _x < x) t → bounded t o₁ ↑x :=
  sorry

theorem bounded.of_gt {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} {x : α} :
    bounded t o₁ o₂ → bounded nil (↑x) o₂ → all (fun (_x : α) => _x > x) t → bounded t (↑x) o₂ :=
  sorry

theorem bounded.to_sep {α : Type u_1} [preorder α] {t₁ : ordnode α} {t₂ : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} {x : α} (h₁ : bounded t₁ o₁ ↑x) (h₂ : bounded t₂ (↑x) o₂) :
    all (fun (y : α) => all (fun (z : α) => y < z) t₂) t₁ :=
  all.imp
    (fun (y : α) (yx : y < x) =>
      all.imp (fun (z : α) (xz : z > x) => lt_trans yx xz) (bounded.mem_gt h₂))
    (bounded.mem_lt h₁)

/-! ### `valid` -/

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. This version of `valid` also puts all elements in the tree in the interval `(lo, hi)`. -/
structure valid' {α : Type u_1} [preorder α] (lo : with_bot α) (t : ordnode α) (hi : with_top α)
    where
  ord : bounded t lo hi
  sz : sized t
  bal : balanced t

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. -/
def valid {α : Type u_1} [preorder α] (t : ordnode α) := valid' ⊥ t ⊤

theorem valid'.mono_left {α : Type u_1} [preorder α] {x : α} {y : α} (xy : x ≤ y) {t : ordnode α}
    {o : with_top α} (h : valid' (↑y) t o) : valid' (↑x) t o :=
  valid'.mk (bounded.mono_left xy (valid'.ord h)) (valid'.sz h) (valid'.bal h)

theorem valid'.mono_right {α : Type u_1} [preorder α] {x : α} {y : α} (xy : x ≤ y) {t : ordnode α}
    {o : with_bot α} (h : valid' o t ↑x) : valid' o t ↑y :=
  valid'.mk (bounded.mono_right xy (valid'.ord h)) (valid'.sz h) (valid'.bal h)

theorem valid'.trans_left {α : Type u_1} [preorder α] {t₁ : ordnode α} {t₂ : ordnode α} {x : α}
    {o₁ : with_bot α} {o₂ : with_top α} (h : bounded t₁ o₁ ↑x) (H : valid' (↑x) t₂ o₂) :
    valid' o₁ t₂ o₂ :=
  valid'.mk (bounded.trans_left h (valid'.ord H)) (valid'.sz H) (valid'.bal H)

theorem valid'.trans_right {α : Type u_1} [preorder α] {t₁ : ordnode α} {t₂ : ordnode α} {x : α}
    {o₁ : with_bot α} {o₂ : with_top α} (H : valid' o₁ t₁ ↑x) (h : bounded t₂ (↑x) o₂) :
    valid' o₁ t₁ o₂ :=
  valid'.mk (bounded.trans_right (valid'.ord H) h) (valid'.sz H) (valid'.bal H)

theorem valid'.of_lt {α : Type u_1} [preorder α] {t : ordnode α} {x : α} {o₁ : with_bot α}
    {o₂ : with_top α} (H : valid' o₁ t o₂) (h₁ : bounded nil o₁ ↑x)
    (h₂ : all (fun (_x : α) => _x < x) t) : valid' o₁ t ↑x :=
  valid'.mk (bounded.of_lt (valid'.ord H) h₁ h₂) (valid'.sz H) (valid'.bal H)

theorem valid'.of_gt {α : Type u_1} [preorder α] {t : ordnode α} {x : α} {o₁ : with_bot α}
    {o₂ : with_top α} (H : valid' o₁ t o₂) (h₁ : bounded nil (↑x) o₂)
    (h₂ : all (fun (_x : α) => _x > x) t) : valid' (↑x) t o₂ :=
  valid'.mk (bounded.of_gt (valid'.ord H) h₁ h₂) (valid'.sz H) (valid'.bal H)

theorem valid'.valid {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α} {o₂ : with_top α}
    (h : valid' o₁ t o₂) : valid t :=
  valid'.mk (bounded.weak (valid'.ord h)) (valid'.sz h) (valid'.bal h)

theorem valid'_nil {α : Type u_1} [preorder α] {o₁ : with_bot α} {o₂ : with_top α}
    (h : bounded nil o₁ o₂) : valid' o₁ nil o₂ :=
  valid'.mk h True.intro True.intro

theorem valid_nil {α : Type u_1} [preorder α] : valid nil := valid'_nil True.intro

theorem valid'.node {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H : balanced_sz (size l) (size r)) (hs : s = size l + size r + 1) :
    valid' o₁ (node s l x r) o₂ :=
  valid'.mk { left := valid'.ord hl, right := valid'.ord hr }
    { left := hs, right := { left := valid'.sz hl, right := valid'.sz hr } }
    { left := H, right := { left := valid'.bal hl, right := valid'.bal hr } }

theorem valid'.dual {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α} {o₂ : with_top α}
    (h : valid' o₁ t o₂) : valid' o₂ (dual t) o₁ :=
  sorry

theorem valid'.dual_iff {α : Type u_1} [preorder α] {t : ordnode α} {o₁ : with_bot α}
    {o₂ : with_top α} : valid' o₁ t o₂ ↔ valid' o₂ (dual t) o₁ :=
  sorry

theorem valid.dual {α : Type u_1} [preorder α] {t : ordnode α} : valid t → valid (dual t) :=
  valid'.dual

theorem valid.dual_iff {α : Type u_1} [preorder α] {t : ordnode α} : valid t ↔ valid (dual t) :=
  valid'.dual_iff

theorem valid'.left {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (H : valid' o₁ (node s l x r) o₂) : valid' o₁ l ↑x :=
  valid'.mk (and.left (valid'.ord H)) (and.left (and.right (valid'.sz H)))
    (and.left (and.right (valid'.bal H)))

theorem valid'.right {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (H : valid' o₁ (node s l x r) o₂) : valid' (↑x) r o₂ :=
  valid'.mk (and.right (valid'.ord H)) (and.right (and.right (valid'.sz H)))
    (and.right (and.right (valid'.bal H)))

theorem valid.left {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    (H : valid (node s l x r)) : valid l :=
  valid'.valid (valid'.left H)

theorem valid.right {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    (H : valid (node s l x r)) : valid r :=
  valid'.valid (valid'.right H)

theorem valid.size_eq {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α} {r : ordnode α}
    (H : valid (node s l x r)) : size (node s l x r) = size l + size r + 1 :=
  and.left (valid'.sz H)

theorem valid'.node' {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H : balanced_sz (size l) (size r)) : valid' o₁ (node' l x r) o₂ :=
  valid'.node hl hr H rfl

theorem valid'_singleton {α : Type u_1} [preorder α] {x : α} {o₁ : with_bot α} {o₂ : with_top α}
    (h₁ : bounded nil o₁ ↑x) (h₂ : bounded nil (↑x) o₂) : valid' o₁ (singleton x) o₂ :=
  valid'.node (valid'_nil h₁) (valid'_nil h₂) (Or.inl zero_le_one) rfl

theorem valid_singleton {α : Type u_1} [preorder α] {x : α} : valid (singleton x) :=
  valid'_singleton True.intro True.intro

theorem valid'.node3_l {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x)
    (hm : valid' (↑x) m ↑y) (hr : valid' (↑y) r o₂) (H1 : balanced_sz (size l) (size m))
    (H2 : balanced_sz (size l + size m + 1) (size r)) : valid' o₁ (node3_l l x m y r) o₂ :=
  valid'.node' (valid'.node' hl hm H1) hr H2

theorem valid'.node3_r {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x)
    (hm : valid' (↑x) m ↑y) (hr : valid' (↑y) r o₂)
    (H1 : balanced_sz (size l) (size m + size r + 1)) (H2 : balanced_sz (size m) (size r)) :
    valid' o₁ (node3_r l x m y r) o₂ :=
  valid'.node' hl (valid'.node' hm hr H2) H1

theorem valid'.node4_l_lemma₁ {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ}
    (lr₂ : bit1 1 * (b + c + 1 + d) ≤ bit0 (bit0 (bit0 (bit0 1))) * a + bit1 (bit0 (bit0 1)))
    (mr₂ : b + c + 1 ≤ bit1 1 * d) (mm₁ : b ≤ bit1 1 * c) : b < bit1 1 * a + 1 :=
  sorry

theorem valid'.node4_l_lemma₂ {b : ℕ} {c : ℕ} {d : ℕ} (mr₂ : b + c + 1 ≤ bit1 1 * d) :
    c ≤ bit1 1 * d :=
  sorry

theorem valid'.node4_l_lemma₃ {b : ℕ} {c : ℕ} {d : ℕ} (mr₁ : bit0 1 * d ≤ b + c + 1)
    (mm₁ : b ≤ bit1 1 * c) : d ≤ bit1 1 * c :=
  sorry

theorem valid'.node4_l_lemma₄ {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ} (lr₁ : bit1 1 * a ≤ b + c + 1 + d)
    (mr₂ : b + c + 1 ≤ bit1 1 * d) (mm₁ : b ≤ bit1 1 * c) : a + b + 1 ≤ bit1 1 * (c + d + 1) :=
  sorry

theorem valid'.node4_l_lemma₅ {a : ℕ} {b : ℕ} {c : ℕ} {d : ℕ}
    (lr₂ : bit1 1 * (b + c + 1 + d) ≤ bit0 (bit0 (bit0 (bit0 1))) * a + bit1 (bit0 (bit0 1)))
    (mr₁ : bit0 1 * d ≤ b + c + 1) (mm₂ : c ≤ bit1 1 * b) : c + d + 1 ≤ bit1 1 * (a + b + 1) :=
  sorry

theorem valid'.node4_l {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {m : ordnode α} {y : α}
    {r : ordnode α} {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x)
    (hm : valid' (↑x) m ↑y) (hr : valid' (↑y) r o₂) (Hm : 0 < size m)
    (H :
      size l = 0 ∧ size m = 1 ∧ size r ≤ 1 ∨
        0 < size l ∧
          ratio * size r ≤ size m ∧
            delta * size l ≤ size m + size r ∧
              bit1 1 * (size m + size r) ≤
                  bit0 (bit0 (bit0 (bit0 1))) * size l + bit1 (bit0 (bit0 1)) ∧
                size m ≤ delta * size r) :
    valid' o₁ (node4_l l x m y r) o₂ :=
  sorry

theorem valid'.rotate_l_lemma₁ {a : ℕ} {b : ℕ} {c : ℕ} (H2 : bit1 1 * a ≤ b + c)
    (hb₂ : c ≤ bit1 1 * b) : a ≤ bit1 1 * b :=
  sorry

theorem valid'.rotate_l_lemma₂ {a : ℕ} {b : ℕ} {c : ℕ}
    (H3 : bit0 1 * (b + c) ≤ bit1 (bit0 (bit0 1)) * a + bit1 1) (h : b < bit0 1 * c) :
    b < bit1 1 * a + 1 :=
  sorry

theorem valid'.rotate_l_lemma₃ {a : ℕ} {b : ℕ} {c : ℕ} (H2 : bit1 1 * a ≤ b + c)
    (h : b < bit0 1 * c) : a + b < bit1 1 * c :=
  sorry

theorem valid'.rotate_l_lemma₄ {a : ℕ} {b : ℕ}
    (H3 : bit0 1 * b ≤ bit1 (bit0 (bit0 1)) * a + bit1 1) :
    bit1 1 * b ≤ bit0 (bit0 (bit0 (bit0 1))) * a + bit1 (bit0 (bit0 1)) :=
  sorry

theorem valid'.rotate_l {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H1 : ¬size l + size r ≤ 1) (H2 : delta * size l < size r)
    (H3 : bit0 1 * size r ≤ bit1 (bit0 (bit0 1)) * size l + bit1 (bit0 1) ∨ size r ≤ bit1 1) :
    valid' o₁ (rotate_l l x r) o₂ :=
  sorry

theorem valid'.rotate_r {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H1 : ¬size l + size r ≤ 1) (H2 : delta * size r < size l)
    (H3 : bit0 1 * size l ≤ bit1 (bit0 (bit0 1)) * size r + bit1 (bit0 1) ∨ size l ≤ bit1 1) :
    valid' o₁ (rotate_r l x r) o₂ :=
  sorry

theorem valid'.balance'_aux {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H₁ : bit0 1 * size r ≤ bit1 (bit0 (bit0 1)) * size l + bit1 (bit0 1) ∨ size r ≤ bit1 1)
    (H₂ : bit0 1 * size l ≤ bit1 (bit0 (bit0 1)) * size r + bit1 (bit0 1) ∨ size l ≤ bit1 1) :
    valid' o₁ (balance' l x r) o₂ :=
  sorry

theorem valid'.balance'_lemma {α : Type u_1} {l : ordnode α} {l' : ℕ} {r : ordnode α} {r' : ℕ}
    (H1 : balanced_sz l' r')
    (H2 : nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ nat.dist (size r) r' ≤ 1 ∧ size l = l') :
    bit0 1 * size r ≤ bit1 (bit0 (bit0 1)) * size l + bit1 (bit0 1) ∨ size r ≤ bit1 1 :=
  sorry

theorem valid'.balance' {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H :
      ∃ (l' : ℕ),
        ∃ (r' : ℕ),
          balanced_sz l' r' ∧
            (nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    valid' o₁ (balance' l x r) o₂ :=
  sorry

theorem valid'.balance {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H :
      ∃ (l' : ℕ),
        ∃ (r' : ℕ),
          balanced_sz l' r' ∧
            (nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    valid' o₁ (balance l x r) o₂ :=
  sorry

theorem valid'.balance_l_aux {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H₁ : size l = 0 → size r ≤ 1) (H₂ : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l)
    (H₃ : bit0 1 * size l ≤ bit1 (bit0 (bit0 1)) * size r + bit1 (bit0 1) ∨ size l ≤ bit1 1) :
    valid' o₁ (balance_l l x r) o₂ :=
  sorry

theorem valid'.balance_l {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H :
      (∃ (l' : ℕ), raised l' (size l) ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised (size r) r' ∧ balanced_sz (size l) r') :
    valid' o₁ (balance_l l x r) o₂ :=
  sorry

theorem valid'.balance_r_aux {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H₁ : size r = 0 → size l ≤ 1) (H₂ : 1 ≤ size r → 1 ≤ size l → size l ≤ delta * size r)
    (H₃ : bit0 1 * size r ≤ bit1 (bit0 (bit0 1)) * size l + bit1 (bit0 1) ∨ size r ≤ bit1 1) :
    valid' o₁ (balance_r l x r) o₂ :=
  sorry

theorem valid'.balance_r {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂)
    (H :
      (∃ (l' : ℕ), raised (size l) l' ∧ balanced_sz l' (size r)) ∨
        ∃ (r' : ℕ), raised r' (size r) ∧ balanced_sz (size l) r') :
    valid' o₁ (balance_r l x r) o₂ :=
  eq.mpr (id (Eq._oldrec (Eq.refl (valid' o₁ (balance_r l x r) o₂)) (propext valid'.dual_iff)))
    (eq.mpr
      (id (Eq._oldrec (Eq.refl (valid' o₂ (dual (balance_r l x r)) o₁)) (dual_balance_r l x r)))
      (valid'.balance_l (valid'.dual hr) (valid'.dual hl) (balance_sz_dual H)))

theorem valid'.erase_max_aux {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α}
    {r : ordnode α} {o₁ : with_bot α} {o₂ : with_top α} (H : valid' o₁ (node s l x r) o₂) :
    valid' o₁ (erase_max (node' l x r)) ↑(find_max' x r) ∧
        size (node' l x r) = size (erase_max (node' l x r)) + 1 :=
  sorry

theorem valid'.erase_min_aux {α : Type u_1} [preorder α] {s : ℕ} {l : ordnode α} {x : α}
    {r : ordnode α} {o₁ : with_bot α} {o₂ : with_top α} (H : valid' o₁ (node s l x r) o₂) :
    valid' (↑(find_min' l x)) (erase_min (node' l x r)) o₂ ∧
        size (node' l x r) = size (erase_min (node' l x r)) + 1 :=
  sorry

theorem erase_min.valid {α : Type u_1} [preorder α] {t : ordnode α} (h : valid t) :
    valid (erase_min t) :=
  sorry

theorem erase_max.valid {α : Type u_1} [preorder α] {t : ordnode α} (h : valid t) :
    valid (erase_max t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (valid (erase_max t))) (propext valid.dual_iff)))
    (eq.mpr (id (Eq._oldrec (Eq.refl (valid (dual (erase_max t)))) (dual_erase_max t)))
      (erase_min.valid (valid.dual h)))

theorem valid'.glue_aux {α : Type u_1} [preorder α] {l : ordnode α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l o₂) (hr : valid' o₁ r o₂)
    (sep : all (fun (x : α) => all (fun (y : α) => x < y) r) l)
    (bal : balanced_sz (size l) (size r)) :
    valid' o₁ (glue l r) o₂ ∧ size (glue l r) = size l + size r :=
  sorry

theorem valid'.glue {α : Type u_1} [preorder α] {l : ordnode α} {x : α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l ↑x) (hr : valid' (↑x) r o₂) :
    balanced_sz (size l) (size r) → valid' o₁ (glue l r) o₂ ∧ size (glue l r) = size l + size r :=
  valid'.glue_aux (valid'.trans_right hl (valid'.ord hr)) (valid'.trans_left (valid'.ord hl) hr)
    (bounded.to_sep (valid'.ord hl) (valid'.ord hr))

theorem valid'.merge_lemma {a : ℕ} {b : ℕ} {c : ℕ} (h₁ : bit1 1 * a < b + c + 1)
    (h₂ : b ≤ bit1 1 * c) : bit0 1 * (a + b) ≤ bit1 (bit0 (bit0 1)) * c + bit1 (bit0 1) :=
  sorry

theorem valid'.merge_aux₁ {α : Type u_1} [preorder α] {o₁ : with_bot α} {o₂ : with_top α} {ls : ℕ}
    {ll : ordnode α} {lx : α} {lr : ordnode α} {rs : ℕ} {rl : ordnode α} {rx : α} {rr : ordnode α}
    {t : ordnode α} (hl : valid' o₁ (node ls ll lx lr) o₂) (hr : valid' o₁ (node rs rl rx rr) o₂)
    (h : delta * ls < rs) (v : valid' o₁ t ↑rx) (e : size t = ls + size rl) :
    valid' o₁ (balance_l t rx rr) o₂ ∧ size (balance_l t rx rr) = ls + rs :=
  sorry

theorem valid'.merge_aux {α : Type u_1} [preorder α] {l : ordnode α} {r : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} (hl : valid' o₁ l o₂) (hr : valid' o₁ r o₂)
    (sep : all (fun (x : α) => all (fun (y : α) => x < y) r) l) :
    valid' o₁ (merge l r) o₂ ∧ size (merge l r) = size l + size r :=
  sorry

theorem valid.merge {α : Type u_1} [preorder α] {l : ordnode α} {r : ordnode α} (hl : valid l)
    (hr : valid r) (sep : all (fun (x : α) => all (fun (y : α) => x < y) r) l) :
    valid (merge l r) :=
  and.left (valid'.merge_aux hl hr sep)

theorem insert_with.valid_aux {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq]
    (f : α → α) (x : α) (hf : ∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) {t : ordnode α}
    {o₁ : with_bot α} {o₂ : with_top α} :
    valid' o₁ t o₂ →
        bounded nil o₁ ↑x →
          bounded nil (↑x) o₂ →
            valid' o₁ (insert_with f x t) o₂ ∧ raised (size t) (size (insert_with f x t)) :=
  sorry

theorem insert_with.valid {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq]
    (f : α → α) (x : α) (hf : ∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) {t : ordnode α}
    (h : valid t) : valid (insert_with f x t) :=
  and.left (insert_with.valid_aux (fun (y : α) => f y) x hf h True.intro True.intro)

theorem insert_eq_insert_with {α : Type u_1} [preorder α] [DecidableRel LessEq] (x : α)
    (t : ordnode α) : ordnode.insert x t = insert_with (fun (_x : α) => x) x t :=
  sorry

theorem insert.valid {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq] (x : α)
    {t : ordnode α} (h : valid t) : valid (ordnode.insert x t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (valid (ordnode.insert x t))) (insert_eq_insert_with x t)))
    (insert_with.valid (fun (_x : α) => x) x
      (fun (_x : α) (_x : x ≤ _x ∧ _x ≤ x) => { left := le_refl x, right := le_refl x }) h)

theorem insert'_eq_insert_with {α : Type u_1} [preorder α] [DecidableRel LessEq] (x : α)
    (t : ordnode α) : insert' x t = insert_with id x t :=
  sorry

theorem insert'.valid {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq] (x : α)
    {t : ordnode α} (h : valid t) : valid (insert' x t) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (valid (insert' x t))) (insert'_eq_insert_with x t)))
    (insert_with.valid id x (fun (_x : α) => id) h)

end ordnode


/-- An `ordset α` is a finite set of values, represented as a tree. The operations on this type
maintain that the tree is balanced and correctly stores subtree sizes at each level. The
correctness property of the tree is baked into the type, so all operations on this type are correct
by construction. -/
def ordset (α : Type u_1) [preorder α] := Subtype fun (t : ordnode α) => ordnode.valid t

namespace ordset


/-- O(1). The empty set. -/
def nil {α : Type u_1} [preorder α] : ordset α := { val := ordnode.nil, property := sorry }

/-- O(1). Get the size of the set. -/
def size {α : Type u_1} [preorder α] (s : ordset α) : ℕ := ordnode.size (subtype.val s)

/-- O(1). Construct a singleton set containing value `a`. -/
protected def singleton {α : Type u_1} [preorder α] (a : α) : ordset α :=
  { val := singleton a, property := ordnode.valid_singleton }

protected instance has_emptyc {α : Type u_1} [preorder α] : has_emptyc (ordset α) :=
  has_emptyc.mk nil

protected instance inhabited {α : Type u_1} [preorder α] : Inhabited (ordset α) :=
  { default := nil }

protected instance has_singleton {α : Type u_1} [preorder α] : has_singleton α (ordset α) :=
  has_singleton.mk ordset.singleton

/-- O(1). Is the set empty? -/
def empty {α : Type u_1} [preorder α] (s : ordset α) := s = ∅

theorem empty_iff {α : Type u_1} [preorder α] {s : ordset α} :
    s = ∅ ↔ ↥(ordnode.empty (subtype.val s)) :=
  sorry

protected instance empty.decidable_pred {α : Type u_1} [preorder α] : decidable_pred empty :=
  fun (s : ordset α) => decidable_of_iff' (↥(ordnode.empty (subtype.val s))) empty_iff

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, this replaces it. -/
protected def insert {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq] (x : α)
    (s : ordset α) : ordset α :=
  { val := ordnode.insert x (subtype.val s), property := sorry }

protected instance has_insert {α : Type u_1} [preorder α] [is_total α LessEq]
    [DecidableRel LessEq] : has_insert α (ordset α) :=
  has_insert.mk ordset.insert

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
def insert' {α : Type u_1} [preorder α] [is_total α LessEq] [DecidableRel LessEq] (x : α)
    (s : ordset α) : ordset α :=
  { val := ordnode.insert' x (subtype.val s), property := sorry }

end Mathlib