/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.list.defs
import Mathlib.data.nat.psub
import PostPort

universes u l u_1 u_2 

namespace Mathlib

/-!
# Ordered sets

This file defines a data structure for ordered sets, supporting a
variety of useful operations including insertion and deletion,
logarithmic time lookup, set operations, folds,
and conversion from lists.

The `ordnode α` operations all assume that `α` has the structure of
a total preorder, meaning a `≤` operation that is

* Transitive: `x ≤ y → y ≤ z → x ≤ z`
* Reflexive: `x ≤ x`
* Total: `x ≤ y ∨ y ≤ x`

For example, in order to use this data structure as a map type, one
can store pairs `(k, v)` where `(k, v) ≤ (k', v')` is defined to mean
`k ≤ k'` (assuming that the key values are linearly ordered).

Two values `x,y` are equivalent if `x ≤ y` and `y ≤ x`. An `ordnode α`
maintains the invariant that it never stores two equivalent nodes;
the insertion operation comes with two variants depending on whether
you want to keep the old value or the new value in case you insert a value
that is equivalent to one in the set.

The operations in this file are not verified, in the sense that they provide
"raw operations" that work for programming purposes but the invariants
are not explicitly in the structure. See `ordset` for a verified version
of this data structure.

## Main definitions

* `ordnode α`: A set of values of type `α`

## Implementation notes

Based on weight balanced trees:

 * Stephen Adams, "Efficient sets: a balancing act",
   Journal of Functional Programming 3(4):553-562, October 1993,
   <http://www.swiss.ai.mit.edu/~adams/BB/>.
 * J. Nievergelt and E.M. Reingold,
   "Binary search trees of bounded balance",
   SIAM journal of computing 2(1), March 1973.

Ported from Haskell's `Data.Set`.

## Tags

ordered map, ordered set, data structure

-/

/-- An `ordnode α` is a finite set of values, represented as a tree.
  The operations on this type maintain that the tree is balanced
  and correctly stores subtree sizes at each level. -/
inductive ordnode (α : Type u) 
where
| nil : ordnode α
| node : ℕ → ordnode α → α → ordnode α → ordnode α

namespace ordnode


protected instance has_emptyc {α : Type u} : has_emptyc (ordnode α) :=
  has_emptyc.mk nil

protected instance inhabited {α : Type u} : Inhabited (ordnode α) :=
  { default := nil }

/-- **Internal use only**

The maximal relative difference between the sizes of
two trees, it corresponds with the `w` in Adams' paper.

According to the Haskell comment, only `(delta, ratio)` settings
of `(3, 2)` and `(4, 2)` will work, and the proofs in
`ordset.lean` assume `delta := 3` and `ratio := 2`. -/
def delta : ℕ :=
  bit1 1

/-- **Internal use only**

The ratio between an outer and inner sibling of the
heavier subtree in an unbalanced setting. It determines
whether a double or single rotation should be performed
to restore balance. It is corresponds with the inverse
of `α` in Adam's article. -/
def ratio : ℕ :=
  bit0 1

/-- O(1). Construct a singleton set containing value `a`.

     singleton 3 = {3} -/
protected def singleton {α : Type u} (a : α) : ordnode α :=
  node 1 nil a nil

protected instance has_singleton {α : Type u} : has_singleton α (ordnode α) :=
  has_singleton.mk ordnode.singleton

/-- O(1). Get the size of the set.

     size {2, 1, 1, 4} = 3  -/
@[simp] def size {α : Type u} : ordnode α → ℕ :=
  sorry

/-- O(1). Is the set empty?

     empty ∅ = tt
     empty {1, 2, 3} = ff -/
def empty {α : Type u} : ordnode α → Bool :=
  sorry

/-- **Internal use only**, because it violates the BST property on the original order.

O(n). The dual of a tree is a tree with its left and right sides reversed throughout.
The dual of a valid BST is valid under the dual order. This is convenient for exploiting
symmetries in the algorithms. -/
@[simp] def dual {α : Type u} : ordnode α → ordnode α :=
  sorry

/-- **Internal use only**

O(1). Construct a node with the correct size information, without rebalancing. -/
def node' {α : Type u} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α :=
  node (size l + size r + 1) l x r

/-- Basic pretty printing for `ordnode α` that shows the structure of the tree.

     repr {3, 1, 2, 4} = ((∅ 1 ∅) 2 ((∅ 3 ∅) 4 ∅)) -/
def repr {α : Type u_1} [has_repr α] : ordnode α → string :=
  sorry

protected instance has_repr {α : Type u_1} [has_repr α] : has_repr (ordnode α) :=
  has_repr.mk repr

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had its left
side grow by 1, or its right side shrink by 1. -/
-- Note: The function has been written with tactics to avoid extra junk

def balance_l {α : Type u} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α := sorry

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had its right
side grow by 1, or its left side shrink by 1. -/
def balance_r {α : Type u} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α := sorry

/-- **Internal use only**

O(1). Rebalance a tree which was previously balanced but has had one side change
by at most 1. -/
def balance {α : Type u} (l : ordnode α) (x : α) (r : ordnode α) : ordnode α := sorry

/-- O(n). Does every element of the map satisfy property `P`?

     all (λ x, x < 5) {1, 2, 3} = true
     all (λ x, x < 5) {1, 2, 3, 5} = false -/
def all {α : Type u} (P : α → Prop) : ordnode α → Prop :=
  sorry

protected instance all.decidable {α : Type u} {P : α → Prop} [decidable_pred P] (t : ordnode α) : Decidable (all P t) :=
  ordnode.rec (id decidable.true)
    (fun (t_size : ℕ) (t_l : ordnode α) (t_x : α) (t_r : ordnode α) (t_ih_l : Decidable (all P t_l))
      (t_ih_r : Decidable (all P t_r)) => id and.decidable)
    t

/-- O(n). Does any element of the map satisfy property `P`?

     any (λ x, x < 2) {1, 2, 3} = true
     any (λ x, x < 2) {2, 3, 5} = false -/
def any {α : Type u} (P : α → Prop) : ordnode α → Prop :=
  sorry

protected instance any.decidable {α : Type u} {P : α → Prop} [decidable_pred P] (t : ordnode α) : Decidable (any P t) :=
  ordnode.rec (id decidable.false)
    (fun (t_size : ℕ) (t_l : ordnode α) (t_x : α) (t_r : ordnode α) (t_ih_l : Decidable (any P t_l))
      (t_ih_r : Decidable (any P t_r)) => id or.decidable)
    t

/-- O(n). Exact membership in the set. This is useful primarily for stating
correctness properties; use `∈` for a version that actually uses the BST property
of the tree.

    emem 2 {1, 2, 3} = true
    emem 4 {1, 2, 3} = false -/
def emem {α : Type u} (x : α) : ordnode α → Prop :=
  any (Eq x)

protected instance emem.decidable {α : Type u} [DecidableEq α] (x : α) (t : ordnode α) : Decidable (emem x t) :=
  any.decidable

/-- O(n). Approximate membership in the set, that is, whether some element in the
set is equivalent to this one in the preorder. This is useful primarily for stating
correctness properties; use `∈` for a version that actually uses the BST property
of the tree.

    amem 2 {1, 2, 3} = true
    amem 4 {1, 2, 3} = false

To see the difference with `emem`, we need a preorder that is not a partial order.
For example, suppose we compare pairs of numbers using only their first coordinate. Then:

    emem (0, 1) {(0, 0), (1, 2)} = false
    amem (0, 1) {(0, 0), (1, 2)} = true
    (0, 1) ∈ {(0, 0), (1, 2)} = true

The `∈` relation is equivalent to `amem` as long as the `ordnode` is well formed,
and should always be used instead of `amem`. -/
def amem {α : Type u} [HasLessEq α] (x : α) : ordnode α → Prop :=
  any fun (y : α) => x ≤ y ∧ y ≤ x

protected instance amem.decidable {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) (t : ordnode α) : Decidable (amem x t) :=
  any.decidable

/-- O(log n). Return the minimum element of the tree, or the provided default value.

     find_min' 37 {1, 2, 3} = 1
     find_min' 37 ∅ = 37 -/
def find_min' {α : Type u} : ordnode α → α → α :=
  sorry

/-- O(log n). Return the minimum element of the tree, if it exists.

     find_min {1, 2, 3} = some 1
     find_min ∅ = none -/
def find_min {α : Type u} : ordnode α → Option α :=
  sorry

/-- O(log n). Return the maximum element of the tree, or the provided default value.

     find_max' 37 {1, 2, 3} = 3
     find_max' 37 ∅ = 37 -/
def find_max' {α : Type u} : α → ordnode α → α :=
  sorry

/-- O(log n). Return the maximum element of the tree, if it exists.

     find_max {1, 2, 3} = some 3
     find_max ∅ = none -/
def find_max {α : Type u} : ordnode α → Option α :=
  sorry

/-- O(log n). Remove the minimum element from the tree, or do nothing if it is already empty.

     erase_min {1, 2, 3} = {2, 3}
     erase_min ∅ = ∅ -/
def erase_min {α : Type u} : ordnode α → ordnode α :=
  sorry

/-- O(log n). Remove the maximum element from the tree, or do nothing if it is already empty.

     erase_max {1, 2, 3} = {1, 2}
     erase_max ∅ = ∅ -/
def erase_max {α : Type u} : ordnode α → ordnode α :=
  sorry

/-- **Internal use only**, because it requires a balancing constraint on the inputs.

O(log n). Extract and remove the minimum element from a nonempty tree. -/
def split_min' {α : Type u} : ordnode α → α → ordnode α → α × ordnode α :=
  sorry

/-- O(log n). Extract and remove the minimum element from the tree, if it exists.

     split_min {1, 2, 3} = some (1, {2, 3})
     split_min ∅ = none -/
def split_min {α : Type u} : ordnode α → Option (α × ordnode α) :=
  sorry

/-- **Internal use only**, because it requires a balancing constraint on the inputs.

O(log n). Extract and remove the maximum element from a nonempty tree. -/
def split_max' {α : Type u} : ordnode α → α → ordnode α → ordnode α × α :=
  sorry

/-- O(log n). Extract and remove the maximum element from the tree, if it exists.

     split_max {1, 2, 3} = some ({1, 2}, 3)
     split_max ∅ = none -/
def split_max {α : Type u} : ordnode α → Option (ordnode α × α) :=
  sorry

/-- **Internal use only**

O(log(m+n)). Concatenate two trees that are balanced and ordered with respect to each other. -/
def glue {α : Type u} : ordnode α → ordnode α → ordnode α :=
  sorry

/-- O(log(m+n)). Concatenate two trees that are ordered with respect to each other.

     merge {1, 2} {3, 4} = {1, 2, 3, 4}
     merge {3, 4} {1, 2} = precondition violation -/
def merge {α : Type u} (l : ordnode α) : ordnode α → ordnode α :=
  ordnode.rec_on l (fun (r : ordnode α) => r)
    fun (ls : ℕ) (ll : ordnode α) (lx : α) (lr : ordnode α) (IHll IHlr : ordnode α → ordnode α) (r : ordnode α) =>
      ordnode.rec_on r (node ls ll lx lr)
        fun (rs : ℕ) (rl : ordnode α) (rx : α) (rr IHrl IHrr : ordnode α) =>
          ite (delta * ls < rs) (balance_l IHrl rx rr)
            (ite (delta * rs < ls) (balance_r ll lx (IHlr (node rs rl rx rr)))
              (glue (node ls ll lx lr) (node rs rl rx rr)))

/-- O(log n). Insert an element above all the others, without any comparisons.
(Assumes that the element is in fact above all the others).

    insert_max {1, 2} 4 = {1, 2, 4}
    insert_max {1, 2} 0 = precondition violation -/
def insert_max {α : Type u} : ordnode α → α → ordnode α :=
  sorry

/-- O(log n). Insert an element below all the others, without any comparisons.
(Assumes that the element is in fact below all the others).

    insert_min {1, 2} 0 = {0, 1, 2}
    insert_min {1, 2} 4 = precondition violation -/
def insert_min {α : Type u} (x : α) : ordnode α → ordnode α :=
  sorry

/-- O(log(m+n)). Build a tree from an element between two trees, without any
assumption on the relative sizes.

    link {1, 2} 4 {5, 6} = {1, 2, 4, 5, 6}
    link {1, 3} 2 {5} = precondition violation -/
def link {α : Type u} (l : ordnode α) (x : α) : ordnode α → ordnode α :=
  ordnode.rec_on l (insert_min x)
    fun (ls : ℕ) (ll : ordnode α) (lx : α) (lr : ordnode α) (IHll IHlr : ordnode α → ordnode α) (r : ordnode α) =>
      ordnode.rec_on r (insert_max l x)
        fun (rs : ℕ) (rl : ordnode α) (rx : α) (rr IHrl IHrr : ordnode α) =>
          ite (delta * ls < rs) (balance_l IHrl rx rr) (ite (delta * rs < ls) (balance_r ll lx (IHlr r)) (node' l x r))

/-- O(n). Filter the elements of a tree satisfying a predicate.

     filter (λ x, x < 3) {1, 2, 4} = {1, 2}
     filter (λ x, x > 5) {1, 2, 4} = ∅ -/
def filter {α : Type u} (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α :=
  sorry

/-- O(n). Split the elements of a tree into those satisfying, and not satisfying, a predicate.

     partition (λ x, x < 3) {1, 2, 4} = ({1, 2}, {3}) -/
def partition {α : Type u} (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α × ordnode α :=
  sorry

/-- O(n). Map a function across a tree, without changing the structure. Only valid when
the function is strictly monotonic, i.e. `x < y → f x < f y`.

     partition (λ x, x + 2) {1, 2, 4} = {2, 3, 6}
     partition (λ x : ℕ, x - 2) {1, 2, 4} = precondition violation -/
def map {α : Type u} {β : Type u_1} (f : α → β) : ordnode α → ordnode β :=
  sorry

/-- O(n). Fold a function across the structure of a tree.

     fold z f {1, 2, 4} = f (f z 1 z) 2 (f z 4 z)

The exact structure of function applications depends on the tree and so
is unspecified. -/
def fold {α : Type u} {β : Sort u_1} (z : β) (f : β → α → β → β) : ordnode α → β :=
  sorry

/-- O(n). Fold a function from left to right (in increasing order) across the tree.

     foldl f z {1, 2, 4} = f (f (f z 1) 2) 4 -/
def foldl {α : Type u} {β : Sort u_1} (f : β → α → β) : β → ordnode α → β :=
  sorry

/-- O(n). Fold a function from right to left (in decreasing order) across the tree.

     foldl f {1, 2, 4} z = f 1 (f 2 (f 4 z)) -/
def foldr {α : Type u} {β : Sort u_1} (f : α → β → β) : ordnode α → β → β :=
  sorry

/-- O(n). Build a list of elements in ascending order from the tree.

     to_list {1, 2, 4} = [1, 2, 4]
     to_list {2, 1, 1, 4} = [1, 2, 4] -/
def to_list {α : Type u} (t : ordnode α) : List α :=
  foldr List.cons t []

/-- O(n). Build a list of elements in descending order from the tree.

     to_rev_list {1, 2, 4} = [4, 2, 1]
     to_rev_list {2, 1, 1, 4} = [4, 2, 1] -/
def to_rev_list {α : Type u} (t : ordnode α) : List α :=
  foldl (flip List.cons) [] t

protected instance has_to_string {α : Type u} [has_to_string α] : has_to_string (ordnode α) :=
  has_to_string.mk
    fun (t : ordnode α) =>
      string.str string.empty (char.of_nat (bit1 (bit1 (bit0 (bit1 (bit1 (bit1 1))))))) ++
          string.intercalate
            (string.str (string.str string.empty (char.of_nat (bit0 (bit0 (bit1 (bit1 (bit0 1)))))))
              (char.of_nat (bit0 (bit0 (bit0 (bit0 (bit0 1)))))))
            (list.map to_string (to_list t)) ++
        string.str string.empty (char.of_nat (bit1 (bit0 (bit1 (bit1 (bit1 (bit1 1)))))))

/-- O(n). True if the trees have the same elements, ignoring structural differences.

     equiv {1, 2, 4} {2, 1, 1, 4} = true
     equiv {1, 2, 4} {1, 2, 3} = false -/
def equiv {α : Type u} (t₁ : ordnode α) (t₂ : ordnode α)  :=
  size t₁ = size t₂ ∧ to_list t₁ = to_list t₂

protected instance equiv.decidable_rel {α : Type u} [DecidableEq α] : DecidableRel equiv :=
  fun (t₁ t₂ : ordnode α) => and.decidable

/-- O(2^n). Constructs the powerset of a given set, that is, the set of all subsets.

     powerset {1, 2, 3} = {∅, {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}} -/
def powerset {α : Type u} (t : ordnode α) : ordnode (ordnode α) :=
  insert_min nil
    (foldr (fun (x : α) (ts : ordnode (ordnode α)) => glue (insert_min (ordnode.singleton x) (map (insert_min x) ts)) ts)
      t nil)

/-- O(m*n). The cartesian product of two sets: `(a, b) ∈ s.prod t` iff `a ∈ s` and `b ∈ t`.

     prod {1, 2} {2, 3} = {(1, 2), (1, 3), (2, 2), (2, 3)} -/
protected def prod {α : Type u} {β : Type u_1} (t₁ : ordnode α) (t₂ : ordnode β) : ordnode (α × β) :=
  fold nil (fun (s₁ : ordnode (α × β)) (a : α) (s₂ : ordnode (α × β)) => merge s₁ (merge (map (Prod.mk a) t₂) s₂)) t₁

/-- O(m+n). Build a set on the disjoint union by combining sets on the factors.
`inl a ∈ s.copair t` iff `a ∈ s`, and `inr b ∈ s.copair t` iff `b ∈ t`.

    copair {1, 2} {2, 3} = {inl 1, inl 2, inr 2, inr 3} -/
protected def copair {α : Type u} {β : Type u_1} (t₁ : ordnode α) (t₂ : ordnode β) : ordnode (α ⊕ β) :=
  merge (map sum.inl t₁) (map sum.inr t₂)

/-- O(n). Map a partial function across a set. The result depends on a proof
that the function is defined on all members of the set.

    pmap (fin.mk : ∀ n, n < 4 → fin 4) {1, 2} H = {(1 : fin 4), (2 : fin 4)} -/
def pmap {α : Type u} {P : α → Prop} {β : Type u_1} (f : (a : α) → P a → β) (t : ordnode α) : all P t → ordnode β :=
  sorry

/-- O(n). "Attach" the information that every element of `t` satisfies property
P to these elements inside the set, producing a set in the subtype.

    attach' (λ x, x < 4) {1, 2} H = ({1, 2} : ordnode {x // x<4}) -/
def attach' {α : Type u} {P : α → Prop} (t : ordnode α) : all P t → ordnode (Subtype fun (a : α) => P a) :=
  pmap Subtype.mk

/-- O(log n). Get the `i`th element of the set, by its index from left to right.

     nth {a, b, c, d} 2 = some c
     nth {a, b, c, d} 5 = none -/
def nth {α : Type u} : ordnode α → ℕ → Option α :=
  sorry

/-- O(log n). Remove the `i`th element of the set, by its index from left to right.

     remove_nth {a, b, c, d} 2 = {a, b, d}
     remove_nth {a, b, c, d} 5 = {a, b, c, d} -/
def remove_nth {α : Type u} : ordnode α → ℕ → ordnode α :=
  sorry

/-- Auxiliary definition for `take`. (Can also be used in lieu of `take` if you know the
index is within the range of the data structure.)

    take_aux {a, b, c, d} 2 = {a, b}
    take_aux {a, b, c, d} 5 = {a, b, c, d} -/
def take_aux {α : Type u} : ordnode α → ℕ → ordnode α :=
  sorry

/-- O(log n). Get the first `i` elements of the set, counted from the left.

     take 2 {a, b, c, d} = {a, b}
     take 5 {a, b, c, d} = {a, b, c, d} -/
def take {α : Type u} (i : ℕ) (t : ordnode α) : ordnode α :=
  ite (size t ≤ i) t (take_aux t i)

/-- Auxiliary definition for `drop`. (Can also be used in lieu of `drop` if you know the
index is within the range of the data structure.)

    drop_aux {a, b, c, d} 2 = {c, d}
    drop_aux {a, b, c, d} 5 = ∅ -/
def drop_aux {α : Type u} : ordnode α → ℕ → ordnode α :=
  sorry

/-- O(log n). Remove the first `i` elements of the set, counted from the left.

     drop 2 {a, b, c, d} = {c, d}
     drop 5 {a, b, c, d} = ∅ -/
def drop {α : Type u} (i : ℕ) (t : ordnode α) : ordnode α :=
  ite (size t ≤ i) nil (drop_aux t i)

/-- Auxiliary definition for `split_at`. (Can also be used in lieu of `split_at` if you know the
index is within the range of the data structure.)

    split_at_aux {a, b, c, d} 2 = ({a, b}, {c, d})
    split_at_aux {a, b, c, d} 5 = ({a, b, c, d}, ∅) -/
def split_at_aux {α : Type u} : ordnode α → ℕ → ordnode α × ordnode α :=
  sorry

/-- O(log n). Split a set at the `i`th element, getting the first `i` and everything else.

     split_at 2 {a, b, c, d} = ({a, b}, {c, d})
     split_at 5 {a, b, c, d} = ({a, b, c, d}, ∅) -/
def split_at {α : Type u} (i : ℕ) (t : ordnode α) : ordnode α × ordnode α :=
  ite (size t ≤ i) (t, nil) (split_at_aux t i)

/-- O(log n). Get an initial segment of the set that satisfies the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    take_while (λ x, x < 4) {1, 2, 3, 4, 5} = {1, 2, 3}
    take_while (λ x, x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def take_while {α : Type u} (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α :=
  sorry

/-- O(log n). Remove an initial segment of the set that satisfies the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    drop_while (λ x, x < 4) {1, 2, 3, 4, 5} = {4, 5}
    drop_while (λ x, x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def drop_while {α : Type u} (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α :=
  sorry

/-- O(log n). Split the set into those satisfying and not satisfying the predicate `p`.
`p` is required to be antitone, that is, `x < y → p y → p x`.

    span (λ x, x < 4) {1, 2, 3, 4, 5} = ({1, 2, 3}, {4, 5})
    span (λ x, x > 4) {1, 2, 3, 4, 5} = precondition violation -/
def span {α : Type u} (p : α → Prop) [decidable_pred p] : ordnode α → ordnode α × ordnode α :=
  sorry

/-- Auxiliary definition for `of_asc_list`.

**Note:** This function is defined by well founded recursion, so it will probably not compute
in the kernel, meaning that you probably can't prove things like
`of_asc_list [1, 2, 3] = {1, 2, 3}` by `rfl`.
This implementation is optimized for VM evaluation. -/
def of_asc_list_aux₁ {α : Type u} (l : List α) : ℕ → ordnode α × Subtype fun (l' : List α) => list.length l' ≤ list.length l :=
  sorry

/-- Auxiliary definition for `of_asc_list`. -/
def of_asc_list_aux₂ {α : Type u} : List α → ordnode α → ℕ → ordnode α :=
  sorry

/-- O(n). Build a set from a list which is already sorted. Performs no comparisons.

     of_asc_list [1, 2, 3] = {1, 2, 3}
     of_asc_list [3, 2, 1] = precondition violation -/
def of_asc_list {α : Type u} : List α → ordnode α :=
  sorry

/-- O(log n). Does the set (approximately) contain the element `x`? That is,
is there an element that is equivalent to `x` in the order?

    1 ∈ {1, 2, 3} = true
    4 ∈ {1, 2, 3} = false

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    (1, 1) ∈ {(0, 1), (1, 2)} = true
    (3, 1) ∈ {(0, 1), (1, 2)} = false -/
def mem {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → Bool :=
  sorry

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
if it exists.

    find 1 {1, 2, 3} = some 1
    find 4 {1, 2, 3} = none

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    find (1, 1) {(0, 1), (1, 2)} = some (1, 2)
    find (3, 1) {(0, 1), (1, 2)} = none -/
def find {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → Option α :=
  sorry

protected instance has_mem {α : Type u} [HasLessEq α] [DecidableRel LessEq] : has_mem α (ordnode α) :=
  has_mem.mk fun (x : α) (t : ordnode α) => ↥(mem x t)

protected instance mem.decidable {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) (t : ordnode α) : Decidable (x ∈ t) :=
  bool.decidable_eq (mem x t) tt

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, the function `f` is used to generate
the element to insert (being passed the current value in the set).

    insert_with f 0 {1, 2, 3} = {0, 1, 2, 3}
    insert_with f 1 {1, 2, 3} = {f 1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert_with f (1, 1) {(0, 1), (1, 2)} = {(0, 1), f (1, 2)}
    insert_with f (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
def insert_with {α : Type u} [HasLessEq α] [DecidableRel LessEq] (f : α → α) (x : α) : ordnode α → ordnode α :=
  sorry

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    adjust_with f 0 {1, 2, 3} = {1, 2, 3}
    adjust_with f 1 {1, 2, 3} = {f 1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    adjust_with f (1, 1) {(0, 1), (1, 2)} = {(0, 1), f (1, 2)}
    adjust_with f (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)} -/
def adjust_with {α : Type u} [HasLessEq α] [DecidableRel LessEq] (f : α → α) (x : α) : ordnode α → ordnode α :=
  sorry

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    update_with f 0 {1, 2, 3} = {1, 2, 3}
    update_with f 1 {1, 2, 3} = {2, 3}     if f 1 = none
                              = {a, 2, 3}  if f 1 = some a -/
def update_with {α : Type u} [HasLessEq α] [DecidableRel LessEq] (f : α → Option α) (x : α) : ordnode α → ordnode α :=
  sorry

/-- O(log n). Modify an element in the set with the given function,
doing nothing if the key is not found.
Note that the element returned by `f` must be equivalent to `x`.

    alter f 0 {1, 2, 3} = {1, 2, 3}     if f none = none
                        = {a, 1, 2, 3}  if f none = some a
    alter f 1 {1, 2, 3} = {2, 3}     if f 1 = none
                        = {a, 2, 3}  if f 1 = some a -/
def alter {α : Type u} [HasLessEq α] [DecidableRel LessEq] (f : Option α → Option α) (x : α) : ordnode α → ordnode α :=
  sorry

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, this replaces it.

    insert 1 {1, 2, 3} = {1, 2, 3}
    insert 4 {1, 2, 3} = {1, 2, 3, 4}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert (1, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 1)}
    insert (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
protected def insert {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → ordnode α :=
  sorry

protected instance has_insert {α : Type u} [HasLessEq α] [DecidableRel LessEq] : has_insert α (ordnode α) :=
  has_insert.mk ordnode.insert

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
If an equivalent element is already in the set, the set is returned as is.

    insert' 1 {1, 2, 3} = {1, 2, 3}
    insert' 4 {1, 2, 3} = {1, 2, 3, 4}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    insert' (1, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)}
    insert' (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2), (3, 1)} -/
def insert' {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → ordnode α :=
  sorry

/-- O(log n). Split the tree into those smaller than `x` and those greater than it.
If an element equivalent to `x` is in the set, it is discarded.

    split 2 {1, 2, 4} = ({1}, {4})
    split 3 {1, 2, 4} = ({1, 2}, {4})
    split 4 {1, 2, 4} = ({1, 2}, ∅)

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    split (1, 1) {(0, 1), (1, 2)} = ({(0, 1)}, ∅)
    split (3, 1) {(0, 1), (1, 2)} = ({(0, 1), (1, 2)}, ∅) -/
def split {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → ordnode α × ordnode α :=
  sorry

/-- O(log n). Split the tree into those smaller than `x` and those greater than it,
plus an element equivalent to `x`, if it exists.

    split 2 {1, 2, 4} = ({1}, some 2, {4})
    split 3 {1, 2, 4} = ({1, 2}, none, {4})
    split 4 {1, 2, 4} = ({1, 2}, some 4, ∅)

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    split (1, 1) {(0, 1), (1, 2)} = ({(0, 1)}, some (1, 2), ∅)
    split (3, 1) {(0, 1), (1, 2)} = ({(0, 1), (1, 2)}, none, ∅) -/
def split3 {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → ordnode α × Option α × ordnode α :=
  sorry

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element.

    erase 1 {1, 2, 3} = {2, 3}
    erase 4 {1, 2, 3} = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    erase (1, 1) {(0, 1), (1, 2)} = {(0, 1)}
    erase (3, 1) {(0, 1), (1, 2)} = {(0, 1), (1, 2)} -/
def erase {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → ordnode α :=
  sorry

/-- Auxiliary definition for `find_lt`. -/
def find_lt_aux {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → α → α :=
  sorry

/-- O(log n). Get the largest element in the tree that is `< x`.

     find_lt 2 {1, 2, 4} = some 1
     find_lt 3 {1, 2, 4} = some 2
     find_lt 0 {1, 2, 4} = none -/
def find_lt {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → Option α :=
  sorry

/-- Auxiliary definition for `find_gt`. -/
def find_gt_aux {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → α → α :=
  sorry

/-- O(log n). Get the smallest element in the tree that is `> x`.

     find_lt 2 {1, 2, 4} = some 4
     find_lt 3 {1, 2, 4} = some 4
     find_lt 4 {1, 2, 4} = none -/
def find_gt {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → Option α :=
  sorry

/-- Auxiliary definition for `find_le`. -/
def find_le_aux {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → α → α :=
  sorry

/-- O(log n). Get the largest element in the tree that is `≤ x`.

     find_le 2 {1, 2, 4} = some 2
     find_le 3 {1, 2, 4} = some 2
     find_le 0 {1, 2, 4} = none -/
def find_le {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → Option α :=
  sorry

/-- Auxiliary definition for `find_ge`. -/
def find_ge_aux {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → α → α :=
  sorry

/-- O(log n). Get the smallest element in the tree that is `≥ x`.

     find_le 2 {1, 2, 4} = some 2
     find_le 3 {1, 2, 4} = some 4
     find_le 5 {1, 2, 4} = none -/
def find_ge {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → Option α :=
  sorry

/-- Auxiliary definition for `find_index`. -/
def find_index_aux {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) : ordnode α → ℕ → Option ℕ :=
  sorry

/-- O(log n). Get the index, counting from the left,
of an element equivalent to `x` if it exists.

    find_index 2 {1, 2, 4} = some 1
    find_index 4 {1, 2, 4} = some 2
    find_index 5 {1, 2, 4} = none -/
def find_index {α : Type u} [HasLessEq α] [DecidableRel LessEq] (x : α) (t : ordnode α) : Option ℕ :=
  find_index_aux x t 0

/-- Auxiliary definition for `is_subset`. -/
def is_subset_aux {α : Type u} [HasLessEq α] [DecidableRel LessEq] : ordnode α → ordnode α → Bool :=
  sorry

/-- O(m+n). Is every element of `t₁` equivalent to some element of `t₂`?

     is_subset {1, 4} {1, 2, 4} = tt
     is_subset {1, 3} {1, 2, 4} = ff -/
def is_subset {α : Type u} [HasLessEq α] [DecidableRel LessEq] (t₁ : ordnode α) (t₂ : ordnode α) : Bool :=
  to_bool (size t₁ ≤ size t₂) && is_subset_aux t₁ t₂

/-- O(m+n). Is every element of `t₁` not equivalent to any element of `t₂`?

     disjoint {1, 3} {2, 4} = tt
     disjoint {1, 2} {2, 4} = ff -/
def disjoint {α : Type u} [HasLessEq α] [DecidableRel LessEq] : ordnode α → ordnode α → Bool :=
  sorry

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. The union of two sets, preferring members of
  `t₁` over those of `t₂` when equivalent elements are encountered.

    union {1, 2} {2, 3} = {1, 2, 3}
    union {1, 3} {2} = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    union {(1, 1)} {(0, 1), (1, 2)} = {(0, 1), (1, 1)} -/
def union {α : Type u} [HasLessEq α] [DecidableRel LessEq] : ordnode α → ordnode α → ordnode α :=
  sorry

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. Difference of two sets.

    diff {1, 2} {2, 3} = {1}
    diff {1, 2, 3} {2} = {1, 3} -/
def diff {α : Type u} [HasLessEq α] [DecidableRel LessEq] : ordnode α → ordnode α → ordnode α :=
  sorry

/-- O(m * log(|m ∪ n| + 1)), m ≤ n. Intersection of two sets, preferring members of
`t₁` over those of `t₂` when equivalent elements are encountered.

    inter {1, 2} {2, 3} = {2}
    inter {1, 3} {2} = ∅ -/
def inter {α : Type u} [HasLessEq α] [DecidableRel LessEq] : ordnode α → ordnode α → ordnode α :=
  sorry

/-- O(n * log n). Build a set from a list, preferring elements that appear earlier in the list
in the case of equivalent elements.

    of_list [1, 2, 3] = {1, 2, 3}
    of_list [2, 1, 1, 3] = {1, 2, 3}

Using a preorder on `ℕ × ℕ` that only compares the first coordinate:

    of_list [(1, 1), (0, 1), (1, 2)] = {(0, 1), (1, 1)} -/
def of_list {α : Type u} [HasLessEq α] [DecidableRel LessEq] (l : List α) : ordnode α :=
  list.foldr insert nil l

/-- O(n * log n). Adaptively chooses between the linear and log-linear algorithm depending
  on whether the input list is already sorted.

    of_list' [1, 2, 3] = {1, 2, 3}
    of_list' [2, 1, 1, 3] = {1, 2, 3} -/
def of_list' {α : Type u} [HasLessEq α] [DecidableRel LessEq] : List α → ordnode α :=
  sorry

/-- O(n * log n). Map a function on a set. Unlike `map` this has no requirements on
`f`, and the resulting set may be smaller than the input if `f` is noninjective.
Equivalent elements are selected with a preference for smaller source elements.

    image (λ x, x + 2) {1, 2, 4} = {3, 4, 6}
    image (λ x : ℕ, x - 2) {1, 2, 4} = {0, 2} -/
def image {α : Type u_1} {β : Type u_2} [HasLessEq β] [DecidableRel LessEq] (f : α → β) (t : ordnode α) : ordnode β :=
  of_list (list.map f (to_list t))

