/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.data.option.defs
import Mathlib.logic.basic
import Mathlib.tactic.cache
import Mathlib.PostPort

universes u_1 u v w u_2 

namespace Mathlib

/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `data/list`
-/

namespace list


/-- Returns whether a list is []. Returns a boolean even if `l = []` is not decidable. -/
def is_nil {α : Type u_1} : List α → Bool :=
  sorry

protected instance has_sdiff {α : Type u} [DecidableEq α] : has_sdiff (List α) :=
  has_sdiff.mk list.diff

/-- Split a list at an index.

     split_at 2 [a, b, c] = ([a, b], [c]) -/
def split_at {α : Type u} : ℕ → List α → List α × List α :=
  sorry

/-- An auxiliary function for `split_on_p`. -/
def split_on_p_aux {α : Type u} (P : α → Prop) [decidable_pred P] : List α → (List α → List α) → List (List α) :=
  sorry

/-- Split a list at every element satisfying a predicate. -/
def split_on_p {α : Type u} (P : α → Prop) [decidable_pred P] (l : List α) : List (List α) :=
  split_on_p_aux P l id

/-- Split a list at every occurrence of an element.

    [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] -/
def split_on {α : Type u} [DecidableEq α] (a : α) (as : List α) : List (List α) :=
  split_on_p (fun (_x : α) => _x = a) as

/-- Concatenate an element at the end of a list.

     concat [a, b] c = [a, b, c] -/
@[simp] def concat {α : Type u} : List α → α → List α :=
  sorry

/-- `head' xs` returns the first element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp] def head' {α : Type u} : List α → Option α :=
  sorry

/-- Convert a list into an array (whose length is the length of `l`). -/
def to_array {α : Type u} (l : List α) : array (length l) α :=
  d_array.mk fun (v : fin (length l)) => nth_le l (subtype.val v) sorry

/-- "inhabited" `nth` function: returns `default` instead of `none` in the case
  that the index is out of bounds. -/
@[simp] def inth {α : Type u} [h : Inhabited α] (l : List α) (n : ℕ) : α :=
  option.iget (nth l n)

/-- Apply a function to the nth tail of `l`. Returns the input without
  using `f` if the index is larger than the length of the list.

     modify_nth_tail f 2 [a, b, c] = [a, b] ++ f [c] -/
@[simp] def modify_nth_tail {α : Type u} (f : List α → List α) : ℕ → List α → List α :=
  sorry

/-- Apply `f` to the head of the list, if it exists. -/
@[simp] def modify_head {α : Type u} (f : α → α) : List α → List α :=
  sorry

/-- Apply `f` to the nth element of the list, if it exists. -/
def modify_nth {α : Type u} (f : α → α) : ℕ → List α → List α :=
  modify_nth_tail (modify_head f)

/-- Apply `f` to the last element of `l`, if it exists. -/
@[simp] def modify_last {α : Type u} (f : α → α) : List α → List α :=
  sorry

/-- `insert_nth n a l` inserts `a` into the list `l` after the first `n` elements of `l`
 `insert_nth 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]`-/
def insert_nth {α : Type u} (n : ℕ) (a : α) : List α → List α :=
  modify_nth_tail (List.cons a) n

/-- Take `n` elements from a list `l`. If `l` has less than `n` elements, append `n - length l`
elements `default α`. -/
def take' {α : Type u} [Inhabited α] (n : ℕ) : List α → List α :=
  sorry

/-- Get the longest initial segment of the list whose members all satisfy `p`.

     take_while (λ x, x < 3) [0, 2, 5, 1] = [0, 2] -/
def take_while {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α :=
  sorry

/-- Fold a function `f` over the list from the left, returning the list
  of partial results.

     scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6] -/
def scanl {α : Type u} {β : Type v} (f : α → β → α) : α → List β → List α :=
  sorry

/-- Auxiliary definition used to define `scanr`. If `scanr_aux f b l = (b', l')`
then `scanr f b l = b' :: l'` -/
def scanr_aux {α : Type u} {β : Type v} (f : α → β → β) (b : β) : List α → β × List β :=
  sorry

/-- Fold a function `f` over the list from the right, returning the list
  of partial results.

     scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0] -/
def scanr {α : Type u} {β : Type v} (f : α → β → β) (b : β) (l : List α) : List β :=
  sorry

/-- Product of a list.

     prod [a, b, c] = ((1 * a) * b) * c -/
def prod {α : Type u} [Mul α] [HasOne α] : List α → α :=
  foldl Mul.mul 1

/-- Sum of a list.

     sum [a, b, c] = ((0 + a) + b) + c -/
-- Later this will be tagged with `to_additive`, but this can't be done yet because of import

-- dependencies.

def sum {α : Type u} [Add α] [HasZero α] : List α → α :=
  foldl Add.add 0

/-- The alternating sum of a list. -/
def alternating_sum {G : Type u_1} [HasZero G] [Add G] [Neg G] : List G → G :=
  sorry

/-- The alternating product of a list. -/
def alternating_prod {G : Type u_1} [HasOne G] [Mul G] [has_inv G] : List G → G :=
  sorry

/-- Given a function `f : α → β ⊕ γ`, `partition_map f l` maps the list by `f`
  whilst partitioning the result it into a pair of lists, `list β × list γ`,
  partitioning the `sum.inl _` into the left list, and the `sum.inr _` into the right list.
  `partition_map (id : ℕ ⊕ ℕ → ℕ ⊕ ℕ) [inl 0, inr 1, inl 2] = ([0,2], [1])`    -/
def partition_map {α : Type u} {β : Type v} {γ : Type w} (f : α → β ⊕ γ) : List α → List β × List γ :=
  sorry

/-- `find p l` is the first element of `l` satisfying `p`, or `none` if no such
  element exists. -/
def find {α : Type u} (p : α → Prop) [decidable_pred p] : List α → Option α :=
  sorry

/-- `mfind tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise. -/
def mfind {α : Type u} {m : Type u → Type v} [Monad m] [alternative m] (tac : α → m PUnit) : List α → m α :=
  mfirst fun (a : α) => tac a $> a

/-- `mbfind' p l` returns the first element `a` of `l` for which `p a` returns
true. `mbfind'` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `list.find`. -/
def mbfind' {m : Type u → Type v} [Monad m] {α : Type u} (p : α → m (ulift Bool)) : List α → m (Option α) :=
  sorry

/-- A variant of `mbfind'` with more restrictive universe levels. -/
def mbfind {m : Type → Type v} [Monad m] {α : Type} (p : α → m Bool) (xs : List α) : m (Option α) :=
  mbfind' (Functor.map ulift.up ∘ p) xs

/-- `many p as` returns true iff `p` returns true for any element of `l`.
`many` short-circuits, so if `p` returns true for any element of `l`, later
elements are not checked. This is a monadic version of `list.any`. -/
-- Implementing this via `mbfind` would give us less universe polymorphism.

def many {m : Type → Type v} [Monad m] {α : Type u} (p : α → m Bool) : List α → m Bool :=
  sorry

/-- `mall p as` returns true iff `p` returns true for all elements of `l`.
`mall` short-circuits, so if `p` returns false for any element of `l`, later
elements are not checked. This is a monadic version of `list.all`. -/
def mall {m : Type → Type v} [Monad m] {α : Type u} (p : α → m Bool) (as : List α) : m Bool :=
  bnot <$> many (fun (a : α) => bnot <$> p a) as

/-- `mbor xs` runs the actions in `xs`, returning true if any of them returns
true. `mbor` short-circuits, so if an action returns true, later actions are
not run. This is a monadic version of `list.bor`. -/
def mbor {m : Type → Type v} [Monad m] : List (m Bool) → m Bool :=
  many id

/-- `mband xs` runs the actions in `xs`, returning true if all of them return
true. `mband` short-circuits, so if an action returns false, later actions are
not run. This is a monadic version of `list.band`. -/
def mband {m : Type → Type v} [Monad m] : List (m Bool) → m Bool :=
  mall id

/-- Auxiliary definition for `foldl_with_index`. -/
def foldl_with_index_aux {α : Type u} {β : Type v} (f : ℕ → α → β → α) : ℕ → α → List β → α :=
  sorry

/-- Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index. -/
def foldl_with_index {α : Type u} {β : Type v} (f : ℕ → α → β → α) (a : α) (l : List β) : α :=
  foldl_with_index_aux f 0 a l

/-- Auxiliary definition for `foldr_with_index`. -/
def foldr_with_index_aux {α : Type u} {β : Type v} (f : ℕ → α → β → β) : ℕ → β → List α → β :=
  sorry

/-- Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index. -/
def foldr_with_index {α : Type u} {β : Type v} (f : ℕ → α → β → β) (b : β) (l : List α) : β :=
  foldr_with_index_aux f 0 b l

/-- `find_indexes p l` is the list of indexes of elements of `l` that satisfy `p`. -/
def find_indexes {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : List ℕ :=
  foldr_with_index (fun (i : ℕ) (a : α) (is : List ℕ) => ite (p a) (i :: is) is) [] l

/-- Returns the elements of `l` that satisfy `p` together with their indexes in
`l`. The returned list is ordered by index. -/
def indexes_values {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) : List (ℕ × α) :=
  foldr_with_index (fun (i : ℕ) (a : α) (l : List (ℕ × α)) => ite (p a) ((i, a) :: l) l) [] l

/-- `indexes_of a l` is the list of all indexes of `a` in `l`. For example:
```
indexes_of a [a, b, a, a] = [0, 2, 3]
```
-/
def indexes_of {α : Type u} [DecidableEq α] (a : α) : List α → List ℕ :=
  find_indexes (Eq a)

/-- Monadic variant of `foldl_with_index`. -/
def mfoldl_with_index {m : Type v → Type w} [Monad m] {α : Type u_1} {β : Type v} (f : ℕ → β → α → m β) (b : β) (as : List α) : m β :=
  foldl_with_index
    (fun (i : ℕ) (ma : m β) (b : α) =>
      do 
        let a ← ma 
        f i a b)
    (pure b) as

/-- Monadic variant of `foldr_with_index`. -/
def mfoldr_with_index {m : Type v → Type w} [Monad m] {α : Type u_1} {β : Type v} (f : ℕ → α → β → m β) (b : β) (as : List α) : m β :=
  foldr_with_index
    (fun (i : ℕ) (a : α) (mb : m β) =>
      do 
        let b ← mb 
        f i a b)
    (pure b) as

/-- Auxiliary definition for `mmap_with_index`. -/
def mmap_with_index_aux {m : Type v → Type w} [Applicative m] {α : Type u_1} {β : Type v} (f : ℕ → α → m β) : ℕ → List α → m (List β) :=
  sorry

/-- Applicative variant of `map_with_index`. -/
def mmap_with_index {m : Type v → Type w} [Applicative m] {α : Type u_1} {β : Type v} (f : ℕ → α → m β) (as : List α) : m (List β) :=
  mmap_with_index_aux f 0 as

/-- Auxiliary definition for `mmap_with_index'`. -/
def mmap_with_index'_aux {m : Type v → Type w} [Applicative m] {α : Type u_1} (f : ℕ → α → m PUnit) : ℕ → List α → m PUnit :=
  sorry

/-- A variant of `mmap_with_index` specialised to applicative actions which
return `unit`. -/
def mmap_with_index' {m : Type v → Type w} [Applicative m] {α : Type u_1} (f : ℕ → α → m PUnit) (as : List α) : m PUnit :=
  mmap_with_index'_aux f 0 as

/-- `lookmap` is a combination of `lookup` and `filter_map`.
  `lookmap f l` will apply `f : α → option α` to each element of the list,
  replacing `a → b` at the first value `a` in the list such that `f a = some b`. -/
def lookmap {α : Type u} (f : α → Option α) : List α → List α :=
  sorry

/-- `countp p l` is the number of elements of `l` that satisfy `p`. -/
def countp {α : Type u} (p : α → Prop) [decidable_pred p] : List α → ℕ :=
  sorry

/-- `count a l` is the number of occurrences of `a` in `l`. -/
def count {α : Type u} [DecidableEq α] (a : α) : List α → ℕ :=
  countp (Eq a)

/-- `is_prefix l₁ l₂`, or `l₁ <+: l₂`, means that `l₁` is a prefix of `l₂`,
  that is, `l₂` has the form `l₁ ++ t` for some `t`. -/
def is_prefix {α : Type u} (l₁ : List α) (l₂ : List α) :=
  ∃ (t : List α), l₁ ++ t = l₂

/-- `is_suffix l₁ l₂`, or `l₁ <:+ l₂`, means that `l₁` is a suffix of `l₂`,
  that is, `l₂` has the form `t ++ l₁` for some `t`. -/
def is_suffix {α : Type u} (l₁ : List α) (l₂ : List α) :=
  ∃ (t : List α), t ++ l₁ = l₂

/-- `is_infix l₁ l₂`, or `l₁ <:+: l₂`, means that `l₁` is a contiguous
  substring of `l₂`, that is, `l₂` has the form `s ++ l₁ ++ t` for some `s, t`. -/
def is_infix {α : Type u} (l₁ : List α) (l₂ : List α) :=
  ∃ (s : List α), ∃ (t : List α), s ++ l₁ ++ t = l₂

infixl:50 " <+: " => Mathlib.list.is_prefix

infixl:50 " <:+ " => Mathlib.list.is_suffix

infixl:50 " <:+: " => Mathlib.list.is_infix

/-- `inits l` is the list of initial segments of `l`.

     inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]] -/
@[simp] def inits {α : Type u} : List α → List (List α) :=
  sorry

/-- `tails l` is the list of terminal segments of `l`.

     tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []] -/
@[simp] def tails {α : Type u} : List α → List (List α) :=
  sorry

def sublists'_aux {α : Type u} {β : Type v} : List α → (List α → List β) → List (List β) → List (List β) :=
  sorry

/-- `sublists' l` is the list of all (non-contiguous) sublists of `l`.
  It differs from `sublists` only in the order of appearance of the sublists;
  `sublists'` uses the first element of the list as the MSB,
  `sublists` uses the first element of the list as the LSB.

     sublists' [1, 2, 3] = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] -/
def sublists' {α : Type u} (l : List α) : List (List α) :=
  sublists'_aux l id []

def sublists_aux {α : Type u} {β : Type v} : List α → (List α → List β → List β) → List β :=
  sorry

/-- `sublists l` is the list of all (non-contiguous) sublists of `l`; cf. `sublists'`
  for a different ordering.

     sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]] -/
def sublists {α : Type u} (l : List α) : List (List α) :=
  [] :: sublists_aux l List.cons

def sublists_aux₁ {α : Type u} {β : Type v} : List α → (List α → List β) → List β :=
  sorry

/-- `forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
  and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
  then `R a b` is satisfied. -/
inductive forall₂ {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
where
| nil : forall₂ R [] []
| cons : ∀ {a : α} {b : β} {l₁ : List α} {l₂ : List β}, R a b → forall₂ R l₁ l₂ → forall₂ R (a :: l₁) (b :: l₂)

/-- Auxiliary definition used to define `transpose`.
  `transpose_aux l L` takes each element of `l` and appends it to the start of
  each element of `L`.

  `transpose_aux [a, b, c] [l₁, l₂, l₃] = [a::l₁, b::l₂, c::l₃]` -/
def transpose_aux {α : Type u} : List α → List (List α) → List (List α) :=
  sorry

/-- transpose of a list of lists, treated as a matrix.

     transpose [[1, 2], [3, 4], [5, 6]] = [[1, 3, 5], [2, 4, 6]] -/
def transpose {α : Type u} : List (List α) → List (List α) :=
  sorry

/-- List of all sections through a list of lists. A section
  of `[L₁, L₂, ..., Lₙ]` is a list whose first element comes from
  `L₁`, whose second element comes from `L₂`, and so on. -/
def sections {α : Type u} : List (List α) → List (List α) :=
  sorry

def permutations_aux2 {α : Type u} {β : Type v} (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β :=
  sorry

def permutations_aux.rec {α : Type u} {C : List α → List α → Sort v} (H0 : (is : List α) → C [] is) (H1 : (t : α) → (ts is : List α) → C ts (t :: is) → C is [] → C (t :: ts) is) (l₁ : List α) (l₂ : List α) : C l₁ l₂ :=
  sorry

def permutations_aux {α : Type u} : List α → List α → List (List α) :=
  sorry

/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations {α : Type u} (l : List α) : List (List α) :=
  l :: permutations_aux l []

/-- `erasep p l` removes the first element of `l` satisfying the predicate `p`. -/
def erasep {α : Type u} (p : α → Prop) [decidable_pred p] : List α → List α :=
  sorry

/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
def extractp {α : Type u} (p : α → Prop) [decidable_pred p] : List α → Option α × List α :=
  sorry

/-- `revzip l` returns a list of pairs of the elements of `l` paired
  with the elements of `l` in reverse order.

`revzip [1,2,3,4,5] = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]`
 -/
def revzip {α : Type u} (l : List α) : List (α × α) :=
  zip l (reverse l)

/-- `product l₁ l₂` is the list of pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂`.

     product [1, 2] [5, 6] = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
def product {α : Type u} {β : Type v} (l₁ : List α) (l₂ : List β) : List (α × β) :=
  list.bind l₁ fun (a : α) => map (Prod.mk a) l₂

/-- `sigma l₁ l₂` is the list of dependent pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂ a`.

     sigma [1, 2] (λ_, [(5 : ℕ), 6]) = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
protected def sigma {α : Type u} {σ : α → Type u_1} (l₁ : List α) (l₂ : (a : α) → List (σ a)) : List (sigma fun (a : α) => σ a) :=
  list.bind l₁ fun (a : α) => map (sigma.mk a) (l₂ a)

/-- Auxliary definition used to define `of_fn`.

  `of_fn_aux f m h l` returns the first `m` elements of `of_fn f`
  appended to `l` -/
def of_fn_aux {α : Type u} {n : ℕ} (f : fin n → α) (m : ℕ) : m ≤ n → List α → List α :=
  sorry

/-- `of_fn f` with `f : fin n → α` returns the list whose ith element is `f i`
  `of_fun f = [f 0, f 1, ... , f(n - 1)]` -/
def of_fn {α : Type u} {n : ℕ} (f : fin n → α) : List α :=
  of_fn_aux f n sorry []

/-- `of_fn_nth_val f i` returns `some (f i)` if `i < n` and `none` otherwise. -/
def of_fn_nth_val {α : Type u} {n : ℕ} (f : fin n → α) (i : ℕ) : Option α :=
  dite (i < n) (fun (h : i < n) => some (f { val := i, property := h })) fun (h : ¬i < n) => none

/-- `disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common. -/
def disjoint {α : Type u} (l₁ : List α) (l₂ : List α) :=
  ∀ {a : α}, a ∈ l₁ → a ∈ l₂ → False

/-- `pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.

     pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3

  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive pairwise {α : Type u} (R : α → α → Prop) : List α → Prop
where
| nil : pairwise R []
| cons : ∀ {a : α} {l : List α}, (∀ (a' : α), a' ∈ l → R a a') → pairwise R l → pairwise R (a :: l)

@[simp] theorem pairwise_cons {α : Type u} {R : α → α → Prop} {a : α} {l : List α} : pairwise R (a :: l) ↔ (∀ (a' : α), a' ∈ l → R a a') ∧ pairwise R l := sorry

protected instance decidable_pairwise {α : Type u} {R : α → α → Prop} [DecidableRel R] (l : List α) : Decidable (pairwise R l) :=
  List.rec (is_true pairwise.nil)
    (fun (hd : α) (tl : List α) (ih : Decidable (pairwise R tl)) =>
      decidable_of_iff' ((∀ (a' : α), a' ∈ tl → R hd a') ∧ pairwise R tl) pairwise_cons)
    l

/-- `pw_filter R l` is a maximal sublist of `l` which is `pairwise R`.
  `pw_filter (≠)` is the erase duplicates function (cf. `erase_dup`), and `pw_filter (<)` finds
  a maximal increasing subsequence in `l`. For example,

     pw_filter (<) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4] -/
def pw_filter {α : Type u} (R : α → α → Prop) [DecidableRel R] : List α → List α :=
  sorry

/-- `chain R a l` means that `R` holds between adjacent elements of `a::l`.

     chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
inductive chain {α : Type u} (R : α → α → Prop) : α → List α → Prop
where
| nil : ∀ {a : α}, chain R a []
| cons : ∀ {a b : α} {l : List α}, R a b → chain R b l → chain R a (b :: l)

/-- `chain' R l` means that `R` holds between adjacent elements of `l`.

     chain' R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
def chain' {α : Type u} (R : α → α → Prop) : List α → Prop :=
  sorry

@[simp] theorem chain_cons {α : Type u} {R : α → α → Prop} {a : α} {b : α} {l : List α} : chain R a (b :: l) ↔ R a b ∧ chain R b l := sorry

protected instance decidable_chain {α : Type u} {R : α → α → Prop} [DecidableRel R] (a : α) (l : List α) : Decidable (chain R a l) :=
  List.rec (fun (a : α) => eq.mpr sorry decidable.true)
    (fun (l_hd : α) (l_tl : List α) (l_ih : (a : α) → Decidable (chain R a l_tl)) (a : α) => eq.mpr sorry and.decidable) l
    a

protected instance decidable_chain' {α : Type u} {R : α → α → Prop} [DecidableRel R] (l : List α) : Decidable (chain' R l) :=
  list.cases_on l (id decidable.true) fun (l_hd : α) (l_tl : List α) => id (list.decidable_chain l_hd l_tl)

/-- `nodup l` means that `l` has no duplicates, that is, any element appears at most
  once in the list. It is defined as `pairwise (≠)`. -/
def nodup {α : Type u} : List α → Prop :=
  pairwise ne

protected instance nodup_decidable {α : Type u} [DecidableEq α] (l : List α) : Decidable (nodup l) :=
  list.decidable_pairwise

/-- `erase_dup l` removes duplicates from `l` (taking only the first occurrence).
  Defined as `pw_filter (≠)`.

     erase_dup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def erase_dup {α : Type u} [DecidableEq α] : List α → List α :=
  pw_filter ne

/-- `range' s n` is the list of numbers `[s, s+1, ..., s+n-1]`.
  It is intended mainly for proving properties of `range` and `iota`. -/
@[simp] def range' : ℕ → ℕ → List ℕ :=
  sorry

/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
def reduce_option {α : Type u_1} : List (Option α) → List α :=
  filter_map id

/-- `ilast' x xs` returns the last element of `xs` if `xs` is non-empty;
it returns `x` otherwise -/
@[simp] def ilast' {α : Type u_1} : α → List α → α :=
  sorry

/-- `last' xs` returns the last element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp] def last' {α : Type u_1} : List α → Option α :=
  sorry

/-- `rotate l n` rotates the elements of `l` to the left by `n`

     rotate [0, 1, 2, 3, 4, 5] 2 = [2, 3, 4, 5, 0, 1] -/
def rotate {α : Type u} (l : List α) (n : ℕ) : List α :=
  sorry

/-- rotate' is the same as `rotate`, but slower. Used for proofs about `rotate`-/
def rotate' {α : Type u} : List α → ℕ → List α :=
  sorry

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
def choose_x {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) (hp : ∃ (a : α), a ∈ l ∧ p a) : Subtype fun (a : α) => a ∈ l ∧ p a :=
  sorry

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns `a : α`, and properties
are given by `choose_mem` and `choose_property`. -/
def choose {α : Type u} (p : α → Prop) [decidable_pred p] (l : List α) (hp : ∃ (a : α), a ∈ l ∧ p a) : α :=
  ↑(choose_x p l hp)

/-- Filters and maps elements of a list -/
def mmap_filter {m : Type → Type v} [Monad m] {α : Type u_1} {β : Type} (f : α → m (Option β)) : List α → m (List β) :=
  sorry

/--
`mmap_upper_triangle f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap_upper_triangle f l` will produce the list
`[f 1 1, f 1 2, f 1 3, f 2 2, f 2 3, f 3 3]`.
-/
def mmap_upper_triangle {m : Type u → Type u_1} [Monad m] {α : Type u} {β : Type u} (f : α → α → m β) : List α → m (List β) :=
  sorry

/--
`mmap'_diag f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap'_diag f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
def mmap'_diag {m : Type → Type u_1} [Monad m] {α : Type u_2} (f : α → α → m Unit) : List α → m Unit :=
  sorry

protected def traverse {F : Type u → Type v} [Applicative F] {α : Type u_1} {β : Type u} (f : α → F β) : List α → F (List β) :=
  sorry

/-- `get_rest l l₁` returns `some l₂` if `l = l₁ ++ l₂`.
  If `l₁` is not a prefix of `l`, returns `none` -/
def get_rest {α : Type u} [DecidableEq α] : List α → List α → Option (List α) :=
  sorry

/--
`list.slice n m xs` removes a slice of length `m` at index `n` in list `xs`.
-/
def slice {α : Type u_1} : ℕ → ℕ → List α → List α :=
  sorry

/--
Left-biased version of `list.map₂`. `map₂_left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.

```
map₂_left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

map₂_left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp] def map₂_left' {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β → γ) : List α → List β → List γ × List β :=
  sorry

/--
Right-biased version of `list.map₂`. `map₂_right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.

```
map₂_right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

map₂_right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂_right' {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂_left' (flip f) bs as

/--
Left-biased version of `list.zip`. `zip_left' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`. Also returns the remaining `bs`.

```
zip_left' [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

zip_left' [1] ['a', 'b'] = ([(1, some 'a')], ['b'])

zip_left' = map₂_left' prod.mk

```
-/
def zip_left' {α : Type u} {β : Type v} : List α → List β → List (α × Option β) × List β :=
  map₂_left' Prod.mk

/--
Right-biased version of `list.zip`. `zip_right' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`. Also returns the remaining `as`.

```
zip_right' [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

zip_right' [1, 2] ['a'] = ([(some 1, 'a')], [2])

zip_right' = map₂_right' prod.mk
```
-/
def zip_right' {α : Type u} {β : Type v} : List α → List β → List (Option α × β) × List α :=
  map₂_right' Prod.mk

/--
Left-biased version of `list.map₂`. `map₂_left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂_left prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂_left prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂_left f as bs = (map₂_left' f as bs).fst
```
-/
@[simp] def map₂_left {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β → γ) : List α → List β → List γ :=
  sorry

/--
Right-biased version of `list.map₂`. `map₂_right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂_right prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂_right prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂_right f as bs = (map₂_right' f as bs).fst
```
-/
def map₂_right {α : Type u} {β : Type v} {γ : Type w} (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂_left (flip f) bs as

/--
Left-biased version of `list.zip`. `zip_left as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`.

```
zip_left [1, 2] ['a'] = [(1, some 'a'), (2, none)]

zip_left [1] ['a', 'b'] = [(1, some 'a')]

zip_left = map₂_left prod.mk
```
-/
def zip_left {α : Type u} {β : Type v} : List α → List β → List (α × Option β) :=
  map₂_left Prod.mk

/--
Right-biased version of `list.zip`. `zip_right as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`.

```
zip_right [1, 2] ['a'] = [(some 1, 'a')]

zip_right [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

zip_right = map₂_right prod.mk
```
-/
def zip_right {α : Type u} {β : Type v} : List α → List β → List (Option α × β) :=
  map₂_right Prod.mk

/--
If all elements of `xs` are `some xᵢ`, `all_some xs` returns the `xᵢ`. Otherwise
it returns `none`.

```
all_some [some 1, some 2] = some [1, 2]
all_some [some 1, none  ] = none
```
-/
def all_some {α : Type u} : List (Option α) → Option (List α) :=
  sorry

/--
`fill_nones xs ys` replaces the `none`s in `xs` with elements of `ys`. If there
are not enough `ys` to replace all the `none`s, the remaining `none`s are
dropped from `xs`.

```
fill_nones [none, some 1, none, none] [2, 3] = [2, 1, 3]
```
-/
def fill_nones {α : Type u_1} : List (Option α) → List α → List α :=
  sorry

/--
`take_list as ns` extracts successive sublists from `as`. For `ns = n₁ ... nₘ`,
it first takes the `n₁` initial elements from `as`, then the next `n₂` ones,
etc. It returns the sublists of `as` -- one for each `nᵢ` -- and the remaining
elements of `as`. If `as` does not have at least as many elements as the sum of
the `nᵢ`, the corresponding sublists will have less than `nᵢ` elements.

```
take_list ['a', 'b', 'c', 'd', 'e'] [2, 1, 1] = ([['a', 'b'], ['c'], ['d']], ['e'])
take_list ['a', 'b'] [3, 1] = ([['a', 'b'], []], [])
```
-/
def take_list {α : Type u_1} : List α → List ℕ → List (List α) × List α :=
  sorry

/--
`to_rbmap as` is the map that associates each index `i` of `as` with the
corresponding element of `as`.

```
to_rbmap ['a', 'b', 'c'] = rbmap_of [(0, 'a'), (1, 'b'), (2, 'c')]
```
-/
def to_rbmap {α : Type u} : List α → rbmap ℕ α :=
  foldl_with_index (fun (i : ℕ) (mapp : rbmap ℕ α) (a : α) => rbmap.insert mapp i a) (mk_rbmap ℕ α)

