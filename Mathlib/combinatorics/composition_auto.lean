/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.data.fintype.card
import Mathlib.data.finset.sort
import Mathlib.tactic.omega.default
import Mathlib.algebra.big_operators.order
import PostPort

universes l u_1 

namespace Mathlib

/-!
# Compositions

A composition of a natural number `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum
of positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : composition n` is a structure, made of a list of integers which are all positive and
  add up to `n`.
* `composition_card` states that the cardinality of `composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `composition_as_set n` (see below), which
  is itself in bijection with the subsets of `fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : composition n` be a composition of `n`. Then
* `c.blocks` is the list of blocks in `c`.
* `c.length` is the number of blocks in the composition.
* `c.blocks_fun : fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.size_up_to : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : fin (c.blocks_fun i) → fin n` is the increasing embedding of the `i`-th block in
  `fin n`;
* `c.index j`, for `j : fin n`, is the index of the block containing `j`.

* `composition.ones n` is the composition of `n` made of ones, i.e., `[1, ..., 1]`.
* `composition.single n (hn : 0 < n)` is the composition of `n` made of a single block of size `n`.

Compositions can also be used to split lists. Let `l` be a list of length `n` and `c` a composition
of `n`.
* `l.split_wrt_composition c` is a list of lists, made of the slices of `l` corresponding to the
  blocks of `c`.
* `join_split_wrt_composition` states that splitting a list and then joining it gives back the
  original list.
* `split_wrt_composition_join` states that joining a list of lists, and then splitting it back
  according to the right composition, gives back the original list of lists.

We turn to the second viewpoint on compositions, that we realize as a finset of `fin (n+1)`.
`c : composition_as_set n` is a structure made of a finset of `fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `composition n` and `composition_as_set n`. We
only construct basic API on `composition_as_set` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `composition_equiv n`. Since there is a straightforward equiv
between `composition_as_set n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `composition_as_set` and called `composition_as_set_equiv n`), we deduce that
`composition_as_set n` and `composition n` are both fintypes of cardinality `2^(n - 1)`
(see `composition_as_set_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/

/-- A composition of `n` is a list of positive integers summing to `n`. -/
structure composition (n : ℕ) 
where
  blocks : List ℕ
  blocks_pos : ∀ {i : ℕ}, i ∈ blocks → 0 < i
  blocks_sum : list.sum blocks = n

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`composition_as_set n`. -/
structure composition_as_set (n : ℕ) 
where
  boundaries : finset (fin (Nat.succ n))
  zero_mem : 0 ∈ boundaries
  last_mem : fin.last n ∈ boundaries

protected instance composition_as_set.inhabited {n : ℕ} : Inhabited (composition_as_set n) :=
  { default := composition_as_set.mk finset.univ sorry sorry }

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/

namespace composition


protected instance has_to_string (n : ℕ) : has_to_string (composition n) :=
  has_to_string.mk fun (c : composition n) => to_string (blocks c)

/-- The length of a composition, i.e., the number of blocks in the composition. -/
def length {n : ℕ} (c : composition n) : ℕ :=
  list.length (blocks c)

theorem blocks_length {n : ℕ} (c : composition n) : list.length (blocks c) = length c :=
  rfl

/-- The blocks of a composition, seen as a function on `fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocks_fun {n : ℕ} (c : composition n) : fin (length c) → ℕ :=
  fun (i : fin (length c)) => list.nth_le (blocks c) ↑i sorry

theorem of_fn_blocks_fun {n : ℕ} (c : composition n) : list.of_fn (blocks_fun c) = blocks c :=
  list.of_fn_nth_le (blocks c)

theorem sum_blocks_fun {n : ℕ} (c : composition n) : (finset.sum finset.univ fun (i : fin (length c)) => blocks_fun c i) = n := sorry

theorem blocks_fun_mem_blocks {n : ℕ} (c : composition n) (i : fin (length c)) : blocks_fun c i ∈ blocks c :=
  list.nth_le_mem (blocks c) (↑i) (blocks_fun._proof_1 c i)

@[simp] theorem one_le_blocks {n : ℕ} (c : composition n) {i : ℕ} (h : i ∈ blocks c) : 1 ≤ i :=
  blocks_pos c h

@[simp] theorem one_le_blocks' {n : ℕ} (c : composition n) {i : ℕ} (h : i < length c) : 1 ≤ list.nth_le (blocks c) i h :=
  one_le_blocks c (list.nth_le_mem (blocks c) i h)

@[simp] theorem blocks_pos' {n : ℕ} (c : composition n) (i : ℕ) (h : i < length c) : 0 < list.nth_le (blocks c) i h :=
  one_le_blocks' c h

theorem one_le_blocks_fun {n : ℕ} (c : composition n) (i : fin (length c)) : 1 ≤ blocks_fun c i :=
  one_le_blocks c (blocks_fun_mem_blocks c i)

theorem length_le {n : ℕ} (c : composition n) : length c ≤ n := sorry

theorem length_pos_of_pos {n : ℕ} (c : composition n) (h : 0 < n) : 0 < length c := sorry

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def size_up_to {n : ℕ} (c : composition n) (i : ℕ) : ℕ :=
  list.sum (list.take i (blocks c))

@[simp] theorem size_up_to_zero {n : ℕ} (c : composition n) : size_up_to c 0 = 0 := sorry

theorem size_up_to_of_length_le {n : ℕ} (c : composition n) (i : ℕ) (h : length c ≤ i) : size_up_to c i = n := sorry

@[simp] theorem size_up_to_length {n : ℕ} (c : composition n) : size_up_to c (length c) = n :=
  size_up_to_of_length_le c (length c) (le_refl (length c))

theorem size_up_to_le {n : ℕ} (c : composition n) (i : ℕ) : size_up_to c i ≤ n := sorry

theorem size_up_to_succ {n : ℕ} (c : composition n) {i : ℕ} (h : i < length c) : size_up_to c (i + 1) = size_up_to c i + list.nth_le (blocks c) i h := sorry

theorem size_up_to_succ' {n : ℕ} (c : composition n) (i : fin (length c)) : size_up_to c (↑i + 1) = size_up_to c ↑i + blocks_fun c i :=
  size_up_to_succ c (subtype.property i)

theorem size_up_to_strict_mono {n : ℕ} (c : composition n) {i : ℕ} (h : i < length c) : size_up_to c i < size_up_to c (i + 1) := sorry

theorem monotone_size_up_to {n : ℕ} (c : composition n) : monotone (size_up_to c) :=
  list.monotone_sum_take (blocks c)

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundary {n : ℕ} (c : composition n) : fin (length c + 1) ↪o fin (n + 1) :=
  order_embedding.of_strict_mono (fun (i : fin (length c + 1)) => { val := size_up_to c ↑i, property := sorry }) sorry

@[simp] theorem boundary_zero {n : ℕ} (c : composition n) : coe_fn (boundary c) 0 = 0 := sorry

@[simp] theorem boundary_last {n : ℕ} (c : composition n) : coe_fn (boundary c) (fin.last (length c)) = fin.last n := sorry

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundaries {n : ℕ} (c : composition n) : finset (fin (n + 1)) :=
  finset.map (rel_embedding.to_embedding (boundary c)) finset.univ

theorem card_boundaries_eq_succ_length {n : ℕ} (c : composition n) : finset.card (boundaries c) = length c + 1 := sorry

/-- To `c : composition n`, one can associate a `composition_as_set n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def to_composition_as_set {n : ℕ} (c : composition n) : composition_as_set n :=
  composition_as_set.mk (boundaries c) sorry sorry

/-- The canonical increasing bijection between `fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
theorem order_emb_of_fin_boundaries {n : ℕ} (c : composition n) : finset.order_emb_of_fin (boundaries c) (card_boundaries_eq_succ_length c) = boundary c := sorry

/-- Embedding the `i`-th block of a composition (identified with `fin (c.blocks_fun i)`) into
`fin n` at the relevant position. -/
def embedding {n : ℕ} (c : composition n) (i : fin (length c)) : fin (blocks_fun c i) ↪o fin n :=
  rel_embedding.trans (fin.nat_add (size_up_to c ↑i)) (fin.cast_le sorry)

@[simp] theorem coe_embedding {n : ℕ} (c : composition n) (i : fin (length c)) (j : fin (blocks_fun c i)) : ↑(coe_fn (embedding c i) j) = size_up_to c ↑i + ↑j :=
  rfl

/--
`index_exists` asserts there is some `i` with `j < c.size_up_to (i+1)`.
In the next definition `index` we use `nat.find` to produce the minimal such index.
-/
theorem index_exists {n : ℕ} (c : composition n) {j : ℕ} (h : j < n) : ∃ (i : ℕ), j < size_up_to c (Nat.succ i) ∧ i < length c := sorry

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index {n : ℕ} (c : composition n) (j : fin n) : fin (length c) :=
  { val := nat.find sorry, property := sorry }

theorem lt_size_up_to_index_succ {n : ℕ} (c : composition n) (j : fin n) : ↑j < size_up_to c ↑(fin.succ (index c j)) :=
  and.left (nat.find_spec (index_exists c (subtype.property j)))

theorem size_up_to_index_le {n : ℕ} (c : composition n) (j : fin n) : size_up_to c ↑(index c j) ≤ ↑j := sorry

/-- Mapping an element `j` of `fin n` to the element in the block containing it, identified with
`fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def inv_embedding {n : ℕ} (c : composition n) (j : fin n) : fin (blocks_fun c (index c j)) :=
  { val := ↑j - size_up_to c ↑(index c j), property := sorry }

@[simp] theorem coe_inv_embedding {n : ℕ} (c : composition n) (j : fin n) : ↑(inv_embedding c j) = ↑j - size_up_to c ↑(index c j) :=
  rfl

theorem embedding_comp_inv {n : ℕ} (c : composition n) (j : fin n) : coe_fn (embedding c (index c j)) (inv_embedding c j) = j := sorry

theorem mem_range_embedding_iff {n : ℕ} (c : composition n) {j : fin n} {i : fin (length c)} : j ∈ set.range ⇑(embedding c i) ↔ size_up_to c ↑i ≤ ↑j ∧ ↑j < size_up_to c (Nat.succ ↑i) := sorry

/-- The embeddings of different blocks of a composition are disjoint. -/
theorem disjoint_range {n : ℕ} (c : composition n) {i₁ : fin (length c)} {i₂ : fin (length c)} (h : i₁ ≠ i₂) : disjoint (set.range ⇑(embedding c i₁)) (set.range ⇑(embedding c i₂)) := sorry

theorem mem_range_embedding {n : ℕ} (c : composition n) (j : fin n) : j ∈ set.range ⇑(embedding c (index c j)) := sorry

theorem mem_range_embedding_iff' {n : ℕ} (c : composition n) {j : fin n} {i : fin (length c)} : j ∈ set.range ⇑(embedding c i) ↔ i = index c j := sorry

theorem index_embedding {n : ℕ} (c : composition n) (i : fin (length c)) (j : fin (blocks_fun c i)) : index c (coe_fn (embedding c i) j) = i := sorry

theorem inv_embedding_comp {n : ℕ} (c : composition n) (i : fin (length c)) (j : fin (blocks_fun c i)) : ↑(inv_embedding c (coe_fn (embedding c i) j)) = ↑j := sorry

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`fin (c.blocks_fun i)`) with `fin n`. -/
def blocks_fin_equiv {n : ℕ} (c : composition n) : (sigma fun (i : fin (length c)) => fin (blocks_fun c i)) ≃ fin n :=
  equiv.mk
    (fun (x : sigma fun (i : fin (length c)) => fin (blocks_fun c i)) => coe_fn (embedding c (sigma.fst x)) (sigma.snd x))
    (fun (j : fin n) => sigma.mk (index c j) (inv_embedding c j)) sorry sorry

theorem blocks_fun_congr {n₁ : ℕ} {n₂ : ℕ} (c₁ : composition n₁) (c₂ : composition n₂) (i₁ : fin (length c₁)) (i₂ : fin (length c₂)) (hn : n₁ = n₂) (hc : blocks c₁ = blocks c₂) (hi : ↑i₁ = ↑i₂) : blocks_fun c₁ i₁ = blocks_fun c₂ i₂ := sorry

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
theorem sigma_eq_iff_blocks_eq {c : sigma fun (n : ℕ) => composition n} {c' : sigma fun (n : ℕ) => composition n} : c = c' ↔ blocks (sigma.snd c) = blocks (sigma.snd c') := sorry

/-! ### The composition `composition.ones` -/

/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : composition n :=
  mk (list.repeat 1 n) sorry sorry

protected instance inhabited {n : ℕ} : Inhabited (composition n) :=
  { default := ones n }

@[simp] theorem ones_length (n : ℕ) : length (ones n) = n :=
  list.length_repeat 1 n

@[simp] theorem ones_blocks (n : ℕ) : blocks (ones n) = list.repeat 1 n :=
  rfl

@[simp] theorem ones_blocks_fun (n : ℕ) (i : fin (length (ones n))) : blocks_fun (ones n) i = 1 := sorry

@[simp] theorem ones_size_up_to (n : ℕ) (i : ℕ) : size_up_to (ones n) i = min i n := sorry

@[simp] theorem ones_embedding {n : ℕ} (i : fin (length (ones n))) (h : 0 < blocks_fun (ones n) i) : coe_fn (embedding (ones n) i) { val := 0, property := h } =
  { val := ↑i, property := lt_of_lt_of_le (subtype.property i) (length_le (ones n)) } := sorry

theorem eq_ones_iff {n : ℕ} {c : composition n} : c = ones n ↔ ∀ (i : ℕ), i ∈ blocks c → i = 1 := sorry

theorem ne_ones_iff {n : ℕ} {c : composition n} : c ≠ ones n ↔ ∃ (i : ℕ), ∃ (H : i ∈ blocks c), 1 < i := sorry

theorem eq_ones_iff_length {n : ℕ} {c : composition n} : c = ones n ↔ length c = n := sorry

theorem eq_ones_iff_le_length {n : ℕ} {c : composition n} : c = ones n ↔ n ≤ length c := sorry

/-! ### The composition `composition.single` -/

/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : composition n :=
  mk [n] sorry sorry

@[simp] theorem single_length {n : ℕ} (h : 0 < n) : length (single n h) = 1 :=
  rfl

@[simp] theorem single_blocks {n : ℕ} (h : 0 < n) : blocks (single n h) = [n] :=
  rfl

@[simp] theorem single_blocks_fun {n : ℕ} (h : 0 < n) (i : fin (length (single n h))) : blocks_fun (single n h) i = n := sorry

@[simp] theorem single_embedding {n : ℕ} (h : 0 < n) (i : fin n) : coe_fn (embedding (single n h) { val := 0, property := single_length h ▸ zero_lt_one }) i = i := sorry

theorem eq_single_iff_length {n : ℕ} (h : 0 < n) {c : composition n} : c = single n h ↔ length c = 1 := sorry

theorem ne_single_iff {n : ℕ} (hn : 0 < n) {c : composition n} : c ≠ single n hn ↔ ∀ (i : fin (length c)), blocks_fun c i < n := sorry

end composition


/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocks_fun 0`, ..., `c.blocks_fun (c.length-1)`. This is inverse to the
join operation.
-/

namespace list


/-- Auxiliary for `list.split_wrt_composition`. -/
def split_wrt_composition_aux {α : Type u_1} : List α → List ℕ → List (List α) :=
  sorry

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def split_wrt_composition {n : ℕ} {α : Type u_1} (l : List α) (c : composition n) : List (List α) :=
  split_wrt_composition_aux l (composition.blocks c)

theorem split_wrt_composition_aux_cons {α : Type u_1} (l : List α) (n : ℕ) (ns : List ℕ) : split_wrt_composition_aux l (n :: ns) = take n l :: split_wrt_composition_aux (drop n l) ns := sorry

theorem length_split_wrt_composition_aux {α : Type u_1} (l : List α) (ns : List ℕ) : length (split_wrt_composition_aux l ns) = length ns := sorry

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp] theorem length_split_wrt_composition {n : ℕ} {α : Type u_1} (l : List α) (c : composition n) : length (split_wrt_composition l c) = composition.length c :=
  length_split_wrt_composition_aux l (composition.blocks c)

theorem map_length_split_wrt_composition_aux {α : Type u_1} {ns : List ℕ} {l : List α} : sum ns ≤ length l → map length (split_wrt_composition_aux l ns) = ns := sorry

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
theorem map_length_split_wrt_composition {α : Type u_1} (l : List α) (c : composition (length l)) : map length (split_wrt_composition l c) = composition.blocks c :=
  map_length_split_wrt_composition_aux (le_of_eq (composition.blocks_sum c))

theorem length_pos_of_mem_split_wrt_composition {α : Type u_1} {l : List α} {l' : List α} {c : composition (length l)} (h : l' ∈ split_wrt_composition l c) : 0 < length l' := sorry

theorem sum_take_map_length_split_wrt_composition {α : Type u_1} (l : List α) (c : composition (length l)) (i : ℕ) : sum (take i (map length (split_wrt_composition l c))) = composition.size_up_to c i := sorry

theorem nth_le_split_wrt_composition_aux {α : Type u_1} (l : List α) (ns : List ℕ) {i : ℕ} (hi : i < length (split_wrt_composition_aux l ns)) : nth_le (split_wrt_composition_aux l ns) i hi = drop (sum (take i ns)) (take (sum (take (i + 1) ns)) l) := sorry

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.size_up_to i` and `c.size_up_to (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
theorem nth_le_split_wrt_composition {n : ℕ} {α : Type u_1} (l : List α) (c : composition n) {i : ℕ} (hi : i < length (split_wrt_composition l c)) : nth_le (split_wrt_composition l c) i hi = drop (composition.size_up_to c i) (take (composition.size_up_to c (i + 1)) l) :=
  nth_le_split_wrt_composition_aux l (composition.blocks c) hi

theorem join_split_wrt_composition_aux {α : Type u_1} {ns : List ℕ} {l : List α} : sum ns = length l → join (split_wrt_composition_aux l ns) = l := sorry

/-- If one splits a list along a composition, and then joins the sublists, one gets back the
original list. -/
@[simp] theorem join_split_wrt_composition {α : Type u_1} (l : List α) (c : composition (length l)) : join (split_wrt_composition l c) = l :=
  join_split_wrt_composition_aux (composition.blocks_sum c)

/-- If one joins a list of lists and then splits the join along the right composition, one gets
back the original list of lists. -/
@[simp] theorem split_wrt_composition_join {α : Type u_1} (L : List (List α)) (c : composition (length (join L))) (h : map length L = composition.blocks c) : split_wrt_composition (join L) c = L := sorry

end list


/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/

/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def composition_as_set_equiv (n : ℕ) : composition_as_set n ≃ finset (fin (n - 1)) :=
  equiv.mk
    (fun (c : composition_as_set n) =>
      set.to_finset
        (set_of fun (i : fin (n - 1)) => { val := 1 + ↑i, property := sorry } ∈ composition_as_set.boundaries c))
    (fun (s : finset (fin (n - 1))) =>
      composition_as_set.mk
        (set.to_finset
          (set_of
            fun (i : fin (Nat.succ n)) => i = 0 ∨ i = fin.last n ∨ ∃ (j : fin (n - 1)), ∃ (hj : j ∈ s), ↑i = ↑j + 1))
        sorry sorry)
    sorry sorry

protected instance composition_as_set_fintype (n : ℕ) : fintype (composition_as_set n) :=
  fintype.of_equiv (finset (fin (n - 1))) (equiv.symm (composition_as_set_equiv n))

theorem composition_as_set_card (n : ℕ) : fintype.card (composition_as_set n) = bit0 1 ^ (n - 1) := sorry

namespace composition_as_set


theorem boundaries_nonempty {n : ℕ} (c : composition_as_set n) : finset.nonempty (boundaries c) :=
  Exists.intro 0 (zero_mem c)

theorem card_boundaries_pos {n : ℕ} (c : composition_as_set n) : 0 < finset.card (boundaries c) :=
  iff.mpr finset.card_pos (boundaries_nonempty c)

/-- Number of blocks in a `composition_as_set`. -/
def length {n : ℕ} (c : composition_as_set n) : ℕ :=
  finset.card (boundaries c) - 1

theorem card_boundaries_eq_succ_length {n : ℕ} (c : composition_as_set n) : finset.card (boundaries c) = length c + 1 :=
  iff.mp (nat.sub_eq_iff_eq_add (card_boundaries_pos c)) rfl

theorem length_lt_card_boundaries {n : ℕ} (c : composition_as_set n) : length c < finset.card (boundaries c) :=
  eq.mpr (id (Eq._oldrec (Eq.refl (length c < finset.card (boundaries c))) (card_boundaries_eq_succ_length c)))
    (lt_add_one (length c))

theorem lt_length {n : ℕ} (c : composition_as_set n) (i : fin (length c)) : ↑i + 1 < finset.card (boundaries c) :=
  nat.add_lt_of_lt_sub_right (subtype.property i)

theorem lt_length' {n : ℕ} (c : composition_as_set n) (i : fin (length c)) : ↑i < finset.card (boundaries c) :=
  lt_of_le_of_lt (nat.le_succ ↑i) (lt_length c i)

/-- Canonical increasing bijection from `fin c.boundaries.card` to `c.boundaries`. -/
def boundary {n : ℕ} (c : composition_as_set n) : fin (finset.card (boundaries c)) ↪o fin (n + 1) :=
  finset.order_emb_of_fin (boundaries c) sorry

@[simp] theorem boundary_zero {n : ℕ} (c : composition_as_set n) : coe_fn (boundary c) { val := 0, property := card_boundaries_pos c } = 0 := sorry

@[simp] theorem boundary_length {n : ℕ} (c : composition_as_set n) : coe_fn (boundary c) { val := length c, property := length_lt_card_boundaries c } = fin.last n := sorry

/-- Size of the `i`-th block in a `composition_as_set`, seen as a function on `fin c.length`. -/
def blocks_fun {n : ℕ} (c : composition_as_set n) (i : fin (length c)) : ℕ :=
  ↑(coe_fn (boundary c) { val := ↑i + 1, property := lt_length c i }) -
    ↑(coe_fn (boundary c) { val := ↑i, property := lt_length' c i })

theorem blocks_fun_pos {n : ℕ} (c : composition_as_set n) (i : fin (length c)) : 0 < blocks_fun c i :=
  nat.lt_sub_left_of_add_lt
    (order_embedding.strict_mono (finset.order_emb_of_fin (boundaries c) rfl)
      (nat.lt_succ_self (subtype.val { val := ↑i, property := lt_length' c i })))

/-- List of the sizes of the blocks in a `composition_as_set`. -/
def blocks {n : ℕ} (c : composition_as_set n) : List ℕ :=
  list.of_fn (blocks_fun c)

@[simp] theorem blocks_length {n : ℕ} (c : composition_as_set n) : list.length (blocks c) = length c :=
  list.length_of_fn (blocks_fun c)

theorem blocks_partial_sum {n : ℕ} (c : composition_as_set n) {i : ℕ} (h : i < finset.card (boundaries c)) : list.sum (list.take i (blocks c)) = ↑(coe_fn (boundary c) { val := i, property := h }) := sorry

theorem mem_boundaries_iff_exists_blocks_sum_take_eq {n : ℕ} (c : composition_as_set n) {j : fin (n + 1)} : j ∈ boundaries c ↔ ∃ (i : ℕ), ∃ (H : i < finset.card (boundaries c)), list.sum (list.take i (blocks c)) = ↑j := sorry

theorem blocks_sum {n : ℕ} (c : composition_as_set n) : list.sum (blocks c) = n := sorry

/-- Associating a `composition n` to a `composition_as_set n`, by registering the sizes of the
blocks as a list of positive integers. -/
def to_composition {n : ℕ} (c : composition_as_set n) : composition n :=
  composition.mk (blocks c) sorry (blocks_sum c)

end composition_as_set


/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `composition` and a
`composition_as_set`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `composition_equiv`.
-/

@[simp] theorem composition.to_composition_as_set_length {n : ℕ} (c : composition n) : composition_as_set.length (composition.to_composition_as_set c) = composition.length c := sorry

@[simp] theorem composition_as_set.to_composition_length {n : ℕ} (c : composition_as_set n) : composition.length (composition_as_set.to_composition c) = composition_as_set.length c := sorry

@[simp] theorem composition.to_composition_as_set_blocks {n : ℕ} (c : composition n) : composition_as_set.blocks (composition.to_composition_as_set c) = composition.blocks c := sorry

@[simp] theorem composition_as_set.to_composition_blocks {n : ℕ} (c : composition_as_set n) : composition.blocks (composition_as_set.to_composition c) = composition_as_set.blocks c :=
  rfl

@[simp] theorem composition_as_set.to_composition_boundaries {n : ℕ} (c : composition_as_set n) : composition.boundaries (composition_as_set.to_composition c) = composition_as_set.boundaries c := sorry

@[simp] theorem composition.to_composition_as_set_boundaries {n : ℕ} (c : composition n) : composition_as_set.boundaries (composition.to_composition_as_set c) = composition.boundaries c :=
  rfl

/-- Equivalence between `composition n` and `composition_as_set n`. -/
def composition_equiv (n : ℕ) : composition n ≃ composition_as_set n :=
  equiv.mk (fun (c : composition n) => composition.to_composition_as_set c)
    (fun (c : composition_as_set n) => composition_as_set.to_composition c) sorry sorry

protected instance composition_fintype (n : ℕ) : fintype (composition n) :=
  fintype.of_equiv (composition_as_set n) (equiv.symm (composition_equiv n))

theorem composition_card (n : ℕ) : fintype.card (composition n) = bit0 1 ^ (n - 1) :=
  eq.mpr
    (id (Eq._oldrec (Eq.refl (fintype.card (composition n) = bit0 1 ^ (n - 1))) (Eq.symm (composition_as_set_card n))))
    (fintype.card_congr (composition_equiv n))

