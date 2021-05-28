/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import PrePort
import Lean3Lib.init.default
import Mathlib.combinatorics.composition
import Mathlib.data.nat.parity
import Mathlib.tactic.apply_fun
import PostPort

universes l 

namespace Mathlib

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
structure partition (n : ℕ) 
where
  parts : multiset ℕ
  parts_pos : ∀ {i : ℕ}, i ∈ parts → 0 < i
  parts_sum : multiset.sum parts = n

namespace partition


/-- A composition induces a partition (just convert the list to a multiset). -/
def of_composition (n : ℕ) (c : composition n) : partition n :=
  mk ↑(composition.blocks c) sorry sorry

theorem of_composition_surj {n : ℕ} : function.surjective (of_composition n) := sorry

/--
Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the

-- proof obligation `l.sum = n`.

def of_sums (n : ℕ) (l : multiset ℕ) (hl : multiset.sum l = n) : partition n :=
  mk (multiset.filter (fun (_x : ℕ) => _x ≠ 0) l) sorry sorry

/-- A `multiset ℕ` induces a partition on its sum. -/
def of_multiset (l : multiset ℕ) : partition (multiset.sum l) :=
  of_sums (multiset.sum l) l sorry

/-- The partition of exactly one part. -/
def indiscrete_partition (n : ℕ) : partition n :=
  of_sums n (singleton n) sorry

protected instance inhabited {n : ℕ} : Inhabited (partition n) :=
  { default := indiscrete_partition n }

/--
The number of times a positive integer `i` appears in the partition `of_sums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `partition.non_zero` combined with `multiset.count_eq_zero_of_not_mem` gives that
this is `0` instead.)
-/
theorem count_of_sums_of_ne_zero {n : ℕ} {l : multiset ℕ} (hl : multiset.sum l = n) {i : ℕ} (hi : i ≠ 0) : multiset.count i (parts (of_sums n l hl)) = multiset.count i l :=
  multiset.count_filter_of_pos hi

theorem count_of_sums_zero {n : ℕ} {l : multiset ℕ} (hl : multiset.sum l = n) : multiset.count 0 (parts (of_sums n l hl)) = 0 :=
  multiset.count_filter_of_neg fun (h : 0 ≠ 0) => h rfl

/--
Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
protected instance fintype (n : ℕ) : fintype (partition n) :=
  fintype.of_surjective (of_composition n) of_composition_surj

/-- The finset of those partitions in which every part is odd. -/
def odds (n : ℕ) : finset (partition n) :=
  finset.filter (fun (c : partition n) => ∀ (i : ℕ), i ∈ parts c → ¬even i) finset.univ

/-- The finset of those partitions in which each part is used at most once. -/
def distincts (n : ℕ) : finset (partition n) :=
  finset.filter (fun (c : partition n) => multiset.nodup (parts c)) finset.univ

/-- The finset of those partitions in which every part is odd and used at most once. -/
def odd_distincts (n : ℕ) : finset (partition n) :=
  odds n ∩ distincts n

